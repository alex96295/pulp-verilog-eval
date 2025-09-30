#!/usr/bin/env bash
set -euo pipefail
trap 'echo "ERROR at ${BASH_SOURCE[0]}:${LINENO}: ${BASH_COMMAND}" >&2' ERR

SCRIPT_NAME="$(basename "$0")"
OUT_DIR="out"
BENCH_DIR="${OUT_DIR}/bench"
LIB_DIR="${OUT_DIR}/lib"
JSON_PATH=""
REPO_ROOT="$(pwd)"

# Defaults (match spec-gen)
PROVIDER="openai"
MODEL="gpt-4o-2024-08-06"
KEY_CFG_PATH="${REPO_ROOT}/key.cfg"
MAX_TOKEN=8192
TOKENS=60000
TEMPERATURE=0.8
TOP_P=0.95

print_help() {
  cat <<EOF
${SCRIPT_NAME} Batch wrapper for bender->morty->spec flows.

USAGE:
  ${SCRIPT_NAME} --json <config.json> [--out out/] [options]
  ${SCRIPT_NAME} --help

INPUT JSON SHAPE:
{
  "assets/common_cells": [
    ["fifo_v3", "assets/common_cells/fifo_v3.sv", "assets/common_cells/fifo_tb.sv", "bench|lib|all (optional, default all)"]
  ]
}

Each tuple is: [<top_module_name>, <rtl_file_path>, <tb_file_path>, <targets?>]
- <targets?> is optional; one of: "bench", "lib", or "all" (default "all").

OPTIONS:
  -j, --json PATH        Path to the JSON config (required)
  -o, --out DIR          Output folder (default: out)
      --provider NAME    LLM provider (default: $PROVIDER)
      --model NAME       LLM model (default: $MODEL)
      --key-cfg PATH     Path to API key config (default: $KEY_CFG_PATH)
      --max-token N      Max tokens per response (default: $MAX_TOKEN)
      --tokens N         Total token budget (default: $TOKENS)
      --temperature F    Sampling temperature (default: $TEMPERATURE)
      --top-p F          Nucleus sampling parameter (default: $TOP_P)
  -h, --help             Show this help

EOF
}

log() { printf '[%s] %s\n' "$(date +'%Y-%m-%d %H:%M:%S')" "$*"; }

sanitize_name() { local base="${1##*/}"; echo "${base%.*}" | tr -cd '[:alnum:]'; }
rtl_basename() { echo "${1##*/}"; }
tb_stem()      { local p="${1##*/}"; echo "${p%.*}"; }

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || { echo "ERROR: '$1' not found in PATH." >&2; exit 1; }
}

collapse_newlines() {
  local infile="$1"
  local outfile="${2:-$1}"   # default to in-place if no outfile given
  [[ -n "$infile" && -f "$infile" ]] || { echo "No such file: $infile" >&2; return 1; }

  # temp file in the same dir (safer mv across filesystems)
  local tmpdir
  tmpdir="$(dirname -- "$outfile")"
  local tmp
  tmp="$(mktemp -- "$tmpdir/.collapse.XXXXXX")" || return 1

  if sed -E ':a;N;$!ba;s/\n{3,}/\n\n/g' -- "$infile" > "$tmp"; then
    mv -f -- "$tmp" "$outfile"
    echo "Processed $infile -> $outfile"
  else
    rm -f -- "$tmp"
    echo "sed failed" >&2
    return 1
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -j|--json) JSON_PATH="$2"; shift 2;;
    -o|--out)  OUT_DIR="$2"; shift 2;;
    --provider) PROVIDER="$2"; shift 2;;
    --model) MODEL="$2"; shift 2;;
    --key-cfg) KEY_CFG_PATH="$2"; shift 2;;
    --max-token) MAX_TOKEN="$2"; shift 2;;
    --tokens) TOKENS="$2"; shift 2;;
    --temperature) TEMPERATURE="$2"; shift 2;;
    --top-p) TOP_P="$2"; shift 2;;
    -h|--help) print_help; exit 0;;
    *) echo "Unknown argument: $1" >&2; print_help; exit 1;;
  esac
done

[[ -n "$JSON_PATH" ]] || { echo "ERROR: --json is required." >&2; print_help; exit 1; }

need_cmd jq
need_cmd oseda
[[ -x "$REPO_ROOT/scripts/bender-wrapper" ]] || { echo "ERROR: scripts/bender-wrapper not found."; exit 1; }
[[ -x "$REPO_ROOT/scripts/spec-gen" ]] || { echo "ERROR: scripts/spec-gen not found."; exit 1; }

mkdir -p "$OUT_DIR" "$BENCH_DIR" "$LIB_DIR"

# map json: include optional 4th field 'targets' with default "all"
mapfile -t LINES < <(jq -r 'to_entries[] | .key as $sub | .value[] | [$sub, .[0], .[1], (.[2] // ""), (.[3] // "all")] | join("\u001f")' "$JSON_PATH")
(( ${#LINES[@]} > 0 )) || { echo "No work found in JSON. Exiting."; exit 0; }

echo "DEBUG: Parsed ${#LINES[@]} entries from $JSON_PATH"
for i in "${!LINES[@]}"; do
  echo "DEBUG: [${i}] ${LINES[$i]}"
done

idx=0

for line in "${LINES[@]}"; do
  IFS=$'\x1f' read -r SUBMOD TOP_NAME RTL TB TARGETS <<<"$line"
  [[ -n "$TOP_NAME" && -n "$RTL" ]] || { log "Skipping tuple with missing TOP or RTL under '$SUBMOD'."; continue; }
  [[ -d "$SUBMOD" ]] || { log "ERROR: Asset folder '$SUBMOD' does not exist."; exit 1; }

  # normalize targets ? flags
  TARGETS_LOWER="$(echo "$TARGETS" | tr '[:upper:]' '[:lower:]')"
  case "$TARGETS_LOWER" in
    bench) BENCH_ENABLED=1; LIB_ENABLED=0;;
    lib)   BENCH_ENABLED=0; LIB_ENABLED=1;;
    all|"") BENCH_ENABLED=1; LIB_ENABLED=1;;
    *) echo "ERROR: Unknown targets spec '$TARGETS' for '$TOP_NAME' (use bench|lib|all)"; exit 1;;
  esac

  echo -e "\n\nProcessing ${TOP_NAME} in ${RTL}, ${TB} from ${SUBMOD} (targets=${TARGETS_LOWER})"

  PROB_ID=$(printf "Prob%03d" "$idx")
  TOP_FILE="$(rtl_basename "$RTL")"
  TOP_BASE="${TOP_FILE%.*}"

  # TB presence flag + derived values only if TB is provided
  TB_PRESENT=0
  if [[ -n "${TB:-}" ]]; then
    TB_PRESENT=1
    TB_STEM_VAL="$(tb_stem "$TB")"
  fi

  log "Asset='$SUBMOD' TOP='$TOP_NAME'"
  log "  RTL: $RTL"
  if [[ $TB_PRESENT -eq 1 ]]; then
    log "  TB : $TB (stem: $TB_STEM_VAL)"
  else
    log "  TB : (none provided)"
  fi
  log "  Targets: bench=${BENCH_ENABLED} lib=${LIB_ENABLED}"

  # Always build RTL (needed by both bench & lib flows)
  ( cd "$SUBMOD" && "$REPO_ROOT/scripts/bender-wrapper" --top "$TOP_FILE" -t rtl )

  # Build TB/test/simulation graphs only when bench is enabled and TB is present
  if [[ $BENCH_ENABLED -eq 1 && $TB_PRESENT -eq 1 ]]; then
    ( cd "$SUBMOD" && "$REPO_ROOT/scripts/bender-wrapper" --top "$TOP_FILE" -t test -t simulation --tb-token "$TB_STEM_VAL" )
    ( cd "$SUBMOD" && "$REPO_ROOT/scripts/bender-wrapper" --top "$TOP_FILE" -t rtl -t test -t simulation --tb-token "$TB_STEM_VAL" )
  fi

  RTL_JSON="$SUBMOD/$TOP_BASE.rtl.json"

  if [[ $BENCH_ENABLED -eq 1 && $TB_PRESENT -eq 1 ]]; then
    TB_JSON="$SUBMOD/$TOP_BASE.tb.json"
    RTLTB_JSON="$SUBMOD/$TOP_BASE.rtltb.json"
  else
    TB_JSON=""; RTLTB_JSON=""
  fi

  RTL_SV_TMP="${TOP_NAME}_ref.sv"
  [[ -f "$RTL_JSON" ]] && oseda morty -f "$RTL_JSON" --strip-comments -o "$RTL_SV_TMP" || log "WARNING: Missing $RTL_JSON"

  if [[ $BENCH_ENABLED -eq 1 && $TB_PRESENT -eq 1 ]]; then
    TB_SV_TMP="${TOP_NAME}_test.sv"
    RTLTB_SV_TMP="${TOP_NAME}_test_golden.sv"
    [[ -f "$TB_JSON" ]] && oseda morty -f "$TB_JSON" --strip-comments -o "$TB_SV_TMP" || log "WARNING: Missing $TB_JSON"
    [[ -f "$RTLTB_JSON" ]] && oseda morty -f "$RTLTB_JSON" --strip-comments -o "$RTLTB_SV_TMP" || log "WARNING: Missing $RTLTB_JSON"
  else
    TB_SV_TMP=""; RTLTB_SV_TMP=""
  fi

  # trim multiple newlines created by morty
  [[ -n "$RTL_SV_TMP" && -f "$RTL_SV_TMP" ]] && collapse_newlines "$RTL_SV_TMP" "$RTL_SV_TMP" || true
  [[ -n "$TB_SV_TMP" && -f "$TB_SV_TMP" ]] && collapse_newlines "$TB_SV_TMP" "$TB_SV_TMP" || true
  [[ -n "$RTLTB_SV_TMP" && -f "$RTLTB_SV_TMP" ]] && collapse_newlines "$RTLTB_SV_TMP" "$RTLTB_SV_TMP" || true

  # Generate specification from RTL in natural language (.txt/.md) and structured (.json)
  $REPO_ROOT/scripts/spec-gen \
    --rtl "$RTL_SV_TMP" \
    --top "$TOP_NAME" \
    --provider "$PROVIDER" \
    --model "$MODEL" \
    --key-cfg "$KEY_CFG_PATH" \
    --out "$TOP_NAME.md" \
    --max-token "$MAX_TOKEN" \
    --tokens "$TOKENS" \
    --temperature "$TEMPERATURE" \
    --top-p "$TOP_P" \
    --emit "$TARGETS_LOWER"

  # Move/cull generated artifacts based on targets to final location
  rm -f "$RTL_JSON" "$SUBMOD/$TOP_BASE.rtl.full.json"
  if [[ $BENCH_ENABLED -eq 1 && $TB_PRESENT -eq 1 ]]; then
    rm -f "${TB_JSON:-}" "${RTLTB_JSON:-}" "$SUBMOD/$TOP_BASE.tb.full.json" "$SUBMOD/$TOP_BASE.rtltb.full.json"
  fi

  RTL_SV="$BENCH_DIR/${PROB_ID}_${TOP_NAME}_ref.sv"
  TB_SV="$BENCH_DIR/${PROB_ID}_${TOP_NAME}_test.sv"
  RTLTB_SV="$BENCH_DIR/${PROB_ID}_${TOP_NAME}_test_golden.sv"

  GEN_TXT="$(ls -1t "${TOP_NAME}.txt" 2>/dev/null | head -n1 || true)"
  GEN_JSON="$(ls -1t "${TOP_NAME}.json" 2>/dev/null | head -n1 || true)"

  if [[ $BENCH_ENABLED -eq 1 ]]; then
    [[ -n "$GEN_TXT" && -f "$GEN_TXT" ]] && mv "$GEN_TXT" "$BENCH_DIR/${PROB_ID}_${TOP_NAME}_prompt.txt" || log "WARNING: Could not find generated ${TOP_NAME}.txt"
    [[ -n "$RTL_SV_TMP" && -f "$RTL_SV_TMP" ]] && mv "$RTL_SV_TMP" "$RTL_SV"
    [[ -n "$TB_SV_TMP" && -f "$TB_SV_TMP" ]] && mv "$TB_SV_TMP" "$TB_SV"
    [[ -n "$RTLTB_SV_TMP" && -f "$RTLTB_SV_TMP" ]] && mv "$RTLTB_SV_TMP" "$RTLTB_SV"
  else
    [[ -n "$RTL_SV_TMP" && -f "$RTL_SV_TMP" ]] && rm -f "$RTL_SV_TMP"
    [[ -n "$TB_SV_TMP" && -f "$TB_SV_TMP" ]] && rm -f "$TB_SV_TMP"
    [[ -n "$RTLTB_SV_TMP" && -f "$RTLTB_SV_TMP" ]] && rm -f "$RTLTB_SV_TMP"
  fi

  if [[ $LIB_ENABLED -eq 1 ]]; then
    [[ -n "$GEN_JSON" && -f "$GEN_JSON" ]] && mv "$GEN_JSON" "$LIB_DIR/${TOP_NAME}.json" || log "WARNING: Could not find generated ${TOP_NAME}.json"
  else
    [[ -n "$GEN_JSON" && -f "$GEN_JSON" ]] && rm -f "$GEN_JSON" || true
  fi

  # Normalize identifiers across generated SVs
  escape_re () { printf '%s' "$1" | sed -e 's/[.[\()*^$\\]/\\&/g'; }
  TOP_NAME_RE="$(escape_re "$TOP_NAME")"

  if [[ -f "$RTL_SV" ]]; then
    perl -0777 -i -pe "s/\b${TOP_NAME_RE}\b/TopModule/g" -- "$RTL_SV"
  fi

  if [[ $BENCH_ENABLED -eq 1 && $TB_PRESENT -eq 1 ]]; then
    if [[ -n "${TB_STEM_VAL:-}" ]]; then
      TB_STEM_RE="$(escape_re "$TB_STEM_VAL")"
      if [[ -f "$TB_SV" ]]; then
	perl -0777 -i -pe "s/\b${TOP_NAME_RE}\b/TopModule/g; s/\b${TB_STEM_RE}\b/TopTestbench/g" -- "$TB_SV"
      fi
      if [[ -f "$RTLTB_SV" ]]; then
	perl -0777 -i -pe "s/\b${TOP_NAME_RE}\b/TopModule/g; s/\b${TB_STEM_RE}\b/TopTestbench/g" -- "$RTLTB_SV"
      fi
    else
      [[ -f "$TB_SV" ]] && perl -0777 -i -pe "s/\b${TOP_NAME_RE}\b/TopModule/g" -- "$TB_SV"
      [[ -f "$RTLTB_SV" ]] && perl -0777 -i -pe "s/\b${TOP_NAME_RE}\b/TopModule/g" -- "$RTLTB_SV"
    fi
  fi

  ((++idx))
done
