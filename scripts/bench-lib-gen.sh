#!/usr/bin/env bash
set -euo pipefail
trap 'echo "ERROR at ${BASH_SOURCE[0]}:${LINENO}: ${BASH_COMMAND}" >&2' ERR

SCRIPT_NAME="$(basename "$0")"
REPO_ROOT="$(pwd)"

# -------- parameter defaults (env can override) --------
: "${OUT_DIR:=out}"
BENCH_DIR="${OUT_DIR}/bench"
LIB_DIR="${OUT_DIR}/lib"
JSON_PATH="${JSON_PATH:-}"              # must be provided via CLI

: "${PROVIDER:=openai}"
: "${MODEL:=gpt-4o-2024-08-06}"
: "${KEY_CFG_PATH:=${REPO_ROOT}/key.cfg}"
: "${MAX_TOKEN:=8192}"
: "${TOKENS:=60000}"
: "${TEMPERATURE:=0.8}"
: "${TOP_P:=0.95}"

# Build a reusable args array for spec-gen
GEN_ARGS=(
  --provider    "$PROVIDER"
  --model       "$MODEL"
  --key-cfg     "$KEY_CFG_PATH"
  --max-token   "$MAX_TOKEN"
  --tokens      "$TOKENS"
  --temperature "$TEMPERATURE"
  --top-p       "$TOP_P"
)

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
  -o, --out DIR          Output folder (default: $OUT_DIR)
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

# -------- utility helpers --------
need_cmd() {
  command -v "$1" >/dev/null 2>&1 || { echo "ERROR: '$1' not found in PATH." >&2; exit 1; }
}
need_file() {
  [[ -r "$1" ]] || { echo "ERROR: required file not found/readable: $1" >&2; exit 1; }
}

# Prefer env overrides BENDER_BIN/MORTY_BIN; then repo script; then CARGO_HOME; then PATH
find_bin() {
  local name="${1:?binary name required}"
  local env_var="${name^^}_BIN"     # e.g. bender -> BENDER_BIN
  local cargo_home="${CARGO_HOME:-$HOME/.cargo}"
  local candidates=()

  # 1) explicit env override
  if [[ -n "${!env_var:-}" ]]; then candidates+=("${!env_var}"); fi
  # 2) repo script shim
  candidates+=("$REPO_ROOT/scripts/$name")
  # 3) cargo bin
  candidates+=("$cargo_home/bin/$name")
  # 4) PATH
  candidates+=("$name")

  for c in "${candidates[@]}"; do
    if [[ -x "$c" ]]; then echo "$c"; return 0; fi
    if command -v "$c" >/dev/null 2>&1; then command -v "$c"; return 0; fi
  done
  echo "ERROR: could not find executable for '$name'. Tried: ${candidates[*]}" >&2
  return 1
}

collapse_newlines() {
  local infile="$1"
  local outfile="${2:-$1}"
  [[ -f "$infile" ]] || { echo "No such file: $infile" >&2; return 1; }
  local tmpdir; tmpdir="$(dirname -- "$outfile")"
  local tmp; tmp="$(mktemp -- "$tmpdir/.collapse.XXXXXX")" || return 1
  if sed -E ':a;N;$!ba;s/\n{3,}/\n\n/g' -- "$infile" > "$tmp"; then
    mv -f -- "$tmp" "$outfile"
  else
    rm -f -- "$tmp"; echo "sed failed" >&2; return 1
  fi
}

sanitize_name() { local base="${1##*/}"; echo "${base%.*}" | tr -cd '[:alnum:]'; }
rtl_basename() { echo "${1##*/}"; }
tb_stem()      { local p="${1##*/}"; echo "${p%.*}"; }

# -------- CLI parsing --------
while [[ $# -gt 0 ]]; do
  case "$1" in
    -j|--json) JSON_PATH="$2"; shift 2;;
    -o|--out)  OUT_DIR="$2"; shift 2;;
    --provider)    PROVIDER="$2"; shift 2;;
    --model)       MODEL="$2"; shift 2;;
    --key-cfg)     KEY_CFG_PATH="$2"; shift 2;;
    --max-token)   MAX_TOKEN="$2"; shift 2;;
    --tokens)      TOKENS="$2"; shift 2;;
    --temperature) TEMPERATURE="$2"; shift 2;;
    --top-p)       TOP_P="$2"; shift 2;;
    -h|--help) print_help; exit 0;;
    *) echo "Unknown argument: $1" >&2; print_help; exit 1;;
  esac
done
# refresh GEN_ARGS in case CLI overrides changed values
GEN_ARGS=(
  --provider    "$PROVIDER"
  --model       "$MODEL"
  --key-cfg     "$KEY_CFG_PATH"
  --max-token   "$MAX_TOKEN"
  --tokens      "$TOKENS"
  --temperature "$TEMPERATURE"
  --top-p       "$TOP_P"
)

[[ -n "$JSON_PATH" ]] || { echo "ERROR: --json is required." >&2; print_help; exit 1; }

# -------- tool guardrails --------
need_cmd jq
need_cmd oseda
need_file "$KEY_CFG_PATH"

BENDER="$(find_bin bender)"
# morty is optional if you only use "oseda morty", but we try to log it if present
if MORTY="$(find_bin morty)"; then
  log "Using morty : $MORTY"
  ("$MORTY" --version || true) 2>/dev/null | sed 's/^/[morty]  /' || true
else
  log "Note: 'morty' standalone binary not found; using 'oseda morty' subcommand."
fi

log "Using bender: $BENDER"
("$BENDER" --version || true) 2>/dev/null | sed 's/^/[bender] /' || true

[[ -x "$REPO_ROOT/scripts/spec-gen" ]] || { echo "ERROR: scripts/spec-gen not found or not executable."; exit 1; }

mkdir -p "$OUT_DIR" "$BENCH_DIR" "$LIB_DIR"

# -------- load JSON worklist --------
mapfile -t LINES < <(jq -r 'to_entries[] | .key as $sub | .value[] | [$sub, .[0], .[1], (.[2] // ""), (.[3] // "all")] | join("\u001f")' "$JSON_PATH")
(( ${#LINES[@]} > 0 )) || { echo "No work found in JSON. Exiting."; exit 0; }

echo "DEBUG: Parsed ${#LINES[@]} entries from $JSON_PATH"
for i in "${!LINES[@]}"; do
  echo "DEBUG: [${i}] ${LINES[$i]}"
done

# -------- main loop --------
idx=0
for line in "${LINES[@]}"; do
  IFS=$'\x1f' read -r SUBMOD TOP_NAME RTL TB TARGETS <<<"$line"
  [[ -n "$TOP_NAME" && -n "$RTL" ]] || { log "Skipping tuple with missing TOP or RTL under '$SUBMOD'."; continue; }
  [[ -d "$SUBMOD" ]] || { log "ERROR: Asset folder '$SUBMOD' does not exist."; exit 1; }

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

  RTL_JSON="$SUBMOD/$TOP_BASE.rtl.json"
  if [[ $BENCH_ENABLED -eq 1 && $TB_PRESENT -eq 1 ]]; then
    TB_JSON="$SUBMOD/$TOP_BASE.tb.json"
    RTLTB_JSON="$SUBMOD/$TOP_BASE.rtltb.json"
  else
    TB_JSON=""; RTLTB_JSON=""
  fi

  # -------- Build graphs with bender (filtered) --------
  # RTL only
  ( cd "$SUBMOD" && "$BENDER" sources --flatten -t rtl --filter-unused --rtl-top "$TOP_BASE" > "$REPO_ROOT/$RTL_JSON" )

  # TB/test/simulation graphs only when bench is enabled and TB is present
  if [[ $BENCH_ENABLED -eq 1 && $TB_PRESENT -eq 1 ]]; then
    # TB-only (test+simulation)
    ( cd "$SUBMOD" && "$BENDER" sources --flatten -t test -t simulation --filter-unused --tb-top "$TB_STEM_VAL" > "$REPO_ROOT/$TB_JSON" )
    # RTL + TB combined (rtl+test+simulation)
    ( cd "$SUBMOD" && "$BENDER" sources --flatten -t rtl -t test -t simulation --filter-unused --rtl-top "$TOP_BASE" --tb-top "$TB_STEM_VAL" > "$REPO_ROOT/$RTLTB_JSON" )
  fi

  # -------- Morty (strip comments) --------
  RTL_SV_TMP="${TOP_NAME}_ref.sv"
  if [[ -f "$RTL_JSON" ]]; then
    oseda morty -f "$RTL_JSON" --strip-comments -o "$RTL_SV_TMP"
  else
    log "WARNING: Missing $RTL_JSON"
  fi

  if [[ $BENCH_ENABLED -eq 1 && $TB_PRESENT -eq 1 ]]; then
    TB_SV_TMP="${TOP_NAME}_test.sv"
    RTLTB_SV_TMP="${TOP_NAME}_test_golden.sv"
    if [[ -f "$TB_JSON" ]]; then
      oseda morty -f "$TB_JSON" --strip-comments -o "$TB_SV_TMP"
    else
      log "WARNING: Missing $TB_JSON"
    fi
    if [[ -f "$RTLTB_JSON" ]]; then
      oseda morty -f "$RTLTB_JSON" --strip-comments -o "$RTLTB_SV_TMP"
    else
      log "WARNING: Missing $RTLTB_JSON"
    fi
  else
    TB_SV_TMP=""; RTLTB_SV_TMP=""
  fi

  # Trim multiple newlines created by morty
  [[ -n "${RTL_SV_TMP:-}"   && -f "$RTL_SV_TMP"   ]] && collapse_newlines "$RTL_SV_TMP"   "$RTL_SV_TMP"   || true
  [[ -n "${TB_SV_TMP:-}"    && -f "$TB_SV_TMP"    ]] && collapse_newlines "$TB_SV_TMP"    "$TB_SV_TMP"    || true
  [[ -n "${RTLTB_SV_TMP:-}" && -f "$RTLTB_SV_TMP" ]] && collapse_newlines "$RTLTB_SV_TMP" "$RTLTB_SV_TMP" || true

  # -------- Generate specification (NL .md and structured .json) --------
  "$REPO_ROOT/scripts/spec-gen" \
    --rtl "$RTL_SV_TMP" \
    --top "$TOP_NAME" \
    --out "$TOP_NAME.md" \
    --emit "$TARGETS_LOWER" \
    "${GEN_ARGS[@]}"

  # -------- Clean JSONs produced for intermediate steps --------
  rm -f "$RTL_JSON" "$SUBMOD/$TOP_BASE.rtl.full.json"
  if [[ $BENCH_ENABLED -eq 1 && $TB_PRESENT -eq 1 ]]; then
    rm -f "${TB_JSON:-}" "${RTLTB_JSON:-}" "$SUBMOD/$TOP_BASE.tb.full.json" "$SUBMOD/$TOP_BASE.rtltb.full.json"
  fi

  # -------- Move generated artifacts to final locations --------
  RTL_SV="$BENCH_DIR/${PROB_ID}_${TOP_NAME}_ref.sv"
  TB_SV="$BENCH_DIR/${PROB_ID}_${TOP_NAME}_test.sv"
  RTLTB_SV="$BENCH_DIR/${PROB_ID}_${TOP_NAME}_test_golden.sv"

  GEN_TXT="$(ls -1t "${TOP_NAME}.txt" 2>/dev/null | head -n1 || true)"
  GEN_JSON="$(ls -1t "${TOP_NAME}.json" 2>/dev/null | head -n1 || true)"

  if [[ $BENCH_ENABLED -eq 1 ]]; then
    [[ -n "$GEN_TXT"  && -f "$GEN_TXT"  ]] && mv "$GEN_TXT"  "$BENCH_DIR/${PROB_ID}_${TOP_NAME}_prompt.txt" || log "WARNING: Could not find generated ${TOP_NAME}.txt"
    [[ -n "$RTL_SV_TMP"   && -f "$RTL_SV_TMP"   ]] && mv "$RTL_SV_TMP"   "$RTL_SV"
    [[ -n "$TB_SV_TMP"    && -f "$TB_SV_TMP"    ]] && mv "$TB_SV_TMP"    "$TB_SV"
    [[ -n "$RTLTB_SV_TMP" && -f "$RTLTB_SV_TMP" ]] && mv "$RTLTB_SV_TMP" "$RTLTB_SV"
  else
    [[ -n "$RTL_SV_TMP"   && -f "$RTL_SV_TMP"   ]] && rm -f "$RTL_SV_TMP"
    [[ -n "$TB_SV_TMP"    && -f "$TB_SV_TMP"    ]] && rm -f "$TB_SV_TMP"
    [[ -n "$RTLTB_SV_TMP" && -f "$RTLTB_SV_TMP" ]] && rm -f "$RTLTB_SV_TMP"
  fi

  if [[ $LIB_ENABLED -eq 1 ]]; then
    [[ -n "$GEN_JSON" && -f "$GEN_JSON" ]] && mv "$GEN_JSON" "$LIB_DIR/${TOP_NAME}.json" || log "WARNING: Could not find generated ${TOP_NAME}.json"
  else
    [[ -n "$GEN_JSON" && -f "$GEN_JSON" ]] && rm -f "$GEN_JSON" || true
  fi

  # -------- Normalize identifiers across generated SVs --------
  escape_re () { printf '%s' "$1" | sed -e 's/[.[\()*^$\\]/\\&/g'; }
  TOP_NAME_RE="$(escape_re "$TOP_NAME")"

  if [[ -f "$RTL_SV" ]]; then
    perl -0777 -i -pe "s/\b${TOP_NAME_RE}\b/TopModule/g" -- "$RTL_SV"
  fi

  if [[ $BENCH_ENABLED -eq 1 && $TB_PRESENT -eq 1 ]]; then
    if [[ -n "${TB_STEM_VAL:-}" ]]; then
      TB_STEM_RE="$(escape_re "$TB_STEM_VAL")"
      [[ -f "$TB_SV"    ]] && perl -0777 -i -pe "s/\b${TOP_NAME_RE}\b/TopModule/g; s/\b${TB_STEM_RE}\b/TopTestbench/g" -- "$TB_SV"
      [[ -f "$RTLTB_SV" ]] && perl -0777 -i -pe "s/\b${TOP_NAME_RE}\b/TopModule/g; s/\b${TB_STEM_RE}\b/TopTestbench/g" -- "$RTLTB_SV"
    else
      [[ -f "$TB_SV"    ]] && perl -0777 -i -pe "s/\b${TOP_NAME_RE}\b/TopModule/g" -- "$TB_SV"
      [[ -f "$RTLTB_SV" ]] && perl -0777 -i -pe "s/\b${TOP_NAME_RE}\b/TopModule/g" -- "$RTLTB_SV"
    fi
  fi

  ((++idx))
done
