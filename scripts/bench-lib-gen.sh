#!/usr/bin/env bash
set -euo pipefail
trap 'echo "ERROR at ${BASH_SOURCE[0]}:${LINENO}: ${BASH_COMMAND}" >&2' ERR

SCRIPT_NAME="$(basename "$0")"
OUT_DIR="out"
BENCH_DIR="${OUT_DIR}/bench"
LIB_DIR="${OUT_DIR}/lib"
DRY_RUN=0
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
    ["fifo_v3", "assets/common_cells/fifo_v3.sv", "assets/common_cells/fifo_tb.sv"]
  ]
}

(Each tuple is: [<top_module_name>, <rtl_file_path>, <tb_file_path>])

OPTIONS:
  -j, --json PATH        Path to the JSON config (required)
  -o, --out DIR          Output folder (default: out)
      --dry-run          Print actions without executing them
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

run_cmd() {
  if [[ "$DRY_RUN" -eq 1 ]]; then
    echo "DRY-RUN: $*"
  else
    eval "$@"
  fi
}

sanitize_name() { local base="${1##*/}"; echo "${base%.*}" | tr -cd '[:alnum:]'; }
rtl_basename() { echo "${1##*/}"; }
tb_stem()      { local p="${1##*/}"; echo "${p%.*}"; }

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || { echo "ERROR: '$1' not found in PATH." >&2; exit 1; }
}

run_in_dir() {
  local dir="$1"; shift
  if [[ "$DRY_RUN" -eq 1 ]]; then
    echo "DRY-RUN (in $dir): $*"
  else
    ( cd "$dir" && eval "$@" )
  fi
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -j|--json) JSON_PATH="$2"; shift 2;;
    -o|--out)  OUT_DIR="$2"; shift 2;;
    --dry-run) DRY_RUN=1; shift;;
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

run_cmd "mkdir -p \"$BENCH_DIR\" \"$LIB_DIR\""

# map json
mapfile -t LINES < <(jq -r 'to_entries[] | .key as $sub | .value[] | [$sub, .[0], .[1], (.[2] // "")] | @tsv' "$JSON_PATH")
(( ${#LINES[@]} > 0 )) || { echo "No work found in JSON. Exiting."; exit 0; }

# --- Debug: show how many lines were parsed and their content ---
echo "DEBUG: Parsed ${#LINES[@]} entries from $JSON_PATH"
for i in "${!LINES[@]}"; do
  echo "DEBUG: [${i}] ${LINES[$i]}"
done

idx=0

for line in "${LINES[@]}"; do
   
  IFS=$'\t' read -r SUBMOD TOP_NAME RTL TB <<<"$line"
  [[ -n "$TOP_NAME" && -n "$RTL" ]] || { log "Skipping tuple with missing TOP or RTL under '$SUBMOD'."; continue; }
  [[ -d "$SUBMOD" ]] || { log "ERROR: Asset folder '$SUBMOD' does not exist."; exit 1; }

  echo "Processing ${TOP_NAME} in ${RTL}, ${TB} from ${SUBMOD}"

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
    log "  TB : (none provided) running RTL-only flow"
  fi

  # Always build RTL
  run_in_dir "$SUBMOD" "\"$REPO_ROOT/scripts/bender-wrapper\" --top \"$TOP_FILE\" -t rtl"

  # Only run TB/test/simulation flows when TB is provided
  if [[ $TB_PRESENT -eq 1 ]]; then
    run_in_dir "$SUBMOD" "\"$REPO_ROOT/scripts/bender-wrapper\" --top \"$TOP_FILE\" -t test -t simulation --tb-token \"$TB_STEM_VAL\""
    run_in_dir "$SUBMOD" "\"$REPO_ROOT/scripts/bender-wrapper\" --top \"$TOP_FILE\" -t rtl -t test -t simulation --tb-token \"$TB_STEM_VAL\""
  fi

  RTL_JSON="$BENCH_DIR/$TOP_BASE.rtl.json"
  run_cmd "mv \"$SUBMOD/$TOP_BASE.rtl.json\" \"$BENCH_DIR/\" || true"

  if [[ $TB_PRESENT -eq 1 ]]; then
    TB_JSON="$BENCH_DIR/$TOP_BASE.tb.json"
    RTLTB_JSON="$BENCH_DIR/$TOP_BASE.rtltb.json"
    run_cmd "mv \"$SUBMOD/$TOP_BASE.tb.json\" \"$BENCH_DIR/\" || true"
    run_cmd "mv \"$SUBMOD/$TOP_BASE.rtltb.json\" \"$BENCH_DIR/\" || true"
  fi

  RTL_SV="$BENCH_DIR/${PROB_ID}_${TOP_NAME}_ref.sv"
  [[ -f "$RTL_JSON" ]] && run_cmd "oseda morty -f \"$RTL_JSON\" -o \"$RTL_SV\"" || log "WARNING: Missing $RTL_JSON"

  if [[ $TB_PRESENT -eq 1 ]]; then
    TB_SV="$BENCH_DIR/${PROB_ID}_${TOP_NAME}_test.sv"
    RTLTB_SV="$BENCH_DIR/${PROB_ID}_${TOP_NAME}_test_golden.sv"
    [[ -f "$TB_JSON" ]] && run_cmd "oseda morty -f \"$TB_JSON\" -o \"$TB_SV\"" || log "WARNING: Missing $TB_JSON"
    [[ -f "$RTLTB_JSON" ]] && run_cmd "oseda morty -f \"$RTLTB_JSON\" -o \"$RTLTB_SV\"" || log "WARNING: Missing $RTLTB_JSON"
  else
    TB_SV=""
    RTLTB_SV=""  
  fi

  # remove byproducts
  rm -f "$RTL_JSON" "$BENCH_DIR/$TOP_BASE.rtl.full.json"
  [[ $TB_PRESENT -eq 1 ]] && rm -f "${TB_JSON:-}" "${RTLTB_JSON:-}" "$BENCH_DIR/$TOP_BASE.tb.full.json" "$BENCH_DIR/$TOP_BASE.rtltb.full.json"

  # Generate specification from a top level (and optionally testbench) in
  # natural language (.txt, .md) and structured (.json)
  run_cmd "\"$REPO_ROOT/scripts/spec-gen\" \
    --tb \"$TB_SV\" \
    --rtl \"$RTL_SV\" \
    --top \"$TOP_NAME\" \
    --provider \"$PROVIDER\" \
    --model \"$MODEL\" \
    --key-cfg \"$KEY_CFG_PATH\" \
    --out \"$TOP_NAME.md\" \
    --max-token \"$MAX_TOKEN\" \
    --tokens \"$TOKENS\" \
    --temperature \"$TEMPERATURE\" \
    --top-p \"$TOP_P\""

  if [[ "$DRY_RUN" -eq 1 ]]; then
    echo "DRY-RUN: Would copy newest \"${TOP_NAME}.txt\" -> \"$BENCH_DIR/${PROB_ID}_${TOP_NAME}_prompt.txt\""
  else
    GEN_TXT="$(ls -1t "${TOP_NAME}.txt" 2>/dev/null | head -n1 || true)"
    GEN_JSON="$(ls -1t "${TOP_NAME}.json" 2>/dev/null | head -n1 || true)"
    [[ -n "$GEN_TXT" && -f "$GEN_TXT" ]] && run_cmd "mv \"$GEN_TXT\" \"$BENCH_DIR/${PROB_ID}_${TOP_NAME}_prompt.txt\"" || log "WARNING: Could not find generated ${TOP_NAME}.txt"
    [[ -n "$GEN_JSON" && -f "$GEN_JSON" ]] && run_cmd "mv \"$GEN_JSON\" \"$LIB_DIR/${TOP_NAME}.json\"" || log "WARNING: Could not find generated ${TOP_NAME}.json"
  fi

  # Normalize module / TB identifiers across generated benchmarks. Replace the
  # DUT module name ($TOP_NAME) with "TopModule" in all generated SVs. Replace
  # the TB stem ($TB_STEM_VAL) with "TopTestbench" in test SVs (if present).
  escape_re () { printf '%s' "$1" | sed -e 's/[.[\()*^$\\]/\\&/g'; }

  TOP_NAME_RE="$(escape_re "$TOP_NAME")"
  if [[ -f "$RTL_SV" ]]; then
    run_cmd "perl -0777 -i -pe 's/\\b${TOP_NAME_RE}\\b/TopModule/g' \"$RTL_SV\""
  fi
  if [[ $TB_PRESENT -eq 1 ]]; then
    if [[ -n "${TB_STEM_VAL:-}" ]]; then
      TB_STEM_RE="$(escape_re "$TB_STEM_VAL")"
      if [[ -f "$TB_SV" ]]; then
        # First normalize DUT name, then TB name
        run_cmd "perl -0777 -i -pe 's/\\b${TOP_NAME_RE}\\b/TopModule/g; s/\\b${TB_STEM_RE}\\b/TopTestbench/g' \"$TB_SV\""
      fi
      if [[ -f "$RTLTB_SV" ]]; then
        run_cmd "perl -0777 -i -pe 's/\\b${TOP_NAME_RE}\\b/TopModule/g; s/\\b${TB_STEM_RE}\\b/TopTestbench/g' \"$RTLTB_SV\""
      fi
    else
      # No TB stem provided; still normalize DUT in test files if they exist
      [[ -f "$TB_SV" ]] && run_cmd "perl -0777 -i -pe 's/\\b${TOP_NAME_RE}\\b/TopModule/g' \"$TB_SV\""
      [[ -f "$RTLTB_SV" ]] && run_cmd "perl -0777 -i -pe 's/\\b${TOP_NAME_RE}\\b/TopModule/g' \"$RTLTB_SV\""
    fi
  fi

  ((++idx))
done
