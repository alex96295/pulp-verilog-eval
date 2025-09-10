#!/usr/bin/env bash
set -euo pipefail

SCRIPT_NAME="$(basename "$0")"
OUT_DIR="out"
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
    ["assets/common_cells/fifo_v3.sv", "assets/common_cells/fifo_tb.sv"]
  ]
}

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

run_cmd "mkdir -p \"$OUT_DIR\""

mapfile -t LINES < <(jq -r 'to_entries[] | .key as $sub | .value[] | [$sub, .[0], .[1]] | @tsv' "$JSON_PATH")
(( ${#LINES[@]} > 0 )) || { echo "No work found in JSON. Exiting."; exit 0; }

for line in "${LINES[@]}"; do
  IFS=$'\t' read -r SUBMOD RTL TB <<<"$line"
  [[ -n "$RTL" && -n "$TB" ]] || { log "Skipping empty tuple under '$SUBMOD'."; continue; }
  [[ -d "$SUBMOD" ]] || { log "ERROR: Asset folder '$SUBMOD' does not exist."; exit 1; }

  NAME="$(sanitize_name "$RTL")"
  TOP_FILE="$(rtl_basename "$RTL")"
  TB_STEM_VAL="$(tb_stem "$TB")"

  log "Asset='$SUBMOD' NAME='$NAME'"
  log "  RTL: $RTL"
  log "  TB : $TB (stem: $TB_STEM_VAL)"

  run_in_dir "$SUBMOD" "\"$REPO_ROOT/scripts/bender-wrapper\" --top \"$TOP_FILE\" -t rtl"
  run_in_dir "$SUBMOD" "\"$REPO_ROOT/scripts/bender-wrapper\" --top \"$TOP_FILE\" -t test -t simulation --tb-token \"$TB_STEM_VAL\""
  run_in_dir "$SUBMOD" "\"$REPO_ROOT/scripts/bender-wrapper\" --top \"$TOP_FILE\" -t rtl -t test -t simulation --tb-token \"$TB_STEM_VAL\""

  TOP_BASE="${TOP_FILE%.*}"
  RTL_JSON="$OUT_DIR/$TOP_BASE.rtl.json"
  TB_JSON="$OUT_DIR/$TOP_BASE.tb.json"
  RTLTB_JSON="$OUT_DIR/$TOP_BASE.rtltb.json"

  run_cmd "mv \"$SUBMOD/$TOP_BASE.rtl.json\" \"$OUT_DIR/\" || true"
  run_cmd "mv \"$SUBMOD/$TOP_BASE.tb.json\" \"$OUT_DIR/\"   || true"
  run_cmd "mv \"$SUBMOD/$TOP_BASE.rtltb.json\" \"$OUT_DIR/\" || true"

  RTL_SV="$OUT_DIR/Prob000_${NAME}_ref.sv"
  TB_SV="$OUT_DIR/Prob000_${NAME}_test.sv"
  RTLTB_SV="$OUT_DIR/Prob000_${NAME}_test_golden.sv"

  [[ -f "$RTL_JSON" ]] && run_cmd "oseda morty -f \"$RTL_JSON\" -o \"$RTL_SV\"" || log "WARNING: Missing $RTL_JSON"
  [[ -f "$TB_JSON" ]] && run_cmd "oseda morty -f \"$TB_JSON\" -o \"$TB_SV\"" || log "WARNING: Missing $TB_JSON"
  [[ -f "$RTLTB_JSON" ]] && run_cmd "oseda morty -f \"$RTLTB_JSON\" -o \"$RTLTB_SV\"" || log "WARNING: Missing $RTLTB_JSON"

  rm -f "$RTL_JSON" "$TB_JSON" "$RTLTB_JSON"

  if [[ -f $TB_SV && -f $RTL_SV ]]; then
    run_cmd "\"$REPO_ROOT/scripts/spec-gen\" \
      --tb $TB_SV \
      --rtl $RTL_SV \
      --name $NAME \
      --provider $PROVIDER \
      --model $MODEL \
      --key-cfg $KEY_CFG_PATH \
      --out $NAME.md \
      --max-token $MAX_TOKEN \
      --tokens $TOKENS \
      --temperature $TEMPERATURE \
      --top-p $TOP_P"

    if [[ "$DRY_RUN" -eq 1 ]]; then
      echo "DRY-RUN: Would copy newest \"${NAME}.txt\" -> \"$OUT_DIR/Prob000_${NAME}_prompt.txt\""
    else
      GEN_TXT="$(ls -1t "${NAME}.txt" 2>/dev/null | head -n1 || true)"
      [[ -n "$GEN_TXT" && -f "$GEN_TXT" ]] && run_cmd "mv \"$GEN_TXT\" \"$OUT_DIR/Prob000_${NAME}_prompt.txt\"" || log "WARNING: Could not find generated ${NAME}.txt"
    fi
  else
    log "Skipping spec step: missing $TB_SV or $RTL_SV"
  fi
done

log "Done. Outputs in: $OUT_DIR"
