#!/usr/bin/env bash
set -euo pipefail

SCRIPT_NAME="$(basename "$0")"
OUT_DIR="out"
DRY_RUN=0
JSON_PATH=""
REPO_ROOT="$(pwd)"

print_help() {
  cat <<EOF
${SCRIPT_NAME} Batch wrapper for bender->morty->spec flows.

USAGE:
  ${SCRIPT_NAME} --json <config.json> [--out out/] [--dry-run]
  ${SCRIPT_NAME} --help

INPUT JSON SHAPE:
{
  "assets/common_cells": [
    ["assets/common_cells/fifo_v3.sv", "assets/common_cells/fifo_tb.sv"]
  ],
  "assets/axi": [
    ["assets/axi/rtl_top.sv", "assets/axi/axi_tb.sv"]
  ]
}

For each [rtl_top_path, tb_top_path] tuple:
  1) cd assets/<submodule> ; call bender-wrapper 3x to produce JSONs in that asset folder:
       a) RTL:   bender-wrapper --top <rtl_basename> -t rtl
       b) TB:    bender-wrapper --top <rtl_basename> -t test -t simulation --tb-token <tb_stem>
       c) RTLTB: bender-wrapper --top <rtl_basename> -t rtl -t test -t simulation --tb-token <tb_stem>
  2) Copy those JSONs into out/
  3) Run Morty on out/*.json to produce in out/:
       *.rtl.json   -> Prob000_<NAME>_ref.sv
       *.tb.json    -> Prob000_<NAME>_test.sv
       *.rtltb.json -> Prob000_<NAME>_test_golden.sv
     where <NAME> is the RTL basename (no ext) with non-alnum removed.
  4) Run scripts/spec-gen using the newly created out/*.sv
  5) Copy <NAME>.txt -> out/Prob000_<NAME>_prompt.txt (if present)

OPTIONS:
  -j, --json PATH     Path to the JSON config (required)
  -o, --out  DIR      Output folder (default: out)
      --dry-run       Print actions without executing them
  -h, --help          Show this help

DEPENDENCIES:
  - jq
  - ./scripts/bender-wrapper
  - oseda (Morty CLI, e.g. "oseda morty")
  - ./scripts/spec-gen

EXAMPLE:
  ${SCRIPT_NAME} --json benchmarks.json --out out
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

sanitize_name() {
  local path="$1"
  local base="${path##*/}"
  base="${base%.*}"
  echo "$base" | tr -cd '[:alnum:]'
}

rtl_basename() { local p="$1"; echo "${p##*/}"; }
tb_stem()      { local p="$1"; p="${p##*/}"; echo "${p%.*}"; }

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
    -o|--out)  OUT_DIR="$2";  shift 2;;
    --dry-run) DRY_RUN=1;     shift;;
    -h|--help) print_help; exit 0;;
    *) echo "Unknown argument: $1" >&2; print_help; exit 1;;
  esac
done

[[ -n "$JSON_PATH" ]] || { echo "ERROR: --json is required." >&2; print_help; exit 1; }

need_cmd jq
need_cmd oseda
[[ -x "$REPO_ROOT/scripts/bender-wrapper" ]] || { echo "ERROR: scripts/bender-wrapper not found or not executable." >&2; exit 1; }
[[ -x "$REPO_ROOT/scripts/spec-gen" ]] || { echo "ERROR: scripts/spec-gen not found or not executable." >&2; exit 1; }

run_cmd "mkdir -p \"$OUT_DIR\""

mapfile -t LINES < <(jq -r 'to_entries[] | .key as $sub | .value[] | [$sub, .[0], .[1]] | @tsv' "$JSON_PATH")
(( ${#LINES[@]} > 0 )) || { echo "No work found in JSON. Exiting."; exit 0; }

for line in "${LINES[@]}"; do
  IFS=$'\t' read -r SUBMOD RTL TB <<<"$line"
  if [[ -z "$RTL" || -z "$TB" ]]; then
    log "Skipping empty tuple under '$SUBMOD'."; continue
  fi
  if [[ ! -d "$SUBMOD" ]]; then
    log "ERROR: Asset folder '$SUBMOD' does not exist."; exit 1
  fi

  NAME="$(sanitize_name "$RTL")"
  [[ -n "$NAME" ]] || { log "ERROR: Failed to sanitize name from RTL: $RTL"; exit 1; }

  TOP_FILE="$(rtl_basename "$RTL")"
  TB_STEM_VAL="$(tb_stem "$TB")"

  log "Asset='$SUBMOD' NAME='$NAME'"
  log "  RTL: $RTL"
  log "  TB : $TB (stem: $TB_STEM_VAL)"

  # Generate trimmed JSONs INSIDE the asset directory
  run_in_dir "$SUBMOD" "\"$REPO_ROOT/scripts/bender-wrapper\" --top \"$TOP_FILE\" -t rtl"
  run_in_dir "$SUBMOD" "\"$REPO_ROOT/scripts/bender-wrapper\" --top \"$TOP_FILE\" -t test -t simulation --tb-token \"$TB_STEM_VAL\""
  run_in_dir "$SUBMOD" "\"$REPO_ROOT/scripts/bender-wrapper\" --top \"$TOP_FILE\" -t rtl -t test -t simulation --tb-token \"$TB_STEM_VAL\""

  # Paths in asset; then copy to out/
  TOP_BASE="${TOP_FILE%.*}"
  ASSET_RTL_JSON="$SUBMOD/$TOP_BASE.rtl.json"
  ASSET_TB_JSON="$SUBMOD/$TOP_BASE.tb.json"
  ASSET_RTLTB_JSON="$SUBMOD/$TOP_BASE.rtltb.json"

  # Move JSONs to out/ (keep originals too)
  run_cmd "mv \"$ASSET_RTL_JSON\" \"$OUT_DIR/\" || true"
  run_cmd "mv \"$ASSET_TB_JSON\" \"$OUT_DIR/\"   || true"
  run_cmd "mv \"$ASSET_RTLTB_JSON\" \"$OUT_DIR/\" || true"

  RTL_JSON="$OUT_DIR/$TOP_BASE.rtl.json"
  TB_JSON="$OUT_DIR/$TOP_BASE.tb.json"
  RTLTB_JSON="$OUT_DIR/$TOP_BASE.rtltb.json"

  # Morty -> single-source SV into out/
  RTL_SV="$OUT_DIR/Prob000_${NAME}_ref.sv"
  TB_SV="$OUT_DIR/Prob000_${NAME}_test.sv"
  RTLTB_SV="$OUT_DIR/Prob000_${NAME}_test_golden.sv"

  if [[ -f "$RTL_JSON" ]]; then
    run_cmd "oseda morty -f \"$RTL_JSON\" -o \"$RTL_SV\""
  else
    log "WARNING: Missing $RTL_JSON"
  fi

  if [[ -f "$TB_JSON" ]]; then
    run_cmd "oseda morty -f \"$TB_JSON\" -o \"$TB_SV\""
  else
    log "WARNING: Missing $TB_JSON"
  fi

  if [[ -f "$RTLTB_JSON" ]]; then
    run_cmd "oseda morty -f \"$RTLTB_JSON\" -o \"$RTLTB_SV\""
  else
    log "WARNING: Missing $RTLTB_JSON"
  fi

  rm -rf "$RTL_JSON" "$TB_JSON" "$RTLTB_JSON"

  # spec-gen using out/*.sv
  if [[ -f $TB_SV && -f $RTL_SV ]]; then
      run_cmd "\"$REPO_ROOT/scripts/spec-gen\" --tb $TB_SV --rtl $RTL_SV --name $NAME --provider openai --model gpt-4o-2024-08-06 --key-cfg-path ../../key.cfg --out $NAME.md --max-token 8192 --tokens 60000 --temperature 0.8 --top-p 0.95"
    # Copy <NAME>.txt -> out/Prob000_<NAME>_prompt.txt
    if [[ "$DRY_RUN" -eq 1 ]]; then
      printf '%s\n' "$REPO_ROOT/scripts/spec-gen --tb $TB_SV --rtl $RTL_SV --name $NAME --provider openai --model gpt-4o-2024-08-06 --key-cfg-path ../../key.cfg --out $NAME.md --max-token 8192 --tokens 60000 --temperature 0.8 --top-p 0.95"
      echo "DRY-RUN: Would copy newest \"${NAME}.txt\" -> \"$OUT_DIR/Prob000_${NAME}_prompt.txt\""
    else
      GEN_TXT="$(ls -1t "${NAME}.txt" 2>/dev/null | head -n1 || true)"
      if [[ -n "$GEN_TXT" && -f "$GEN_TXT" ]]; then
        run_cmd "mv \"$GEN_TXT\" \"$OUT_DIR/Prob000_${NAME}_prompt.txt\""
      else
        log "WARNING: Could not find generated ${NAME}.txt after spec step."
      fi
    fi
  else
    log "Skipping spec step: missing $TB_SV or $RTL_SV"
  fi
done

log "Done. Outputs in: $OUT_DIR"
