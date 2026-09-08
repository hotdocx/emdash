#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Fresh-source measurements on 2026-09-07: the parametric cycles owner took
# 72.8 s and its reviewer 78.1 s; subsequent source/warning joins hit 90 s.
# Recheck exact sources below, retaining their objects only in this disposable
# tree. This avoids repeated dependency checking without making proofs opaque.
: "${EMDASH_TYPECHECK_TIMEOUT:=90s}"
: "${EMDASH_LAMBDAPI_WARNINGS:=0}"
warning_flags=(-w)
case "$EMDASH_LAMBDAPI_WARNINGS" in
  1|true|TRUE|yes|YES|on|ON) warning_flags=(); mode=warnings ;;
  0|false|FALSE|no|NO|off|OFF) mode=quiet ;;
  *) printf 'invalid warning setting: %s\n' "$EMDASH_LAMBDAPI_WARNINGS" >&2; exit 2 ;;
esac
extra_flags=()
if [[ -n "${EMDASH_LAMBDAPI_FLAGS:-}" ]]; then
  read -r -a extra_flags <<< "$EMDASH_LAMBDAPI_FLAGS"
fi

owners=(
  emdash3_2_chain_pair_map_cycle_lifts.lp
  emdash3_2_hom_factor_source_isos.lp
  emdash3_2_short_exact_row_chain_columns.lp
  emdash3_2_snake_row_target_factors.lp
  emdash3_2_snake_row_target_cycles.lp
)
reviewers=(
  examples/chain_pair_map_cycle_lifts.lp
  examples/hom_factor_source_isos.lp
  examples/snake_row_target_factor.lp
  examples/snake_row_target_cycles.lp
)
mkdir -p logs/probes
log_file="$(pwd)/logs/probes/snake-row-target-cycles-${mode}-$(date +%Y%m%d-%H%M%S).log"
stage_root="$(mktemp -d /tmp/emdash-snake-target-cycles.XXXXXX)"
cleanup() {
  case "$stage_root" in
    /tmp/emdash-snake-target-cycles.??????) ;;
    *) printf 'unexpected temporary path: %s\n' "$stage_root" >&2; return 1 ;;
  esac
  # Remove only copied sources and generated object kinds from this exact tree.
  # An unexpected file survives and causes rmdir to report the incomplete cleanup.
  local file
  for file in "$stage_root"/*.lp "$stage_root"/*.lpo \
      "$stage_root"/*.lpi "$stage_root"/*.lpj "$stage_root"/lambdapi.pkg \
      "$stage_root"/examples/*.lp "$stage_root"/examples/*.lpo \
      "$stage_root"/examples/*.lpi "$stage_root"/examples/*.lpj; do
    if [[ -f "$file" || -L "$file" ]]; then unlink -- "$file"; fi
  done
  rmdir -- "$stage_root/examples" "$stage_root"
}
trap cleanup EXIT
mkdir -p "$stage_root/examples"
cp lambdapi.pkg ./*.lp "$stage_root/"
for file in "${reviewers[@]}"; do cp "$file" "$stage_root/examples/"; done

check_object() {
  local file="$1" started="$SECONDS" rc elapsed
  printf 'checking %s with fresh exact objects (timeout %s, %s)\n' \
    "$file" "$EMDASH_TYPECHECK_TIMEOUT" "$mode"
  printf 'checking %s with fresh exact objects (timeout %s, %s)\n' \
    "$file" "$EMDASH_TYPECHECK_TIMEOUT" "$mode" >>"$log_file"
  set +e
  timeout --signal=INT "$EMDASH_TYPECHECK_TIMEOUT" \
    lambdapi check -c --no-colors "${warning_flags[@]}" "${extra_flags[@]}" \
    "$file" >>"$log_file" 2>&1
  rc=$?
  set -e
  elapsed=$((SECONDS - started))
  printf 'finished %s: exit %s, elapsed %ss\n' "$file" "$rc" "$elapsed"
  printf 'finished %s: exit %s, elapsed %ss\n' "$file" "$rc" "$elapsed" >>"$log_file"
  if [[ "$rc" -ne 0 ]]; then
    tail -40 "$log_file" >&2
    printf 'check failed; log: %s\n' "$log_file" >&2
    return "$rc"
  fi
}

printf 'target-cycle check log: %s\n' "$log_file"
cd "$stage_root"
check_object emdash3_2.lp
for file in "${owners[@]}" "${reviewers[@]}"; do check_object "$file"; done
printf 'target-cycle checks succeeded; log: %s\n' "$log_file"
