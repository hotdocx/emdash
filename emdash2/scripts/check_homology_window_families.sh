#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Keep each source and reviewer independently bounded while sharing only this
# fresh exact-source dependency tree. No persistent object cache or opaque proof.
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

prerequisites=(
  emdash3_2_zero_arrow_cone_chain_pairs.lp
  emdash3_2_short_exact_rows.lp
  emdash3_2_homology_connecting_cover.lp
  emdash3_2_homology_connecting_left_lift.lp
  emdash3_2_homology_connecting_target_cycles.lp
  emdash3_2_homology_connecting_cover_kernel.lp
  emdash3_2_homology_connecting_cover_kernel_lift.lp
  emdash3_2_homology_record_boundary_factors.lp
  emdash3_2_homology_connecting_cover_kernel_boundary.lp
  emdash3_2_homology_connecting_cycles_descent.lp
  emdash3_2_homology_connecting_source_boundary_cover.lp
  emdash3_2_homology_connecting_source_boundary_zero.lp
  emdash3_2_homology_connecting_source_boundary_descent.lp
  emdash3_2_homology_record_connecting.lp
  emdash3_2_chain_pair_homology_records.lp
)
owners=(
  emdash3_2_short_exact_row_families.lp
  emdash3_2_homology_window_families.lp
  emdash3_2_homology_window_columns.lp
  emdash3_2_homology_window_column_usability.lp
  emdash3_2_homology_window_connecting_transformation.lp
)
reviewers=(
  examples/homology_window_families.lp
  examples/homology_window_connecting_transformation.lp
  examples/homology_window_column_usability.lp
  examples/homology_record_connecting_whole.lp
)
mkdir -p logs/probes
log_file="$(pwd)/logs/probes/homology-window-families-${mode}-$(date +%Y%m%d-%H%M%S).log"
stage_root="$(mktemp -d /tmp/emdash-homology-window-families.XXXXXX)"
cleanup() {
  case "$stage_root" in
    /tmp/emdash-homology-window-families.??????) ;;
    *) printf 'unexpected temporary path: %s\n' "$stage_root" >&2; return 1 ;;
  esac
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
    tail -30 "$log_file" | cut -c1-260 >&2
    printf 'check failed; log: %s\n' "$log_file" >&2
    return "$rc"
  fi
}

printf 'homology-window-families check log: %s\n' "$log_file"
cd "$stage_root"
check_object emdash3_2.lp
for file in "${prerequisites[@]}"; do check_object "$file"; done
printf 'BASELINE_BOUNDARY: original dependencies complete\n' >>"$log_file"
for file in "${owners[@]}"; do check_object "$file"; done
for file in "${reviewers[@]}"; do check_object "$file"; done
printf 'homology-window-families checks succeeded; log: %s\n' "$log_file"
