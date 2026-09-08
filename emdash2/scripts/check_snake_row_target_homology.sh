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
  emdash3_2_short_exact_row_chain_columns.lp
  emdash3_2_snake_row_target_factors.lp
  emdash3_2_snake_row_target_cycles.lp
  emdash3_2_abelian_snake_covered_reconstruction.lp
  emdash3_2_homology_cokernel_inclusion_monic.lp
  emdash3_2_normal_mono_epic_factors.lp
  emdash3_2_hom_factor_comparison_pasting.lp
  emdash3_2_normal_mono_cycle_factors.lp
  emdash3_2_cokernel_codomain_comparison_projection.lp
  emdash3_2_snake_row_target_cokernel_iso.lp
)
owners=(
  emdash3_2_snake_row_target_cokernel_projection.lp
  emdash3_2_snake_row_target_homology_normal.lp
  emdash3_2_snake_row_target_homology_factor.lp
)
reviewers=(
  examples/snake_row_target_cokernel_projection.lp
  examples/snake_row_target_homology_normal.lp
  examples/snake_row_target_homology_factor.lp
)
mkdir -p logs/probes
log_file="$(pwd)/logs/probes/snake-row-target-homology-${mode}-$(date +%Y%m%d-%H%M%S).log"
stage_root="$(mktemp -d /tmp/emdash-snake-target-homology.XXXXXX)"
cleanup() {
  case "$stage_root" in
    /tmp/emdash-snake-target-homology.??????) ;;
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
cp examples/snake_row_target_cycles.lp "$stage_root/examples/"
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
    tail -30 "$log_file" >&2
    printf 'check failed; log: %s\n' "$log_file" >&2
    return "$rc"
  fi
}

printf 'target-homology check log: %s\n' "$log_file"
cd "$stage_root"
check_object emdash3_2.lp
for file in "${prerequisites[@]}" "${owners[@]}"; do check_object "$file"; done
check_object examples/snake_row_target_cycles.lp
for file in "${reviewers[@]}"; do check_object "$file"; done
printf 'target-homology checks succeeded; log: %s\n' "$log_file"
