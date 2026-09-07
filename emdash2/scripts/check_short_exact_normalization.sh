#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

: "${EMDASH_TYPECHECK_TIMEOUT:=90s}"
: "${EMDASH_LAMBDAPI_WARNINGS:=0}"
warning_flags=(-w)
case "$EMDASH_LAMBDAPI_WARNINGS" in
  1|true|TRUE|yes|YES|on|ON) warning_flags=() ;;
  0|false|FALSE|no|NO|off|OFF) ;;
  *) printf 'invalid warning setting: %s\n' "$EMDASH_LAMBDAPI_WARNINGS" >&2; exit 2 ;;
esac
extra_flags=()
if [[ -n "${EMDASH_LAMBDAPI_FLAGS:-}" ]]; then
  read -r -a extra_flags <<< "$EMDASH_LAMBDAPI_FLAGS"
fi

scratch_root="$(mktemp -d /tmp/emdash-normalization.XXXXXX)"
mkdir -p "$scratch_root/examples"
cleanup() {
  case "$scratch_root" in
    /tmp/emdash-normalization.??????) ;;
    *) printf 'unexpected temporary path: %s\n' "$scratch_root" >&2; return 1 ;;
  esac
  # Remove only the generated file kinds this build owns. Unknown content is
  # retained: rmdir then fails instead of recursively deleting it.
  local file
  for file in "$scratch_root"/*.lp "$scratch_root"/*.lpo \
      "$scratch_root"/*.lpi "$scratch_root"/*.lpj \
      "$scratch_root"/lambdapi.pkg "$scratch_root"/examples/*.lp \
      "$scratch_root"/examples/*.lpo; do
    if [[ -f "$file" || -L "$file" ]]; then unlink -- "$file"; fi
  done
  rmdir -- "$scratch_root/examples" "$scratch_root"
}
trap cleanup EXIT
cp lambdapi.pkg ./*.lp "$scratch_root/"
cp examples/short_exact_rows.lp "$scratch_root/examples/"
cp examples/monic_image_iso.lp "$scratch_root/examples/"
cp examples/monic_selected_row_comparison.lp "$scratch_root/examples/"
cp examples/short_exact_normalization_structure.lp "$scratch_root/examples/"
cp examples/short_exact_normalization.lp "$scratch_root/examples/"
cp examples/short_exact_comparisons.lp "$scratch_root/examples/"

check_object() {
  local file="$1"
  printf 'checking %s with fresh exact dependency objects\n' "$file"
  timeout --signal=INT "$EMDASH_TYPECHECK_TIMEOUT" \
    lambdapi check -c "${warning_flags[@]}" "${extra_flags[@]}" "$file"
}
cd "$scratch_root"
check_object emdash3_2_short_exact_cokernel_comparison.lp
check_object emdash3_2_short_exact_rows.lp
check_object emdash3_2_kernel_short_exact_rows.lp
check_object emdash3_2_selected_short_exact_rows.lp
check_object emdash3_2_monic_image_comparison.lp
check_object emdash3_2_short_exact_row_comparison_fibres.lp
check_object emdash3_2_monic_selected_row_comparison.lp
check_object emdash3_2_short_exact_normalization_foundation.lp
check_object emdash3_2_short_exact_normalization_isos.lp
check_object emdash3_2_short_exact_normalization_projections.lp
check_object emdash3_2_short_exact_normalization.lp
check_object examples/short_exact_rows.lp
check_object examples/monic_image_iso.lp
check_object examples/monic_selected_row_comparison.lp
check_object examples/short_exact_normalization_structure.lp
check_object examples/short_exact_normalization.lp
check_object examples/short_exact_comparisons.lp
