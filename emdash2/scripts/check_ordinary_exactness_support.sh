#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
formal_root="$(pwd)"

: "${EMDASH_TYPECHECK_TIMEOUT:=90s}"
: "${EMDASH_LAMBDAPI_WARNINGS:=0}"

warning_flags=(-w)
case "$EMDASH_LAMBDAPI_WARNINGS" in
  1|true|TRUE|yes|YES|on|ON)
    warning_flags=()
    ;;
  0|false|FALSE|no|NO|off|OFF)
    ;;
  *)
    printf 'invalid EMDASH_LAMBDAPI_WARNINGS value: %s\n' \
      "$EMDASH_LAMBDAPI_WARNINGS" >&2
    exit 2
    ;;
esac

extra_flags=()
if [[ -n "${EMDASH_LAMBDAPI_FLAGS:-}" ]]; then
  read -r -a extra_flags <<< "$EMDASH_LAMBDAPI_FLAGS"
fi

scratch_root="$(mktemp -d /tmp/emdash-ordinary-exactness.XXXXXX)"
cleanup() {
  case "$scratch_root" in
    /tmp/emdash-ordinary-exactness.*) rm -rf -- "$scratch_root" ;;
    *) printf 'refusing to remove unexpected temporary path: %s\n' \
         "$scratch_root" >&2 ;;
  esac
}
trap cleanup EXIT

scratch="$scratch_root/emdash2"
mkdir -p "$scratch/examples"
cp lambdapi.pkg ./*.lp "$scratch/"
cp examples/computational_exactness_reindex.lp "$scratch/examples/"

check_object() {
  local file="$1"
  printf 'checking %s with fresh exact dependency objects\n' "$file"
  EMDASH_LP_TIMEOUT="$EMDASH_TYPECHECK_TIMEOUT" \
    bash "$formal_root/scripts/lambdapi_resource_guard.sh" \
    lambdapi check -c "${warning_flags[@]}" "${extra_flags[@]}" "$file"
}

cd "$scratch"

# Each source is checked in a separate bounded invocation. Generated objects
# live only in the isolated temporary copy. Retained ordinary support reuses
# those exact parents without rechecking its full source closure in one process.
check_object emdash3_2_exactness_covers_foundation.lp
check_object emdash3_2_exactness_covers.lp
check_object emdash3_2_exactness_covers_from_exact.lp
check_object emdash3_2_abelian_canonical_kernel_exactness.lp
check_object emdash3_2_abelian_canonical_cokernel_foundation.lp
check_object emdash3_2_abelian_canonical_cokernel_factor.lp
check_object emdash3_2_abelian_canonical_cokernel_epic.lp
check_object emdash3_2_abelian_canonical_cokernel_exactness.lp
check_object emdash3_2_abelian_canonical_cokernel_covers.lp
check_object emdash3_2_preadditive_difference_paths.lp
check_object emdash3_2_exactness_extensions_foundation.lp
check_object emdash3_2_exactness_extensions_to_exact_foundation.lp
check_object emdash3_2_exactness_extensions_to_exact_extension.lp
check_object emdash3_2_exactness_extensions_to_exact_zero.lp
check_object emdash3_2_exactness_extensions_to_exact.lp
check_object emdash3_2_abelian_canonical_kernel_extensions_foundation.lp
check_object emdash3_2_abelian_canonical_kernel_extensions.lp
check_object emdash3_2_exactness_reindex.lp
check_object examples/computational_exactness_reindex.lp
