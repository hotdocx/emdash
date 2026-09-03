#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

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

scratch_root="$(mktemp -d /tmp/emdash-six-term.XXXXXX)"
cleanup() {
  case "$scratch_root" in
    /tmp/emdash-six-term.*) rm -rf -- "$scratch_root" ;;
    *) printf 'refusing to remove unexpected temporary path: %s\n' \
         "$scratch_root" >&2 ;;
  esac
}
trap cleanup EXIT

scratch="$scratch_root/emdash2"
mkdir -p "$scratch/examples"
cp lambdapi.pkg ./*.lp "$scratch/"
cp examples/abelian_snake_six_term_inner_zero.lp "$scratch/examples/"
cp examples/abelian_snake_six_term_result.lp "$scratch/examples/"

check_object() {
  local file="$1"
  printf 'checking %s with fresh exact dependency objects\n' "$file"
  if command -v timeout >/dev/null 2>&1; then
    timeout --signal=INT "$EMDASH_TYPECHECK_TIMEOUT" \
      lambdapi check -c "${warning_flags[@]}" "${extra_flags[@]}" "$file"
  else
    lambdapi check -c "${warning_flags[@]}" "${extra_flags[@]}" "$file"
  fi
}

cd "$scratch"

# Each source is checked in a separate bounded invocation. Generated objects
# live only in the isolated temporary copy and let the two independently green
# dependency branches meet without rechecking their full source closures in
# one 90-second process.
check_object emdash3_2_abelian_snake_six_term_inner_kernel_factor.lp
check_object emdash3_2_abelian_snake_six_term_inner_cokernel_middle_zero_foundation.lp
check_object emdash3_2_abelian_snake_six_term_kernel_zero.lp
check_object emdash3_2_abelian_snake_six_term_cokernel_zero.lp
check_object emdash3_2_abelian_snake_connecting.lp
check_object emdash3_2_abelian_snake_connecting_result.lp
check_object emdash3_2_abelian_snake_six_term_inner_kernel_u_zero_foundation.lp
check_object emdash3_2_abelian_snake_six_term_inner_kernel_q2_zero_foundation.lp
check_object emdash3_2_abelian_snake_six_term_inner_kernel_zero.lp
check_object emdash3_2_abelian_snake_six_term_inner_cokernel_p1_zero_foundation.lp
check_object emdash3_2_abelian_snake_six_term_inner_cokernel_zero.lp
check_object emdash3_2_abelian_snake_six_term_result.lp
check_object emdash3_2_abelian_snake_six_term_result_projections.lp
check_object examples/abelian_snake_six_term_inner_zero.lp
check_object examples/abelian_snake_six_term_result.lp
