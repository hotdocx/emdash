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
    printf 'invalid EMDASH_LAMBDAPI_WARNINGS value: %s\n' "$EMDASH_LAMBDAPI_WARNINGS" >&2
    exit 2
    ;;
esac

extra_flags=()
if [[ -n "${EMDASH_LAMBDAPI_FLAGS:-}" ]]; then
  read -r -a extra_flags <<< "$EMDASH_LAMBDAPI_FLAGS"
fi

check_file() {
  local file="$1"
  if command -v timeout >/dev/null 2>&1; then
    timeout --signal=INT "$EMDASH_TYPECHECK_TIMEOUT" \
      lambdapi check "${warning_flags[@]}" "${extra_flags[@]}" "$file"
  else
    lambdapi check "${warning_flags[@]}" "${extra_flags[@]}" "$file"
  fi
}

six_term_examples_checked=0
normalization_examples_checked=0
for file in examples/*.lp; do
  printf 'checking %s\n' "$file"
  if [[ "$file" == "examples/abelian_snake_six_term_inner_zero.lp" ||
        "$file" == "examples/abelian_snake_six_term_result.lp" ||
        "$file" == "examples/abelian_snake_exact_first.lp" ||
        "$file" == "examples/abelian_snake_exact_second.lp" ||
        "$file" == "examples/abelian_snake_exact_third.lp" ||
        "$file" == "examples/abelian_snake_six_term_exact_pairs.lp" ||
        "$file" == "examples/abelian_snake_six_term_exact_structure.lp" ||
        "$file" == "examples/abelian_snake_six_term_exact_result.lp" ]]; then
    if [[ "$six_term_examples_checked" -eq 0 ]]; then
      ./scripts/check_abelian_snake_six_term.sh
      six_term_examples_checked=1
    fi
  elif [[ "$file" == "examples/short_exact_rows.lp" ||
         "$file" == "examples/monic_image_iso.lp" ||
         "$file" == "examples/monic_selected_row_comparison.lp" ||
         "$file" == "examples/short_exact_normalization_structure.lp" ||
         "$file" == "examples/short_exact_normalization.lp" ]]; then
    if [[ "$normalization_examples_checked" -eq 0 ]]; then
      ./scripts/check_short_exact_normalization.sh
      normalization_examples_checked=1
    fi
  else
    check_file "$file"
  fi
done
