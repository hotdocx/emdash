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
  case "$file" in
    examples/one_cat_native_exact_arrow_pairs.lp|\
    examples/one_cat_native_snake_six_term_result.lp|\
    examples/one_cat_native_snake_six_term_inputs.lp)
      ./scripts/check_native_snake_six_term.sh "$file"
      return ;;
  esac
  if command -v timeout >/dev/null 2>&1; then
    timeout --signal=INT "$EMDASH_TYPECHECK_TIMEOUT" \
      lambdapi check "${warning_flags[@]}" "${extra_flags[@]}" "$file"
  else
    lambdapi check "${warning_flags[@]}" "${extra_flags[@]}" "$file"
  fi
}

normalization_examples_checked=0
ordinary_rows_examples_checked=0
ordinary_cycles_examples_checked=0
homology_exact_window_examples_checked=0
homology_window_families_examples_checked=0
homology_arrow_tails_examples_checked=0
homology_bounded_prerequisites_checked=0
homology_bounded_generator_checked=0
for file in examples/*.lp; do
  printf 'checking %s\n' "$file"
  if [[ "$file" == "examples/short_exact_rows.lp" ||
          "$file" == "examples/monic_image_iso.lp" ||
          "$file" == "examples/monic_selected_row_comparison.lp" ||
          "$file" == "examples/short_exact_normalization_structure.lp" ||
          "$file" == "examples/short_exact_normalization.lp" ]]; then
    if [[ "$normalization_examples_checked" -eq 0 ]]; then
      ./scripts/check_short_exact_normalization.sh
      normalization_examples_checked=1
    fi
  elif [[ "$file" == "examples/abelian_structure_elimination.lp" ]]; then
    if [[ "$ordinary_rows_examples_checked" -eq 0 ]]; then
      ./scripts/check_ordinary_row_comparisons.sh
      ordinary_rows_examples_checked=1
    fi
  elif [[ "$file" == "examples/chain_pair_map_cycle_lifts.lp" ||
          "$file" == "examples/hom_factor_source_isos.lp" ]]; then
    if [[ "$ordinary_cycles_examples_checked" -eq 0 ]]; then
      ./scripts/check_ordinary_cycle_factors.sh
      ordinary_cycles_examples_checked=1
    fi
  elif [[ "$file" == "examples/homology_window_families.lp" ||
          "$file" == "examples/homology_window_connecting_transformation.lp" ||
          "$file" == "examples/homology_window_column_usability.lp" ]]; then
    if [[ "$homology_window_families_examples_checked" -eq 0 ]]; then
      ./scripts/check_homology_window_families.sh
      homology_window_families_examples_checked=1
    fi
  elif [[ "$file" == "examples/finite_arrow_tail_init.lp" ||
          "$file" == "examples/short_exact_row_zero.lp" ||
          "$file" == "examples/homology_row_field_spans.lp" ||
          "$file" == "examples/homology_bounded_generator.lp" ||
          "$file" == "examples/homology_bounded_generator_arrows.lp" ]]; then
    if [[ "$homology_bounded_generator_checked" -eq 0 ]]; then
      ./scripts/check_homology_bounded_generator.sh
      homology_bounded_generator_checked=1
    fi
  elif [[ "$file" == "examples/preadditive_zero_identity.lp" ||
          "$file" == "examples/homology_whole_zero.lp" ||
          "$file" == "examples/homology_window_extension.lp" ||
          "$file" == "examples/homology_row_spans.lp" ]]; then
    if [[ "$homology_bounded_prerequisites_checked" -eq 0 ]]; then
      ./scripts/check_homology_bounded_prerequisites.sh
      homology_bounded_prerequisites_checked=1
    fi
  elif [[ "$file" == "examples/finite_arrow_tails.lp" ||
          "$file" == "examples/computational_exact_arrow_tails.lp" ||
          "$file" == "examples/homology_adjacent_window_tails.lp" ]]; then
    if [[ "$homology_arrow_tails_examples_checked" -eq 0 ]]; then
      ./scripts/check_homology_arrow_tails.sh
      homology_arrow_tails_examples_checked=1
    fi
  elif [[ "$file" == "examples/homology_exact_window.lp" ]]; then
    if [[ "$homology_exact_window_examples_checked" -eq 0 ]]; then
      ./scripts/check_homology_exact_window.sh
      homology_exact_window_examples_checked=1
    fi
  else
    check_file "$file"
  fi
done
