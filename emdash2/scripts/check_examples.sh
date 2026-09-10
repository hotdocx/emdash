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
snake_rows_examples_checked=0
snake_target_cycles_examples_checked=0
snake_target_homology_examples_checked=0
snake_source_boundary_examples_checked=0
homology_connecting_examples_checked=0
homology_exact_window_examples_checked=0
homology_window_families_examples_checked=0
homology_arrow_tails_examples_checked=0
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
  elif [[ "$file" == "examples/chain_pair_map_snake.lp" ||
         "$file" == "examples/abelian_structure_elimination.lp" ||
         "$file" == "examples/snake_row_comparisons.lp" ||
         "$file" == "examples/snake_row_source_cycle_iso.lp" ||
         "$file" == "examples/snake_row_target_cokernel_iso.lp" ||
         "$file" == "examples/abelian_snake_row_comparisons.lp" ||
         "$file" == "examples/short_exact_row_snake.lp" ||
         "$file" == "examples/short_exact_row_snake_target.lp" ]]; then
    if [[ "$snake_rows_examples_checked" -eq 0 ]]; then
      ./scripts/check_snake_row_comparisons.sh
      snake_rows_examples_checked=1
    fi
  elif [[ "$file" == "examples/chain_pair_map_cycle_lifts.lp" ||
          "$file" == "examples/hom_factor_source_isos.lp" ||
          "$file" == "examples/snake_row_target_factor.lp" ||
          "$file" == "examples/snake_row_target_cycles.lp" ]]; then
    if [[ "$snake_target_cycles_examples_checked" -eq 0 ]]; then
      ./scripts/check_snake_row_target_cycles.sh
      snake_target_cycles_examples_checked=1
    fi
  elif [[ "$file" == "examples/snake_row_target_cokernel_projection.lp" ||
          "$file" == "examples/snake_row_target_homology_normal.lp" ||
          "$file" == "examples/snake_row_target_homology_factor.lp" ]]; then
    if [[ "$snake_target_homology_examples_checked" -eq 0 ]]; then
      ./scripts/check_snake_row_target_homology.sh
      snake_target_homology_examples_checked=1
    fi
  elif [[ "$file" == "examples/snake_row_source_second_comparison.lp" ||
          "$file" == "examples/snake_row_source_boundary_covered.lp" ||
          "$file" == "examples/snake_row_source_boundary_zero.lp" ]]; then
    if [[ "$snake_source_boundary_examples_checked" -eq 0 ]]; then
      ./scripts/check_snake_row_source_boundary.sh
      snake_source_boundary_examples_checked=1
    fi
  elif [[ "$file" == "examples/homology_connecting_factor.lp" ||
          "$file" == "examples/homology_connecting.lp" ]]; then
    if [[ "$homology_connecting_examples_checked" -eq 0 ]]; then
      ./scripts/check_homology_connecting.sh
      homology_connecting_examples_checked=1
    fi
  elif [[ "$file" == "examples/homology_window_families.lp" ||
          "$file" == "examples/homology_window_connecting_transformation.lp" ||
          "$file" == "examples/homology_window_column_usability.lp" ]]; then
    if [[ "$homology_window_families_examples_checked" -eq 0 ]]; then
      ./scripts/check_homology_window_families.sh
      homology_window_families_examples_checked=1
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
