#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# During early development, a “hung” typecheck usually indicates a
# rewrite/unification issue. Use one measured per-target ceiling for focused
# and registered checks so near-boundary valid terms are classified uniformly.
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

files=("$@")
if [[ ${#files[@]} -eq 0 ]]; then
  files=(emdash3_2.lp emdash3_2_presheaves.lp emdash3_2_fibrewise_sigma.lp emdash3_2_nat_arithmetic.lp emdash3_2_finite_families.lp emdash3_2_commutative_algebra.lp emdash3_2_commutative_algebra_category.lp emdash3_2_commutative_algebra_product.lp emdash3_2_commutative_algebra_f2.lp emdash3_2_commutative_algebra_finite.lp emdash3_2_commutative_algebra_polynomial.lp emdash3_2_commutative_algebra_localization.lp emdash3_2_commutative_algebra_localization_unit.lp emdash3_2_commutative_algebra_localization_zero.lp emdash3_2_commutative_algebra_localization_idempotent.lp emdash3_2_commutative_algebra_localization_comparison.lp emdash3_2_commutative_algebra_localization_overlap.lp emdash3_2_commutative_algebra_presheaves.lp emdash3_2_walking_end_hit.lp emdash3_2_eq1_hom_action.lp emdash3_2_eq1_evidence_property.lp emdash3_2_telescope_localization_hit.lp emdash3_2_integer_localization.lp emdash3_2_circle_hit.lp emdash3_2_walking_circle_completion.lp emdash3_2_groupoidal_closure.lp emdash3_2_path_pseudo_laxity.lp emdash3_2_gray_profiles.lp emdash3_2_walking_arrow.lp emdash3_2_gray_right_closure.lp emdash3_2_gray_walking_square.lp emdash3_2_truncation_reflector.lp emdash3_2_circle_connectedness.lp emdash3_2_sieves.lp emdash3_2_sites.lp emdash3_2_sieve_extensions.lp emdash3_2_generated_topologies.lp emdash3_2_ringed_sites.lp emdash3_2_site_basis.lp emdash3_2_commutative_algebra_ringed_space_covers.lp emdash3_2_commutative_algebra_binary_covers.lp emdash3_2_commutative_algebra_ringed_space_restrictions.lp emdash3_2_commutative_algebra_locality.lp emdash3_2_commutative_algebra_local_ringed_sites.lp emdash3_2_commutative_algebra_matching.lp emdash3_2_commutative_algebra_glue.lp emdash3_2_commutative_algebra_affine_glue.lp emdash3_2_commutative_algebra_zariski.lp emdash3_2_commutative_algebra_zariski_topology.lp emdash3_2_commutative_algebra_localization_split.lp emdash3_2_commutative_algebra_affine_spec.lp emdash3_2_commutative_algebra_affine_zariski.lp emdash3_2_commutative_algebra_affine_ringed_sites.lp emdash3_2_commutative_algebra_affine_locality.lp emdash3_2_commutative_algebra_affine_schemes.lp emdash3_2_commutative_algebra_affine_basis.lp emdash3_2_commutative_algebra_affine_cover_charts.lp emdash3_2_commutative_algebra_affine_cover_presentations.lp emdash3_2_commutative_algebra_affine_cover_refinements.lp emdash3_2_commutative_algebra_locally_ringed_space_presentations.lp emdash3_2_commutative_algebra_site_relative_schemes.lp emdash3_2_commutative_algebra_affine_points.lp emdash3_2_commutative_algebra_affine_intersections.lp emdash3_2_commutative_algebra_affine_atlas.lp emdash3_2_checks.lp)
  files+=(emdash3_2_finite_limits.lp)
  files+=(emdash3_2_direct_cover_questions.lp)
  files+=(emdash3_2_direct_cover_question_families.lp)
  files+=(emdash3_2_direct_cover_algebras.lp)
  files+=(emdash3_2_direct_cover_internal_sheaves.lp)
  files+=(emdash3_2_direct_cover_completion_hit.lp)
  files+=(emdash3_2_direct_cover_completion_eliminator.lp)
  files+=(emdash3_2_commutative_algebra_scheme_chart_overlaps.lp)
  files+=(emdash3_2_commutative_algebra_laurent.lp)
  files+=(emdash3_2_commutative_algebra_scheme_laurent_overlaps.lp)
  files+=(emdash3_2_commutative_algebra_projective_line.lp)
fi

for file in "${files[@]}"; do
  check_file "$file"
done
