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
  files=(emdash3_2.lp emdash3_2_presheaves.lp emdash3_2_nat_arithmetic.lp emdash3_2_finite_families.lp emdash3_2_commutative_algebra.lp emdash3_2_commutative_algebra_category.lp emdash3_2_commutative_algebra_product.lp emdash3_2_commutative_algebra_f2.lp emdash3_2_commutative_algebra_finite.lp emdash3_2_commutative_algebra_polynomial.lp emdash3_2_commutative_algebra_localization.lp emdash3_2_commutative_algebra_localization_unit.lp emdash3_2_commutative_algebra_localization_zero.lp emdash3_2_commutative_algebra_localization_idempotent.lp emdash3_2_commutative_algebra_localization_comparison.lp emdash3_2_commutative_algebra_localization_overlap.lp emdash3_2_commutative_algebra_presheaves.lp emdash3_2_walking_end_hit.lp emdash3_2_eq1_hom_action.lp emdash3_2_eq1_evidence_property.lp emdash3_2_sieves.lp emdash3_2_sites.lp emdash3_2_generated_topologies.lp emdash3_2_ringed_sites.lp emdash3_2_site_basis.lp emdash3_2_commutative_algebra_ringed_space_covers.lp emdash3_2_commutative_algebra_ringed_space_restrictions.lp emdash3_2_commutative_algebra_locality.lp emdash3_2_commutative_algebra_matching.lp emdash3_2_commutative_algebra_glue.lp emdash3_2_commutative_algebra_affine_glue.lp emdash3_2_commutative_algebra_zariski.lp emdash3_2_commutative_algebra_zariski_topology.lp emdash3_2_commutative_algebra_localization_split.lp emdash3_2_commutative_algebra_affine_spec.lp emdash3_2_commutative_algebra_affine_zariski.lp emdash3_2_commutative_algebra_affine_ringed_sites.lp emdash3_2_commutative_algebra_affine_locality.lp emdash3_2_commutative_algebra_affine_schemes.lp emdash3_2_commutative_algebra_affine_basis.lp emdash3_2_commutative_algebra_affine_points.lp emdash3_2_commutative_algebra_affine_intersections.lp emdash3_2_commutative_algebra_affine_atlas.lp emdash3_2_checks.lp)
fi

for file in "${files[@]}"; do
  check_file "$file"
done
