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
  files=(emdash3_2.lp emdash3_2_preadditive_categories.lp emdash3_2_presheaves.lp emdash3_2_fibrewise_sigma.lp emdash3_2_nat_arithmetic.lp emdash3_2_finite_families.lp emdash3_2_commutative_algebra.lp emdash3_2_commutative_algebra_derived_laws.lp emdash3_2_commutative_algebra_category.lp emdash3_2_commutative_algebra_product.lp emdash3_2_commutative_algebra_f2.lp emdash3_2_commutative_algebra_finite.lp emdash3_2_commutative_algebra_finite_modules.lp emdash3_2_commutative_algebra_presentations.lp emdash3_2_commutative_algebra_bounded_free_complexes.lp emdash3_2_commutative_algebra_bounded_free_chain_maps.lp emdash3_2_commutative_algebra_finite_free_category.lp emdash3_2_commutative_algebra_presentation_operations.lp emdash3_2_commutative_algebra_matrix_additive_laws.lp emdash3_2_commutative_algebra_matrix_subtractive_laws.lp emdash3_2_commutative_algebra_presentation_additive_operations.lp emdash3_2_commutative_algebra_presentation_subtractive_operations.lp emdash3_2_commutative_algebra_presentation_agreement_operations.lp emdash3_2_commutative_algebra_freyd_presentations.lp emdash3_2_commutative_algebra_freyd_operations.lp emdash3_2_commutative_algebra_freyd_usability.lp emdash3_2_commutative_algebra_freyd_preadditive_class_laws.lp emdash3_2_commutative_algebra_freyd_preadditive_laws.lp emdash3_2_commutative_algebra_freyd_preadditive.lp emdash3_2_commutative_algebra_polynomial.lp emdash3_2_commutative_algebra_localization.lp emdash3_2_commutative_algebra_localization_unit.lp emdash3_2_commutative_algebra_localization_zero.lp emdash3_2_commutative_algebra_localization_idempotent.lp emdash3_2_commutative_algebra_localization_comparison.lp emdash3_2_commutative_algebra_localization_overlap.lp emdash3_2_commutative_algebra_presheaves.lp emdash3_2_walking_end_hit.lp emdash3_2_eq1_hom_action.lp emdash3_2_eq1_evidence_property.lp emdash3_2_telescope_localization_hit.lp emdash3_2_integer_localization.lp emdash3_2_circle_hit.lp emdash3_2_groupoidal_interval_hit.lp emdash3_2_walking_interval_comparison.lp emdash3_2_walking_interval_restriction.lp emdash3_2_walking_interval_extension.lp emdash3_2_walking_interval_universality.lp emdash3_2_walking_circle_completion.lp emdash3_2_walking_circle_restriction.lp emdash3_2_walking_circle_extension.lp emdash3_2_walking_circle_universality.lp emdash3_2_walking_circle_monodromy.lp emdash3_2_groupoidal_closure.lp emdash3_2_path_pseudo_laxity.lp emdash3_2_gray_profiles.lp emdash3_2_walking_arrow.lp emdash3_2_gray_right_closure.lp emdash3_2_gray_walking_square.lp emdash3_2_gray_interchanger.lp emdash3_2_truncation_reflector.lp emdash3_2_truncation_set_path_induction.lp emdash3_2_circle_connectedness.lp emdash3_2_sieves.lp emdash3_2_sites.lp emdash3_2_sieve_extensions.lp emdash3_2_generated_topologies.lp emdash3_2_ringed_sites.lp emdash3_2_site_basis.lp emdash3_2_commutative_algebra_ringed_space_covers.lp emdash3_2_commutative_algebra_binary_covers.lp emdash3_2_commutative_algebra_ringed_space_restrictions.lp emdash3_2_commutative_algebra_locality.lp emdash3_2_commutative_algebra_local_ringed_sites.lp emdash3_2_commutative_algebra_matching.lp emdash3_2_commutative_algebra_glue.lp emdash3_2_commutative_algebra_affine_glue.lp emdash3_2_commutative_algebra_zariski.lp emdash3_2_commutative_algebra_zariski_topology.lp emdash3_2_commutative_algebra_localization_split.lp emdash3_2_commutative_algebra_affine_spec.lp emdash3_2_commutative_algebra_affine_zariski.lp emdash3_2_commutative_algebra_affine_ringed_sites.lp emdash3_2_commutative_algebra_affine_locality.lp emdash3_2_commutative_algebra_affine_schemes.lp emdash3_2_commutative_algebra_affine_basis.lp emdash3_2_commutative_algebra_affine_cover_charts.lp emdash3_2_commutative_algebra_affine_cover_presentations.lp emdash3_2_commutative_algebra_affine_cover_refinements.lp emdash3_2_commutative_algebra_locally_ringed_space_presentations.lp emdash3_2_commutative_algebra_site_relative_schemes.lp emdash3_2_commutative_algebra_affine_points.lp emdash3_2_commutative_algebra_affine_intersections.lp emdash3_2_commutative_algebra_affine_atlas.lp)
  files+=(emdash3_2_finite_family_sums.lp)
  files+=(emdash3_2_commutative_algebra_matrix_blocks.lp)
  files+=(emdash3_2_commutative_algebra_matrix_block_laws.lp)
  files+=(emdash3_2_commutative_algebra_matrix_zero_rows.lp)
  files+=(emdash3_2_commutative_algebra_finite_free_direct_sums.lp)
  files+=(emdash3_2_commutative_algebra_finite_free_preadditive.lp)
  files+=(emdash3_2_commutative_algebra_finite_free_binary_products.lp)
  files+=(emdash3_2_commutative_algebra_finite_free_terminal_zero.lp)
  files+=(emdash3_2_commutative_algebra_finite_free_cartesian.lp)
  files+=(emdash3_2_commutative_algebra_finite_free_additive.lp)
  files+=(emdash3_2_commutative_algebra_presentation_direct_sums.lp)
  files+=(emdash3_2_commutative_algebra_presentation_direct_sum_agreements.lp)
  files+=(emdash3_2_commutative_algebra_freyd_direct_sums.lp)
  files+=(emdash3_2_commutative_algebra_freyd_binary_products.lp)
  files+=(emdash3_2_commutative_algebra_freyd_terminal_zero.lp)
  files+=(emdash3_2_commutative_algebra_freyd_cartesian.lp)
  files+=(emdash3_2_additive_categories.lp)
  files+=(emdash3_2_weak_kernels.lp)
  files+=(emdash3_2_computational_weak_pullbacks.lp)
  files+=(emdash3_2_computational_weak_pullback_compatibility.lp)
  files+=(emdash3_2_computational_weak_pullback_cones.lp)
  files+=(emdash3_2_kernels_cokernels.lp)
  files+=(emdash3_2_computational_fiber_products.lp)
  files+=(emdash3_2_computational_pushouts.lp)
  files+=(emdash3_2_computational_homology.lp)
  files+=(emdash3_2_short_exact_sequences.lp)
  files+=(emdash3_2_abelian_categories.lp)
  files+=(emdash3_2_abelian_fiber_pushout_stability.lp)
  files+=(emdash3_2_preabelian_bimorphism_lemmas.lp)
  files+=(emdash3_2_abelian_images.lp)
  files+=(emdash3_2_abelian_image_bimorphisms.lp)
  files+=(emdash3_2_abelian_snake_lemma.lp)
  files+=(emdash3_2_abelian_snake_normal_epi_foundation.lp)
  files+=(emdash3_2_abelian_snake_normal_epi.lp)
  files+=(emdash3_2_abelian_snake_normal_mono_foundation.lp)
  files+=(emdash3_2_abelian_snake_normal_mono_test_foundation.lp)
  files+=(emdash3_2_abelian_snake_connecting.lp)
  files+=(emdash3_2_abelian_snake_connecting_result.lp)
  files+=(emdash3_2_abelian_bimorphisms.lp)
  files+=(emdash3_2_commutative_algebra_freyd_additive.lp)
  files+=(emdash3_2_commutative_algebra_freyd_cokernels.lp)
  files+=(emdash3_2_commutative_algebra_freyd_kernels.lp)
  files+=(emdash3_2_commutative_algebra_freyd_witnessed_preabelian.lp)
  files+=(emdash3_2_commutative_algebra_freyd_normal_monomorphisms.lp)
  files+=(emdash3_2_commutative_algebra_freyd_normal_epimorphisms.lp)
  files+=(emdash3_2_commutative_algebra_freyd_witnessed_abelian.lp)
  files+=(emdash3_2_commutative_algebra_freyd_snake_connecting.lp)
  files+=(emdash3_2_commutative_algebra_freyd_homology.lp)
  files+=(emdash3_2_commutative_algebra_freyd_functorial_homology.lp)
  files+=(emdash3_2_commutative_algebra_freyd_bounded_complexes.lp)
  files+=(emdash3_2_commutative_algebra_freyd_images.lp)
  files+=(emdash3_2_gray_interchanger_orientation.lp)
  files+=(emdash3_2_gray_transformation_graph.lp)
  files+=(emdash3_2_gray_cubes.lp)
  files+=(emdash3_2_gray_transformation_graph_profile.lp)
  files+=(emdash3_2_gray_cube_decoder.lp)
  files+=(emdash3_2_gray_cube_dimension2.lp)
  files+=(emdash3_2_monads.lp)
  files+=(emdash3_2_triangular_binary_products.lp)
  files+=(emdash3_2_terminal_objects.lp)
  files+=(emdash3_2_cartesian_categories.lp)
  files+=(emdash3_2_triangular_binary_products_finite_limits.lp)
  files+=(emdash3_2_pullbacks.lp)
  files+=(emdash3_2_slice_dependent_products.lp)
  files+=(emdash3_2_checks.lp)
  files+=(emdash3_2_semisimplicial_face_codes.lp)
  files+=(emdash3_2_semisimplicial_index.lp)
  files+=(emdash3_2_simplex_shapes.lp)
  files+=(emdash3_2_coherent_nerve_levels.lp)
  files+=(emdash3_2_tetrahedron_faces.lp)
  files+=(emdash3_2_join_mapping_recursion.lp)
  files+=(emdash3_2_join_cross_compatibility.lp)
  files+=(emdash3_2_join_generator_compatibility.lp)
  files+=(emdash3_2_face_realization.lp)
  files+=(emdash3_2_dependent_simplex_bridge.lp)
  files+=(emdash3_2_dependent_simplex_path_associator.lp)
  files+=(emdash3_2_dependent_simplex_represented_source.lp)
  files+=(emdash3_2_dependent_simplex_native_dimensions.lp)
  files+=(emdash3_2_dependent_simplex_dimension4.lp)
  files+=(emdash3_2_dependent_simplex_codes.lp)
  files+=(emdash3_2_dependent_simplex_code_map.lp)
  files+=(emdash3_2_dependent_simplex_faces.lp)
  files+=(emdash3_2_shaped_pathout.lp)
  files+=(emdash3_2_pathout_transformation_reframing.lp)
  files+=(emdash3_2_pathout_transformation_lift.lp)
  files+=(emdash3_2_ordinal_join_pathout_successor.lp)
  files+=(emdash3_2_dependent_simplex_ordinal_adequacy.lp)
  files+=(emdash3_2_dependent_simplex_ordinal_filler.lp)
  files+=(emdash3_2_dependent_simplex_ordinal_dimension3.lp)
  files+=(emdash3_2_dependent_simplex_ordinal_dimension4.lp)
  files+=(emdash3_2_dependent_simplex_ordinal_recursive.lp)
  files+=(emdash3_2_prof_reindex_terminal_normalization.lp)
  files+=(emdash3_2_cubical_dependent_hom.lp)
  files+=(emdash3_2_cubical_square_total.lp)
  files+=(emdash3_2_cubical_internalization.lp)
  files+=(emdash3_2_cubical_arrow.lp)
  files+=(emdash3_2_cubical_arrow_composition.lp)
  files+=(emdash3_2_readable_pseudofunctors.lp)
  files+=(emdash3_2_cubical_arrow_functor.lp)
  files+=(emdash3_2_cubical_square_level.lp)
  files+=(emdash3_2_cubical_levels.lp)
  files+=(emdash3_2_semicubical_face_codes.lp)
  files+=(emdash3_2_semicubical_index.lp)
  files+=(emdash3_2_semicubical_face_action.lp)
  files+=(emdash3_2_semicubical_nerve.lp)
  files+=(emdash3_2_semicubical_frames.lp)
  files+=(emdash3_2_semicubical_representables.lp)
  files+=(emdash3_2_cubical.lp)
  files+=(emdash3_2_cubical_yoneda.lp)
  files+=(emdash3_2_semisimplicial_diagrams.lp)
  files+=(emdash3_2_simplex2_sieves.lp)
  files+=(emdash3_2_path_groupoid_2horn_fillers.lp)
  files+=(emdash3_2_semisimplicial_decalage.lp)
  files+=(emdash3_2_finite_limits.lp)
  files+=(emdash3_2_direct_cover_questions.lp)
  files+=(emdash3_2_direct_cover_question_families.lp)
  files+=(emdash3_2_direct_cover_algebras.lp)
  files+=(emdash3_2_direct_cover_internal_sheaves.lp)
  files+=(emdash3_2_direct_cover_completion_hit.lp)
  files+=(emdash3_2_direct_cover_completion_eliminator.lp)
  files+=(emdash3_2_groupoidification_hit.lp)
  files+=(emdash3_2_groupoidification_universality.lp)
  files+=(emdash3_2_set_path_pointwise_transformation.lp)
  files+=(emdash3_2_groupoidification_set_extensionality.lp)
  files+=(emdash3_2_groupoidification_composition.lp)
  files+=(emdash3_2_groupoidification_interval_recovery.lp)
  files+=(emdash3_2_commutative_algebra_scheme_chart_overlaps.lp)
  files+=(emdash3_2_commutative_algebra_laurent.lp)
  files+=(emdash3_2_commutative_algebra_scheme_laurent_overlaps.lp)
  files+=(emdash3_2_commutative_algebra_projective_line.lp)
fi

for file in "${files[@]}"; do
  check_file "$file"
done
