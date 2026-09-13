#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import time
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CORE_CHECK_FILES = [
    Path("emdash3_2.lp"),
    Path("emdash3_2_preadditive_categories.lp"),
    Path("emdash3_2_additive_categories.lp"),
    Path("emdash3_2_weak_kernels.lp"),
    Path("emdash3_2_computational_weak_pullbacks.lp"),
    Path("emdash3_2_computational_weak_pullback_compatibility.lp"),
    Path("emdash3_2_computational_weak_pullback_cones.lp"),
    Path("emdash3_2_kernels_cokernels.lp"),
    Path("emdash3_2_computational_fiber_products.lp"),
    Path("emdash3_2_computational_pushouts.lp"),
    Path("emdash3_2_computational_homology.lp"),
    Path("emdash3_2_short_exact_sequences.lp"),
    Path("emdash3_2_exactness_reindex.lp"),
    Path("emdash3_2_abelian_categories.lp"),
    Path("emdash3_2_abelian_fiber_pushout_stability.lp"),
    Path("emdash3_2_preabelian_bimorphism_lemmas.lp"),
    Path("emdash3_2_abelian_images.lp"),
    Path("emdash3_2_abelian_image_bimorphisms.lp"),
    Path("emdash3_2_abelian_snake_lemma.lp"),
    Path("emdash3_2_abelian_snake_six_term_kernel_beta_foundation.lp"),
    Path("emdash3_2_abelian_snake_six_term_kernels.lp"),
    Path("emdash3_2_abelian_snake_six_term_cokernel_beta_foundation.lp"),
    Path("emdash3_2_abelian_snake_six_term_cokernels.lp"),
    Path("emdash3_2_abelian_snake_six_term_kernel_zero_foundation.lp"),
    Path("emdash3_2_abelian_snake_six_term_kernel_zero.lp"),
    Path("emdash3_2_abelian_snake_six_term_cokernel_zero_foundation.lp"),
    Path("emdash3_2_abelian_snake_six_term_cokernel_zero.lp"),
    Path("emdash3_2_abelian_snake_six_term_inner_kernel_factor.lp"),
    Path("emdash3_2_abelian_snake_six_term_inner_cokernel_cofactor.lp"),
    Path("emdash3_2_abelian_snake_six_term_inner_cokernel_middle_zero_foundation.lp"),
    Path("emdash3_2_abelian_snake_normal_epi_foundation.lp"),
    Path("emdash3_2_abelian_snake_normal_epi.lp"),
    Path("emdash3_2_abelian_snake_normal_mono_foundation.lp"),
    Path("emdash3_2_abelian_snake_normal_mono_test_foundation.lp"),
    Path("emdash3_2_abelian_snake_connecting.lp"),
    Path("emdash3_2_abelian_snake_covered_reconstruction.lp"),
    Path("emdash3_2_abelian_snake_connecting_result.lp"),
    Path("emdash3_2_abelian_snake_six_term_inner_kernel_u_zero_foundation.lp"),
    Path("emdash3_2_abelian_snake_six_term_inner_kernel_q2_zero_foundation.lp"),
    Path("emdash3_2_abelian_snake_six_term_inner_kernel_zero.lp"),
    Path("emdash3_2_abelian_snake_six_term_inner_cokernel_p1_zero_foundation.lp"),
    Path("emdash3_2_abelian_snake_six_term_inner_cokernel_zero.lp"),
    Path("emdash3_2_abelian_snake_six_term_result.lp"),
    Path("emdash3_2_abelian_snake_six_term_result_projections.lp"),
    Path("emdash3_2_exactness_covers_foundation.lp"),
    Path("emdash3_2_exactness_covers.lp"),
    Path("emdash3_2_exactness_covers_from_exact.lp"),
    Path("emdash3_2_abelian_canonical_kernel_exactness.lp"),
    Path("emdash3_2_abelian_canonical_cokernel_foundation.lp"),
    Path("emdash3_2_abelian_canonical_cokernel_factor.lp"),
    Path("emdash3_2_abelian_canonical_cokernel_epic.lp"),
    Path("emdash3_2_abelian_canonical_cokernel_exactness.lp"),
    Path("emdash3_2_abelian_canonical_cokernel_covers.lp"),
    Path("emdash3_2_abelian_snake_exact_first_foundation.lp"),
    Path("emdash3_2_abelian_snake_exact_first_row_cover_projections.lp"),
    Path("emdash3_2_abelian_snake_exact_first_alpha_zero.lp"),
    Path("emdash3_2_abelian_snake_exact_first_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_first_comparison.lp"),
    Path("emdash3_2_abelian_snake_exact_first_result.lp"),
    Path("emdash3_2_preadditive_difference_paths.lp"),
    Path("emdash3_2_abelian_snake_exact_second_pullback.lp"),
    Path("emdash3_2_abelian_snake_exact_second_xi.lp"),
    Path("emdash3_2_abelian_snake_exact_second_q2_pi.lp"),
    Path("emdash3_2_abelian_snake_exact_second_pi_zero.lp"),
    Path("emdash3_2_abelian_snake_exact_second_alpha_cover_foundation.lp"),
    Path("emdash3_2_abelian_snake_exact_second_alpha_cover_object.lp"),
    Path("emdash3_2_abelian_snake_exact_second_alpha_cover_epi.lp"),
    Path("emdash3_2_abelian_snake_exact_second_alpha_cover_epic.lp"),
    Path("emdash3_2_abelian_snake_exact_second_alpha_cover_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_second_beta_difference.lp"),
    Path("emdash3_2_abelian_snake_exact_second_kernel_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_second_epsilon_paths.lp"),
    Path("emdash3_2_abelian_snake_exact_second_epsilon_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_second_iota_comparison.lp"),
    Path("emdash3_2_abelian_snake_exact_second_cover_comparison.lp"),
    Path("emdash3_2_abelian_snake_exact_second_total_cover.lp"),
    Path("emdash3_2_abelian_snake_exact_second_cover_witness.lp"),
    Path("emdash3_2_abelian_snake_exact_second_result.lp"),
    Path("emdash3_2_exactness_extensions_foundation.lp"),
    Path("emdash3_2_exactness_extensions_to_exact_foundation.lp"),
    Path("emdash3_2_exactness_extensions_to_exact_extension.lp"),
    Path("emdash3_2_exactness_extensions_to_exact_zero.lp"),
    Path("emdash3_2_exactness_extensions_to_exact.lp"),
    Path("emdash3_2_abelian_canonical_kernel_extensions_foundation.lp"),
    Path("emdash3_2_abelian_canonical_kernel_extensions.lp"),
    Path("emdash3_2_abelian_snake_exact_third_pushout.lp"),
    Path("emdash3_2_abelian_snake_exact_third_zeta.lp"),
    Path("emdash3_2_abelian_snake_exact_third_zeta_epsilon.lp"),
    Path("emdash3_2_abelian_snake_exact_third_zeta_iota_to_su.lp"),
    Path("emdash3_2_abelian_snake_exact_third_su_path.lp"),
    Path("emdash3_2_abelian_snake_exact_third_zeta_zero.lp"),
    Path("emdash3_2_abelian_snake_exact_third_gamma_extension_foundation.lp"),
    Path("emdash3_2_abelian_snake_exact_third_gamma_extension_object.lp"),
    Path("emdash3_2_abelian_snake_exact_third_gamma_extension_monomorphism.lp"),
    Path("emdash3_2_abelian_snake_exact_third_gamma_extension_is_monic.lp"),
    Path("emdash3_2_abelian_snake_exact_third_gamma_extension_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_third_gamma_extension_path.lp"),
    Path("emdash3_2_abelian_snake_exact_third_beta_difference.lp"),
    Path("emdash3_2_abelian_snake_exact_third_cokernel_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_third_mu_reconstruction.lp"),
    Path("emdash3_2_abelian_snake_exact_third_difference_mu.lp"),
    Path("emdash3_2_abelian_snake_exact_third_pi_comparison.lp"),
    Path("emdash3_2_abelian_snake_exact_third_pi_epic.lp"),
    Path("emdash3_2_abelian_snake_exact_third_extension_comparison.lp"),
    Path("emdash3_2_abelian_snake_exact_third_extension_witness.lp"),
    Path("emdash3_2_abelian_snake_exact_third_result.lp"),
    Path("emdash3_2_abelian_snake_exact_fourth_foundation.lp"),
    Path("emdash3_2_abelian_snake_exact_fourth_extension.lp"),
    Path("emdash3_2_abelian_snake_exact_fourth_extension_projections.lp"),
    Path("emdash3_2_abelian_snake_exact_fourth_gamma_zero.lp"),
    Path("emdash3_2_abelian_snake_exact_fourth_cokernel_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_fourth_comparison.lp"),
    Path("emdash3_2_abelian_snake_exact_fourth_result.lp"),
    Path("emdash3_2_abelian_snake_six_term_exact_pairs.lp"),
    Path("emdash3_2_abelian_snake_six_term_exact_data_intro.lp"),
    Path("emdash3_2_abelian_snake_six_term_exact_result_foundation.lp"),
    Path("emdash3_2_abelian_snake_six_term_exact_result_projections.lp"),
    Path("emdash3_2_abelian_snake_six_term_exact_pair_paths.lp"),
    Path("emdash3_2_abelian_snake_six_term_canonical_exactness.lp"),
    Path("emdash3_2_abelian_snake_six_term_exact_result.lp"),
    Path("emdash3_2_abelian_bimorphisms.lp"),
    Path("emdash3_2_iso_evidence_constructors.lp"),
    Path("emdash3_2_mono_epi_comparisons.lp"),
    Path("emdash3_2_cokernel_composite_comparison.lp"),
    Path("emdash3_2_cokernel_composite_pushout.lp"),
    Path("emdash3_2_cokernel_composite_monic.lp"),
    Path("emdash3_2_abelian_cokernel_composite_monic.lp"),
    Path("emdash3_2_homology_cokernel_inclusion.lp"),
    Path("emdash3_2_homology_cokernel_inclusion_monic.lp"),
    Path("emdash3_2_abelian_homology_cokernel_inclusion.lp"),
    Path("emdash3_2_hom_factor_spaces.lp"),
    Path("emdash3_2_hom_factor_cubical.lp"),
    Path("emdash3_2_hom_factor_source_isos.lp"),
    Path("emdash3_2_hom_factor_composition.lp"),
    Path("emdash3_2_hom_factor_views.lp"),
    Path("emdash3_2_hom_factor_epic_descent.lp"),
    Path("emdash3_2_cokernel_monic_factor_descent.lp"),
    Path("emdash3_2_iso_evidence_monic.lp"),
    Path("emdash3_2_kernel_maps.lp"),
    Path("emdash3_2_strict_transfor_component_paths.lp"),
    Path("emdash3_2_kernel_cokernel_adjunctions.lp"),
    Path("emdash3_2_image_coimage_adjunction_families.lp"),
    Path("emdash3_2_kernel_adjunction_presentations.lp"),
    Path("emdash3_2_cokernel_adjunction_presentations.lp"),
    Path("emdash3_2_adjunction_mates.lp"),
    Path("emdash3_2_kernel_cokernel_adjunction_mates.lp"),
    Path("emdash3_2_zero_arrow_diagram_observations.lp"),
    Path("emdash3_2_zero_arrow_universal_tests.lp"),
    Path("emdash3_2_kernel_cokernel_adjunction_observations.lp"),
    Path("emdash3_2_kernel_adjunction_mates.lp"),
    Path("emdash3_2_cokernel_adjunction_mates.lp"),
    Path("emdash3_2_homology_adjunction_families.lp"),
    Path("emdash3_2_homology_families.lp"),
    Path("emdash3_2_homology_family_selected_views.lp"),
    Path("emdash3_2_zero_arrow_cones.lp"),
    Path("emdash3_2_one_cat_zero_cones.lp"),
    Path("emdash3_2_zero_arrow_cone_chain_pairs.lp"),
    Path("emdash3_2_zero_arrow_cone_adjunction_homology.lp"),
    Path("emdash3_2_zero_arrow_cone_homology.lp"),
    Path("emdash3_2_commutative_algebra_freyd_zero_cones.lp"),
    Path("emdash3_2_kernel_adjunction_unmates.lp"),
    Path("emdash3_2_kernel_adjunction_unmate_paths.lp"),
    Path("emdash3_2_chain_pair_diagrams.lp"),
    Path("emdash3_2_chain_pair_zero_cones.lp"),
    Path("emdash3_2_chain_pair_zero_cone_comparisons.lp"),
    Path("emdash3_2_kernel_adjunction_records.lp"),
    Path("emdash3_2_cokernel_adjunction_records.lp"),
    Path("emdash3_2_homology_adjunction_record_data.lp"),
    Path("emdash3_2_homology_family_records.lp"),
    Path("emdash3_2_chain_pair_homology_records.lp"),
    Path("emdash3_2_commutative_algebra_freyd_chain_pair_data.lp"),
    Path("emdash3_2_commutative_algebra_freyd_zero_cone_inputs.lp"),
    Path("emdash3_2_one_cat_arrow_diagrams.lp"),
    Path("emdash3_2_walking_arrow_native_observation.lp"),
    Path("emdash3_2_functor_reconstruction_paths.lp"),
    Path("emdash3_2_one_cat_diagram_reconstruction.lp"),
    Path("emdash3_2_one_cat_zero_arrow_inputs.lp"),
    Path("emdash3_2_one_cat_chain_pair_inputs.lp"),
    Path("emdash3_2_one_cat_zero_diagram_inputs.lp"),
    Path("emdash3_2_one_cat_native_square_paths.lp"),
    Path("emdash3_2_one_cat_diagram_map_paths.lp"),
    Path("emdash3_2_one_cat_adjunction_cancellation.lp"),
    Path("emdash3_2_one_cat_adjunction_records.lp"),
    Path("emdash3_2_one_cat_adjunction_selected_views.lp"),
    Path("emdash3_2_one_cat_homology_adjunction_records.lp"),
    Path("emdash3_2_one_cat_chain_pair_homology_records.lp"),
    Path("emdash3_2_commutative_algebra_freyd_native_inputs.lp"),
    Path("emdash3_2_commutative_algebra_freyd_adjunction_homology.lp"),
    Path("emdash3_2_chain_pair_diagram_maps.lp"),
    Path("emdash3_2_one_cat_chain_pair_native_maps.lp"),
    Path("emdash3_2_one_cat_chain_pair_homology_maps.lp"),
    Path("emdash3_2_adjunction_untranspose_naturality.lp"),
    Path("emdash3_2_zero_arrow_cone_map_introduction.lp"),
    Path("emdash3_2_kernel_presentation_inclusion_properties.lp"),
    Path("emdash3_2_kernel_presentation_boundary_naturality.lp"),
    Path("emdash3_2_chain_pair_zero_cone_maps.lp"),
    Path("emdash3_2_commutative_algebra_freyd_chain_map_data.lp"),
    Path("emdash3_2_commutative_algebra_freyd_native_maps.lp"),
    Path("emdash3_2_commutative_algebra_freyd_adjunction_homology_maps.lp"),
    Path("emdash3_2_commutative_algebra_freyd_zero_cone_maps.lp"),
    Path("emdash3_2_commutative_algebra_freyd_homology_models.lp"),
    Path("emdash3_2_commutative_algebra_freyd_homology_model_records.lp"),
    Path("emdash3_2_commutative_algebra_freyd_homology_model_connecting.lp"),
    Path("emdash3_2_commutative_algebra_freyd_homology_model_normality.lp"),
    Path("emdash3_2_commutative_algebra_freyd_chain_map_introduction.lp"),
    Path("emdash3_2_commutative_algebra_freyd_homology_model_maps.lp"),
    Path("emdash3_2_kernel_map_laws.lp"),
    Path("emdash3_2_kernel_map_isos.lp"),
    Path("emdash3_2_cokernel_maps.lp"),
    Path("emdash3_2_cokernel_map_laws.lp"),
    Path("emdash3_2_cokernel_map_isos.lp"),
    Path("emdash3_2_chain_pair_maps.lp"),
    Path("emdash3_2_chain_pair_cubical_maps.lp"),
    Path("emdash3_2_chain_pair_native_triangles.lp"),
    Path("emdash3_2_chain_pair_map_cycle_lifts.lp"),
    Path("emdash3_2_chain_pair_map_composition.lp"),
    Path("emdash3_2_homology_cycle_maps.lp"),
    Path("emdash3_2_homology_maps.lp"),
    Path("emdash3_2_homology_cycle_map_laws.lp"),
    Path("emdash3_2_homology_map_laws.lp"),
    Path("emdash3_2_homology_map_isos.lp"),
    Path("emdash3_2_chain_pair_map_snake.lp"),
    Path("emdash3_2_snake_row_comparisons.lp"),
    Path("emdash3_2_kernel_domain_comparison.lp"),
    Path("emdash3_2_iso_comparison_reconstruction.lp"),
    Path("emdash3_2_hfiber_cancellation.lp"),
    Path("emdash3_2_hom_factor_universality.lp"),
    Path("emdash3_2_short_exact_universal_records.lp"),
    Path("emdash3_2_homology_connecting_cover.lp"),
    Path("emdash3_2_homology_connecting_left_lift.lp"),
    Path("emdash3_2_homology_connecting_target_cycles.lp"),
    Path("emdash3_2_homology_connecting_cover_kernel.lp"),
    Path("emdash3_2_homology_connecting_cover_kernel_lift.lp"),
    Path("emdash3_2_homology_record_boundary_factors.lp"),
    Path("emdash3_2_homology_connecting_cover_kernel_boundary.lp"),
    Path("emdash3_2_homology_connecting_cycles_descent.lp"),
    Path("emdash3_2_homology_connecting_source_boundary_cover.lp"),
    Path("emdash3_2_homology_connecting_source_boundary_zero.lp"),
    Path("emdash3_2_homology_connecting_source_boundary_descent.lp"),
    Path("emdash3_2_homology_record_connecting.lp"),
    Path("emdash3_2_hom_factor_zero_descent.lp"),
    Path("emdash3_2_homology_record_cancellation.lp"),
    Path("emdash3_2_homology_family_map_factors.lp"),
    Path("emdash3_2_chain_pair_homology_actions.lp"),
    Path("emdash3_2_homology_connecting_projection_zero.lp"),
    Path("emdash3_2_homology_connecting_inclusion_zero.lp"),
    Path("emdash3_2_homology_window.lp"),
    Path("emdash3_2_homology_connecting_cover_quotient.lp"),
    Path("emdash3_2_homology_connecting_characterization.lp"),
    Path("emdash3_2_homology_boundary_naturality.lp"),
    Path("emdash3_2_cokernel_record_covers.lp"),
    Path("emdash3_2_homology_map_kernel_covers.lp"),
    Path("emdash3_2_homology_map_corrections.lp"),
    Path("emdash3_2_chain_pair_cycle_factors.lp"),
    Path("emdash3_2_homology_record_cycle_lifts.lp"),
    Path("emdash3_2_homology_first_exactness.lp"),
    Path("emdash3_2_homology_epic_covers.lp"),
    Path("emdash3_2_homology_second_exactness.lp"),
    Path("emdash3_2_homology_third_exactness.lp"),
    Path("emdash3_2_homology_exact_window.lp"),
    Path("emdash3_2_homology_exact_window_result.lp"),
    Path("emdash3_2_finite_arrow_tails.lp"),
    Path("emdash3_2_finite_arrow_tail_append.lp"),
    Path("emdash3_2_computational_exact_arrow_tails.lp"),
    Path("emdash3_2_preadditive_zero_identity.lp"),
    Path("emdash3_2_homology_record_zero.lp"),
    Path("emdash3_2_homology_whole_zero.lp"),
    Path("emdash3_2_homology_window_extension.lp"),
    Path("emdash3_2_homology_row_triples.lp"),
    Path("emdash3_2_homology_row_spans.lp"),
    Path("emdash3_2_finite_arrow_tail_arrows.lp"),
    Path("emdash3_2_finite_arrow_tail_init.lp"),
    Path("emdash3_2_short_exact_row_zero.lp"),
    Path("emdash3_2_homology_row_field_spans.lp"),
    Path("emdash3_2_homology_row_field_span_case.lp"),
    Path("emdash3_2_homology_row_fields_extension.lp"),
    Path("emdash3_2_homology_bounded_generator.lp"),
    Path("emdash3_2_short_exact_row_families.lp"),
    Path("emdash3_2_homology_window_families.lp"),
    Path("emdash3_2_homology_window_columns.lp"),
    Path("emdash3_2_homology_window_column_usability.lp"),
    Path("emdash3_2_homology_window_connecting_transformation.lp"),
    Path("emdash3_2_kernel_domain_comparison_factors.lp"),
    Path("emdash3_2_cokernel_codomain_comparison.lp"),
    Path("emdash3_2_snake_row_source_cycle_iso.lp"),
    Path("emdash3_2_snake_row_source_cycle_factor.lp"),
    Path("emdash3_2_snake_row_target_cokernel_iso.lp"),
    Path("emdash3_2_abelian_structure_elimination.lp"),
    Path("emdash3_2_abelian_snake_row_comparisons.lp"),
    Path("emdash3_2_short_exact_row_snake.lp"),
    Path("emdash3_2_short_exact_kernel_comparison.lp"),
    Path("emdash3_2_short_exact_cokernel_foundation.lp"),
    Path("emdash3_2_short_exact_cokernel_inverse_test.lp"),
    Path("emdash3_2_short_exact_cokernel_comparison.lp"),
    Path("emdash3_2_short_exact_rows.lp"),
    Path("emdash3_2_short_exact_row_chain_columns.lp"),
    Path("emdash3_2_hom_factor_chain_zero.lp"),
    Path("emdash3_2_short_exact_row_chain_projection.lp"),
    Path("emdash3_2_snake_row_source_compared_boundary.lp"),
    Path("emdash3_2_abelian_snake_second_postcomposition.lp"),
    Path("emdash3_2_snake_row_source_embedding_monic.lp"),
    Path("emdash3_2_snake_row_source_second_comparison.lp"),
    Path("emdash3_2_snake_row_source_upper_factor.lp"),
    Path("emdash3_2_snake_row_source_boundary_covered.lp"),
    Path("emdash3_2_snake_row_source_boundary_zero.lp"),
    Path("emdash3_2_snake_row_target_factors.lp"),
    Path("emdash3_2_snake_row_target_cycles.lp"),
    Path("emdash3_2_normal_mono_epic_factors.lp"),
    Path("emdash3_2_hom_factor_comparison_pasting.lp"),
    Path("emdash3_2_normal_mono_cycle_factors.lp"),
    Path("emdash3_2_cokernel_codomain_comparison_projection.lp"),
    Path("emdash3_2_snake_row_target_cokernel_projection.lp"),
    Path("emdash3_2_snake_row_target_homology_normal.lp"),
    Path("emdash3_2_snake_row_target_homology_factor.lp"),
    Path("emdash3_2_homology_connecting_factor.lp"),
    Path("emdash3_2_homology_connecting.lp"),
    Path("emdash3_2_kernel_short_exact_rows.lp"),
    Path("emdash3_2_selected_short_exact_rows.lp"),
    Path("emdash3_2_monic_image_comparison.lp"),
    Path("emdash3_2_short_exact_row_comparison_fibres.lp"),
    Path("emdash3_2_monic_selected_row_comparison.lp"),
    Path("emdash3_2_short_exact_normalization_foundation.lp"),
    Path("emdash3_2_short_exact_normalization_isos.lp"),
    Path("emdash3_2_short_exact_normalization_projections.lp"),
    Path("emdash3_2_short_exact_normalization.lp"),
    Path("emdash3_2_presheaves.lp"),
    Path("emdash3_2_fibrewise_sigma.lp"),
    Path("emdash3_2_nat_arithmetic.lp"),
    Path("emdash3_2_finite_families.lp"),
    Path("emdash3_2_finite_family_sums.lp"),
    Path("emdash3_2_finite_limits.lp"),
    Path("emdash3_2_commutative_algebra.lp"),
    Path("emdash3_2_commutative_algebra_derived_laws.lp"),
    Path("emdash3_2_commutative_algebra_category.lp"),
    Path("emdash3_2_commutative_algebra_product.lp"),
    Path("emdash3_2_commutative_algebra_f2.lp"),
    Path("emdash3_2_commutative_algebra_finite.lp"),
    Path("emdash3_2_commutative_algebra_finite_modules.lp"),
    Path("emdash3_2_commutative_algebra_presentations.lp"),
    Path("emdash3_2_commutative_algebra_bounded_free_complexes.lp"),
    Path("emdash3_2_commutative_algebra_bounded_free_chain_maps.lp"),
    Path("emdash3_2_commutative_algebra_finite_free_category.lp"),
    Path("emdash3_2_commutative_algebra_finite_free_direct_sums.lp"),
    Path("emdash3_2_commutative_algebra_finite_free_preadditive.lp"),
    Path("emdash3_2_commutative_algebra_finite_free_binary_products.lp"),
    Path("emdash3_2_commutative_algebra_finite_free_terminal_zero.lp"),
    Path("emdash3_2_commutative_algebra_finite_free_cartesian.lp"),
    Path("emdash3_2_commutative_algebra_finite_free_additive.lp"),
    Path("emdash3_2_commutative_algebra_finite_free_weak_pullbacks.lp"),
    Path("emdash3_2_commutative_algebra_freyd_kernel_choices.lp"),
    Path("emdash3_2_commutative_algebra_presentation_operations.lp"),
    Path("emdash3_2_commutative_algebra_presentation_direct_sums.lp"),
    Path("emdash3_2_commutative_algebra_presentation_direct_sum_agreements.lp"),
    Path("emdash3_2_commutative_algebra_matrix_additive_laws.lp"),
    Path("emdash3_2_commutative_algebra_matrix_blocks.lp"),
    Path("emdash3_2_commutative_algebra_matrix_block_laws.lp"),
    Path("emdash3_2_commutative_algebra_matrix_zero_rows.lp"),
    Path("emdash3_2_commutative_algebra_matrix_subtractive_laws.lp"),
    Path("emdash3_2_commutative_algebra_presentation_additive_operations.lp"),
    Path("emdash3_2_commutative_algebra_presentation_subtractive_operations.lp"),
    Path("emdash3_2_commutative_algebra_presentation_agreement_operations.lp"),
    Path("emdash3_2_commutative_algebra_freyd_presentations.lp"),
    Path("emdash3_2_commutative_algebra_freyd_operations.lp"),
    Path("emdash3_2_commutative_algebra_freyd_usability.lp"),
    Path("emdash3_2_commutative_algebra_freyd_preadditive_class_laws.lp"),
    Path("emdash3_2_commutative_algebra_freyd_preadditive_laws.lp"),
    Path("emdash3_2_commutative_algebra_freyd_preadditive.lp"),
    Path("emdash3_2_commutative_algebra_freyd_direct_sums.lp"),
    Path("emdash3_2_commutative_algebra_freyd_binary_products.lp"),
    Path("emdash3_2_commutative_algebra_freyd_terminal_zero.lp"),
    Path("emdash3_2_commutative_algebra_freyd_cartesian.lp"),
    Path("emdash3_2_commutative_algebra_freyd_additive.lp"),
    Path("emdash3_2_commutative_algebra_freyd_cokernels.lp"),
    Path("emdash3_2_commutative_algebra_freyd_kernels.lp"),
    Path("emdash3_2_commutative_algebra_freyd_kernel_compatibility.lp"),
    Path("emdash3_2_commutative_algebra_freyd_selected_kernel_embedding.lp"),
    Path("emdash3_2_commutative_algebra_freyd_selected_kernel_lifting.lp"),
    Path("emdash3_2_commutative_algebra_freyd_selected_kernel_uniqueness.lp"),
    Path("emdash3_2_commutative_algebra_freyd_kernel_choices_from_weak_kernels.lp"),
    Path("emdash3_2_commutative_algebra_freyd_kernel_choice_providers.lp"),
    Path("emdash3_2_commutative_algebra_freyd_selected_homology.lp"),
    Path("emdash3_2_commutative_algebra_freyd_actual_homology.lp"),
    Path("emdash3_2_commutative_algebra_freyd_witnessed_preabelian.lp"),
    Path("emdash3_2_commutative_algebra_freyd_normal_monomorphisms.lp"),
    Path("emdash3_2_commutative_algebra_freyd_normal_epimorphisms.lp"),
    Path("emdash3_2_commutative_algebra_freyd_witnessed_abelian.lp"),
    Path("emdash3_2_commutative_algebra_freyd_snake_connecting.lp"),
    Path("emdash3_2_commutative_algebra_freyd_homology.lp"),
    Path("emdash3_2_commutative_algebra_freyd_functorial_homology.lp"),
    Path("emdash3_2_commutative_algebra_freyd_bounded_complexes.lp"),
    Path("emdash3_2_commutative_algebra_freyd_explicit_spines.lp"),
    Path("emdash3_2_commutative_algebra_freyd_explicit_epimorphisms.lp"),
    Path("emdash3_2_commutative_algebra_freyd_bounded_chain_maps.lp"),
    Path("emdash3_2_commutative_algebra_freyd_short_exact_rows.lp"),
    Path("emdash3_2_commutative_algebra_freyd_bounded_short_exact.lp"),
    Path("emdash3_2_commutative_algebra_freyd_images.lp"),
    Path("emdash3_2_commutative_algebra_polynomial.lp"),
    Path("emdash3_2_commutative_algebra_localization.lp"),
    Path("emdash3_2_commutative_algebra_laurent.lp"),
    Path("emdash3_2_commutative_algebra_localization_unit.lp"),
    Path("emdash3_2_commutative_algebra_localization_zero.lp"),
    Path("emdash3_2_commutative_algebra_localization_idempotent.lp"),
    Path("emdash3_2_commutative_algebra_localization_comparison.lp"),
    Path("emdash3_2_commutative_algebra_localization_overlap.lp"),
    Path("emdash3_2_commutative_algebra_presheaves.lp"),
    Path("emdash3_2_walking_end_hit.lp"),
    Path("emdash3_2_eq1_hom_action.lp"),
    Path("emdash3_2_eq1_evidence_property.lp"),
    Path("emdash3_2_strict_pointwise_equivalences.lp"),
    Path("emdash3_2_telescope_localization_hit.lp"),
    Path("emdash3_2_integer_localization.lp"),
    Path("emdash3_2_circle_hit.lp"),
    Path("emdash3_2_groupoidal_interval_hit.lp"),
    Path("emdash3_2_walking_interval_comparison.lp"),
    Path("emdash3_2_walking_interval_restriction.lp"),
    Path("emdash3_2_walking_interval_extension.lp"),
    Path("emdash3_2_walking_interval_universality.lp"),
    Path("emdash3_2_groupoidification_hit.lp"),
    Path("emdash3_2_groupoidification_universality.lp"),
    Path("emdash3_2_set_path_pointwise_transformation.lp"),
    Path("emdash3_2_groupoidification_set_extensionality.lp"),
    Path("emdash3_2_groupoidification_composition.lp"),
    Path("emdash3_2_groupoidification_interval_recovery.lp"),
    Path("emdash3_2_walking_circle_completion.lp"),
    Path("emdash3_2_walking_circle_restriction.lp"),
    Path("emdash3_2_walking_circle_extension.lp"),
    Path("emdash3_2_walking_circle_universality.lp"),
    Path("emdash3_2_walking_circle_monodromy.lp"),
    Path("emdash3_2_groupoidal_closure.lp"),
    Path("emdash3_2_path_pseudo_laxity.lp"),
    Path("emdash3_2_gray_profiles.lp"),
    Path("emdash3_2_walking_arrow.lp"),
    Path("emdash3_2_diagram_evaluation.lp"),
    Path("emdash3_2_walking_arrow_introduction.lp"),
    Path("emdash3_2_arrow_diagram_families.lp"),
    Path("emdash3_2_zero_arrow_diagrams.lp"),
    Path("emdash3_2_gray_right_closure.lp"),
    Path("emdash3_2_gray_walking_square.lp"),
    Path("emdash3_2_gray_interchanger.lp"),
    Path("emdash3_2_gray_interchanger_orientation.lp"),
    Path("emdash3_2_gray_transformation_graph.lp"),
    Path("emdash3_2_gray_cubes.lp"),
    Path("emdash3_2_gray_transformation_graph_profile.lp"),
    Path("emdash3_2_gray_cube_decoder.lp"),
    Path("emdash3_2_gray_cube_dimension2.lp"),
    Path("emdash3_2_truncation_reflector.lp"),
    Path("emdash3_2_truncation_set_path_induction.lp"),
    Path("emdash3_2_semisimplicial_face_codes.lp"),
    Path("emdash3_2_semisimplicial_index.lp"),
    Path("emdash3_2_simplex_shapes.lp"),
    Path("emdash3_2_coherent_nerve_levels.lp"),
    Path("emdash3_2_tetrahedron_faces.lp"),
    Path("emdash3_2_join_mapping_recursion.lp"),
    Path("emdash3_2_join_cross_compatibility.lp"),
    Path("emdash3_2_join_generator_compatibility.lp"),
    Path("emdash3_2_face_realization.lp"),
    Path("emdash3_2_dependent_simplex_bridge.lp"),
    Path("emdash3_2_dependent_simplex_path_associator.lp"),
    Path("emdash3_2_dependent_simplex_represented_source.lp"),
    Path("emdash3_2_dependent_simplex_native_dimensions.lp"),
    Path("emdash3_2_dependent_simplex_dimension4.lp"),
    Path("emdash3_2_dependent_simplex_codes.lp"),
    Path("emdash3_2_dependent_simplex_code_map.lp"),
    Path("emdash3_2_dependent_simplex_faces.lp"),
    Path("emdash3_2_shaped_pathout.lp"),
    Path("emdash3_2_pathout_transformation_reframing.lp"),
    Path("emdash3_2_pathout_transformation_lift.lp"),
    Path("emdash3_2_ordinal_join_pathout_successor.lp"),
    Path("emdash3_2_dependent_simplex_ordinal_adequacy.lp"),
    Path("emdash3_2_dependent_simplex_ordinal_filler.lp"),
    Path("emdash3_2_dependent_simplex_ordinal_dimension3.lp"),
    Path("emdash3_2_dependent_simplex_ordinal_dimension4.lp"),
    Path("emdash3_2_dependent_simplex_ordinal_recursive.lp"),
    Path("emdash3_2_cubical_dependent_hom.lp"),
    Path("emdash3_2_cubical_square_total.lp"),
    Path("emdash3_2_cubical_internalization.lp"),
    Path("emdash3_2_cubical_arrow.lp"),
    Path("emdash3_2_cubical_arrow_composition.lp"),
    Path("emdash3_2_readable_pseudofunctors.lp"),
    Path("emdash3_2_cubical_arrow_functor.lp"),
    Path("emdash3_2_cubical_square_level.lp"),
    Path("emdash3_2_cubical_levels.lp"),
    Path("emdash3_2_semicubical_face_codes.lp"),
    Path("emdash3_2_semicubical_index.lp"),
    Path("emdash3_2_semicubical_face_action.lp"),
    Path("emdash3_2_semicubical_nerve.lp"),
    Path("emdash3_2_semicubical_frames.lp"),
    Path("emdash3_2_semicubical_representables.lp"),
    Path("emdash3_2_cubical.lp"),
    Path("emdash3_2_cubical_yoneda.lp"),
    Path("emdash3_2_semisimplicial_diagrams.lp"),
    Path("emdash3_2_simplex2_sieves.lp"),
    Path("emdash3_2_path_groupoid_2horn_fillers.lp"),
    Path("emdash3_2_semisimplicial_decalage.lp"),
    Path("emdash3_2_circle_connectedness.lp"),
    Path("emdash3_2_sieves.lp"),
    Path("emdash3_2_sites.lp"),
    Path("emdash3_2_sieve_extensions.lp"),
    Path("emdash3_2_direct_cover_questions.lp"),
    Path("emdash3_2_direct_cover_question_families.lp"),
    Path("emdash3_2_direct_cover_algebras.lp"),
    Path("emdash3_2_direct_cover_internal_sheaves.lp"),
    Path("emdash3_2_direct_cover_completion_hit.lp"),
    Path("emdash3_2_direct_cover_completion_locality.lp"),
    Path("emdash3_2_direct_cover_completion_eliminator.lp"),
    Path("emdash3_2_direct_cover_completion_universality.lp"),
    Path("emdash3_2_direct_cover_sheafification.lp"),
    Path("emdash3_2_generated_topologies.lp"),
    Path("emdash3_2_ringed_sites.lp"),
    Path("emdash3_2_site_basis.lp"),
    Path("emdash3_2_commutative_algebra_ringed_space_covers.lp"),
    Path("emdash3_2_commutative_algebra_binary_covers.lp"),
    Path("emdash3_2_commutative_algebra_ringed_space_restrictions.lp"),
    Path("emdash3_2_commutative_algebra_locality.lp"),
    Path("emdash3_2_commutative_algebra_local_ringed_sites.lp"),
    Path("emdash3_2_commutative_algebra_matching.lp"),
    Path("emdash3_2_commutative_algebra_glue.lp"),
    Path("emdash3_2_commutative_algebra_affine_glue.lp"),
    Path("emdash3_2_commutative_algebra_zariski.lp"),
    Path("emdash3_2_commutative_algebra_zariski_topology.lp"),
    Path("emdash3_2_commutative_algebra_localization_split.lp"),
    Path("emdash3_2_commutative_algebra_affine_spec.lp"),
    Path("emdash3_2_commutative_algebra_affine_zariski.lp"),
    Path("emdash3_2_commutative_algebra_affine_ringed_sites.lp"),
    Path("emdash3_2_commutative_algebra_affine_locality.lp"),
    Path("emdash3_2_commutative_algebra_affine_schemes.lp"),
    Path("emdash3_2_commutative_algebra_affine_basis.lp"),
    Path("emdash3_2_commutative_algebra_affine_cover_charts.lp"),
    Path("emdash3_2_commutative_algebra_affine_cover_presentations.lp"),
    Path("emdash3_2_commutative_algebra_affine_cover_refinements.lp"),
    Path("emdash3_2_commutative_algebra_locally_ringed_space_presentations.lp"),
    Path("emdash3_2_commutative_algebra_site_relative_schemes.lp"),
    Path("emdash3_2_commutative_algebra_scheme_chart_overlaps.lp"),
    Path("emdash3_2_commutative_algebra_scheme_laurent_overlaps.lp"),
    Path("emdash3_2_commutative_algebra_projective_line.lp"),
    Path("emdash3_2_commutative_algebra_affine_points.lp"),
    Path("emdash3_2_commutative_algebra_affine_intersections.lp"),
    Path("emdash3_2_commutative_algebra_affine_atlas.lp"),
    Path("emdash3_2_monads.lp"),
    Path("emdash3_2_triangular_binary_products.lp"),
    Path("emdash3_2_terminal_objects.lp"),
    Path("emdash3_2_cartesian_categories.lp"),
    Path("emdash3_2_triangular_binary_products_finite_limits.lp"),
    Path("emdash3_2_pullbacks.lp"),
    Path("emdash3_2_slice_dependent_products.lp"),
    Path("emdash3_2_checks.lp"),
]
# Run the two consistently near-timeout aggregate targets before sustained
# sequential checking can make their measurements load/thermal sensitive.
# Results remain reported in CORE_CHECK_FILES order.
CHECK_PRIORITY_FILES = [
    Path("emdash3_2_checks.lp"),
    Path("emdash3_2_commutative_algebra_affine_glue.lp"),
]
SPECIAL_SIX_TERM_CHECK_FILES = {
    Path("emdash3_2_abelian_snake_six_term_inner_kernel_u_zero_foundation.lp"),
    Path("emdash3_2_abelian_snake_six_term_inner_kernel_q2_zero_foundation.lp"),
    Path("emdash3_2_abelian_snake_six_term_inner_kernel_zero.lp"),
    Path("emdash3_2_abelian_snake_six_term_inner_cokernel_p1_zero_foundation.lp"),
    Path("emdash3_2_abelian_snake_six_term_inner_cokernel_zero.lp"),
    Path("emdash3_2_abelian_snake_six_term_result.lp"),
    Path("emdash3_2_abelian_snake_six_term_result_projections.lp"),
    Path("emdash3_2_exactness_covers_foundation.lp"),
    Path("emdash3_2_exactness_covers.lp"),
    Path("emdash3_2_exactness_covers_from_exact.lp"),
    Path("emdash3_2_abelian_canonical_kernel_exactness.lp"),
    Path("emdash3_2_abelian_canonical_cokernel_foundation.lp"),
    Path("emdash3_2_abelian_canonical_cokernel_factor.lp"),
    Path("emdash3_2_abelian_canonical_cokernel_epic.lp"),
    Path("emdash3_2_abelian_canonical_cokernel_exactness.lp"),
    Path("emdash3_2_abelian_canonical_cokernel_covers.lp"),
    Path("emdash3_2_abelian_snake_exact_first_foundation.lp"),
    Path("emdash3_2_abelian_snake_exact_first_row_cover_projections.lp"),
    Path("emdash3_2_abelian_snake_exact_first_alpha_zero.lp"),
    Path("emdash3_2_abelian_snake_exact_first_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_first_comparison.lp"),
    Path("emdash3_2_abelian_snake_exact_first_result.lp"),
    Path("emdash3_2_preadditive_difference_paths.lp"),
    Path("emdash3_2_abelian_snake_exact_second_pullback.lp"),
    Path("emdash3_2_abelian_snake_exact_second_xi.lp"),
    Path("emdash3_2_abelian_snake_exact_second_q2_pi.lp"),
    Path("emdash3_2_abelian_snake_exact_second_pi_zero.lp"),
    Path("emdash3_2_abelian_snake_exact_second_alpha_cover_foundation.lp"),
    Path("emdash3_2_abelian_snake_exact_second_alpha_cover_object.lp"),
    Path("emdash3_2_abelian_snake_exact_second_alpha_cover_epi.lp"),
    Path("emdash3_2_abelian_snake_exact_second_alpha_cover_epic.lp"),
    Path("emdash3_2_abelian_snake_exact_second_alpha_cover_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_second_beta_difference.lp"),
    Path("emdash3_2_abelian_snake_exact_second_kernel_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_second_epsilon_paths.lp"),
    Path("emdash3_2_abelian_snake_exact_second_epsilon_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_second_iota_comparison.lp"),
    Path("emdash3_2_abelian_snake_exact_second_cover_comparison.lp"),
    Path("emdash3_2_abelian_snake_exact_second_total_cover.lp"),
    Path("emdash3_2_abelian_snake_exact_second_cover_witness.lp"),
    Path("emdash3_2_abelian_snake_exact_second_result.lp"),
    Path("emdash3_2_exactness_extensions_foundation.lp"),
    Path("emdash3_2_exactness_extensions_to_exact_foundation.lp"),
    Path("emdash3_2_exactness_extensions_to_exact_extension.lp"),
    Path("emdash3_2_exactness_extensions_to_exact_zero.lp"),
    Path("emdash3_2_exactness_extensions_to_exact.lp"),
    Path("emdash3_2_abelian_canonical_kernel_extensions_foundation.lp"),
    Path("emdash3_2_abelian_canonical_kernel_extensions.lp"),
    Path("emdash3_2_abelian_snake_exact_third_pushout.lp"),
    Path("emdash3_2_abelian_snake_exact_third_zeta.lp"),
    Path("emdash3_2_abelian_snake_exact_third_zeta_epsilon.lp"),
    Path("emdash3_2_abelian_snake_exact_third_zeta_iota_to_su.lp"),
    Path("emdash3_2_abelian_snake_exact_third_su_path.lp"),
    Path("emdash3_2_abelian_snake_exact_third_zeta_zero.lp"),
    Path("emdash3_2_abelian_snake_exact_third_gamma_extension_foundation.lp"),
    Path("emdash3_2_abelian_snake_exact_third_gamma_extension_object.lp"),
    Path("emdash3_2_abelian_snake_exact_third_gamma_extension_monomorphism.lp"),
    Path("emdash3_2_abelian_snake_exact_third_gamma_extension_is_monic.lp"),
    Path("emdash3_2_abelian_snake_exact_third_gamma_extension_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_third_gamma_extension_path.lp"),
    Path("emdash3_2_abelian_snake_exact_third_beta_difference.lp"),
    Path("emdash3_2_abelian_snake_exact_third_cokernel_factor.lp"),
    Path("emdash3_2_abelian_snake_exact_third_mu_reconstruction.lp"),
    Path("emdash3_2_abelian_snake_exact_third_difference_mu.lp"),
    Path("emdash3_2_abelian_snake_exact_third_pi_comparison.lp"),
    Path("emdash3_2_abelian_snake_exact_third_pi_epic.lp"),
    Path("emdash3_2_abelian_snake_exact_third_extension_comparison.lp"),
    Path("emdash3_2_abelian_snake_exact_third_extension_witness.lp"),
    Path("emdash3_2_abelian_snake_exact_third_result.lp"),
    Path("examples/abelian_snake_six_term_inner_zero.lp"),
    Path("examples/abelian_snake_six_term_result.lp"),
    Path("examples/abelian_snake_exact_first.lp"),
    Path("examples/abelian_snake_exact_second.lp"),
    Path("examples/abelian_snake_exact_third.lp"),
    Path("emdash3_2_abelian_snake_six_term_exact_pairs.lp"),
    Path("emdash3_2_abelian_snake_six_term_exact_data_intro.lp"),
    Path("emdash3_2_abelian_snake_six_term_exact_result_foundation.lp"),
    Path("emdash3_2_abelian_snake_six_term_exact_result_projections.lp"),
    Path("emdash3_2_abelian_snake_six_term_exact_pair_paths.lp"),
    Path("emdash3_2_abelian_snake_six_term_canonical_exactness.lp"),
    Path("emdash3_2_abelian_snake_six_term_exact_result.lp"),
    Path("examples/abelian_snake_six_term_exact_pairs.lp"),
    Path("examples/abelian_snake_six_term_exact_structure.lp"),
    Path("examples/abelian_snake_six_term_exact_result.lp"),
}
SPECIAL_NORMALIZATION_CHECK_FILES = {
    Path("emdash3_2_short_exact_rows.lp"),
    Path("emdash3_2_kernel_short_exact_rows.lp"),
    Path("emdash3_2_selected_short_exact_rows.lp"),
    Path("emdash3_2_monic_image_comparison.lp"),
    Path("emdash3_2_short_exact_row_comparison_fibres.lp"),
    Path("emdash3_2_monic_selected_row_comparison.lp"),
    Path("emdash3_2_short_exact_normalization_foundation.lp"),
    Path("emdash3_2_short_exact_normalization_isos.lp"),
    Path("emdash3_2_short_exact_normalization_projections.lp"),
    Path("emdash3_2_short_exact_normalization.lp"),
    Path("examples/short_exact_rows.lp"),
    Path("examples/monic_image_iso.lp"),
    Path("examples/monic_selected_row_comparison.lp"),
    Path("examples/short_exact_normalization_structure.lp"),
    Path("examples/short_exact_normalization.lp"),
}
SPECIAL_SNAKE_ROW_CHECK_FILES = {
    Path("emdash3_2_chain_pair_map_snake.lp"),
    Path("emdash3_2_snake_row_comparisons.lp"),
    Path("emdash3_2_kernel_domain_comparison.lp"),
    Path("emdash3_2_cokernel_codomain_comparison.lp"),
    Path("emdash3_2_snake_row_source_cycle_iso.lp"),
    Path("emdash3_2_snake_row_target_cokernel_iso.lp"),
    Path("emdash3_2_abelian_structure_elimination.lp"),
    Path("emdash3_2_abelian_snake_row_comparisons.lp"),
    Path("emdash3_2_short_exact_row_snake.lp"),
    Path("examples/chain_pair_map_snake.lp"),
    Path("examples/abelian_structure_elimination.lp"),
    Path("examples/snake_row_comparisons.lp"),
    Path("examples/snake_row_source_cycle_iso.lp"),
    Path("examples/snake_row_target_cokernel_iso.lp"),
    Path("examples/abelian_snake_row_comparisons.lp"),
    Path("examples/short_exact_row_snake.lp"),
    Path("examples/short_exact_row_snake_target.lp"),
}
SPECIAL_SNAKE_TARGET_CYCLE_CHECK_FILES = {
    Path("emdash3_2_chain_pair_map_cycle_lifts.lp"),
    Path("emdash3_2_hom_factor_source_isos.lp"),
    Path("emdash3_2_short_exact_row_chain_columns.lp"),
    Path("emdash3_2_snake_row_target_factors.lp"),
    Path("emdash3_2_snake_row_target_cycles.lp"),
    Path("examples/chain_pair_map_cycle_lifts.lp"),
    Path("examples/hom_factor_source_isos.lp"),
    Path("examples/snake_row_target_factor.lp"),
    Path("examples/snake_row_target_cycles.lp"),
}
SPECIAL_SNAKE_TARGET_HOMOLOGY_CHECK_FILES = {
    Path("emdash3_2_snake_row_target_cokernel_projection.lp"),
    Path("emdash3_2_snake_row_target_homology_normal.lp"),
    Path("emdash3_2_snake_row_target_homology_factor.lp"),
    Path("examples/snake_row_target_cokernel_projection.lp"),
    Path("examples/snake_row_target_homology_normal.lp"),
    Path("examples/snake_row_target_homology_factor.lp"),
}
SPECIAL_SNAKE_SOURCE_BOUNDARY_CHECK_FILES = {
    Path("emdash3_2_snake_row_source_second_comparison.lp"),
    Path("emdash3_2_snake_row_source_boundary_covered.lp"),
    Path("emdash3_2_snake_row_source_boundary_zero.lp"),
    Path("examples/snake_row_source_second_comparison.lp"),
    Path("examples/snake_row_source_boundary_covered.lp"),
    Path("examples/snake_row_source_boundary_zero.lp"),
}
SPECIAL_HOMOLOGY_CONNECTING_CHECK_FILES = {
    Path("emdash3_2_homology_connecting_factor.lp"),
    Path("emdash3_2_homology_connecting.lp"),
    Path("examples/homology_connecting_factor.lp"),
    Path("examples/homology_connecting.lp"),
}
SPECIAL_HOMOLOGY_EXACT_WINDOW_CHECK_FILES = {
    Path("emdash3_2_homology_exact_window.lp"),
    Path("emdash3_2_homology_exact_window_result.lp"),
    Path("examples/homology_exact_window.lp"),
}
SPECIAL_HOMOLOGY_WINDOW_FAMILY_CHECK_FILES = {
    Path("emdash3_2_short_exact_row_families.lp"),
    Path("emdash3_2_homology_window_families.lp"),
    Path("emdash3_2_homology_window_columns.lp"),
    Path("emdash3_2_homology_window_column_usability.lp"),
    Path("emdash3_2_homology_window_connecting_transformation.lp"),
    Path("examples/homology_window_families.lp"),
    Path("examples/homology_window_connecting_transformation.lp"),
    Path("examples/homology_window_column_usability.lp"),
}
SPECIAL_HOMOLOGY_ARROW_TAIL_CHECK_FILES = {
    Path("emdash3_2_finite_arrow_tails.lp"),
    Path("emdash3_2_finite_arrow_tail_append.lp"),
    Path("emdash3_2_computational_exact_arrow_tails.lp"),
    Path("examples/finite_arrow_tails.lp"),
    Path("examples/computational_exact_arrow_tails.lp"),
    Path("examples/homology_adjacent_window_tails.lp"),
}
SPECIAL_HOMOLOGY_BOUNDED_PREREQUISITES = {
    Path("emdash3_2_preadditive_zero_identity.lp"),
    Path("emdash3_2_homology_record_zero.lp"),
    Path("emdash3_2_homology_whole_zero.lp"),
    Path("emdash3_2_homology_window_extension.lp"),
    Path("emdash3_2_homology_row_triples.lp"),
    Path("emdash3_2_homology_row_spans.lp"),
    Path("examples/preadditive_zero_identity.lp"),
    Path("examples/homology_whole_zero.lp"),
    Path("examples/homology_window_extension.lp"),
    Path("examples/homology_row_spans.lp"),
}
SPECIAL_HOMOLOGY_BOUNDED_GENERATOR = {
    Path("emdash3_2_finite_arrow_tail_arrows.lp"),
    Path("emdash3_2_finite_arrow_tail_init.lp"),
    Path("emdash3_2_short_exact_row_zero.lp"),
    Path("emdash3_2_homology_row_field_spans.lp"),
    Path("emdash3_2_homology_row_field_span_case.lp"),
    Path("emdash3_2_homology_row_fields_extension.lp"),
    Path("emdash3_2_homology_bounded_generator.lp"),
    Path("examples/finite_arrow_tail_init.lp"),
    Path("examples/short_exact_row_zero.lp"),
    Path("examples/homology_row_field_spans.lp"),
    Path("examples/homology_bounded_generator.lp"),
    Path("examples/homology_bounded_generator_arrows.lp"),
}
ISOLATED_CHECK_GROUPS = (
    (SPECIAL_HOMOLOGY_BOUNDED_GENERATOR, "./scripts/check_homology_bounded_generator.sh"),
    (SPECIAL_HOMOLOGY_BOUNDED_PREREQUISITES, "./scripts/check_homology_bounded_prerequisites.sh"),
    (SPECIAL_HOMOLOGY_ARROW_TAIL_CHECK_FILES, "./scripts/check_homology_arrow_tails.sh"),
    (SPECIAL_HOMOLOGY_WINDOW_FAMILY_CHECK_FILES, "./scripts/check_homology_window_families.sh"),
    (SPECIAL_HOMOLOGY_EXACT_WINDOW_CHECK_FILES, "./scripts/check_homology_exact_window.sh"),
    (SPECIAL_HOMOLOGY_CONNECTING_CHECK_FILES, "./scripts/check_homology_connecting.sh"),
    (SPECIAL_SNAKE_SOURCE_BOUNDARY_CHECK_FILES, "./scripts/check_snake_row_source_boundary.sh"),
    (SPECIAL_SNAKE_TARGET_HOMOLOGY_CHECK_FILES, "./scripts/check_snake_row_target_homology.sh"),
    (SPECIAL_SNAKE_TARGET_CYCLE_CHECK_FILES, "./scripts/check_snake_row_target_cycles.sh"),
    (SPECIAL_SIX_TERM_CHECK_FILES, "./scripts/check_abelian_snake_six_term.sh"),
    (SPECIAL_NORMALIZATION_CHECK_FILES, "./scripts/check_short_exact_normalization.sh"),
    (SPECIAL_SNAKE_ROW_CHECK_FILES, "./scripts/check_snake_row_comparisons.sh"),
)
EXAMPLES_DIR = ROOT / "examples"
HEALTH_REPORT = ROOT / "reports" / "REPORT_EMDASH_HEALTH.md"
HEALTH_STATE = ROOT / "logs" / "check-health-state.json"
HEALTH_STATE_VERSION = 1
SOURCE_METRICS_SNAPSHOT_RE = re.compile(
    r"^- Source-metrics snapshot: `sha256:(?P<digest>[0-9a-f]{64})`$", re.MULTILINE
)
CHECK_CONTENT_SNAPSHOT_RE = re.compile(
    r"^- Check-content snapshot: `sha256:(?P<digest>[0-9a-f]{64})`$", re.MULTILINE
)
DEFAULT_REGISTERED_TIMEOUT = "90s"


@dataclass
class CheckResult:
    file: str
    returncode: int | None
    duration_s: float | None
    evidence: str = "current"


def run_command(cmd: list[str], timeout_value: str | None = None) -> tuple[int, str, float]:
    full_cmd = cmd
    if timeout_value and shutil.which("timeout"):
        full_cmd = ["timeout", "--signal=INT", timeout_value, *cmd]

    start = time.perf_counter()
    proc = subprocess.run(
        full_cmd,
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    duration = time.perf_counter() - start
    return proc.returncode, proc.stdout, duration


def lambdapi_version() -> str:
    try:
        proc = subprocess.run(
            ["lambdapi", "--version"],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    except FileNotFoundError:
        return "not found"
    return " ".join(proc.stdout.strip().split()) or f"exit {proc.returncode}"


def check_files() -> list[Path]:
    examples = sorted(path.relative_to(ROOT) for path in EXAMPLES_DIR.glob("*.lp"))
    return [*CORE_CHECK_FILES, *examples]


def lambdapi_check_command(path: Path) -> list[str]:
    warnings = os.environ.get("EMDASH_LAMBDAPI_WARNINGS", "0").lower()
    if warnings in {"1", "true", "yes", "on"}:
        warning_flags: list[str] = []
    elif warnings in {"0", "false", "no", "off"}:
        warning_flags = ["-w"]
    else:
        raise ValueError(f"invalid EMDASH_LAMBDAPI_WARNINGS value: {warnings}")

    extra_flags = shlex.split(os.environ.get("EMDASH_LAMBDAPI_FLAGS", ""))
    return ["lambdapi", "check", *warning_flags, *extra_flags, str(path)]


def count_lines(path: Path) -> dict[str, int | dict[str, int]]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    counts: dict[str, int | dict[str, int]] = {
        "lines": len(lines),
        "nonblank_lines": sum(1 for line in lines if line.strip()),
        "comment_lines": sum(1 for line in lines if line.lstrip().startswith("//")),
        "symbols": 0,
        "rules": 0,
        "unif_rules": 0,
        "asserts": 0,
        "todos": 0,
        "deferred_mentions": 0,
        "sections": {},
    }

    symbol_re = re.compile(
        r"^\s*(?:(?:injective|constant|sequential|opaque|private|protected)\s+)*symbol\b"
    )
    rule_re = re.compile(r"^\s*rule\b")
    unif_rule_re = re.compile(r"^\s*unif_rule\b")
    assert_re = re.compile(r"^\s*assert\b")
    section_re = re.compile(r"^//\s+([0-9]+)\.\s+(.*\S)\s*$")

    section_starts: list[tuple[int, str]] = []
    for i, line in enumerate(lines, start=1):
        if symbol_re.match(line):
            counts["symbols"] = int(counts["symbols"]) + 1
        if rule_re.match(line):
            counts["rules"] = int(counts["rules"]) + 1
        if unif_rule_re.match(line):
            counts["unif_rules"] = int(counts["unif_rules"]) + 1
        if assert_re.match(line):
            counts["asserts"] = int(counts["asserts"]) + 1
        if "TODO" in line:
            counts["todos"] = int(counts["todos"]) + 1
        if "deferred" in line.lower():
            counts["deferred_mentions"] = int(counts["deferred_mentions"]) + 1
        m = section_re.match(line)
        if m:
            section_starts.append((i, f"{m.group(1)}. {m.group(2)}"))

    sections: dict[str, int] = {}
    for idx, (start, name) in enumerate(section_starts):
        end = section_starts[idx + 1][0] - 1 if idx + 1 < len(section_starts) else len(lines)
        sections[name] = end - start + 1
    counts["sections"] = sections
    return counts


def source_metrics_snapshot(files: dict[str, dict]) -> str:
    """Hash only the stable source-metric payload, excluding timings/date."""
    canonical = json.dumps(
        files,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(canonical).hexdigest()


def check_content_snapshot(files: list[Path], root: Path = ROOT) -> str:
    """Hash exact checked file paths and bytes for resumable evidence."""
    digest = hashlib.sha256()
    for path in sorted(files, key=str):
        digest.update(str(path).encode("utf-8"))
        digest.update(b"\0")
        digest.update((root / path).read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def report_source_metrics_snapshot(report: str) -> str | None:
    match = SOURCE_METRICS_SNAPSHOT_RE.search(report)
    return None if match is None else match.group("digest")


def report_check_content_snapshot(report: str) -> str | None:
    match = CHECK_CONTENT_SNAPSHOT_RE.search(report)
    return None if match is None else match.group("digest")


def report_snapshot_issue(
    expected: str,
    report: str,
    expected_content: str | None = None,
) -> str | None:
    actual_metrics = report_source_metrics_snapshot(report)
    if actual_metrics is None:
        return "health report has no source-metrics snapshot"
    if actual_metrics != expected:
        return (
            "health report source metrics are stale: "
            f"recorded sha256:{actual_metrics}, current sha256:{expected}"
        )
    if expected_content is not None:
        actual_content = report_check_content_snapshot(report)
        if actual_content is None:
            return "health report has no check-content snapshot"
        if actual_content != expected_content:
            return (
                "health report checked contents are stale: "
                f"recorded sha256:{actual_content}, "
                f"current sha256:{expected_content}"
            )
    return None


def check_state_identity(
    files: list[Path],
    content_snapshot: str,
    version: str,
    timeout_value: str,
) -> dict[str, object]:
    return {
        "state_version": HEALTH_STATE_VERSION,
        "files": [str(path) for path in files],
        "content_snapshot": content_snapshot,
        "lambdapi_version": version,
        "timeout": timeout_value,
        "warnings_enabled": os.environ.get("EMDASH_LAMBDAPI_WARNINGS", "0").lower()
        in {"1", "true", "yes", "on"},
        "extra_lambdapi_flags": os.environ.get("EMDASH_LAMBDAPI_FLAGS", ""),
    }


def resume_identity_is_compatible(
    previous: dict[str, object],
    current: dict[str, object],
    root: Path = ROOT,
) -> bool:
    """Accept exact state, or an additive file-list extension with exact old bytes."""
    if previous == current:
        return True

    stable_keys = (
        "state_version",
        "lambdapi_version",
        "timeout",
        "warnings_enabled",
        "extra_lambdapi_flags",
    )
    if any(previous.get(key) != current.get(key) for key in stable_keys):
        return False

    previous_files = previous.get("files")
    current_files = current.get("files")
    previous_snapshot = previous.get("content_snapshot")
    if not isinstance(previous_files, list) or not isinstance(current_files, list):
        return False
    if not isinstance(previous_snapshot, str):
        return False
    if not set(previous_files).issubset(set(current_files)):
        return False

    paths: list[Path] = []
    for file_name in previous_files:
        if not isinstance(file_name, str):
            return False
        path = Path(file_name)
        if path.is_absolute() or ".." in path.parts or not (root / path).is_file():
            return False
        paths.append(path)
    return check_content_snapshot(paths, root) == previous_snapshot


def load_resume_checks(
    path: Path,
    identity: dict[str, object],
    root: Path = ROOT,
) -> dict[str, CheckResult]:
    try:
        state = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return {}
    previous_identity = state.get("identity")
    if not isinstance(previous_identity, dict):
        return {}
    if not resume_identity_is_compatible(previous_identity, identity, root):
        return {}
    previous_files = previous_identity.get("files")
    allowed_files = set(previous_files) if isinstance(previous_files, list) else None
    checks: dict[str, CheckResult] = {}
    for file_name, item in state.get("checks", {}).items():
        if isinstance(item, dict) and item.get("returncode") == 0 and (
            allowed_files is None or file_name in allowed_files
        ):
            checks[file_name] = CheckResult(
                file=file_name,
                returncode=0,
                duration_s=item.get("duration_s"),
                evidence="resumed",
            )
    return checks


def write_resume_checks(
    path: Path,
    identity: dict[str, object],
    checks: dict[str, CheckResult],
) -> None:
    successful = {
        file_name: {
            "returncode": 0,
            "duration_s": result.duration_s,
        }
        for file_name, result in checks.items()
        if result.returncode == 0
    }
    state = {
        "identity": identity,
        "updated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "checks": successful,
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(state, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def check_execution_order(files: list[Path]) -> list[Path]:
    prioritized = [path for path in CHECK_PRIORITY_FILES if path in files]
    return [*prioritized, *(path for path in files if path not in prioritized)]


def run_checks(
    files: list[Path],
    timeout_value: str,
    resumed: dict[str, CheckResult] | None = None,
    continue_after_failure: bool = False,
    save_success: Callable[[dict[str, CheckResult]], None] | None = None,
) -> tuple[list[CheckResult], int]:
    results_by_file: dict[str, CheckResult] = dict(resumed or {})
    overall = 0
    checked_groups: set[str] = set()
    for rel in check_execution_order(files):
        if str(rel) in results_by_file and results_by_file[str(rel)].returncode == 0:
            result = results_by_file[str(rel)]
            duration = result.duration_s
            duration_text = "unknown" if duration is None else f"{duration:.3f}s"
            label = "resumed" if result.evidence == "resumed" else "already checked"
            print(f"{rel}: {label} exit 0, {duration_text}")
            continue
        group = next(
            ((members, script) for members, script in ISOLATED_CHECK_GROUPS if rel in members),
            None,
        )
        if group is not None:
            members, script = group
            if script in checked_groups:
                continue
            pending = [
                path
                for path in files
                if path in members
                and str(path) not in results_by_file
            ]
            rc, output, duration = run_command([script])
            share = duration / max(1, len(pending))
            for path in pending:
                results_by_file[str(path)] = CheckResult(
                    str(path), rc, share, "current-isolated-object-chain"
                )
                print(f"{path}: isolated-chain exit {rc}, {share:.3f}s share")
            checked_groups.add(script)
            if rc == 0 and save_success is not None:
                save_success(results_by_file)
            elif rc != 0:
                overall = overall or rc
                tail = "\n".join(output.splitlines()[-40:])
                print(tail, file=sys.stderr)
                if not continue_after_failure:
                    break
            continue
        cmd = lambdapi_check_command(rel)
        rc, output, duration = run_command(cmd, timeout_value)
        results_by_file[str(rel)] = CheckResult(str(rel), rc, duration)
        print(f"{rel}: exit {rc}, {duration:.3f}s")
        if rc == 0 and save_success is not None:
            save_success(results_by_file)
        elif rc != 0:
            overall = overall or rc
            tail = "\n".join(output.splitlines()[-40:])
            print(tail, file=sys.stderr)
            if not continue_after_failure:
                break
    results = [results_by_file[str(path)] for path in files if str(path) in results_by_file]
    if len(results) != len(files):
        overall = overall or 1
    return results, overall


def build_payload(args: argparse.Namespace) -> tuple[dict, int]:
    timeout_value = os.environ.get(
        "EMDASH_TYPECHECK_TIMEOUT", DEFAULT_REGISTERED_TIMEOUT
    )
    files_to_check = check_files()
    files = {str(path): count_lines(ROOT / path) for path in files_to_check}
    content_snapshot = check_content_snapshot(files_to_check)
    version = lambdapi_version()
    identity = check_state_identity(
        files_to_check,
        content_snapshot,
        version,
        timeout_value,
    )
    if args.no_check:
        checks = [CheckResult(str(path), None, None) for path in files_to_check]
        rc = 0
    elif args.resume:
        resumed = load_resume_checks(HEALTH_STATE, identity)

        def save_success(results: dict[str, CheckResult]) -> None:
            write_resume_checks(HEALTH_STATE, identity, results)

        checks, rc = run_checks(
            files_to_check,
            timeout_value,
            resumed=resumed,
            continue_after_failure=True,
            save_success=save_success,
        )
    else:
        checks, rc = run_checks(files_to_check, timeout_value)

    payload = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "lambdapi_version": version,
        "timeout": timeout_value,
        "warnings_enabled": os.environ.get(
            "EMDASH_LAMBDAPI_WARNINGS", "0"
        ).lower()
        in {"1", "true", "yes", "on"},
        "extra_lambdapi_flags": os.environ.get("EMDASH_LAMBDAPI_FLAGS", ""),
        "core_files": [str(path) for path in CORE_CHECK_FILES],
        "example_files": [str(path) for path in files_to_check if str(path).startswith("examples/")],
        "checks": [result.__dict__ for result in checks],
        "files": files,
        "source_metrics_snapshot": source_metrics_snapshot(files),
        "check_content_snapshot": content_snapshot,
        "resume_enabled": args.resume,
        "resumed_check_count": sum(
            1 for result in checks if result.evidence == "resumed"
        ),
    }
    return payload, rc


def write_log(payload: dict, path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(payload, ensure_ascii=False, sort_keys=True))
        f.write("\n")


def format_report(payload: dict) -> str:
    lines = [
        "# EMDASH Health Report",
        "",
        f"Generated: {payload['generated_at']}",
        "",
        "This report is generated by `scripts/check_metrics.py`.",
        "",
        "## Environment",
        "",
        f"- Lambdapi: `{payload['lambdapi_version']}`",
        f"- Timeout: `{payload['timeout']}`",
        f"- Warnings enabled: `{payload['warnings_enabled']}`",
        f"- Extra Lambdapi flags: `{payload['extra_lambdapi_flags']}`",
        f"- Source-metrics snapshot: `sha256:{payload['source_metrics_snapshot']}`",
        f"- Check-content snapshot: `sha256:{payload['check_content_snapshot']}`",
        f"- Resumable evidence: `{payload.get('resume_enabled', False)}`",
        f"- Resumed successful checks: `{payload.get('resumed_check_count', 0)}`",
        "",
        "## Typecheck Timings",
        "",
        "| File | Exit | Seconds | Evidence |",
        "| --- | ---: | ---: | --- |",
    ]
    for check in payload["checks"]:
        duration = check["duration_s"]
        duration_text = "" if duration is None else f"{duration:.3f}"
        exit_text = "" if check["returncode"] is None else str(check["returncode"])
        evidence = check.get("evidence", "current")
        lines.append(
            f"| `{check['file']}` | {exit_text} | {duration_text} | {evidence} |"
        )

    lines.extend([
        "",
        "## Source Metrics",
        "",
        "| File | Lines | Symbols | Rules | Unif Rules | Asserts | TODO | Deferred |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ])
    for file_name, counts in payload["files"].items():
        lines.append(
            f"| `{file_name}` | {counts['lines']} | {counts['symbols']} | "
            f"{counts['rules']} | {counts['unif_rules']} | {counts['asserts']} | "
            f"{counts['todos']} | {counts['deferred_mentions']} |"
        )

    example_files = payload.get("example_files", [])
    if example_files:
        durations = {
            check["file"]: check["duration_s"]
            for check in payload["checks"]
            if check["file"] in example_files
        }
        exits = {
            check["file"]: check["returncode"]
            for check in payload["checks"]
            if check["file"] in example_files
        }
        lines.extend([
            "",
            "## Reviewer Milestone Examples",
            "",
            "| Example | Exit | Seconds | Lines | Asserts |",
            "| --- | ---: | ---: | ---: | ---: |",
        ])
        for file_name in example_files:
            counts = payload["files"][file_name]
            duration = durations.get(file_name)
            duration_text = "" if duration is None else f"{duration:.3f}"
            exit_value = exits.get(file_name)
            exit_text = "" if exit_value is None else str(exit_value)
            lines.append(
                f"| `{file_name}` | {exit_text} | {duration_text} | "
                f"{counts['lines']} | {counts['asserts']} |"
            )

    main_sections = payload["files"].get("emdash3_2.lp", {}).get("sections", {})
    if main_sections:
        lines.extend([
            "",
            "## `emdash3_2.lp` Section Sizes",
            "",
            "| Section | Lines |",
            "| --- | ---: |",
        ])
        for section, size in main_sections.items():
            lines.append(f"| {section} | {size} |")

    lines.append("")
    return "\n".join(lines)


def format_brief(payload: dict, rc: int) -> str:
    checks = payload["checks"]
    checked = [check for check in checks if check["returncode"] is not None]
    if not checked:
        return (
            f"source metrics collected: {len(payload['files'])} file(s); "
            "Lambdapi checks skipped"
        )
    total_s = sum(check["duration_s"] or 0 for check in checked)
    failed = [check for check in checked if check["returncode"] != 0]
    status = "passed" if rc == 0 else "failed"
    lines = [
        f"check metrics {status}: {len(checked)} file(s), {total_s:.3f}s total",
    ]
    resumed = sum(1 for check in checked if check.get("evidence") == "resumed")
    if resumed:
        lines.append(f"resumed exact-snapshot successes: {resumed}")
    if failed:
        lines.append("failed files:")
        for check in failed:
            lines.append(f"- {check['file']}: exit {check['returncode']}")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Collect EMDASH typecheck and source-health metrics."
    )
    parser.add_argument(
        "--no-check",
        action="store_true",
        help="Collect source metrics without running Lambdapi checks.",
    )
    parser.add_argument(
        "--resume",
        action="store_true",
        help=(
            "Reuse only exit-0 evidence with the exact checked-content and "
            "environment identity; continue after failures and retain progress."
        ),
    )
    parser.add_argument(
        "--update-log",
        action="store_true",
        help="Append JSON metrics to logs/check-metrics.jsonl.",
    )
    parser.add_argument(
        "--write-report",
        action="store_true",
        help="Write reports/REPORT_EMDASH_HEALTH.md.",
    )
    parser.add_argument(
        "--check-report",
        action="store_true",
        help="Fail if the health report's stable source metrics are stale.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Print JSON instead of the markdown summary.",
    )
    parser.add_argument(
        "--brief",
        action="store_true",
        help="Print only a compact summary after per-file check timings.",
    )
    args = parser.parse_args()

    if args.no_check and args.resume:
        parser.error("--no-check and --resume cannot be combined")

    payload, rc = build_payload(args)

    report_rc = 0
    if args.check_report:
        if not HEALTH_REPORT.exists():
            print(
                f"{HEALTH_REPORT.relative_to(ROOT)}: health report is missing",
                file=sys.stderr,
            )
            report_rc = 1
        else:
            issue = report_snapshot_issue(
                payload["source_metrics_snapshot"],
                HEALTH_REPORT.read_text(encoding="utf-8"),
                payload["check_content_snapshot"],
            )
            if issue is None:
                print(
                    "health source-metrics snapshot check passed: "
                    f"sha256:{payload['source_metrics_snapshot']}"
                )
            else:
                print(
                    f"{HEALTH_REPORT.relative_to(ROOT)}: {issue}; run `make health`",
                    file=sys.stderr,
                )
                report_rc = 1

    if args.update_log:
        write_log(payload, ROOT / "logs" / "check-metrics.jsonl")
    if args.write_report and (rc == 0 or args.no_check):
        HEALTH_REPORT.write_text(
            format_report(payload),
            encoding="utf-8",
        )
    elif args.write_report:
        print(
            f"{HEALTH_REPORT.relative_to(ROOT)}: not updated because checks failed",
            file=sys.stderr,
        )

    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    elif args.brief:
        print(format_brief(payload, rc))
    else:
        print(format_report(payload))
    return rc or report_rc


if __name__ == "__main__":
    raise SystemExit(main())
