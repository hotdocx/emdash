/**
 * @file tests/main_tests.ts
 * @description Main entry point for running all test suites via node:test.
 */
// Import test files. The `node:test` runner will discover `describe` and `it` blocks in these files.
import './v3_2_elab0_tests';
import './v3_2_elab1c_tests';
import './v3_2_core_binder_tests';
import './v3_2_core_context_tests';
import './v3_2_core_session_tests';
import './v3_2_core_signature_tests';
import './v3_2_core_serialization_tests';
import './v3_2_core_checker_tests';
import './v3_2_dependent_context_tests';
import './v3_2_telescope_structural_tests';
import './v3_2_context_dependency_tests';
import './v3_2_categorical_context_dependency_tests';
import './v3_2_categorical_fibred_product_proposal_tests';
import './v3_2_categorical_fibred_structure_proposal_tests';
import './v3_2_categorical_fibred_binder_contract_tests';
import './v3_2_categorical_fibred_transfd_contract_tests';
import './v3_2_categorical_grouped_sequential_contract_tests';
import './v3_2_categorical_fibred_weaken_reindex_transfer_tests';
import './v3_2_categorical_fibred_weaken_reindex_tests';
import './v3_2_categorical_fibred_weaken_reindex_demo_tests';
import './v3_2_categorical_comprehension_proposal_tests';
import './v3_2_manifest_tests';
import './v3_2_runtime_tests';
import './v3_2_runtime_rewrite_tests';
import './v3_2_conversion_tests';
import './v3_2_lf_beta_tests';
import './v3_2_lf_definition_tests';
import './v3_2_lf_conversion_tests';
import './v3_2_lf_builder_tests';
import './v3_2_lf_profile_proposal_tests';
import './v3_2_directed_1a_proposal_tests';
import './v3_2_continuation_review_tests';
import './v3_2_directed_1a_tests';
import './v3_2_directed_1b_proposal_tests';
import './v3_2_directed_1b_review_tests';
import './v3_2_directed_foundation_proposal_tests';
import './v3_2_directed_foundation_review_tests';
import './v3_2_directed_foundation_tests';
import './v3_2_directed_foundation_2_proposal_tests';
import './v3_2_directed_foundation_2_review_tests';
import './v3_2_directed_foundation_2_tests';
import './v3_2_directed_1b_tests';
import './v3_2_directed_1c_proposal_tests';
import './v3_2_directed_1c_review_tests';
import './v3_2_directed_1c_tests';
import './v3_2_directed_graduation_proposal_tests';
import './v3_2_directed_graduation_review_tests';
import './v3_2_directed_dependent_demo_tests';
import './v3_2_categorical_surface_spec_tests';
import './v3_2_categorical_surface_tests';
import './v3_2_categorical_bracket_tests';
import './v3_2_categorical_structural_transfer_tests';
import './v3_2_categorical_dependent_transfer_tests';
import './v3_2_categorical_program_tests';
import './v3_2_categorical_dependent_program_tests';
import './v3_2_categorical_dependent_eta_tests';
import './v3_2_categorical_dependent_composition_tests';
import './v3_2_categorical_comprehension_transfer_tests';
import './v3_2_categorical_comprehension_demo_tests';
import './v3_2_categorical_fibred_product_transfer_tests';
import './v3_2_categorical_fibred_product_demo_tests';
import './v3_2_categorical_fibred_structure_transfer_tests';
import './v3_2_categorical_fibred_binder_transfer_tests';
import './v3_2_categorical_fibred_binder_tests';
import './v3_2_categorical_fibred_transfd_transfer_tests';
import './v3_2_categorical_fibred_transfd_tests';
import './v3_2_categorical_grouped_sequential_tests';
import './v3_2_categorical_fibred_dependent_target_transfer_tests';
import './v3_2_categorical_fibred_dependent_target_tests';
import './v3_2_categorical_fibred_structure_demo_tests';
import './v3_2_categorical_fibred_binder_demo_tests';
import './v3_2_categorical_fibred_transfd_demo_tests';
import './v3_2_categorical_grouped_sequential_demo_tests';
import './v3_2_categorical_fibred_dependent_target_demo_tests';
import './v3_2_categorical_bracket_demo_tests';
import './v3_2_categorical_dependent_eta_demo_tests';
import './v3_2_categorical_dependent_composition_demo_tests';
import './v3_2_categorical_fibred_graduation_proposal_tests';
import './v3_2_categorical_fibred_graduation_review_tests';
import './v3_2_categorical_displayed_bracket_proposal_tests';
import './v3_2_categorical_displayed_bracket_review_tests';
import './v3_2_categorical_displayed_bracket_tests';
import './v3_2_categorical_displayed_bracket_demo_tests';
import './v3_2_categorical_displayed_lifting_proposal_tests';
import './v3_2_categorical_displayed_lifting_review_tests';
import './v3_2_categorical_displayed_evaluation_audit_tests';
import './v3_2_categorical_displayed_evaluation_owner_proposal_tests';
import './v3_2_categorical_displayed_evaluation_owner_review_tests';
import './v3_2_categorical_displayed_evaluation_transfer_tests';
import './v3_2_categorical_displayed_evaluation_tests';
import './v3_2_categorical_displayed_evaluation_demo_tests';
import './v3_2_categorical_displayed_evaluation_conformance_tests';
import './v3_2_categorical_displayed_chain_proposal_tests';
import './v3_2_categorical_displayed_chain_review_tests';
import './v3_2_categorical_displayed_chain_transfer_correction_proposal_tests';
import './v3_2_categorical_displayed_chain_transfer_correction_review_tests';
import './v3_2_categorical_displayed_chain_constant_functor_correction_proposal_tests';
import './v3_2_categorical_displayed_chain_constant_functor_correction_review_tests';
import './v3_2_categorical_displayed_chain_computation_closure_correction_proposal_tests';
import './v3_2_categorical_displayed_chain_computation_closure_correction_review_tests';
import './v3_2_categorical_displayed_chain_transfer_tests';
import './v3_2_categorical_displayed_chain_tests';
import './v3_2_categorical_displayed_chain_demo_tests';
import './v3_2_categorical_displayed_graduation_proposal_tests';
import './v3_2_categorical_displayed_graduation_review_tests';
import './v3_2_categorical_displayed_chain_2a_closure_proposal_tests';
import './v3_2_categorical_displayed_chain_2a_closure_review_tests';
import './v3_2_categorical_displayed_chain_2a_transfer_tests';
import './v3_2_categorical_displayed_chain_2a_tests';
import './v3_2_categorical_displayed_nd_audit_tests';
import './v3_2_categorical_displayed_nd_review_tests';
import './v3_2_categorical_displayed_nd_1a_tests';
import './v3_2_categorical_displayed_nd_higher_audit_tests';
import './v3_2_categorical_displayed_nd_higher_review_tests';
import './v3_2_categorical_displayed_nd_higher_foundation_transfer_tests';
import './v3_2_categorical_displayed_nd_higher_target_tests';
import './v3_2_categorical_usability_graduation_proposal_tests';
import './v3_2_categorical_usability_graduation_review_tests';
import './v3_2_categorical_dependent_usability_review_tests';
import './v3_2_lambdapi_export_inventory_tests';
import './v3_2_metatheory_review_tests';
import './v3_2_differential_owner_tests';
import './v3_2_differential_rule_tests';
import './v3_2_differential_higher_cell_tests';
import './v3_2_migration_inventory_tests';
import './v3_2_migration_readiness_tests';
import './v3_2_proof_state_tests';
import './v3_2_pattern_unification_tests';
import './v3_2_proof_refinement_tests';
import './v3_2_browser_api_tests';
import './v3_2_graduation_tests';
import './v3_2_graduation_review_tests';
import './v3_2_probe_diagnostic_tests';
import './v3_2_release_policy_tests';
import './v3_2_release_completion_tests';
import './v3_2_lf_transfer_tests';
import './v3_2_lf_transfer_compiler_tests';
import './v3_2_lf_transfer_runtime_tests';
import './v3_2_lf_transfer_visibility_tests';
import './v3_2_lf_transfer_proof_tests';
import './v3_2_lf_transfer_inductive_tests';
import './v3_2_lf_transfer_mixed_tests';
import './v3_2_lf_runtime_fragment_tests';
import './v3_2_lf_transfer_acquisition_tests';
import './v3_2_scale_stress_1_representation_tests';
import './v3_2_scale_stress_1b_proposal_tests';
import './v3_2_scale_stress_2_representation_tests';
import './v3_2_scale_stress_2b_representation_tests';
import './v3_2_scale_stress_2b2_representation_tests';
import './v3_2_scale_stress_2b3_representation_tests';
import './v3_2_scale_stress_3a1_representation_tests';
import './v3_2_scale_stress_3a2a_representation_tests';
import './v3_2_scale_stress_3a2b_representation_tests';
import './v3_2_scale_stress_3b_acquisition_tests';
import './v3_2_scale_kind_pi_audit_tests';
import './v3_2_scale_inductive_1b_proposal_tests';

// Global setup or teardown for all tests can be managed here if needed,
// using `before` and `after` hooks from `node:test` if run in the same process,
// or by scripts if tests are run as separate processes.

// The main function is now significantly simpler or can be removed if
// `package.json` scripts directly invoke `node --test` on specific files or patterns.
// For now, keep a small message identifying the explicit v3.2 suite.

function main() {
    console.log('\nStarting the emdash v3.2 TypeScript test suite...');
    console.log('Test discovery and execution are handled by node:test.');

    // No explicit test running loop here. `node:test` handles it.

    // If you need to perform actions after all tests (e.g. coverage report generation),
    // those would typically be orchestrated by the test command in package.json or a CI script.

    // The `process.exit` calls are removed as `node:test` will handle exit codes based on test outcomes.
}

if (require.main === module) {
    main();
}
