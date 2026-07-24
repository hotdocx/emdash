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
import './v3_2_core_checker_tests';
import './v3_2_dependent_context_tests';
import './v3_2_telescope_structural_tests';
import './v3_2_manifest_tests';
import './v3_2_runtime_tests';
import './v3_2_runtime_rewrite_tests';
import './v3_2_conversion_tests';
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
