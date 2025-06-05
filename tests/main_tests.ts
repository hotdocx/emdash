/**
 * @file tests/main_tests.ts
 * @description Main entry point for running all test suites via node:test.
 */
import { getDebugVerbose, setDebugVerbose } from '../src/state';

// Import test files. The `node:test` runner will discover `describe` and `it` blocks in these files.
// import './phase1_tests';
// import './implicit_args_tests';
// import './elaboration_options_tests';
// import './church_encoding_tests';
// import './church_encoding_implicit_tests';
import './higher_order_unification_tests';

// Global setup or teardown for all tests can be managed here if needed,
// using `before` and `after` hooks from `node:test` if run in the same process,
// or by scripts if tests are run as separate processes.

// The main function is now significantly simpler or can be removed if 
// `package.json` scripts directly invoke `node --test` on specific files or patterns.
// For now, we can keep a simple main to control global settings like debug verbosity.

function main() {
    const originalDebugVerbose = getDebugVerbose();
    // Set to true to see verbose logs from the core, false for cleaner test output.
    // This will apply to all tests imported and run by node:test in this process.
    setDebugVerbose(false);

    console.log("\nStarting test execution with node:test runner...");
    console.log("Test discovery and execution will be handled by node:test.");
    console.log("Ensure tests are run using a command like: node --test tests/main_tests.ts");

    // No explicit test running loop here. `node:test` handles it.

    // If you need to perform actions after all tests (e.g. coverage report generation),
    // those would typically be orchestrated by the test command in package.json or a CI script.

    // The `process.exit` calls are removed as `node:test` will handle exit codes based on test outcomes.
}

if (require.main === module) {
    main();
    // Note: `node:test` runs tests defined in imported modules automatically.
    // The `main()` function here is mostly for global setup like `setDebugVerbose`.
    // The actual test execution is kicked off by the `node --test` command itself.
}