/**
 * @file tests/utils.ts
 * @description Utility functions for running tests.
 */

// Helper function to assert equality for test cases
export function assertEqual(actual: string, expected: string, message: string) {
    if (actual !== expected) {
        console.error(`Assertion Failed: ${message}`);
        console.error(`Expected: ${expected}`);
        console.error(`Actual:   ${actual}`);
        // For automated test environments, throwing an error is essential.
        throw new Error(`Assertion Failed: ${message}\nExpected: ${expected}\nActual:   ${actual}`);
    }
    console.log(`Assertion Passed: ${message}`);
}

export function assert(condition: boolean, message: string) {
    if (!condition) {
        console.error(`Assertion Failed: ${message}`);
        throw new Error(`Assertion Failed: ${message}`);
    }
    console.log(`Assertion Passed: ${message}`);
}