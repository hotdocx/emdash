/**
 * Frozen FIBRED-GROUPED-SEQUENTIAL-1 contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT,
    validateCoreCategoricalGroupedSequentialContract
} from '../src/v3_2';

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe('FIBRED-GROUPED-SEQUENTIAL-1 frozen contract', () => {
    it('freezes one scalable dependency-directed lowering', () => {
        validateCoreCategoricalGroupedSequentialContract();
        assert.equal(
            CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT
                .input.minimumSiblingCount,
            2
        );
        assert.match(
            CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT
                .presentations.sequential.finiteAlgorithm,
            /accumulated projection-to-base/u
        );
        assert.match(
            CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT
                .presentations.grouped.finiteAlgorithm,
            /left-associated/u
        );
    });

    it('does not smuggle in a total-category comparison', () => {
        const objectConformance =
            CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT
                .objectConformance;
        assert.equal(
            objectConformance.totalCategoryEqualityClaimed,
            false
        );
        assert.equal(
            objectConformance.totalCategoryEquivalenceClaimed,
            false
        );
        assert.equal(
            objectConformance.arrowLevelTotalComparisonClaimed,
            false
        );
    });

    it('adds no kernel or deployed-profile authority', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT.semanticDelta,
            {
                newLambdapiOwners: 0,
                newLambdapiRuntimeRules: 0,
                newLambdapiProofRules: 0,
                newIntrinsicCoreOwners: 0,
                browserProfilePromotion: false
            }
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT
        );
    });
});
