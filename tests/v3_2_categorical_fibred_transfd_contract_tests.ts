/**
 * Frozen FIBRED-TRANSFD-1 direct/next-hom contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT,
    validateCoreCategoricalFibredTransfdContract
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

describe(
    'FIBRED-TRANSFD-1 direct/next-hom contract',
    () => {
        it('freezes coherent eta and both component levels', () => {
            validateCoreCategoricalFibredTransfdContract();
            assert.equal(
                CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT
                    .surface.provisionalNotation,
                'λ k :^nd K. body'
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT
                    .supportedBody.id,
                'coherent-component-eta'
            );
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT
                    .consumers.map(consumer => consumer.id),
                [
                    'fibre-component',
                    'fibre-point',
                    'higher-naturality-cell'
                ]
            );
        });

        it('keeps category proof comparison distinct from runtime bridges', () => {
            const presentations =
                CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT
                    .classifierPresentations;
            assert.equal(
                presentations.directOrdinaryCategoryRelation,
                'active-direct-second-hom-proof-rule'
            );
            assert.equal(
                presentations.directOrdinaryRuntimeRelation,
                'category-not-equal-object-classifiers-equal'
            );
            assert.equal(
                presentations.sigmaPiRuntimeRelation,
                'active-next-hom-and-sigma-uncurrying-reduction'
            );
        });

        it('adds no mathematical or deployed-profile authority', () => {
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT.semanticDelta,
                {
                    newLambdapiOwners: 0,
                    newLambdapiRuntimeRules: 0,
                    newLambdapiProofRules: 0,
                    newIntrinsicCoreOwners: 0,
                    browserProfilePromotion: false
                }
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT
            );
        });
    }
);
