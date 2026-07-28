/**
 * Frozen FIBRED-BINDER-1 direct/nested classifier contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT,
    validateCoreCategoricalFibredBinderContract
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
    'FIBRED-BINDER-1 direct/nested abstraction contract',
    () => {
        it('freezes identity, eta, and composition over one hidden telescope', () => {
            validateCoreCategoricalFibredBinderContract();
            assert.equal(
                CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT
                    .surface.hiddenTelescope,
                'λ (k :^n K; a :^f E[k]). body[k,a]'
            );
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT
                    .supportedBodies.map(body => body.id),
                ['identity', 'eta', 'composition']
            );
            assert.equal(
                CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT
                    .surface.callbackEvaluationCount,
                1
            );
        });

        it('keeps direct/nested compatibility proof-only', () => {
            const presentations =
                CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT
                    .classifierPresentations;
            assert.equal(
                presentations.proofTimeRelation,
                'active-sigma-pi-uncurrying-unification'
            );
            assert.equal(
                presentations.runtimeRelation,
                'intentionally-not-equal'
            );
            assert.equal(
                presentations.preserveElaboratedPresentation,
                true
            );
        });

        it('adds no mathematical or product-profile authority', () => {
            assert.deepEqual(
                CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT.semanticDelta,
                {
                    newLambdapiOwners: 0,
                    newLambdapiRuntimeRules: 0,
                    newLambdapiProofRules: 0,
                    newIntrinsicCoreOwners: 0,
                    browserProfilePromotion: false
                }
            );
            assertDeepFrozen(
                CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT
            );
        });
    }
);
