/**
 * DIRECT-MIXED-PRODUCT-DISTRIBUTION-1G generic transfer coverage.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_BOUNDARY,
    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_CORE_NAMES,
    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_RUNTIME_MODULE,
    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_RUNTIME_POLICY,
    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_MODULE,
    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_POLICY,
    CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_PROGRAM_REVISION,
    compileCoreCategoricalDirectMixedProductDistributionTransfer
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

describe('DIRECT-MIXED-PRODUCT-DISTRIBUTION-1G transfer', () => {
    it('pins exactly one owner and three active projection rules', () => {
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_PROGRAM_REVISION,
            'DIRECT-MIXED-PRODUCT-DISTRIBUTION-1G-' +
                'CATEGORICAL-PROGRAM-1'
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_MODULE
                .declarations.map(entry => entry.symbol.name),
            ['Functor_catd_product_funcd']
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_RUNTIME_MODULE
                .runtimeRules.map(rule => rule.id),
            [
                'categorical.direct-mixed-product-distribution.point',
                'categorical.direct-mixed-product-distribution.full-action',
                'categorical.direct-mixed-product-distribution.capped-action'
            ]
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_POLICY
                .entries.map(entry => entry.policy),
            ['opaque-signature']
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_RUNTIME_POLICY
                .entries.map(entry => entry.policy),
            ['runtime-rewrite', 'runtime-rewrite', 'runtime-rewrite']
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_BOUNDARY
                .decision,
            'D-DTTLF-USABILITY-048'
        );
        assert.deepEqual(
            [
                CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_BOUNDARY
                    .activeLambdapiOwnerDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_BOUNDARY
                    .activeLambdapiRuleDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_BOUNDARY
                    .intrinsicCoreOwnerDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_BOUNDARY
                    .ownerSpecificCheckerOrEvaluatorDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_BOUNDARY
                    .externalOracleDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_BOUNDARY
                    .externalCoherenceEvidenceDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_BOUNDARY
                    .contextualIrNodeDelta
            ],
            [1, 3, 0, 0, 0, 0, 0]
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_BOUNDARY
                .transfersContextualCurry,
            false
        );
        assert.doesNotMatch(
            JSON.stringify({
                declaration:
                    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_MODULE,
                runtime:
                    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_RUNTIME_MODULE
            }),
            /mixed_curry|coerc|cast/u
        );
        assert.match(
            CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_CORE_NAMES
                .distributor,
            /Functor_catd_product_funcd/u
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_BOUNDARY
        );
    });

    it('checks the owner and all rules in TypeScript', () => {
        const compilation =
            compileCoreCategoricalDirectMixedProductDistributionTransfer();
        assert.equal(compilation.compiled.declarations.length, 1);
        assert.equal(compilation.runtimeFragment.localProgram.rules.length, 3);
        assert.deepEqual(
            compilation.runtimeFragment.localProgram.rules.map(rule =>
                rule.subjectValidation.kind
            ),
            [
                'typescript-checked',
                'typescript-checked',
                'typescript-checked'
            ]
        );
        assert.deepEqual(
            compilation.composedRuntime.ruleIds.slice(-3),
            [
                'categorical.direct-mixed-product-distribution.point',
                'categorical.direct-mixed-product-distribution.full-action',
                'categorical.direct-mixed-product-distribution.capped-action'
            ]
        );
        assertDeepFrozen(compilation.compiled.declarations);
        assertDeepFrozen(compilation.runtimeFragment.localProgram.rules);
    });
});
