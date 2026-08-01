/**
 * DIRECT-MIXED-INTRODUCTION-1D one-rule runtime transfer coverage.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_BOUNDARY,
    CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_RUNTIME_MODULE,
    CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_RUNTIME_POLICY,
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES,
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    compileCoreCategoricalDirectMixedIntroductionTransfer,
    coreCategoricalDisplayedNdHigherFoundationCoreName,
    coreCategoricalDisplayedEvaluationCoreName,
    coreCategoricalMixedActionCoreName,
    coreCategoricalStructuralSymbolCoreName,
    kernelApplication,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from '../src/v3_2';
import type {
    KernelExpression,
    Plicity
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

describe('DIRECT-MIXED-INTRODUCTION-1D runtime transfer', () => {
    it('pins a zero-declaration, one-rule generic boundary', () => {
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_RUNTIME_MODULE
                .declarations.length,
            0
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_RUNTIME_MODULE
                .runtimeRules.length,
            1
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_RUNTIME_POLICY
                .entries.map(entry => entry.policy),
            ['runtime-rewrite']
        );
        assert.deepEqual(
            [
                CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_BOUNDARY
                    .activeLambdapiOwnerDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_BOUNDARY
                    .activeLambdapiRuleDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_BOUNDARY
                    .intrinsicCoreOwnerDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_BOUNDARY
                    .ownerSpecificCheckerOrEvaluatorDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_BOUNDARY
                    .externalCoherenceEvidenceDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_BOUNDARY
                    .contextualBinderDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_BOUNDARY
                    .textOrBrowserDelta
            ],
            [0, 1, 0, 0, 0, 1, 0]
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_BOUNDARY
                .transfersContextualCurry,
            false
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_BOUNDARY
        );
    });

    it('subject-checks the rule after the existing mixed-action runtime',
    () => {
        const compilation =
            compileCoreCategoricalDirectMixedIntroductionTransfer();
        assert.equal(compilation.runtime.rules.length, 1);
        assert.equal(
            compilation.runtime.rules[0].subjectValidation.kind,
            'typescript-checked'
        );
        assert.equal(
            compilation.composedRuntime.ruleIds.at(-1),
            'categorical.direct-mixed-introduction.' +
                'target-postcomposition-projection'
        );
    });

    it('projects a whole fibre functor and retains object and arrow action',
    () => {
        const compilation =
            compileCoreCategoricalDirectMixedIntroductionTransfer();
        const p = provenance(
            'derived',
            'direct mixed executable projection witness'
        );
        const free = (name: string): KernelExpression =>
            kernelFree(name, p);
        const call = (
            name: string,
            arguments_: readonly {
                readonly plicity: Plicity;
                readonly value: KernelExpression;
            }[]
        ): KernelExpression => kernelCall(
            kernelFree(name, p),
            arguments_,
            p
        );
        const K = free('direct_transfer_K');
        const A = free('direct_transfer_A');
        const B = free('direct_transfer_B');
        const D = free('direct_transfer_D');
        const G = free('direct_transfer_G');
        const k = free('direct_transfer_k');
        const H = free('direct_transfer_H');
        const w = free('direct_transfer_w');
        const wPrime = free('direct_transfer_w_prime');
        const h = free('direct_transfer_h');
        const cat = kernelApplication('category-of-categories', [], p);
        const opK = call(
            CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
                .oppositeCategory,
            [{ plicity: 'explicit', value: K }]
        );
        const catdK = kernelApplication(
            'displayed-category-category',
            [{ value: K }],
            p
        );
        const fibre = (
            base: KernelExpression,
            family: KernelExpression
        ): KernelExpression => kernelApplication(
            'functor-object',
            [
                { value: base },
                { value: cat },
                { value: family },
                { value: k }
            ],
            p
        );
        const sourceFibre = fibre(opK, A);
        const middleFibre = fibre(K, B);
        const targetFibre = fibre(K, D);
        const functorCategory = (
            source: KernelExpression,
            target: KernelExpression
        ): KernelExpression => call(
            coreCategoricalStructuralSymbolCoreName(
                CORE_CATEGORICAL_STRUCTURAL_SYMBOLS.functorCategory
            ),
            [
                { plicity: 'explicit', value: source },
                { plicity: 'explicit', value: target }
            ]
        );
        const stable = (
            target: KernelExpression
        ): KernelExpression => call(
            coreCategoricalDisplayedEvaluationCoreName(
                'stableFunctorFamily'
            ),
            [
                { plicity: 'implicit', value: K },
                { plicity: 'explicit', value: A },
                { plicity: 'explicit', value: target }
            ]
        );
        const partial = call(
            coreCategoricalMixedActionCoreName(
                'mixedFunctorFamilyPartial'
            ),
            [
                { plicity: 'implicit', value: K },
                { plicity: 'explicit', value: A }
            ]
        );
        const targetAction = kernelApplication(
            'functor-hom-capped',
            [
                { value: catdK },
                { value: catdK },
                { value: partial },
                { value: B },
                { value: D },
                { value: G }
            ],
            p
        );
        const component = kernelApplication(
            'transfor-component-capped',
            [
                { value: K },
                { value: cat },
                { value: stable(B) },
                { value: stable(D) },
                { value: k },
                { value: targetAction }
            ],
            p
        );
        const before = kernelApplication(
            'functor-object',
            [
                { value: functorCategory(sourceFibre, middleFibre) },
                { value: functorCategory(sourceFibre, targetFibre) },
                { value: component },
                { value: H }
            ],
            p
        );
        const projected = compilation.composedRuntime.rewriteHead(before);
        assert.equal(projected.status, 'rewritten');
        if (projected.status !== 'rewritten') {
            assert.fail('Direct mixed whole-functor projection did not fire');
        }
        assert.equal(
            projected.ruleId,
            'categorical.direct-mixed-introduction.' +
                'target-postcomposition-projection'
        );

        const identityCat = call(
            coreCategoricalDisplayedNdHigherFoundationCoreName(
                'identityArrow'
            ),
            [
                { plicity: 'explicit', value: cat },
                { plicity: 'explicit', value: cat }
            ]
        );
        const normalizedTarget = kernelApplication(
            'functor-object',
            [
                { value: cat },
                { value: cat },
                { value: identityCat },
                { value: targetFibre }
            ],
            p
        );

        const objectAction = compilation.composedRuntime.rewriteHead(
            kernelApplication(
                'functor-object',
                [
                    { value: sourceFibre },
                    { value: normalizedTarget },
                    { value: projected.after },
                    { value: w }
                ],
                p
            )
        );
        const arrowAction = compilation.composedRuntime.rewriteHead(
            kernelApplication(
                'functor-hom-capped',
                [
                    { value: sourceFibre },
                    { value: normalizedTarget },
                    { value: projected.after },
                    { value: w },
                    { value: wPrime },
                    { value: h }
                ],
                p
            )
        );
        assert.equal(objectAction.status, 'rewritten');
        assert.equal(arrowAction.status, 'rewritten');
        if (
            objectAction.status === 'rewritten' &&
            arrowAction.status === 'rewritten'
        ) {
            assert.equal(
                kernelExpressionEquals(
                    objectAction.after,
                    arrowAction.after
                ),
                false
            );
        }
    });
});
