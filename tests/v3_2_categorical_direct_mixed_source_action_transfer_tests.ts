/**
 * DIRECT-MIXED-SOURCE-ACTION-1E2 and D-046 prerequisite coverage.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_BOUNDARY,
    CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_RUNTIME_MODULE,
    CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_RUNTIME_POLICY,
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES,
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    compileCoreCategoricalDirectMixedSourceActionTransfer,
    coreCategoricalDisplayedEvaluationCoreName,
    coreCategoricalDisplayedNdHigherFoundationCoreName,
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

describe('DIRECT-MIXED-SOURCE-ACTION-1E2 runtime transfer', () => {
    it('pins one existing prerequisite plus one new generic projection',
    () => {
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_RUNTIME_MODULE
                .declarations.length,
            0
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_RUNTIME_MODULE
                .runtimeRules.length,
            2
        );
        assert.deepEqual(
            [
                CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_BOUNDARY
                    .parentDecision,
                CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_BOUNDARY
                    .decision
            ],
            [
                'D-DTTLF-USABILITY-045',
                'D-DTTLF-USABILITY-046'
            ]
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_RUNTIME_POLICY
                .entries.map(entry => entry.policy),
            ['runtime-rewrite', 'runtime-rewrite']
        );
        assert.deepEqual(
            [
                CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_BOUNDARY
                    .existingPrerequisiteRuntimeRuleCount,
                CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_BOUNDARY
                    .newMathematicalRuntimeRuleCount,
                CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_BOUNDARY
                    .activeLambdapiOwnerDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_BOUNDARY
                    .activeLambdapiRuleDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_BOUNDARY
                    .intrinsicCoreOwnerDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_BOUNDARY
                    .ownerSpecificCheckerOrEvaluatorDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_BOUNDARY
                    .externalCoherenceEvidenceDelta
            ],
            [1, 1, 0, 1, 0, 0, 0]
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_BOUNDARY
                .transfersContextualCurry,
            false
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DIRECT_MIXED_SOURCE_ACTION_BOUNDARY
        );
    });

    it('subject-checks both rules without an external oracle', () => {
        const compilation =
            compileCoreCategoricalDirectMixedSourceActionTransfer();
        assert.deepEqual(
            compilation.runtime.rules.map(rule =>
                rule.subjectValidation.kind
            ),
            ['typescript-checked', 'typescript-checked']
        );
        assert.deepEqual(
            compilation.composedRuntime.ruleIds.slice(-2),
            [
                'categorical.direct-mixed-source-action.' +
                    'opposite-hom-endpoints',
                'categorical.direct-mixed-source-action.' +
                    'source-composition-projection'
            ]
        );
    });

    it('reverses opposite Hom endpoints without collapsing categories',
    () => {
        const compilation =
            compileCoreCategoricalDirectMixedSourceActionTransfer();
        const p = provenance('derived', 'opposite Hom transfer witness');
        const A = kernelFree('source_action_category', p);
        const X = kernelFree('source_action_X', p);
        const Y = kernelFree('source_action_Y', p);
        const opA = kernelCall(
            kernelFree(
                CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
                    .oppositeCategory,
                p
            ),
            [{ plicity: 'explicit', value: A }],
            p
        );
        const before = kernelApplication(
            'hom-category',
            [{ value: opA }, { value: X }, { value: Y }],
            p
        );
        const expected = kernelApplication(
            'hom-category',
            [{ value: A }, { value: Y }, { value: X }],
            p
        );
        const reduced = compilation.composedRuntime.rewriteHead(before);

        assert.equal(reduced.status, 'rewritten');
        if (reduced.status !== 'rewritten') {
            assert.fail('Opposite Hom endpoint rule did not fire');
        }
        assert.equal(
            reduced.ruleId,
            'categorical.direct-mixed-source-action.' +
                'opposite-hom-endpoints'
        );
        assert.equal(kernelExpressionEquals(reduced.after, expected), true);
        assert.equal(kernelExpressionEquals(opA, A), false);
    });

    it('projects the contravariant source action to an iterable composite',
    () => {
        const compilation =
            compileCoreCategoricalDirectMixedSourceActionTransfer();
        const p = provenance('derived', 'direct source action witness');
        const free = (name: string): KernelExpression => kernelFree(name, p);
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
        const K = free('source_action_K');
        const APrime = free('source_action_A_prime');
        const A = free('source_action_A');
        const B = free('source_action_B');
        const L = free('source_action_L');
        const k = free('source_action_k');
        const H = free('source_action_H');
        const a = free('source_action_a');
        const aPrime = free('source_action_a_prime');
        const ell = free('source_action_ell');
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
        const catdOpK = kernelApplication(
            'displayed-category-category',
            [{ value: opK }],
            p
        );
        const opCatdOpK = call(
            CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
                .oppositeCategory,
            [{ plicity: 'explicit', value: catdOpK }]
        );
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
        const stable = (
            source: KernelExpression,
            target: KernelExpression
        ): KernelExpression => call(
            coreCategoricalDisplayedEvaluationCoreName(
                'stableFunctorFamily'
            ),
            [
                { plicity: 'implicit', value: K },
                { plicity: 'explicit', value: source },
                { plicity: 'explicit', value: target }
            ]
        );
        const partial = (source: KernelExpression): KernelExpression =>
            call(
                coreCategoricalMixedActionCoreName(
                    'mixedFunctorFamilyPartial'
                ),
                [
                    { plicity: 'implicit', value: K },
                    { plicity: 'explicit', value: source }
                ]
            );
        const mixed = call(
            coreCategoricalDisplayedNdHigherFoundationCoreName(
                'mixedFunctorFamily'
            ),
            [{ plicity: 'explicit', value: K }]
        );
        const constructorAction = kernelApplication(
            'functor-hom-capped',
            [
                { value: opCatdOpK },
                { value: functorCategory(catdK, catdK) },
                { value: mixed },
                { value: A },
                { value: APrime },
                { value: L }
            ],
            p
        );
        const familyAction = kernelApplication(
            'transfor-component-capped',
            [
                { value: catdK },
                { value: catdK },
                { value: partial(A) },
                { value: partial(APrime) },
                { value: B },
                { value: constructorAction }
            ],
            p
        );
        const fibreAction = kernelApplication(
            'transfor-component-capped',
            [
                { value: K },
                { value: cat },
                { value: stable(A, B) },
                { value: stable(APrime, B) },
                { value: k },
                { value: familyAction }
            ],
            p
        );
        const sourceFibre = fibre(opK, APrime);
        const middleFibre = fibre(opK, A);
        const targetFibre = fibre(K, B);
        const before = kernelApplication(
            'functor-object',
            [
                { value: functorCategory(middleFibre, targetFibre) },
                { value: functorCategory(sourceFibre, targetFibre) },
                { value: fibreAction },
                { value: H }
            ],
            p
        );
        const LAtK = kernelApplication(
            'transfor-component-capped',
            [
                { value: opK },
                { value: cat },
                { value: APrime },
                { value: A },
                { value: k },
                { value: L }
            ],
            p
        );
        const expected = call(
            coreCategoricalStructuralSymbolCoreName(
                CORE_CATEGORICAL_STRUCTURAL_SYMBOLS.functorComposition
            ),
            [
                { plicity: 'implicit', value: sourceFibre },
                { plicity: 'implicit', value: middleFibre },
                { plicity: 'implicit', value: targetFibre },
                { plicity: 'explicit', value: H },
                { plicity: 'explicit', value: LAtK }
            ]
        );
        const projected = compilation.composedRuntime.rewriteHead(before);

        assert.equal(projected.status, 'rewritten');
        if (projected.status !== 'rewritten') {
            assert.fail('Direct mixed source projection did not fire');
        }
        assert.equal(
            projected.ruleId,
            'categorical.direct-mixed-source-action.' +
                'source-composition-projection'
        );
        assert.equal(
            kernelExpressionEquals(projected.after, expected),
            true
        );

        const objectAction = compilation.composedRuntime.rewriteHead(
            kernelApplication(
                'functor-object',
                [
                    { value: sourceFibre },
                    { value: targetFibre },
                    { value: projected.after },
                    { value: a }
                ],
                p
            )
        );
        const arrowAction = compilation.composedRuntime.rewriteHead(
            kernelApplication(
                'functor-hom-capped',
                [
                    { value: sourceFibre },
                    { value: targetFibre },
                    { value: projected.after },
                    { value: a },
                    { value: aPrime },
                    { value: ell }
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
