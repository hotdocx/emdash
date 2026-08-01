/**
 * DIRECT-MIXED-WEAKENING-1J generic transfer coverage.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES,
    CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_BOUNDARY,
    CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_CORE_NAMES,
    CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_RUNTIME_MODULE,
    CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_RUNTIME_POLICY,
    CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_MODULE,
    CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_POLICY,
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    compileCoreCategoricalDirectMixedWeakeningTransfer,
    coreCategoricalDisplayedNdHigherFoundationCoreName,
    coreCategoricalStructuralSymbolCoreName,
    kernelApplication,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    provenance,
    serializeCoreExpression
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

describe('DIRECT-MIXED-WEAKENING-1J transfer', () => {
    it('pins two signatures and exactly three active projections', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_MODULE
                .declarations.map(entry => entry.symbol.name),
            ['hom_postcomp_func', 'Functor_catd_const_funcd']
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_RUNTIME_MODULE
                .runtimeRules.map(rule => rule.id),
            [
                'categorical.direct-mixed-weakening.point',
                'categorical.direct-mixed-weakening.full-action',
                'categorical.direct-mixed-weakening.capped-action'
            ]
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_POLICY
                .entries.map(entry => entry.policy),
            ['opaque-signature', 'opaque-signature']
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_RUNTIME_POLICY
                .entries.map(entry => entry.policy),
            ['runtime-rewrite', 'runtime-rewrite', 'runtime-rewrite']
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_BOUNDARY.decision,
            'D-DTTLF-USABILITY-050'
        );
        assert.deepEqual(
            [
                CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_BOUNDARY
                    .activeLambdapiOwnerDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_BOUNDARY
                    .activeLambdapiRuleDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_BOUNDARY
                    .preExistingSignatureAcquisitionDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_BOUNDARY
                    .intrinsicCoreOwnerDelta,
                CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_BOUNDARY
                    .externalCoherenceEvidenceDelta
            ],
            [1, 3, 1, 0, 0]
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_BOUNDARY
                .directNestedIntroductionRemainsFundamental,
            true
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_BOUNDARY
                .transfersContextualCurry,
            false
        );
        assert.doesNotMatch(
            JSON.stringify({
                declaration:
                    CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_MODULE,
                runtime:
                    CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_RUNTIME_MODULE
            }),
            /mixed_curry|mix_uncurried_family|coerc|cast/u
        );
        assert.match(
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_CORE_NAMES.weakening,
            /Functor_catd_const_funcd/u
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_BOUNDARY
        );
    });

    it('checks both declarations and all rules in TypeScript', () => {
        const compilation =
            compileCoreCategoricalDirectMixedWeakeningTransfer();
        assert.equal(compilation.compiled.declarations.length, 2);
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
                'categorical.direct-mixed-weakening.point',
                'categorical.direct-mixed-weakening.full-action',
                'categorical.direct-mixed-weakening.capped-action'
            ]
        );
        assertDeepFrozen(compilation.compiled.declarations);
        assertDeepFrozen(compilation.runtimeFragment.localProgram.rules);
    });

    it('projects the fibre owner and keeps base and higher action iterable',
    () => {
        const compilation =
            compileCoreCategoricalDirectMixedWeakeningTransfer();
        const runtime = compilation.composedRuntime;
        const p = provenance('derived', 'direct mixed weakening witness');
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
        const K = free('weakening_K');
        const A = free('weakening_A');
        const B = free('weakening_B');
        const x = free('weakening_x');
        const y = free('weakening_y');
        const k = free('weakening_k');
        const baseArrow = free('weakening_p');
        const nextBaseArrow = free('weakening_q');
        const higherCell = free('weakening_alpha');
        const b = free('weakening_b');
        const bPrime = free('weakening_b_prime');
        const innerArrow = free('weakening_beta');
        const cat = kernelApplication('category-of-categories', [], p);
        const opK = call(
            CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
                .oppositeCategory,
            [{ plicity: 'explicit', value: K }]
        );
        const fibre = (
            base: KernelExpression,
            family: KernelExpression,
            point: KernelExpression
        ): KernelExpression => kernelApplication(
            'functor-object',
            [
                { value: base },
                { value: cat },
                { value: family },
                { value: point }
            ],
            p
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
        const Ak = fibre(opK, A, k);
        const Bk = fibre(K, B, k);
        const Ax = fibre(opK, A, x);
        const Ay = fibre(opK, A, y);
        const Bx = fibre(K, B, x);
        const By = fibre(K, B, y);
        const stable = call(
            coreCategoricalDisplayedNdHigherFoundationCoreName(
                'mixedFunctorFamily'
            ),
            [
                { plicity: 'implicit', value: K },
                { plicity: 'explicit', value: A },
                { plicity: 'explicit', value: B }
            ]
        );
        const weakening = call(
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_CORE_NAMES.weakening,
            [
                { plicity: 'implicit', value: K },
                { plicity: 'implicit', value: A },
                { plicity: 'implicit', value: B }
            ]
        );
        const constantAtK = call(
            coreCategoricalStructuralSymbolCoreName(
                CORE_CATEGORICAL_STRUCTURAL_SYMBOLS
                    .constantFunctorAbstraction
            ),
            [
                { plicity: 'implicit', value: Ak },
                { plicity: 'implicit', value: Bk }
            ]
        );

        const point = runtime.rewriteHead(kernelApplication(
            'transfor-component-capped',
            [
                { value: K },
                { value: cat },
                { value: B },
                { value: stable },
                { value: k },
                { value: weakening }
            ],
            p
        ));
        assert.equal(point.status, 'rewritten');
        if (point.status !== 'rewritten') {
            assert.fail('Direct mixed weakening point rule did not fire');
        }
        assert.equal(
            point.ruleId,
            'categorical.direct-mixed-weakening.point'
        );
        assert.equal(
            kernelExpressionEquals(point.after, constantAtK),
            true
        );

        const pointTarget = functorCategory(Ak, Bk);
        const objectAction = runtime.rewriteHead(kernelApplication(
            'functor-object',
            [
                { value: Bk },
                { value: pointTarget },
                { value: point.after },
                { value: b }
            ],
            p
        ));
        const innerAction = runtime.rewriteHead(kernelApplication(
            'functor-hom-capped',
            [
                { value: Bk },
                { value: pointTarget },
                { value: point.after },
                { value: b },
                { value: bPrime },
                { value: innerArrow }
            ],
            p
        ));
        // D050 stops at the stable ordinary weakening owner. Its own
        // fapp0/fapp1 projections are active and checked in Lambdapi but are
        // not part of this TypeScript transfer profile.
        assert.equal(objectAction.status, 'irreducible');
        assert.equal(innerAction.status, 'irreducible');
        assert.equal(
            kernelExpressionEquals(
                objectAction.expression,
                innerAction.expression
            ),
            false
        );
        assert.match(
            serializeCoreExpression(objectAction.expression),
            /Const_func_func/u
        );
        assert.match(
            serializeCoreExpression(innerAction.expression),
            /Const_func_func/u
        );

        const capped = runtime.rewriteHead(kernelApplication(
            'transfor-hom-capped',
            [
                { value: K },
                { value: cat },
                { value: B },
                { value: stable },
                { value: x },
                { value: y },
                { value: weakening },
                { value: baseArrow }
            ],
            p
        ));
        assert.equal(capped.status, 'rewritten');
        if (capped.status !== 'rewritten') {
            assert.fail('Direct mixed weakening capped rule did not fire');
        }
        assert.equal(
            capped.ruleId,
            'categorical.direct-mixed-weakening.capped-action'
        );
        assert.match(serializeCoreExpression(capped.after), /functor-hom/u);

        const full = runtime.rewriteHead(kernelApplication(
            'transfor-hom-full',
            [
                { value: K },
                { value: cat },
                { value: B },
                { value: stable },
                { value: x },
                { value: y },
                { value: weakening }
            ],
            p
        ));
        assert.equal(full.status, 'rewritten');
        if (full.status !== 'rewritten') {
            assert.fail('Direct mixed weakening full rule did not fire');
        }
        assert.equal(
            full.ruleId,
            'categorical.direct-mixed-weakening.full-action'
        );
        assert.match(
            serializeCoreExpression(full.after),
            new RegExp(
                CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_CORE_NAMES
                    .homPostcomposition,
                'u'
            )
        );

        const homKxy = kernelApplication(
            'hom-category',
            [{ value: K }, { value: x }, { value: y }],
            p
        );
        const fullTarget = functorCategory(
            Bx,
            functorCategory(Ay, By)
        );
        const higher = runtime.rewriteHead(kernelApplication(
            'functor-hom-capped',
            [
                { value: homKxy },
                { value: fullTarget },
                { value: full.after },
                { value: baseArrow },
                { value: nextBaseArrow },
                { value: higherCell }
            ],
            p
        ));
        assert.equal(higher.status, 'rewritten');
        if (higher.status === 'rewritten') {
            assert.equal(
                kernelExpressionEquals(higher.after, capped.after),
                false
            );
        }

        // Keep the endpoint fibres visibly distinct in the witness.
        assert.equal(kernelExpressionEquals(Ax, Ay), false);
    });
});
