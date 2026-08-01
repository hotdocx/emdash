/**
 * DIRECT-MIXED-CONSTANT-MIDDLE-COMPOSITION-1M surface coverage.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_PROGRAM_REVISION,
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    coreCategoricalDirectMixedConstantMiddleCoreName,
    serializeCoreExpression
} from '../src/v3_2';
import type {
    CoreCategoricalSlotToken
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

const fixture = (suffix: string) => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            `tests/fixtures/categorical-direct-constant-${suffix}.ts`,
        profile: 'fibred-direct-mixed-introduction-1'
    });
    const K = emdash.category(`direct_constant_${suffix}_K`);
    const opK = emdash.oppositeCategory(K);
    const C = emdash.displayedFamily(
        `direct_constant_${suffix}_C`,
        K
    );
    const A = emdash.displayedFamily(
        `direct_constant_${suffix}_A`,
        opK
    );
    const B = emdash.displayedFamily(
        `direct_constant_${suffix}_B`,
        K
    );
    return { emdash, K, opK, C, A, B };
};

describe('DIRECT-MIXED-CONSTANT-MIDDLE-COMPOSITION-1M binder', () => {
    it('keeps direct nesting fundamental and composes one constant middle',
    () => {
        const { emdash, K, opK, C, A, B } = fixture('one');
        const X = emdash.category('direct_constant_one_X');
        const constantKX = emdash.constantDisplayedFamily(K, X);
        const constantOpKX = emdash.constantDisplayedFamily(opK, X);
        const F = emdash.displayedFunctor(
            'direct_constant_one_F',
            C,
            emdash.mixedDisplayedFunctorFamily(A, constantKX)
        );
        const G = emdash.displayedFunctor(
            'direct_constant_one_G',
            C,
            emdash.mixedDisplayedFunctorFamily(constantOpKX, B)
        );

        // Fundamental source form:
        //   lambda^n k. lambda^f c. lambda^f a. G[c](F[c](a))
        const result = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'a', family: A },
            B,
            (c, a) => emdash.apply(
                emdash.apply(G, c),
                emdash.apply(emdash.apply(F, c), a)
            )
        );
        const compiled = emdash.compile(result);
        const evidence = emdash.inspect(result).abstractions.find(
            candidate => candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );
        const core = serializeCoreExpression(compiled.explicitTerm);

        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_PROGRAM_REVISION,
            'DIRECT-MIXED-NEGATIVE-TOWER-1P-CATEGORICAL-PROGRAM-1'
        );
        assert.match(
            core,
            new RegExp(
                coreCategoricalDirectMixedConstantMiddleCoreName(
                    'displayedComposition'
                ),
                'u'
            )
        );
        assert.equal(compiled.surfaceType.tag, 'displayed-functor');
        assert.equal(compiled.productionLambdapiDependency, false);
        assert.equal(evidence?.constantMiddleApplicationCount, 1);
        assert.equal(evidence?.outerUsageCount, 2);
        assert.equal(evidence?.innerUsageCount, 1);
        assert.equal(evidence?.leafCount, 1);
        assert.deepEqual(evidence?.bindingModes, [
            'natural',
            'functorial',
            'functorial'
        ]);
        assert.ok(
            evidence?.dependentPrerequisites.includes(
                'mixed-functor-constant-middle-composition'
            )
        );
        assert.doesNotMatch(
            core,
            /mixed_curry|mix_uncurried_family|total.context|coerc|cast/u
        );
        assertDeepFrozen(emdash.inspect(result));
    });

    it('iterates the same recursive node through two constant middles',
    () => {
        const { emdash, K, opK, C, A, B } = fixture('chain');
        const X = emdash.category('direct_constant_chain_X');
        const Y = emdash.category('direct_constant_chain_Y');
        const constantKX = emdash.constantDisplayedFamily(K, X);
        const constantOpKX = emdash.constantDisplayedFamily(opK, X);
        const constantKY = emdash.constantDisplayedFamily(K, Y);
        const constantOpKY = emdash.constantDisplayedFamily(opK, Y);
        const F = emdash.displayedFunctor(
            'direct_constant_chain_F',
            C,
            emdash.mixedDisplayedFunctorFamily(A, constantKX)
        );
        const G = emdash.displayedFunctor(
            'direct_constant_chain_G',
            C,
            emdash.mixedDisplayedFunctorFamily(
                constantOpKX,
                constantKY
            )
        );
        const H = emdash.displayedFunctor(
            'direct_constant_chain_H',
            C,
            emdash.mixedDisplayedFunctorFamily(constantOpKY, B)
        );
        const result = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'a', family: A },
            B,
            (c, a) => emdash.apply(
                emdash.apply(H, c),
                emdash.apply(
                    emdash.apply(G, c),
                    emdash.apply(emdash.apply(F, c), a)
                )
            )
        );
        const compiled = emdash.compile(result);
        const evidence = emdash.inspect(result).abstractions.find(
            candidate => candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );
        const owner = coreCategoricalDirectMixedConstantMiddleCoreName(
            'displayedComposition'
        );
        const core = serializeCoreExpression(compiled.explicitTerm);

        assert.equal(
            core.split(owner).length - 1,
            2
        );
        assert.equal(evidence?.constantMiddleApplicationCount, 2);
        assert.equal(evidence?.outerUsageCount, 3);
        assert.equal(evidence?.innerUsageCount, 1);
        assert.equal(evidence?.pairNodeCount, 0);
        assert.doesNotMatch(core, /mixed_curry|coerc|cast/u);
        assertDeepFrozen(emdash.inspect(result));
    });

    it('composes above recursive source, target and pair structure', () => {
        const { emdash, K, opK, C, A, B } = fixture('structured');
        const APrime = emdash.displayedFamily(
            'direct_constant_structured_A_prime',
            opK
        );
        const L = emdash.displayedFunctor(
            'direct_constant_structured_L',
            APrime,
            A
        );
        const X = emdash.category('direct_constant_structured_X');
        const Y = emdash.category('direct_constant_structured_Y');
        const XY = emdash.productCategory(X, Y);
        const constantKX = emdash.constantDisplayedFamily(K, X);
        const constantKY = emdash.constantDisplayedFamily(K, Y);
        const constantKXY = emdash.constantDisplayedFamily(K, XY);
        const constantOpKXY = emdash.constantDisplayedFamily(opK, XY);
        const F = emdash.displayedFunctor(
            'direct_constant_structured_F',
            C,
            emdash.mixedDisplayedFunctorFamily(A, constantKX)
        );
        const F2 = emdash.displayedFunctor(
            'direct_constant_structured_F2',
            C,
            emdash.mixedDisplayedFunctorFamily(A, constantKY)
        );
        const pack = emdash.displayedFunctor(
            'direct_constant_structured_pack',
            emdash.displayedProduct(constantKX, constantKY),
            constantKXY
        );
        const G = emdash.displayedFunctor(
            'direct_constant_structured_G',
            C,
            emdash.mixedDisplayedFunctorFamily(constantOpKXY, B)
        );
        const result = emdash.mixedDisplayedFunctorLambda(
            { name: 'c', family: C },
            { name: 'aPrime', family: APrime },
            B,
            (c, aPrime) => {
                const a = emdash.apply(L, aPrime);
                const pair = emdash.fibrePair(
                    emdash.apply(emdash.apply(F, c), a),
                    emdash.apply(emdash.apply(F2, c), a)
                );
                return emdash.apply(
                    emdash.apply(G, c),
                    emdash.apply(pack, pair)
                );
            }
        );
        const compiled = emdash.compile(result);
        const evidence = emdash.inspect(result).abstractions.find(
            candidate => candidate.rule ===
                'categorical.direct-mixed-displayed-functor'
        );
        const core = serializeCoreExpression(compiled.explicitTerm);

        assert.equal(compiled.surfaceType.tag, 'displayed-functor');
        assert.equal(evidence?.constantMiddleApplicationCount, 1);
        assert.equal(evidence?.leafCount, 2);
        assert.equal(evidence?.sourceChainLength, 2);
        assert.equal(evidence?.targetChainLength, 1);
        assert.equal(evidence?.pairNodeCount, 1);
        assert.equal(evidence?.pairDepth, 1);
        assert.match(core, /Functor_catd_product_funcd/u);
        assert.match(
            core,
            new RegExp(
                coreCategoricalDirectMixedConstantMiddleCoreName(
                    'displayedComposition'
                ),
                'u'
            )
        );
        assert.doesNotMatch(core, /mixed_curry|coerc|cast/u);
        assertDeepFrozen(emdash.inspect(result));
    });

    it('fails closed for unequal constant fibres', () => {
        const { emdash, K, opK, C, A, B } = fixture('unequal');
        const X = emdash.category('direct_constant_unequal_X');
        const Y = emdash.category('direct_constant_unequal_Y');
        const F = emdash.displayedFunctor(
            'direct_constant_unequal_F',
            C,
            emdash.mixedDisplayedFunctorFamily(
                A,
                emdash.constantDisplayedFamily(K, X)
            )
        );
        const G = emdash.displayedFunctor(
            'direct_constant_unequal_G',
            C,
            emdash.mixedDisplayedFunctorFamily(
                emdash.constantDisplayedFamily(opK, Y),
                B
            )
        );

        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: A },
                B,
                (c, a) => emdash.apply(
                    emdash.apply(G, c),
                    emdash.apply(emdash.apply(F, c), a)
                )
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
    });

    it('does not generalize the node to a nonconstant middle', () => {
        const { emdash, K, opK, C, A, B } = fixture('nonconstant');
        const D = emdash.displayedFamily(
            'direct_constant_nonconstant_D',
            K
        );
        const E = emdash.displayedFamily(
            'direct_constant_nonconstant_E',
            opK
        );
        const F = emdash.displayedFunctor(
            'direct_constant_nonconstant_F',
            C,
            emdash.mixedDisplayedFunctorFamily(A, D)
        );
        const G = emdash.displayedFunctor(
            'direct_constant_nonconstant_G',
            C,
            emdash.mixedDisplayedFunctorFamily(E, B)
        );

        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'c', family: C },
                { name: 'a', family: A },
                B,
                (c, a) => emdash.apply(
                    emdash.apply(G, c),
                    emdash.apply(emdash.apply(F, c), a)
                )
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
    });

    it('rejects the non-opposite constant source orientation', () => {
        const { emdash, K, B } = fixture('orientation');
        const X = emdash.category('direct_constant_orientation_X');

        assert.throws(
            () => emdash.mixedDisplayedFunctorFamily(
                emdash.constantDisplayedFamily(K, X),
                B
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'DISPLAYED_BASE_MISMATCH'
        );
    });

    it('rejects a subject applied to an escaped outer token', () => {
        const { emdash, K, opK, C, A, B } = fixture('foreign_outer');
        const X = emdash.category('direct_constant_foreign_outer_X');
        const constantKX = emdash.constantDisplayedFamily(K, X);
        const constantOpKX = emdash.constantDisplayedFamily(opK, X);
        const F = emdash.displayedFunctor(
            'direct_constant_foreign_outer_F',
            C,
            emdash.mixedDisplayedFunctorFamily(A, constantKX)
        );
        const G = emdash.displayedFunctor(
            'direct_constant_foreign_outer_G',
            C,
            emdash.mixedDisplayedFunctorFamily(constantOpKX, B)
        );
        let escapedOuter: CoreCategoricalSlotToken | undefined;
        emdash.mixedDisplayedFunctorLambda(
            { name: 'oldC', family: C },
            { name: 'oldA', family: A },
            constantKX,
            (c, a) => {
                escapedOuter = c;
                return emdash.apply(emdash.apply(F, c), a);
            }
        );
        if (escapedOuter === undefined) {
            assert.fail('Direct binder did not expose its scoped test token');
        }

        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'newC', family: C },
                { name: 'newA', family: A },
                B,
                (c, a) => emdash.apply(
                    emdash.apply(G, escapedOuter),
                    emdash.apply(emdash.apply(F, c), a)
                )
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'ESCAPED_SLOT'
        );
    });

    it('does not treat a bound pointwise functor as a closed G subject',
    () => {
        const { emdash, K, opK, A, B } = fixture('open_subject');
        const X = emdash.category('direct_constant_open_subject_X');
        const constantKX = emdash.constantDisplayedFamily(K, X);
        const constantOpKX = emdash.constantDisplayedFamily(opK, X);
        const C = emdash.mixedDisplayedFunctorFamily(constantOpKX, B);
        const F = emdash.displayedFunctor(
            'direct_constant_open_subject_F',
            C,
            emdash.mixedDisplayedFunctorFamily(A, constantKX)
        );

        assert.throws(
            () => emdash.mixedDisplayedFunctorLambda(
                { name: 'openG', family: C },
                { name: 'a', family: A },
                B,
                (openG, a) => emdash.apply(
                    openG,
                    emdash.apply(emdash.apply(F, openG), a)
                )
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );
    });
});
