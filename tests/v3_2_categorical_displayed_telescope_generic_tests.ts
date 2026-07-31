/**
 * DISPLAYED-TELESCOPE-GENERIC-1 arbitrary finite canonical layer fold.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreCategoricalTerm,
    serializeCoreCategoricalExpression
} from '../src/v3_2';

const loweredCore = (
    emdash: CoreCategoricalProgram,
    term: CoreCategoricalTerm
): string => {
    const ir = emdash.inspect(term).ir;
    if (ir.tag !== 'explicit-core-term') {
        assert.fail('Closed displayed abstraction lost explicit Core');
    }
    return serializeCoreCategoricalExpression(ir.term);
};

const twoLayerCore = (
    emdash: CoreCategoricalProgram
): string => {
    const K = emdash.category('generic_two_K');
    const A = emdash.displayedFamily('generic_two_A', K);
    const sigmaA = emdash.totalCategory(A);
    const B = emdash.displayedFamily('generic_two_B', sigmaA);
    const liftedA = emdash.pullbackFamily(
        A,
        emdash.sigmaProjection(A)
    );
    const abstraction = emdash.displayedDependentContextLambda(
        [
            { name: 'a', family: A },
            { name: 'b', family: B }
        ],
        liftedA,
        ([a]) => a
    );
    return loweredCore(emdash, abstraction);
};

const fourBindingCore = (
    emdash: CoreCategoricalProgram
): string => {
    const K = emdash.category('generic_four_K');
    const A = emdash.displayedFamily('generic_four_A', K);
    const sigmaA = emdash.totalCategory(A);
    const B = emdash.displayedFamily('generic_four_B', sigmaA);
    const C = emdash.displayedFamily('generic_four_C', sigmaA);
    const P = emdash.displayedProduct(B, C);
    const sigmaP = emdash.totalCategory(P);
    const D = emdash.displayedFamily('generic_four_D', sigmaP);
    const liftedA = emdash.pullbackFamily(
        emdash.pullbackFamily(
            A,
            emdash.sigmaProjection(A)
        ),
        emdash.sigmaProjection(P)
    );
    const abstraction = emdash.displayedDependentContextLambda(
        [
            { name: 'a', family: A },
            { name: 'b', family: B },
            { name: 'c', family: C },
            { name: 'd', family: D }
        ],
        liftedA,
        ([a]) => a
    );
    return loweredCore(emdash, abstraction);
};

const deepFixture = (emdash: CoreCategoricalProgram) => {
    const K = emdash.category('generic_deep_K');
    const A = emdash.displayedFamily('generic_deep_A', K);
    const sigmaA = emdash.totalCategory(A);
    const B = emdash.displayedFamily('generic_deep_B', sigmaA);
    const C = emdash.displayedFamily('generic_deep_C', sigmaA);
    const P = emdash.displayedProduct(B, C);
    const sigmaP = emdash.totalCategory(P);
    const D = emdash.displayedFamily('generic_deep_D', sigmaP);
    const sigmaD = emdash.totalCategory(D);
    const E = emdash.displayedFamily('generic_deep_E', sigmaD);
    const F = emdash.displayedFamily('generic_deep_F', sigmaD);
    const Q = emdash.displayedProduct(E, F);
    const projectionA = emdash.sigmaProjection(A);
    const projectionP = emdash.sigmaProjection(P);
    const projectionD = emdash.sigmaProjection(D);
    const liftedA = emdash.pullbackFamily(
        emdash.pullbackFamily(
            emdash.pullbackFamily(A, projectionA),
            projectionP
        ),
        projectionD
    );
    const liftedD = emdash.pullbackFamily(D, projectionD);
    const bindings = [
        { name: 'a', family: A },
        { name: 'b', family: B },
        { name: 'c', family: C },
        { name: 'd', family: D },
        { name: 'e', family: E },
        { name: 'f', family: F }
    ] as const;
    return {
        emdash,
        K,
        A,
        sigmaA,
        sigmaD,
        E,
        F,
        Q,
        liftedA,
        liftedD,
        bindings
    };
};

const mixedProgram = new CoreCategoricalProgram({
    sourceFile:
        'tests/fixtures/categorical-displayed-telescope-generic.ts',
    profile: 'fibred-displayed-mixed-nest-1'
});
const predecessorProgram = new CoreCategoricalProgram({
    sourceFile:
        'tests/fixtures/categorical-displayed-telescope-predecessor.ts',
    profile: 'fibred-displayed-chain-2a'
});
const mixedDeep = deepFixture(mixedProgram);

describe('DISPLAYED-TELESCOPE-GENERIC-1 canonical layer fold', () => {
    it('preserves the completed two- and four-binding explicit Core',
    () => {
        assert.equal(
            twoLayerCore(mixedProgram),
            twoLayerCore(predecessorProgram)
        );
        assert.equal(
            fourBindingCore(mixedProgram),
            fourBindingCore(predecessorProgram)
        );
    });

    it('compiles four layers and two sibling blocks with frozen evidence',
    () => {
        const {
            emdash,
            liftedA,
            liftedD,
            Q,
            bindings
        } = mixedDeep;
        let callbackCount = 0;
        const early = emdash.displayedDependentContextLambda(
            bindings,
            liftedA,
            ([a]) => a
        );
        const middle = emdash.displayedDependentContextLambda(
            bindings,
            liftedD,
            ([, , , d]) => d
        );
        const finalPair = emdash.displayedDependentContextLambda(
            bindings,
            Q,
            ([, , , , e, f]) => {
                callbackCount += 1;
                return emdash.fibrePair(e, f);
            }
        );
        const earlyInspection = emdash.inspect(early);
        const middleInspection = emdash.inspect(middle);
        const pairCompilation = emdash.compile(finalPair);
        const evidence = pairCompilation.abstractions.at(-1);

        assert.equal(callbackCount, 1);
        assert.equal(earlyInspection.type.tag, 'displayed-functor');
        assert.equal(
            middleInspection.type.tag,
            'displayed-functor'
        );
        assert.equal(pairCompilation.surfaceType.tag, 'displayed-functor');
        assert.equal(
            evidence?.rule,
            'categorical.displayed-generic-dependent-context-bracket'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-generic-dependent-context-bracket'
        ) {
            assert.fail('Missing generic displayed telescope evidence');
        }
        assert.deepEqual(
            evidence.layers.map(layer => layer.bindingNames),
            [['a'], ['b', 'c'], ['d'], ['e', 'f']]
        );
        assert.equal(evidence.contextSize, 6);
        assert.equal(
            evidence.contextRelation,
            'arbitrary-finite-canonical-layer-fold'
        );
        assert.equal(Object.isFrozen(evidence), true);
        assert.equal(Object.isFrozen(evidence.layers), true);
        assert.equal(Object.isFrozen(evidence.layers[1]), true);
        assert.equal(Object.isFrozen(evidence.body), true);
        assert.match(
            loweredCore(emdash, early),
            /section-pullback/u
        );
        assert.match(
            pairCompilation.explicitCore,
            /displayed-product-pair/u
        );
        assert.equal(pairCompilation.productionLambdapiDependency, false);
    });

    it('retains an internalized base-arrow cell beyond fixed depth',
    () => {
        const {
            emdash,
            sigmaD,
            Q,
            liftedA,
            bindings
        } = mixedDeep;
        const early = emdash.displayedDependentContextLambda(
            bindings,
            liftedA,
            ([a]) => a
        );
        const x = emdash.object('generic_deep_x', sigmaD);
        const y = emdash.object('generic_deep_y', sigmaD);
        const p = emdash.hom('generic_deep_p', sigmaD, x, y);
        const q = emdash.object(
            'generic_deep_q',
            emdash.fibre(Q, x)
        );
        const cell = emdash.displayedFunctorInternalCell(
            early,
            p,
            q
        );
        const compilation = emdash.compile(cell);

        assert.equal(compilation.surfaceType.tag, 'hom');
        assert.match(
            compilation.explicitCore,
            /displayed-internal-cell/u
        );
        assert.equal(compilation.productionLambdapiDependency, false);
    });

    it('hosts the canonical mixed target and homd_int consumer',
    () => {
        const {
            emdash,
            sigmaD,
            Q,
            bindings
        } = mixedDeep;
        const Z = emdash.category('generic_deep_Z');
        const classifier = emdash.constantDisplayedFamily(
            sigmaD,
            emdash.displayedCategoryCategory(Z)
        );
        const Ebar = emdash.section(
            'generic_deep_Ebar',
            emdash.oppositeDisplayedFamily(classifier)
        );
        const Dbar = emdash.section(
            'generic_deep_Dbar',
            classifier
        );
        const H = emdash.mixedDisplayedHomFamily(
            classifier,
            Ebar,
            Dbar
        );
        const nested = emdash.displayedFunctor(
            'generic_deep_nested',
            Q,
            H
        );
        let outerCallbackCount = 0;
        let innerCallbackCount = 0;
        const factored = emdash.displayedDependentContextLambda(
            bindings,
            H,
            ([, , , , e, f]) => {
                outerCallbackCount += 1;
                const pair = emdash.fibrePair(e, f);
                const inner = emdash.apply(nested, pair);
                return emdash.nestedDisplayedFunctorLambda(
                    'z',
                    inner,
                    z => {
                        innerCallbackCount += 1;
                        return emdash.apply(inner, z);
                    }
                );
            }
        );
        const x = emdash.object('generic_mixed_x', sigmaD);
        const y = emdash.object('generic_mixed_y', sigmaD);
        const p = emdash.hom('generic_mixed_p', sigmaD, x, y);
        const q = emdash.object(
            'generic_mixed_q',
            emdash.fibre(Q, x)
        );
        const moved = emdash.apply(factored, p, {
            expectedShape: 'transport-functor'
        });
        const inner = emdash.apply(moved, q);
        const innerCompilation = emdash.compile(inner);
        const internalHom = emdash.compile(
            emdash.displayedInternalHom(inner)
        );

        assert.equal(outerCallbackCount, 1);
        assert.equal(innerCallbackCount, 1);
        assert.equal(
            emdash.compile(factored).surfaceType.tag,
            'displayed-functor'
        );
        assert.equal(
            innerCompilation.surfaceType.tag,
            'displayed-functor'
        );
        assert.match(internalHom.explicitCore, /homd_int/u);
        assert.match(
            internalHom.explicitCore,
            /displayed-functor-transport/u
        );
    });

    it('fails closed for noncanonical layer and target bases', () => {
        const {
            emdash,
            K,
            A,
            sigmaA
        } = mixedDeep;
        const L = emdash.category('generic_wrong_L');
        const wrongNext = emdash.displayedFamily(
            'generic_wrong_next',
            L
        );
        const B = emdash.displayedFamily(
            'generic_right_next',
            sigmaA
        );
        const wrongTarget = emdash.displayedFamily(
            'generic_wrong_target',
            K
        );

        assert.throws(
            () => emdash.displayedDependentContextLambda(
                [
                    { name: 'a', family: A },
                    { name: 'wrong', family: wrongNext }
                ],
                wrongNext,
                ([, wrong]) => wrong
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'DISPLAYED_BASE_MISMATCH'
        );
        assert.throws(
            () => emdash.displayedDependentContextLambda(
                [
                    { name: 'a', family: A },
                    { name: 'b', family: B }
                ],
                wrongTarget,
                ([a]) => a
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'DISPLAYED_BASE_MISMATCH'
        );
    });

    it('rejects duplicate, one-layer, and predecessor overreach',
    () => {
        const value = mixedDeep;
        const sameLayer = value.emdash.displayedFamily(
            'generic_same_layer',
            value.K
        );
        assert.throws(
            () => value.emdash.displayedDependentContextLambda(
                [
                    { name: 'a', family: value.A },
                    { name: 'a', family: sameLayer }
                ],
                value.A,
                ([a]) => a
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'INVALID_DISPLAYED_CONTEXT'
        );
        assert.throws(
            () => value.emdash.displayedDependentContextLambda(
                [
                    { name: 'a', family: value.A },
                    { name: 'x', family: sameLayer }
                ],
                value.A,
                ([a]) => a
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'INVALID_DISPLAYED_CONTEXT'
        );

        const predecessor = deepFixture(predecessorProgram);
        assert.throws(
            () => predecessor.emdash.displayedDependentContextLambda(
                predecessor.bindings,
                predecessor.Q,
                ([, , , , e, f]) =>
                    predecessor.emdash.fibrePair(e, f)
            ),
            (error: unknown) =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'INVALID_DISPLAYED_CONTEXT'
        );
    });
});
