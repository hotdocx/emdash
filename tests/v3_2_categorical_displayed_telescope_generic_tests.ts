/**
 * DISPLAYED-TELESCOPE-GENERIC-1 arbitrary finite canonical layer fold and
 * TEXT-PARITY-MIXED-1 adapter parity.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_REVISION,
    CoreCategoricalDisplayedFamily,
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreCategoricalTerm,
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    CoreCategoricalTextErrorCode,
    CoreCategoricalTextTermExpected,
    elaborateCoreCategoricalText,
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

const point = (
    emdash: CoreCategoricalProgram,
    transformation: CoreCategoricalTerm,
    argument: CoreCategoricalTerm
): CoreCategoricalTerm => emdash.apply(
    transformation,
    argument,
    { expectedShape: 'point-component' }
);

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
        B,
        C,
        D,
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
const predecessorDeep = deepFixture(predecessorProgram);

const contextualTransforFixture = () => {
    const emdash = mixedProgram;
    const K = emdash.category('generic_nd_context_K');
    const A = emdash.displayedFamily('generic_nd_context_A', K);
    const C = emdash.displayedFamily('generic_nd_context_C', K);
    const siblingProduct = emdash.displayedProduct(A, C);
    const siblingTarget = emdash.displayedFamily(
        'generic_nd_context_sibling_D',
        K
    );
    const siblingF = emdash.displayedFunctor(
        'generic_nd_context_sibling_F',
        siblingProduct,
        siblingTarget
    );
    const siblingG = emdash.displayedFunctor(
        'generic_nd_context_sibling_G',
        siblingProduct,
        siblingTarget
    );
    const siblingEta = emdash.displayedTransfor(
        'generic_nd_context_sibling_eta',
        siblingF,
        siblingG
    );

    const sigmaA = emdash.totalCategory(A);
    const B = emdash.displayedFamily('generic_nd_context_B', sigmaA);
    const liftedA = emdash.pullbackFamily(
        A,
        emdash.sigmaProjection(A)
    );
    const dependentProduct = emdash.displayedProduct(liftedA, B);
    const D = emdash.displayedFamily('generic_nd_context_D', sigmaA);
    const Q = emdash.displayedFamily('generic_nd_context_Q', sigmaA);
    const F = emdash.displayedFunctor(
        'generic_nd_context_F',
        dependentProduct,
        D
    );
    const G = emdash.displayedFunctor(
        'generic_nd_context_G',
        dependentProduct,
        D
    );
    const H = emdash.displayedFunctor(
        'generic_nd_context_H',
        dependentProduct,
        D
    );
    const postMapper = emdash.displayedFunctor(
        'generic_nd_context_post',
        D,
        Q
    );
    const eta = emdash.displayedTransfor(
        'generic_nd_context_eta',
        F,
        G
    );
    const theta = emdash.displayedTransfor(
        'generic_nd_context_theta',
        G,
        H
    );
    const x = emdash.object('generic_nd_context_x', sigmaA);
    const y = emdash.object('generic_nd_context_y', sigmaA);
    const p = emdash.hom('generic_nd_context_p', sigmaA, x, y);
    const u = emdash.object(
        'generic_nd_context_u',
        emdash.fibre(B, x)
    );
    const bindings = [
        { name: 'a', family: A },
        { name: 'b', family: B }
    ] as const;
    return {
        emdash,
        K,
        A,
        C,
        siblingProduct,
        siblingTarget,
        siblingEta,
        sigmaA,
        B,
        liftedA,
        dependentProduct,
        D,
        Q,
        F,
        G,
        H,
        postMapper,
        eta,
        theta,
        x,
        p,
        u,
        bindings
    };
};

const contextualTransfor = contextualTransforFixture();

const textSourceFile =
    'tests/fixtures/categorical-text-mixed-generic.emdash';

const familyBinding = (
    name: string,
    value: CoreCategoricalDisplayedFamily
): CoreCategoricalTextBinding => Object.freeze({
    name,
    kind: 'displayed-family' as const,
    value
});

const termBinding = (
    name: string,
    value: CoreCategoricalTerm
): CoreCategoricalTextBinding => Object.freeze({
    name,
    kind: 'term' as const,
    value
});

const deepTextEnvironment = (
    data: ReturnType<typeof deepFixture>,
    terms: readonly CoreCategoricalTextBinding[] = []
): readonly CoreCategoricalTextBinding[] => Object.freeze([
    familyBinding('A', data.A),
    familyBinding('B', data.B),
    familyBinding('C', data.C),
    familyBinding('D', data.D),
    familyBinding('E', data.E),
    familyBinding('F', data.F),
    ...terms
]);

const deepTextExpected = (
    data: ReturnType<typeof deepFixture>,
    target: CoreCategoricalDisplayedFamily,
    bodyExpected:
        | { readonly kind: 'mixed-nested-displayed-eta' }
        | undefined = undefined
): CoreCategoricalTextTermExpected => Object.freeze({
    kind: 'displayed-dependent-context-functor' as const,
    sourceGroups: Object.freeze([
        Object.freeze([data.A]),
        Object.freeze([data.B, data.C]),
        Object.freeze([data.D]),
        Object.freeze([data.E, data.F])
    ]),
    target,
    ...(bodyExpected === undefined ? {} : { bodyExpected })
});

const contextualNdExpected = (
    sourceGroups:
        readonly (readonly CoreCategoricalDisplayedFamily[])[]
): CoreCategoricalTextTermExpected => Object.freeze({
    kind: 'displayed-dependent-context-transfor' as const,
    sourceGroups
});

const contextualNdEnvironment = (
    terms: readonly CoreCategoricalTextBinding[] = []
): readonly CoreCategoricalTextBinding[] => Object.freeze([
    familyBinding('A', contextualTransfor.A),
    familyBinding('B', contextualTransfor.B),
    familyBinding('C', contextualTransfor.C),
    ...terms
]);

const elaborateDeepText = (
    data: ReturnType<typeof deepFixture>,
    source: string,
    expected: CoreCategoricalTextTermExpected,
    environment = deepTextEnvironment(data)
): CoreCategoricalTerm => elaborateCoreCategoricalText(
    data.emdash,
    {
        source,
        sourceFile: textSourceFile,
        environment,
        expected
    }
);

const captureTextError = (
    action: () => unknown,
    code: CoreCategoricalTextErrorCode
): CoreCategoricalTextError => {
    let captured: unknown;
    try {
        action();
    } catch (error: unknown) {
        captured = error;
    }
    assert.equal(captured instanceof CoreCategoricalTextError, true);
    const diagnostic = captured as CoreCategoricalTextError;
    assert.equal(diagnostic.code, code);
    assert.equal(diagnostic.span.file, textSourceFile);
    return diagnostic;
};

const shallowNestedTextFixture = () => {
    const emdash = mixedProgram;
    const K = emdash.category('generic_text_shallow_K');
    const A = emdash.displayedFamily(
        'generic_text_shallow_A',
        K
    );
    const sigmaA = emdash.totalCategory(A);
    const B = emdash.displayedFamily(
        'generic_text_shallow_B',
        sigmaA
    );
    const Z = emdash.category('generic_text_shallow_Z');
    const classifier = emdash.constantDisplayedFamily(
        sigmaA,
        emdash.displayedCategoryCategory(Z)
    );
    const Ebar = emdash.section(
        'generic_text_shallow_Ebar',
        emdash.oppositeDisplayedFamily(classifier)
    );
    const Dbar = emdash.section(
        'generic_text_shallow_Dbar',
        classifier
    );
    const H = emdash.mixedDisplayedHomFamily(
        classifier,
        Ebar,
        Dbar
    );
    const nested = emdash.displayedFunctor(
        'generic_text_shallow_nested',
        B,
        H
    );
    const environment: readonly CoreCategoricalTextBinding[] =
        Object.freeze([
            familyBinding('A', A),
            familyBinding('B', B),
            termBinding('nested', nested)
        ]);
    const expected: CoreCategoricalTextTermExpected =
        Object.freeze({
            kind:
                'displayed-dependent-context-functor' as const,
            sourceGroups: Object.freeze([
                Object.freeze([A]),
                Object.freeze([B])
            ]),
            target: H,
            bodyExpected: Object.freeze({
                kind: 'mixed-nested-displayed-eta' as const
            })
        });
    return {
        emdash,
        K,
        A,
        sigmaA,
        B,
        H,
        nested,
        environment,
        expected
    };
};

const falseLayerTextFixture = () => {
    const emdash = mixedProgram;
    const K = emdash.category('generic_text_layers_K');
    const L = emdash.displayedFamily('generic_text_layers_L', K);
    const R = emdash.displayedFamily('generic_text_layers_R', K);
    const product = emdash.displayedProduct(L, R);
    const total = emdash.totalCategory(product);
    const D = emdash.displayedFamily(
        'generic_text_layers_D',
        total
    );
    const environment: readonly CoreCategoricalTextBinding[] =
        Object.freeze([
            familyBinding('L', L),
            familyBinding('R', R),
            familyBinding('D', D)
        ]);
    const falseExpected: CoreCategoricalTextTermExpected =
        Object.freeze({
            kind:
                'displayed-dependent-context-functor' as const,
            sourceGroups: Object.freeze([
                Object.freeze([L]),
                Object.freeze([R]),
                Object.freeze([D])
            ]),
            target: D
        });
    return {
        emdash,
        L,
        R,
        D,
        environment,
        falseExpected
    };
};

const shallowNestedText = shallowNestedTextFixture();
const falseLayerText = falseLayerTextFixture();

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

        const predecessor = predecessorDeep;
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

    it('abstracts a paired eta over one independent sibling layer', () => {
        const {
            emdash,
            A,
            C,
            siblingEta
        } = contextualTransfor;
        let callbacks = 0;
        const abstraction =
            emdash.displayedTransforDependentContextLambda(
                [
                    { name: 'a', family: A },
                    { name: 'c', family: C }
                ],
                ([a, c]) => {
                    callbacks += 1;
                    return point(
                        emdash,
                        siblingEta,
                        emdash.fibrePair(a, c)
                    );
                }
            );
        const compilation = emdash.compile(abstraction);
        const evidence = compilation.abstractions.at(-1);

        assert.equal(callbacks, 1);
        assert.equal(compilation.surfaceType.tag, 'displayed-transfor');
        assert.equal(
            evidence?.rule,
            'categorical.displayed-transfor-dependent-context'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-dependent-context'
        ) {
            assert.fail('Missing contextual telescope evidence');
        }
        assert.deepEqual(evidence.bindingNames, ['a', 'c']);
        assert.deepEqual(evidence.bindingModes, ['natural', 'natural']);
        assert.deepEqual(
            evidence.layers.map(layer => layer.bindingNames),
            [['a', 'c']]
        );
        assert.equal(evidence.contextSize, 3);
        assert.equal(
            evidence.contextRelation,
            'canonical-finite-displayed-telescope'
        );
        assert.equal(Object.isFrozen(evidence), true);
        assert.equal(Object.isFrozen(evidence.layers), true);
        assert.equal(Object.isFrozen(evidence.layers[0]), true);
        assert.equal(Object.isFrozen(evidence.body), true);
    });

    it('uses both variables across one genuine dependency edge and retains actions',
        () => {
        const {
            emdash,
            eta,
            x,
            p,
            u,
            bindings
        } = contextualTransfor;
        const abstraction =
            emdash.displayedTransforDependentContextLambda(
                bindings,
                ([a, b]) => point(
                    emdash,
                    eta,
                    emdash.fibrePair(a, b)
                )
            );
        const compilation = emdash.compile(abstraction);
        const evidence = compilation.abstractions.at(-1);

        assert.equal(compilation.surfaceType.tag, 'displayed-transfor');
        assert.match(
            compilation.explicitCore,
            /displayed-transfor-horizontal-action/u
        );
        assert.match(compilation.explicitCore, /section-pullback/u);
        assert.match(compilation.explicitCore, /displayed-product-pair/u);
        assert.match(compilation.explicitCore, /sigma-category/u);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-transfor-dependent-context'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-dependent-context'
        ) {
            assert.fail('Missing dependent contextual-transfor evidence');
        }
        assert.deepEqual(
            evidence.layers.map(layer => layer.bindingNames),
            [['a'], ['b']]
        );
        assert.equal(
            evidence.bodyRule,
            'categorical.displayed-transfor-context-whiskering'
        );
        assert.equal(evidence.orientation, 'pre');
        assert.equal(
            evidence.dependentPrerequisites.includes(
                'displayed-transfor-horizontal-action'
            ),
            true
        );

        const component = emdash.displayedTransforPoint(
            abstraction,
            x,
            u
        );
        const higher = emdash.displayedTransforNaturality(
            abstraction,
            p,
            u
        );
        assert.equal(emdash.compile(component).surfaceType.tag, 'hom');
        assert.equal(emdash.compile(higher).surfaceType.tag, 'hom');
        assert.match(
            emdash.compile(higher).explicitCore,
            /displayed-transfor-higher-cell/u
        );
    });

    it('shares identity, composition, and both whiskering orientations',
        () => {
        const {
            emdash,
            bindings,
            eta,
            theta,
            postMapper
        } = contextualTransfor;
        let callbacks = 0;
        const contextualPair = (
            a: CoreCategoricalTerm,
            b: CoreCategoricalTerm
        ): CoreCategoricalTerm => emdash.fibrePair(a, b);
        const identity =
            emdash.displayedTransforDependentContextLambda(
                bindings,
                ([a, b]) => {
                    callbacks += 1;
                    return emdash.identityCell(contextualPair(a, b));
                }
            );
        const composition =
            emdash.displayedTransforDependentContextLambda(
                bindings,
                ([a, b]) => {
                    callbacks += 1;
                    const pair = contextualPair(a, b);
                    return emdash.composeCells(
                        point(emdash, theta, pair),
                        point(emdash, eta, pair)
                    );
                }
            );
        const pre = emdash.displayedTransforDependentContextLambda(
            bindings,
            ([a, b]) => {
                callbacks += 1;
                return point(emdash, eta, contextualPair(a, b));
            }
        );
        const post = emdash.displayedTransforDependentContextLambda(
            bindings,
            ([a, b]) => {
                callbacks += 1;
                return point(
                    emdash,
                    postMapper,
                    point(emdash, eta, contextualPair(a, b))
                );
            }
        );

        assert.equal(callbacks, 4);
        const evidenceOf = (term: CoreCategoricalTerm) => {
            const evidence = emdash.inspect(term).abstractions.at(-1);
            if (
                evidence?.rule !==
                    'categorical.displayed-transfor-dependent-context'
            ) {
                assert.fail('Missing contextual telescope evidence');
            }
            return evidence;
        };
        assert.equal(
            evidenceOf(identity).bodyRule,
            'categorical.displayed-transfor-context-identity'
        );
        assert.equal(
            evidenceOf(composition).bodyRule,
            'categorical.displayed-transfor-context-composition'
        );
        assert.equal(evidenceOf(pre).orientation, 'pre');
        assert.equal(evidenceOf(post).orientation, 'post');
        assert.match(
            emdash.compile(composition).explicitCore,
            /generic-category-composition/u
        );
        assert.match(
            emdash.compile(post).explicitCore,
            /displayed-transfor-horizontal-action/u
        );
    });

    it('recurses through four layers using an early accessor and final pair',
        () => {
        const {
            emdash,
            sigmaD,
            liftedA,
            Q,
            bindings
        } = mixedDeep;
        const endpointFamily = emdash.displayedProduct(liftedA, Q);
        const target = emdash.displayedFamily(
            'generic_deep_nd_target',
            sigmaD
        );
        const sourceEndpoint = emdash.displayedFunctor(
            'generic_deep_nd_source',
            endpointFamily,
            target
        );
        const targetEndpoint = emdash.displayedFunctor(
            'generic_deep_nd_target_functor',
            endpointFamily,
            target
        );
        const eta = emdash.displayedTransfor(
            'generic_deep_nd_eta',
            sourceEndpoint,
            targetEndpoint
        );
        let callbacks = 0;
        const abstraction =
            emdash.displayedTransforDependentContextLambda(
                bindings,
                ([a, , , , e, f]) => {
                    callbacks += 1;
                    return point(
                        emdash,
                        eta,
                        emdash.fibrePair(
                            a,
                            emdash.fibrePair(e, f)
                        )
                    );
                }
            );
        const inspection = emdash.inspect(abstraction);
        const evidence = inspection.abstractions.at(-1);

        assert.equal(callbacks, 1);
        assert.equal(inspection.type.tag, 'displayed-transfor');
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-dependent-context'
        ) {
            assert.fail('Missing deep contextual telescope evidence');
        }
        assert.deepEqual(
            evidence.layers.map(layer => layer.bindingNames),
            [['a'], ['b', 'c'], ['d'], ['e', 'f']]
        );
        assert.equal(evidence.contextSize, 7);
        assert.equal(evidence.orientation, 'pre');
        assert.equal(Object.isFrozen(evidence.layers[3]), true);
    });

    it('preserves compact unary nd and the displayed-functor telescope',
        () => {
        const {
            emdash,
            dependentProduct,
            F,
            G,
            eta
        } = contextualTransfor;
        const compact = emdash.displayedTransforContextLambda(
            'generic_nd_compact',
            F,
            G,
            a => point(emdash, eta, a)
        );
        assert.equal(emdash.compare(compact, eta).status, 'equal');
        assert.equal(
            emdash.inspect(compact).abstractions.at(-1)?.rule,
            'categorical.displayed-transfor-context-eta'
        );
        const identityFunctor = emdash.displayedFunctorLambda(
            'generic_nd_compact_identity',
            dependentProduct,
            dependentProduct,
            a => a
        );
        assert.equal(
            emdash.compile(identityFunctor).surfaceType.tag,
            'displayed-functor'
        );
    });

    it('fails closed across the dependent-context negative matrix', () => {
        const {
            emdash,
            A,
            B,
            sigmaA,
            eta,
            p,
            bindings
        } = contextualTransfor;
        assert.throws(
            () => emdash.displayedTransforDependentContextLambda(
                [
                    { name: 'a', family: A },
                    { name: 'a', family: B }
                ],
                () => p
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'INVALID_DISPLAYED_CONTEXT'
        );
        assert.throws(
            () => emdash.displayedTransforDependentContextLambda(
                [{ name: 'a', family: A }],
                () => p
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'INVALID_DISPLAYED_CONTEXT'
        );

        const wrongBase = emdash.category('generic_nd_wrong_base');
        const wrongLayer = emdash.displayedFamily(
            'generic_nd_wrong_layer',
            wrongBase
        );
        assert.throws(
            () => emdash.displayedTransforDependentContextLambda(
                [
                    { name: 'a', family: A },
                    { name: 'wrong', family: wrongLayer }
                ],
                () => p
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );

        for (const [options, code] of [
            [
                { variation: 'functorial' as const },
                'CLASSIFIER_ARGUMENT_MISMATCH'
            ],
            [
                { dependency: 'ordinary' as const },
                'CLASSIFIER_ARGUMENT_MISMATCH'
            ],
            [
                { polarity: 'contravariant' as const },
                'POLARITY_MISMATCH'
            ],
            [
                { cellLevel: 'arrow' as const },
                'CLASSIFIER_ARGUMENT_MISMATCH'
            ]
        ] as const) {
            assert.throws(
                () => emdash.displayedTransforDependentContextLambda(
                    bindings,
                    () => p,
                    options
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === code
            );
        }

        const Wrong = emdash.displayedFamily('generic_nd_Wrong', sigmaA);
        const WrongTarget = emdash.displayedFamily(
            'generic_nd_WrongTarget',
            sigmaA
        );
        const wrongF = emdash.displayedFunctor(
            'generic_nd_wrong_F',
            Wrong,
            WrongTarget
        );
        const wrongG = emdash.displayedFunctor(
            'generic_nd_wrong_G',
            Wrong,
            WrongTarget
        );
        const wrongEta = emdash.displayedTransfor(
            'generic_nd_wrong_eta',
            wrongF,
            wrongG
        );
        assert.throws(
            () => emdash.displayedTransforDependentContextLambda(
                bindings,
                ([a]) => point(emdash, wrongEta, a)
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.throws(
            () => emdash.displayedTransforDependentContextLambda(
                bindings,
                () => p
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );

        const foreign = new CoreCategoricalProgram();
        const foreignK = foreign.category('generic_nd_foreign_K');
        const foreignTerm = foreign.object(
            'generic_nd_foreign_x',
            foreignK
        );
        assert.throws(
            () => emdash.displayedTransforDependentContextLambda(
                bindings,
                () => foreignTerm
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'FOREIGN_TERM'
        );

        let escaped: CoreCategoricalTerm | undefined;
        emdash.displayedTransforDependentContextLambda(
            bindings,
            ([a, b]) => {
                escaped = a;
                return point(emdash, eta, emdash.fibrePair(a, b));
            }
        );
        assert.throws(
            () => emdash.identityCell(escaped as CoreCategoricalTerm),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'ESCAPED_SLOT'
        );
        assert.throws(
            () => predecessorProgram
                .displayedTransforDependentContextLambda(
                    predecessorDeep.bindings,
                    () => p
                ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_MIXED_MODE'
        );

        const recovered =
            emdash.displayedTransforDependentContextLambda(
                bindings,
                ([a, b]) => point(
                    emdash,
                    eta,
                    emdash.fibrePair(a, b)
                )
            );
        assert.equal(emdash.compile(recovered).surfaceType.tag,
            'displayed-transfor');
    });

    it('parses grouped nd text with sibling and dependent direct parity',
        () => {
        const {
            emdash,
            A,
            B,
            C,
            siblingEta,
            eta,
            bindings
        } = contextualTransfor;
        const siblingGroups = Object.freeze([
            Object.freeze([A, C])
        ]);
        const siblingEnvironment = contextualNdEnvironment([
            termBinding('siblingEta', siblingEta)
        ]);
        const siblingParsed = elaborateCoreCategoricalText(
            emdash,
            {
                source:
                    'λ^nd (a : A, c : C). ' +
                    'siblingEta (fibrePair a c)',
                sourceFile: textSourceFile,
                environment: siblingEnvironment,
                expected: contextualNdExpected(siblingGroups)
            }
        );
        const siblingDirect =
            emdash.displayedTransforDependentContextLambda(
                [
                    { name: 'a', family: A },
                    { name: 'c', family: C }
                ],
                ([a, c]) => point(
                    emdash,
                    siblingEta,
                    emdash.fibrePair(a, c)
                )
            );

        const dependentGroups = Object.freeze([
            Object.freeze([A]),
            Object.freeze([B])
        ]);
        const dependentEnvironment = contextualNdEnvironment([
            termBinding('eta', eta)
        ]);
        const annotated = elaborateCoreCategoricalText(
            emdash,
            {
                source:
                    'λ^nd (a : A; b : B). ' +
                    'eta (fibrePair a b)',
                sourceFile: textSourceFile,
                environment: dependentEnvironment,
                expected: contextualNdExpected(dependentGroups)
            }
        );
        const omitted = elaborateCoreCategoricalText(
            emdash,
            {
                source: 'λ^nd (a; b). eta (fibrePair a b)',
                sourceFile: textSourceFile,
                environment: dependentEnvironment,
                expected: contextualNdExpected(dependentGroups)
            }
        );
        const dependentDirect =
            emdash.displayedTransforDependentContextLambda(
                bindings,
                ([a, b]) => point(
                    emdash,
                    eta,
                    emdash.fibrePair(a, b)
                )
            );
        const compareDirectText = (
            parsed: CoreCategoricalTerm,
            direct: CoreCategoricalTerm
        ) => {
            const parsedCompilation = emdash.compile(parsed);
            const directCompilation = emdash.compile(direct);
            assert.equal(
                parsedCompilation.explicitCore,
                directCompilation.explicitCore
            );
            assert.equal(
                parsedCompilation.explicitInferredType,
                directCompilation.explicitInferredType
            );
        };

        compareDirectText(siblingParsed, siblingDirect);
        compareDirectText(annotated, dependentDirect);
        compareDirectText(omitted, dependentDirect);
        const evidence = emdash.inspect(annotated).abstractions.at(-1);
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-dependent-context'
        ) {
            assert.fail('Missing parsed contextual telescope evidence');
        }
        assert.deepEqual(
            evidence.layers.map(layer => layer.bindingNames),
            [['a'], ['b']]
        );
        assert.equal(Object.isFrozen(evidence), true);
        assert.equal(Object.isFrozen(evidence.layers), true);
        assert.equal(Object.isFrozen(evidence.layers[1]), true);
        assert.equal(Object.isFrozen(evidence.body), true);
    });

    it('parses grouped nd text recursive cells and both whiskerings', () => {
        const {
            emdash,
            A,
            B,
            eta,
            theta,
            postMapper,
            bindings
        } = contextualTransfor;
        const expected = contextualNdExpected([
            [A],
            [B]
        ]);
        const environment = contextualNdEnvironment([
            termBinding('eta', eta),
            termBinding('theta', theta),
            termBinding('postMapper', postMapper)
        ]);
        const parse = (body: string) => elaborateCoreCategoricalText(
            emdash,
            {
                source: `λ^nd (a; b). ${body}`,
                sourceFile: textSourceFile,
                environment,
                expected
            }
        );
        const parsed = [
            parse('identityCell (fibrePair a b)'),
            parse(
                'composeCells (theta (fibrePair a b)) ' +
                    '(eta (fibrePair a b))'
            ),
            parse('eta (fibrePair a b)'),
            parse('postMapper (eta (fibrePair a b))')
        ];
        const pair = (
            a: CoreCategoricalTerm,
            b: CoreCategoricalTerm
        ) => emdash.fibrePair(a, b);
        const direct = [
            emdash.displayedTransforDependentContextLambda(
                bindings,
                ([a, b]) => emdash.identityCell(pair(a, b))
            ),
            emdash.displayedTransforDependentContextLambda(
                bindings,
                ([a, b]) => emdash.composeCells(
                    point(emdash, theta, pair(a, b)),
                    point(emdash, eta, pair(a, b))
                )
            ),
            emdash.displayedTransforDependentContextLambda(
                bindings,
                ([a, b]) => point(emdash, eta, pair(a, b))
            ),
            emdash.displayedTransforDependentContextLambda(
                bindings,
                ([a, b]) => point(
                    emdash,
                    postMapper,
                    point(emdash, eta, pair(a, b))
                )
            )
        ];

        parsed.forEach((term, index) => {
            assert.equal(
                emdash.compile(term).explicitCore,
                emdash.compile(direct[index]).explicitCore
            );
        });
        const evidence = parsed.map(term => {
            const value = emdash.inspect(term).abstractions.at(-1);
            if (
                value?.rule !==
                    'categorical.displayed-transfor-dependent-context'
            ) {
                assert.fail('Missing parsed contextual telescope evidence');
            }
            return value;
        });
        assert.equal(
            evidence[0]?.bodyRule,
            'categorical.displayed-transfor-context-identity'
        );
        assert.equal(
            evidence[1]?.bodyRule,
            'categorical.displayed-transfor-context-composition'
        );
        assert.equal(evidence[2]?.orientation, 'pre');
        assert.equal(evidence[3]?.orientation, 'post');
    });

    it('parses grouped nd text through four canonical layers', () => {
        const data = mixedDeep;
        const endpointFamily = data.emdash.displayedProduct(
            data.liftedA,
            data.Q
        );
        const target = data.emdash.displayedFamily(
            'generic_text_deep_nd_target',
            data.sigmaD
        );
        const sourceEndpoint = data.emdash.displayedFunctor(
            'generic_text_deep_nd_source',
            endpointFamily,
            target
        );
        const targetEndpoint = data.emdash.displayedFunctor(
            'generic_text_deep_nd_target_functor',
            endpointFamily,
            target
        );
        const eta = data.emdash.displayedTransfor(
            'generic_text_deep_nd_eta',
            sourceEndpoint,
            targetEndpoint
        );
        const parsed = elaborateDeepText(
            data,
            'λ^nd (a : A; b : B, c : C; d : D; ' +
                'e : E, f : F). ' +
                'deepEta (fibrePair a (fibrePair e f))',
            contextualNdExpected([
                [data.A],
                [data.B, data.C],
                [data.D],
                [data.E, data.F]
            ]),
            deepTextEnvironment(data, [termBinding('deepEta', eta)])
        );
        const inspection = data.emdash.inspect(parsed);
        const evidence = inspection.abstractions.at(-1);

        assert.equal(inspection.type.tag, 'displayed-transfor');
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-dependent-context'
        ) {
            assert.fail('Missing deep parsed contextual evidence');
        }
        assert.deepEqual(
            evidence.layers.map(layer => layer.bindingNames),
            [['a'], ['b', 'c'], ['d'], ['e', 'f']]
        );
        assert.equal(evidence.contextSize, 7);
        assert.equal(Object.isFrozen(evidence.layers[3]), true);
    });

    it('fails closed for invalid grouped nd text contracts and bodies',
        () => {
        const {
            emdash,
            A,
            B,
            C,
            D,
            p
        } = contextualTransfor;
        const expected = contextualNdExpected([[A], [B]]);
        const environment = contextualNdEnvironment([
            termBinding('p', p)
        ]);
        const reject = (
            source: string,
            requested: CoreCategoricalTextTermExpected,
            code: CoreCategoricalTextErrorCode,
            bindings = environment,
            program = emdash
        ) => captureTextError(
            () => elaborateCoreCategoricalText(
                program,
                {
                    source,
                    sourceFile: textSourceFile,
                    environment: bindings,
                    expected: requested
                }
            ),
            code
        );

        reject(
            'λ^nd (a; b). identityCell (fibrePair a b)',
            {
                kind: 'displayed-dependent-context-functor',
                sourceGroups: [[A], [B]],
                target: D
            },
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        reject(
            'λ^nd (a; b). identityCell (fibrePair a b)',
            contextualNdExpected([[A, B]]),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        reject(
            'λ^nd (a : C; b : B). ' +
                'identityCell (fibrePair a b)',
            expected,
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        reject(
            'λ^n (a; b). identityCell (fibrePair a b)',
            expected,
            'UNSUPPORTED_BINDER_MODE'
        );
        reject(
            'λ^nd (a; b). p',
            expected,
            'CATEGORICAL_REJECTION'
        );

        const predecessorExpected = contextualNdExpected([
            [predecessorDeep.A],
            [predecessorDeep.B]
        ]);
        reject(
            'λ^nd (a; b). identityCell (fibrePair a b)',
            predecessorExpected,
            'CATEGORICAL_REJECTION',
            deepTextEnvironment(predecessorDeep),
            predecessorProgram
        );
    });

    it('parses deep nested mixed eta and reaches the homd_int consumer',
    () => {
        const data = mixedDeep;
        const Z = data.emdash.category('generic_text_Z');
        const classifier = data.emdash.constantDisplayedFamily(
            data.sigmaD,
            data.emdash.displayedCategoryCategory(Z)
        );
        const Ebar = data.emdash.section(
            'generic_text_Ebar',
            data.emdash.oppositeDisplayedFamily(classifier)
        );
        const Dbar = data.emdash.section(
            'generic_text_Dbar',
            classifier
        );
        const H = data.emdash.mixedDisplayedHomFamily(
            classifier,
            Ebar,
            Dbar
        );
        const nested = data.emdash.displayedFunctor(
            'generic_text_nested',
            data.Q,
            H
        );
        const source =
            'λ^fd (a : A; b : B, c : C; d : D; ' +
            'e : E, f : F). λ^fd z. ' +
            'nested (fibrePair e f) z';
        const parsed = elaborateDeepText(
            data,
            source,
            deepTextExpected(
                data,
                H,
                { kind: 'mixed-nested-displayed-eta' }
            ),
            deepTextEnvironment(data, [
                termBinding('nested', nested)
            ])
        );
        const direct = data.emdash.displayedDependentContextLambda(
            data.bindings,
            H,
            ([, , , , e, f]) => {
                const inner = data.emdash.apply(
                    nested,
                    data.emdash.fibrePair(e, f)
                );
                return data.emdash.nestedDisplayedFunctorLambda(
                    'z',
                    inner,
                    z => data.emdash.apply(inner, z)
                );
            }
        );
        const parsedCompilation = data.emdash.compile(parsed);
        const directCompilation = data.emdash.compile(direct);
        assert.equal(
            parsedCompilation.explicitCore,
            directCompilation.explicitCore
        );
        assert.equal(
            parsedCompilation.explicitInferredType,
            directCompilation.explicitInferredType
        );
        assert.deepEqual(
            parsedCompilation.abstractions.map(evidence => evidence.rule),
            directCompilation.abstractions.map(evidence => evidence.rule)
        );
        assert.equal(
            parsedCompilation.abstractions.some(evidence =>
                evidence.rule ===
                    'categorical.mixed-nested-displayed-eta'
            ),
            true
        );
        const genericEvidence = parsedCompilation.abstractions.at(-1);
        if (
            genericEvidence?.rule !==
                'categorical.displayed-generic-dependent-context-bracket'
        ) {
            assert.fail('Missing parsed generic telescope evidence');
        }
        assert.deepEqual(
            genericEvidence.layers.map(layer => layer.bindingNames),
            [['a'], ['b', 'c'], ['d'], ['e', 'f']]
        );
        assert.equal(
            CORE_CATEGORICAL_TEXT_REVISION,
            'CONTEXTUAL-ND-TELESCOPE-TEXT-PARITY-1AN-CATEGORICAL-TEXT-1'
        );

        const x = data.emdash.object(
            'generic_text_x',
            data.sigmaD
        );
        const y = data.emdash.object(
            'generic_text_y',
            data.sigmaD
        );
        const p = data.emdash.hom(
            'generic_text_p',
            data.sigmaD,
            x,
            y
        );
        const q = data.emdash.object(
            'generic_text_q',
            data.emdash.fibre(data.Q, x)
        );
        const moved = data.emdash.apply(parsed, p, {
            expectedShape: 'transport-functor'
        });
        const inner = data.emdash.apply(moved, q);
        const internalHom = data.emdash.compile(
            data.emdash.displayedInternalHom(inner)
        );
        assert.match(internalHom.explicitCore, /homd_int/u);
        assert.match(
            internalHom.explicitCore,
            /displayed-functor-transport/u
        );
    });

    it('rejects false layer punctuation and unqualified nested forms',
    () => {
        const layers = falseLayerText;
        const mismatch = captureTextError(
            () => elaborateCoreCategoricalText(
                layers.emdash,
                {
                    source: 'λ^fd (l; r; d). d',
                    sourceFile: textSourceFile,
                    environment: layers.environment,
                    expected: layers.falseExpected
                }
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        assert.match(
            mismatch.detail,
            /canonical sibling\/dependency layers/u
        );

        const data = shallowNestedText;
        const source =
            'λ^fd (a; b). λ^fd z. nested b z';
        captureTextError(
            () => elaborateCoreCategoricalText(
                data.emdash,
                {
                    source,
                    sourceFile: textSourceFile,
                    environment: data.environment,
                    expected: {
                        kind:
                            'displayed-dependent-context-functor',
                        sourceGroups: [[data.A], [data.B]],
                        target: data.H
                    }
                }
            ),
            'UNSUPPORTED_NESTED_ABSTRACTION'
        );
        captureTextError(
            () => elaborateCoreCategoricalText(
                data.emdash,
                {
                    source:
                        'λ^fd (a; b). nested b',
                    sourceFile: textSourceFile,
                    environment: data.environment,
                    expected: data.expected
                }
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        captureTextError(
            () => elaborateCoreCategoricalText(
                data.emdash,
                {
                    source:
                        source.replace('λ^fd z.', 'λ^fd b.'),
                    sourceFile: textSourceFile,
                    environment: data.environment,
                    expected: data.expected
                }
            ),
            'DUPLICATE_BINDING'
        );
        captureTextError(
            () => elaborateCoreCategoricalText(
                data.emdash,
                {
                    source: source.replace('λ^fd z.', 'λ^n z.'),
                    sourceFile: textSourceFile,
                    environment: data.environment,
                    expected: data.expected
                }
            ),
            'UNSUPPORTED_BINDER_MODE'
        );
        captureTextError(
            () => elaborateCoreCategoricalText(
                data.emdash,
                {
                    source: source.replace('nested b z', 'nested b b'),
                    sourceFile: textSourceFile,
                    environment: data.environment,
                    expected: data.expected
                }
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        captureTextError(
            () => elaborateCoreCategoricalText(
                data.emdash,
                {
                    source:
                        source.replace('λ^fd z.', 'λ^fd z : B.'),
                    sourceFile: textSourceFile,
                    environment: data.environment,
                    expected: data.expected
                }
            ),
            'INCOMPATIBLE_ABSTRACTION_EXPECTATION'
        );
        captureTextError(
            () => elaborateCoreCategoricalText(
                data.emdash,
                {
                    source: source.replace('nested b z', 'nested z'),
                    sourceFile: textSourceFile,
                    environment: data.environment,
                    expected: data.expected
                }
            ),
            'CATEGORICAL_REJECTION'
        );
        captureTextError(
            () => elaborateDeepText(
                predecessorDeep,
                'λ^fd (a; b, c; d; e, f). fibrePair e f',
                deepTextExpected(predecessorDeep, predecessorDeep.Q)
            ),
            'CATEGORICAL_REJECTION'
        );
    });
});
