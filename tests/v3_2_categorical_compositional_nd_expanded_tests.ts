/**
 * D-DTTLF-USABILITY-077 expanded `lambda^n k. lambda^n a` parity.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreCategoricalSlotToken,
    CoreCategoricalTerm
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

const point = (
    emdash: CoreCategoricalProgram,
    transformation: CoreCategoricalTerm,
    argument: CoreCategoricalTerm
): CoreCategoricalTerm => emdash.apply(
    transformation,
    argument,
    { expectedShape: 'point-component' }
);

const map = (
    emdash: CoreCategoricalProgram,
    functor: CoreCategoricalTerm,
    argument: CoreCategoricalTerm,
    expectedShape: 'object-value' | 'arrow-value' = 'object-value'
): CoreCategoricalTerm => emdash.apply(
    functor,
    argument,
    { expectedShape }
);

const fibreFunctor = (
    emdash: CoreCategoricalProgram,
    functor: CoreCategoricalTerm,
    base: CoreCategoricalTerm
): CoreCategoricalTerm => emdash.apply(
    functor,
    base,
    { expectedShape: 'fibre-functor' }
);

const expandedNatural = (
    emdash: CoreCategoricalProgram,
    name: string,
    source: CoreCategoricalTerm,
    target: CoreCategoricalTerm,
    body: (
        base: CoreCategoricalSlotToken,
        fibre: CoreCategoricalSlotToken
    ) => CoreCategoricalTerm
): CoreCategoricalTerm => emdash.transforLambda(
    `${name}Base`,
    source,
    target,
    base => emdash.transforLambda(
        name,
        fibreFunctor(emdash, source, base),
        fibreFunctor(emdash, target, base),
        fibre => body(base, fibre)
    )
);

const mappedDisplayedFunctor = (
    emdash: CoreCategoricalProgram,
    name: string,
    source: Parameters<
        CoreCategoricalProgram['displayedFunctorLambda']
    >[1],
    target: Parameters<
        CoreCategoricalProgram['displayedFunctorLambda']
    >[2],
    chain: readonly CoreCategoricalTerm[]
): CoreCategoricalTerm => emdash.displayedFunctorLambda(
    name,
    source,
    target,
    a => chain.reduce(
        (current, functor) => map(emdash, functor, current),
        a as CoreCategoricalTerm
    )
);

const buildFixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/categorical-compositional-nd-expanded.ts',
        profile: 'compositional-natural-binder-1'
    });
    const K = emdash.category('expanded_nd_K');
    const C = emdash.displayedFamily('expanded_nd_C', K);
    const E = emdash.displayedFamily('expanded_nd_E', K);
    const D = emdash.displayedFamily('expanded_nd_D', K);
    const Q = emdash.displayedFamily('expanded_nd_Q', K);
    const L = emdash.displayedFunctor('expanded_nd_L', C, E);
    const F = emdash.displayedFunctor('expanded_nd_F', E, D);
    const G = emdash.displayedFunctor('expanded_nd_G', E, D);
    const H = emdash.displayedFunctor('expanded_nd_H', E, D);
    const M = emdash.displayedFunctor('expanded_nd_M', D, Q);
    const eta = emdash.displayedTransfor('expanded_nd_eta', F, G);
    const theta = emdash.displayedTransfor('expanded_nd_theta', G, H);
    const x = emdash.object('expanded_nd_x', K);
    const y = emdash.object('expanded_nd_y', K);
    const p = emdash.hom('expanded_nd_p', K, x, y);
    const u = emdash.object('expanded_nd_u', emdash.fibre(E, x));
    return {
        emdash,
        K,
        C,
        E,
        D,
        Q,
        L,
        F,
        G,
        H,
        M,
        eta,
        theta,
        x,
        y,
        p,
        u
    };
};

let sharedFixture: ReturnType<typeof buildFixture> | undefined;
const fixture = (): ReturnType<typeof buildFixture> => {
    sharedFixture ??= buildFixture();
    return sharedFixture;
};

describe('COMPOSITIONAL-ND-EXPANDED-1D', () => {
    it('shares eta Core while retaining the ordinary iterated-Hom facade',
        () => {
        const { emdash, F, G, eta } = fixture();
        let outerCallbacks = 0;
        let innerCallbacks = 0;
        let capturedBase: CoreCategoricalSlotToken | undefined;
        let capturedEndpoint: CoreCategoricalTerm | undefined;
        const expanded = emdash.transforLambda(
            'kEta',
            F,
            G,
            k => {
                outerCallbacks += 1;
                capturedBase = k;
                const Fk = fibreFunctor(emdash, F, k);
                const Gk = fibreFunctor(emdash, G, k);
                capturedEndpoint = Fk;
                return emdash.transforLambda(
                    'aEta',
                    Fk,
                    Gk,
                    a => {
                        innerCallbacks += 1;
                        return point(emdash, eta, a);
                    }
                );
            }
        );
        const compact = emdash.displayedTransforContextLambda(
            'aEtaCompact',
            F,
            G,
            a => point(emdash, eta, a)
        );
        const expandedCompilation = emdash.compile(expanded);
        const compactCompilation = emdash.compile(compact);
        const inspection = emdash.inspect(expanded);

        assert.equal(outerCallbacks, 1);
        assert.equal(innerCallbacks, 1);
        assert.equal(expandedCompilation.surfaceType.tag, 'hom');
        assert.equal(
            compactCompilation.surfaceType.tag,
            'displayed-transfor'
        );
        assert.equal(
            expandedCompilation.explicitCore,
            compactCompilation.explicitCore
        );
        assert.match(
            expandedCompilation.explicitExpectedType,
            /hom-classifier/u
        );
        assert.equal(
            inspection.abstractions.at(-1)?.rule,
            'categorical.ordinary-transfor-contextual-transfor'
        );
        assert.equal(
            inspection.abstractions.some(evidence =>
                evidence.rule ===
                    'categorical.displayed-transfor-context-eta'
            ),
            true
        );
        assertDeepFrozen(inspection);
        assert.ok(capturedBase);
        assert.ok(capturedEndpoint);
        assert.throws(
            () => fibreFunctor(emdash, F, capturedBase),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'ESCAPED_SLOT'
        );
        assert.throws(
            () => emdash.inspect(capturedEndpoint),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'ESCAPED_SLOT'
        );
    });

    it('shares identity, composition, and both whiskering orientations',
        () => {
        const {
            emdash,
            C,
            E,
            D,
            Q,
            L,
            F,
            G,
            H,
            M,
            eta,
            theta
        } = fixture();
        const identityExpanded = expandedNatural(
            emdash,
            'identity',
            F,
            F,
            (_k, a) => emdash.identityCell(map(emdash, F, a))
        );
        const identityCompact = emdash.displayedTransforContextLambda(
            'identityCompact',
            F,
            F,
            a => emdash.identityCell(map(emdash, F, a))
        );
        const compositionExpanded = expandedNatural(
            emdash,
            'composition',
            F,
            H,
            (_k, a) => emdash.composeCells(
                point(emdash, theta, a),
                point(emdash, eta, a)
            )
        );
        const compositionCompact =
            emdash.displayedTransforContextLambda(
                'compositionCompact',
                F,
                H,
                a => emdash.composeCells(
                    point(emdash, theta, a),
                    point(emdash, eta, a)
                )
            );
        const postSource = mappedDisplayedFunctor(
            emdash,
            'expanded_nd_MF',
            E,
            Q,
            [F, M]
        );
        const postTarget = mappedDisplayedFunctor(
            emdash,
            'expanded_nd_MG',
            E,
            Q,
            [G, M]
        );
        const preSource = mappedDisplayedFunctor(
            emdash,
            'expanded_nd_FL',
            C,
            D,
            [L, F]
        );
        const preTarget = mappedDisplayedFunctor(
            emdash,
            'expanded_nd_GL',
            C,
            D,
            [L, G]
        );
        const postExpanded = expandedNatural(
            emdash,
            'post',
            postSource,
            postTarget,
            (_k, a) => point(emdash, M, point(emdash, eta, a))
        );
        const postCompact = emdash.displayedTransforContextLambda(
            'postCompact',
            postSource,
            postTarget,
            a => point(emdash, M, point(emdash, eta, a))
        );
        const preExpanded = expandedNatural(
            emdash,
            'pre',
            preSource,
            preTarget,
            (_k, a) => point(emdash, eta, map(emdash, L, a))
        );
        const preCompact = emdash.displayedTransforContextLambda(
            'preCompact',
            preSource,
            preTarget,
            a => point(emdash, eta, map(emdash, L, a))
        );

        for (const [expanded, compact] of [
            [identityExpanded, identityCompact],
            [compositionExpanded, compositionCompact],
            [postExpanded, postCompact],
            [preExpanded, preCompact]
        ] as const) {
            assert.equal(
                emdash.compile(expanded).explicitCore,
                emdash.compile(compact).explicitCore
            );
            assert.equal(
                emdash.compare(expanded, compact, 20_000).status,
                'equal'
            );
        }
        assert.match(
            emdash.compile(compositionExpanded).explicitCore,
            /generic-category-composition/u
        );
        assert.match(
            emdash.compile(postExpanded).explicitCore,
            /displayed-transfor-horizontal-action/u
        );
        assert.match(
            emdash.compile(preExpanded).explicitCore,
            /displayed-transfor-horizontal-action/u
        );
    });

    it('retains component, point, and internal base-arrow action', () => {
        const { emdash, F, G, eta, x, p, u } = fixture();
        const expanded = expandedNatural(
            emdash,
            'action',
            F,
            G,
            (_k, a) => point(emdash, eta, a)
        );
        const compact = emdash.displayedTransforContextLambda(
            'actionCompact',
            F,
            G,
            a => point(emdash, eta, a)
        );
        const expandedComponent = emdash.displayedTransforComponent(
            expanded,
            x
        );
        const compactComponent = emdash.displayedTransforComponent(
            compact,
            x
        );
        const expandedPoint = emdash.displayedTransforPoint(
            expanded,
            x,
            u
        );
        const compactPoint = emdash.displayedTransforPoint(
            compact,
            x,
            u
        );
        const expandedHigher = emdash.displayedTransforNaturality(
            expanded,
            p,
            u
        );
        const compactHigher = emdash.displayedTransforNaturality(
            compact,
            p,
            u
        );

        assert.equal(
            emdash.compare(
                expandedComponent,
                compactComponent,
                20_000
            ).status,
            'equal'
        );
        assert.equal(
            emdash.compare(expandedPoint, compactPoint, 20_000).status,
            'equal'
        );
        assert.equal(
            emdash.compare(expandedHigher, compactHigher, 20_000).status,
            'equal'
        );
        assert.equal(emdash.compile(expandedComponent).surfaceType.tag,
            'transfor');
        assert.equal(emdash.compile(expandedPoint).surfaceType.tag, 'hom');
        assert.equal(emdash.compile(expandedHigher).surfaceType.tag, 'hom');
        assert.match(
            emdash.compile(expandedHigher).explicitCore,
            /displayed-transfor-higher-cell/u
        );
    });

    it('fails closed on missing nesting, endpoint mismatch, and bad bodies',
        () => {
        const { emdash, K, E, F, G, eta } = fixture();
        const Wrong = emdash.displayedFamily('expanded_nd_Wrong', K);
        const WrongFunctor = emdash.displayedFunctor(
            'expanded_nd_WrongFunctor',
            E,
            Wrong
        );
        assert.throws(
            () => emdash.transforLambda(
                'wrongOuter',
                F,
                WrongFunctor,
                _k => {
                    throw new Error('unreachable');
                }
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.throws(
            () => emdash.transforLambda(
                'missingInner',
                F,
                G,
                k => emdash.apply(eta, k, {
                    expectedShape: 'displayed-component'
                })
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'MISSING_STRUCTURAL_OWNER'
        );
        assert.throws(
            () => emdash.transforLambda(
                'wrongInner',
                F,
                G,
                k => emdash.transforLambda(
                    'aWrongInner',
                    fibreFunctor(emdash, F, k),
                    fibreFunctor(emdash, F, k),
                    a => emdash.identityCell(map(emdash, F, a))
                )
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.throws(
            () => expandedNatural(
                emdash,
                'badBody',
                F,
                G,
                (_k, a) => a
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );
        assert.throws(
            () => emdash.transforLambda(
                'indexedOutside',
                F,
                G,
                k => {
                    const Fk = fibreFunctor(emdash, F, k);
                    const Gk = fibreFunctor(emdash, G, k);
                    return emdash.transforLambda(
                        'aIndexedOutside',
                        Fk,
                        Gk,
                        a => point(emdash, eta, a),
                        { dependency: 'displayed' }
                    );
                }
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
    });

    it('preserves root ordinary, first-hom, and compact displayed binders',
        () => {
        const { emdash, E, D, F, G, eta } = fixture();
        const A = emdash.category('expanded_nd_A');
        const B = emdash.category('expanded_nd_B');
        const U = emdash.functor('expanded_nd_U', A, B);
        const V = emdash.functor('expanded_nd_V', A, B);
        const alpha = emdash.transfor('expanded_nd_alpha', U, V);
        const root = emdash.transforLambda(
            'rootStillWorks',
            U,
            V,
            a => point(emdash, alpha, a)
        );
        const firstHom = emdash.transforLambda(
            'firstHomStillWorks',
            E,
            D,
            k => emdash.lambda(
                'firstHomA',
                emdash.fibre(E, k),
                emdash.fibre(D, k),
                a => map(emdash, F, a)
            )
        );
        const compact = emdash.displayedTransforContextLambda(
            'compactStillWorks',
            F,
            G,
            a => point(emdash, eta, a)
        );

        assert.equal(
            emdash.compile(root).explicitCore,
            emdash.compile(alpha).explicitCore
        );
        assert.equal(emdash.compile(firstHom).surfaceType.tag, 'transfor');
        assert.equal(
            emdash.compile(compact).surfaceType.tag,
            'displayed-transfor'
        );
    });
});
