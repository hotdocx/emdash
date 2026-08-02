/**
 * D-DTTLF-USABILITY-074 compositional ordinary-natural binder coverage.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalSlotToken,
    CoreCategoricalTerm,
    CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_BOUNDARY,
    coreCategoricalCompositionalNaturalCoreName,
    coreCategoricalFibredTransfdCoreName
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

const buildFixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/categorical-compositional-natural-binder.ts',
        profile: 'compositional-natural-binder-1'
    });
    const A = emdash.category('natural_binder_A');
    const B = emdash.category('natural_binder_B');
    const C = emdash.category('natural_binder_C');
    const X = emdash.category('natural_binder_X');
    const F = emdash.functor('natural_binder_F', A, B);
    const G = emdash.functor('natural_binder_G', A, B);
    const H = emdash.functor('natural_binder_H', A, B);
    const L = emdash.functor('natural_binder_L', X, A);
    const M = emdash.functor('natural_binder_M', B, C);
    const eta = emdash.transfor('natural_binder_eta', F, G);
    const theta = emdash.transfor('natural_binder_theta', G, H);
    const FL = emdash.composeFunctors(F, L);
    const GL = emdash.composeFunctors(G, L);
    const MF = emdash.composeFunctors(M, F);
    const MG = emdash.composeFunctors(M, G);
    return {
        emdash,
        A,
        B,
        C,
        X,
        F,
        G,
        H,
        L,
        M,
        eta,
        theta,
        FL,
        GL,
        MF,
        MG
    };
};

let sharedFixture: ReturnType<typeof buildFixture> | undefined;
const fixture = (): ReturnType<typeof buildFixture> => {
    sharedFixture ??= buildFixture();
    return sharedFixture;
};

describe('COMPOSITIONAL-NATURAL-BINDER-1B', () => {
    it('imports exactly the two existing classifier-exact actions', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_BOUNDARY.declarationNames,
            [
                'comp_cat_con_fapp1_func',
                'comp_cat_cov_fapp1_func'
            ]
        );
        assert.equal(
            CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_BOUNDARY
                .runtimeRuleCount,
            0
        );
        assert.equal(
            CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_BOUNDARY
                .activeKernelOwnerDelta,
            0
        );
    });

    it('recovers eta exactly after one callback', () => {
        const { emdash, F, G, eta } = fixture();
        let callbacks = 0;
        let captured: CoreCategoricalSlotToken | undefined;
        const abstraction = emdash.transforLambda(
            'a',
            F,
            G,
            a => {
                callbacks += 1;
                captured = a;
                return point(emdash, eta, a);
            }
        );
        const compiled = emdash.compile(abstraction);
        const etaCompiled = emdash.compile(eta);
        const evidence = emdash.inspect(abstraction).abstractions.at(-1);

        assert.equal(callbacks, 1);
        assert.equal(compiled.explicitCore, etaCompiled.explicitCore);
        assert.equal(
            compiled.explicitInferredType,
            compiled.explicitExpectedType
        );
        assert.equal(
            evidence?.rule,
            'categorical.ordinary-transfor-eta'
        );
        assert.equal(evidence?.bodyUsageCount, 1);
        assertDeepFrozen(emdash.inspect(abstraction));
        assert.ok(captured);
        assert.throws(
            () => point(emdash, eta, captured),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'ESCAPED_SLOT'
        );
    });

    it('recursively constructs identity and vertical composition', () => {
        const { emdash, A, F, G, H, eta, theta } = fixture();
        const identity = emdash.transforLambda(
            'aIdentity',
            F,
            F,
            a => emdash.identityCell(map(emdash, F, a))
        );
        const composition = emdash.transforLambda(
            'aComposition',
            F,
            H,
            a => emdash.composeCells(
                point(emdash, theta, a),
                point(emdash, eta, a)
            )
        );
        const identityCompilation = emdash.compile(identity);
        const compositionCompilation = emdash.compile(composition);
        const x = emdash.object('natural_binder_x', A);
        const closedComponent = emdash.compile(
            point(emdash, composition, x)
        );

        assert.match(
            identityCompilation.explicitCore,
            new RegExp(
                coreCategoricalFibredTransfdCoreName('identity-arrow'),
                'u'
            )
        );
        assert.equal(
            emdash.inspect(identity).abstractions.at(-1)?.rule,
            'categorical.ordinary-transfor-identity'
        );
        assert.match(
            compositionCompilation.explicitCore,
            /generic-category-composition/u
        );
        assert.equal(
            emdash.inspect(composition).abstractions.at(-1)?.rule,
            'categorical.ordinary-transfor-composition'
        );
        assert.equal(closedComponent.surfaceType.tag, 'hom');
        assert.equal(
            closedComponent.explicitInferredType,
            closedComponent.explicitExpectedType
        );
    });

    it('constructs both fixed whiskering orientations', () => {
        const {
            emdash,
            eta,
            L,
            M,
            FL,
            GL,
            MF,
            MG
        } = fixture();
        const prewhiskered = emdash.transforLambda(
            'xPre',
            FL,
            GL,
            x => point(emdash, eta, map(emdash, L, x))
        );
        const postwhiskered = emdash.transforLambda(
            'aPost',
            MF,
            MG,
            a => map(
                emdash,
                M,
                point(emdash, eta, a),
                'arrow-value'
            )
        );
        const preCompilation = emdash.compile(prewhiskered);
        const postCompilation = emdash.compile(postwhiskered);
        const preEvidence =
            emdash.inspect(prewhiskered).abstractions.at(-1);
        const postEvidence =
            emdash.inspect(postwhiskered).abstractions.at(-1);

        assert.match(
            preCompilation.explicitCore,
            new RegExp(
                coreCategoricalCompositionalNaturalCoreName(
                    'prewhiskeringAction'
                ),
                'u'
            )
        );
        assert.equal(
            preEvidence?.rule,
            'categorical.ordinary-transfor-whiskering'
        );
        assert.equal(preEvidence?.orientation, 'pre');
        assert.match(
            postCompilation.explicitCore,
            new RegExp(
                coreCategoricalCompositionalNaturalCoreName(
                    'postwhiskeringAction'
                ),
                'u'
            )
        );
        assert.equal(
            postEvidence?.rule,
            'categorical.ordinary-transfor-whiskering'
        );
        assert.equal(postEvidence?.orientation, 'post');
        assert.equal(preCompilation.surfaceType.tag, 'transfor');
        assert.equal(postCompilation.surfaceType.tag, 'transfor');
        assert.match(
            preCompilation.explicitInferredType,
            /object-classifier/u
        );
        assert.match(
            preCompilation.explicitExpectedType,
            /transfor-classifier/u
        );
    });

    it('rejects arbitrary point arrows without coherence payloads', () => {
        const { emdash, B, F, G } = fixture();
        const u = emdash.object('natural_binder_u', B);
        const v = emdash.object('natural_binder_v', B);
        const arbitrary = emdash.hom(
            'natural_binder_arbitrary',
            B,
            u,
            v
        );

        assert.throws(
            () => emdash.transforLambda(
                'aRejected',
                F,
                G,
                () => arbitrary
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'MISSING_STRUCTURAL_OWNER'
        );
    });

    it('preserves the existing compact displayed-natural eta route', () => {
        const { emdash } = fixture();
        const K = emdash.category('natural_binder_K');
        const E = emdash.displayedFamily('natural_binder_E', K);
        const D = emdash.displayedFamily('natural_binder_D', K);
        const FF = emdash.displayedFunctor('natural_binder_FF', E, D);
        const GG = emdash.displayedFunctor('natural_binder_GG', E, D);
        const displayedEta = emdash.displayedTransfor(
            'natural_binder_displayed_eta',
            FF,
            GG
        );
        const abstraction = emdash.displayedTransforLambda(
            'k',
            FF,
            GG,
            k => emdash.apply(displayedEta, k, {
                expectedShape: 'displayed-component'
            })
        );

        assert.equal(
            emdash.compile(abstraction).explicitCore,
            emdash.compile(displayedEta).explicitCore
        );
        assert.equal(
            emdash.inspect(abstraction).abstractions.at(-1)?.rule,
            'categorical.displayed-transfor-eta'
        );
    });
});
