/**
 * D-DTTLF-USABILITY-058/061 fixed-head contextual `:^nd` whiskering.
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
    CoreCategoricalTerm,
    CoreLfComparisonResult
} from '../src/v3_2';

const runtimeRuleIds = (
    result: CoreLfComparisonResult
): readonly string[] => result.trace.flatMap(entry =>
    entry.reduction.kind === 'runtime'
        ? [entry.reduction.ruleId]
        : []
);

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
    argument: CoreCategoricalTerm
): CoreCategoricalTerm => emdash.apply(
    functor,
    argument,
    { expectedShape: 'object-value' }
);

const fixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/categorical-direct-contextual-nd-whiskering.ts',
        profile: 'fibred-transfd-1'
    });
    const K = emdash.category('context_nd_whisker_K');
    const C0 = emdash.displayedFamily('context_nd_whisker_C0', K);
    const C1 = emdash.displayedFamily('context_nd_whisker_C1', K);
    const E = emdash.displayedFamily('context_nd_whisker_E', K);
    const D = emdash.displayedFamily('context_nd_whisker_D', K);
    const Q = emdash.displayedFamily('context_nd_whisker_Q', K);
    const R = emdash.displayedFamily('context_nd_whisker_R', K);
    const L0 = emdash.displayedFunctor(
        'context_nd_whisker_L0',
        C0,
        C1
    );
    const L1 = emdash.displayedFunctor(
        'context_nd_whisker_L1',
        C1,
        E
    );
    const F = emdash.displayedFunctor('context_nd_whisker_F', E, D);
    const G = emdash.displayedFunctor('context_nd_whisker_G', E, D);
    const G2 = emdash.displayedFunctor('context_nd_whisker_G2', E, D);
    const H0 = emdash.displayedFunctor('context_nd_whisker_H0', D, Q);
    const H1 = emdash.displayedFunctor('context_nd_whisker_H1', Q, R);
    const eta = emdash.displayedTransfor(
        'context_nd_whisker_eta',
        F,
        G
    );
    const theta = emdash.displayedTransfor(
        'context_nd_whisker_theta',
        G,
        G2
    );
    const x = emdash.object('context_nd_whisker_x', K);
    const y = emdash.object('context_nd_whisker_y', K);
    const p = emdash.hom('context_nd_whisker_p', K, x, y);
    const uE = emdash.object(
        'context_nd_whisker_uE',
        emdash.fibre(E, x)
    );
    const uC0 = emdash.object(
        'context_nd_whisker_uC0',
        emdash.fibre(C0, x)
    );
    return {
        emdash,
        K,
        C0,
        C1,
        E,
        D,
        Q,
        R,
        L0,
        L1,
        F,
        G,
        G2,
        H0,
        H1,
        eta,
        theta,
        x,
        p,
        uE,
        uC0
    };
};

const mappedDisplayedFunctor = (
    emdash: CoreCategoricalProgram,
    name: string,
    source: Parameters<CoreCategoricalProgram['displayedFunctorLambda']>[1],
    target: Parameters<CoreCategoricalProgram['displayedFunctorLambda']>[2],
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

describe('D-058/061 direct contextual displayed-natural whiskering', () => {
    const shared = fixture();

    it('recovers symmetric fixed-head post- and prewhiskering', () => {
        const {
            emdash,
            C1,
            E,
            D,
            Q,
            L1,
            F,
            G,
            H0,
            eta
        } = shared;
        const postSource = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_HF',
            E,
            Q,
            [F, H0]
        );
        const postTarget = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_HG',
            E,
            Q,
            [G, H0]
        );
        const preSource = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_FL',
            C1,
            D,
            [L1, F]
        );
        const preTarget = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_GL',
            C1,
            D,
            [L1, G]
        );
        let callbacks = 0;
        const post = emdash.displayedTransforContextLambda(
            'post',
            postSource,
            postTarget,
            a => {
                callbacks += 1;
                return point(emdash, H0, point(emdash, eta, a));
            }
        );
        const pre = emdash.displayedTransforContextLambda(
            'pre',
            preSource,
            preTarget,
            a => {
                callbacks += 1;
                return point(emdash, eta, map(emdash, L1, a));
            }
        );

        assert.equal(callbacks, 2);
        for (const [term, orientation] of [
            [post, 'post'],
            [pre, 'pre']
        ] as const) {
            assert.equal(
                emdash.compile(term).surfaceType.tag,
                'displayed-transfor'
            );
            assert.match(
                emdash.compile(term).explicitCore,
                /displayed-transfor-horizontal-action/u
            );
            const evidence = emdash.inspect(term).abstractions.at(-1);
            assert.equal(
                evidence?.rule,
                'categorical.displayed-transfor-context-whiskering'
            );
            if (
                evidence?.rule !==
                    'categorical.displayed-transfor-context-whiskering'
            ) {
                assert.fail('Missing contextual whiskering evidence');
            }
            assert.equal(evidence.orientation, orientation);
            assert.deepEqual(
                evidence.bindingModes,
                ['natural', 'natural']
            );
            assert.equal(
                evidence.dependentPrerequisites.includes(
                    'displayed-transfor-horizontal-action'
                ),
                true
            );
        }
    });

    it('computes both point equations and retains internal higher action',
        () => {
        const {
            emdash,
            C1,
            E,
            D,
            Q,
            L1,
            F,
            G,
            H0,
            eta,
            x,
            p,
            uE
        } = shared;
        const postSource = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_point_HF',
            E,
            Q,
            [F, H0]
        );
        const postTarget = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_point_HG',
            E,
            Q,
            [G, H0]
        );
        const preSource = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_point_FL',
            C1,
            D,
            [L1, F]
        );
        const preTarget = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_point_GL',
            C1,
            D,
            [L1, G]
        );
        const post = emdash.displayedTransforContextLambda(
            'postPoint',
            postSource,
            postTarget,
            a => point(emdash, H0, point(emdash, eta, a))
        );
        const pre = emdash.displayedTransforContextLambda(
            'prePoint',
            preSource,
            preTarget,
            a => point(emdash, eta, map(emdash, L1, a))
        );

        const postPoint = emdash.displayedTransforPoint(
            post,
            x,
            uE
        );
        const H0x = emdash.apply(H0, x, {
            expectedShape: 'fibre-functor'
        });
        const expectedPostPoint = emdash.apply(
            H0x,
            emdash.displayedTransforPoint(eta, x, uE)
        );
        const postComparison = emdash.compare(
            postPoint,
            expectedPostPoint,
            60_000
        );
        assert.equal(postComparison.status, 'equal');
        assert.equal(
            runtimeRuleIds(postComparison).includes(
                'categorical.transfd.horizontal-component'
            ),
            true
        );
        assert.equal(
            runtimeRuleIds(postComparison).includes(
                'categorical.transfd.horizontal-point'
            ),
            true
        );
        assert.equal(
            runtimeRuleIds(postComparison).includes(
                'categorical.transfd.identity-capped-action'
            ),
            true
        );

        const L1x = emdash.apply(L1, x, {
            expectedShape: 'fibre-functor'
        });
        const uC1 = emdash.object(
            'context_nd_whisker_uC1',
            emdash.fibre(C1, x)
        );
        const expectedPrePoint = emdash.displayedTransforPoint(
            eta,
            x,
            emdash.apply(L1x, uC1)
        );
        const preComparison = emdash.compare(
            emdash.displayedTransforPoint(pre, x, uC1),
            expectedPrePoint,
            60_000
        );
        assert.equal(preComparison.status, 'equal');
        assert.equal(
            runtimeRuleIds(preComparison).includes(
                'categorical.transfd.identity-base-action'
            ),
            true
        );

        for (const [term, object] of [
            [post, uE],
            [pre, uC1]
        ] as const) {
            const higher = emdash.displayedTransforNaturality(
                term,
                p,
                object
            );
            assert.equal(emdash.compile(higher).surfaceType.tag, 'hom');
            assert.match(
                emdash.compile(higher).explicitCore,
                /displayed-transfor-higher-cell/u
            );
        }
    });

    it('recurses through finite mapper chains, identity, and composition',
        () => {
        const {
            emdash,
            C0,
            E,
            R,
            L0,
            L1,
            F,
            G2,
            H0,
            H1,
            eta,
            theta
        } = shared;
        const composed = emdash.composeDisplayedTransfor(theta, eta);
        const postSource = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_chain_post_source',
            E,
            R,
            [F, H0, H1]
        );
        const postTarget = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_chain_post_target',
            E,
            R,
            [G2, H0, H1]
        );
        const preSource = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_chain_pre_source',
            C0,
            shared.D,
            [L0, L1, F]
        );
        const preTarget = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_chain_pre_target',
            C0,
            shared.D,
            [L0, L1, G2]
        );
        const post = emdash.displayedTransforContextLambda(
            'postChain',
            postSource,
            postTarget,
            a => point(
                emdash,
                H1,
                point(
                    emdash,
                    H0,
                    point(emdash, composed, a)
                )
            )
        );
        const pre = emdash.displayedTransforContextLambda(
            'preChain',
            preSource,
            preTarget,
            a => point(
                emdash,
                composed,
                map(emdash, L1, map(emdash, L0, a))
            )
        );
        assert.match(
            emdash.compile(post).explicitCore,
            /generic-category-composition/u
        );
        assert.match(
            emdash.compile(pre).explicitCore,
            /generic-category-composition/u
        );
        assert.equal(
            emdash.inspect(post).abstractions.at(-1)?.rule,
            'categorical.displayed-transfor-context-whiskering'
        );
        assert.equal(
            emdash.inspect(pre).abstractions.at(-1)?.rule,
            'categorical.displayed-transfor-context-whiskering'
        );

        const identity = emdash.identityCell(F);
        const postIdentity = emdash.displayedTransforContextLambda(
            'postIdentity',
            mappedDisplayedFunctor(
                emdash,
                'context_nd_whisker_identity_HF',
                E,
                shared.Q,
                [F, H0]
            ),
            mappedDisplayedFunctor(
                emdash,
                'context_nd_whisker_identity_HF_target',
                E,
                shared.Q,
                [F, H0]
            ),
            a => point(emdash, H0, point(emdash, identity, a))
        );
        const preIdentity = emdash.displayedTransforContextLambda(
            'preIdentity',
            mappedDisplayedFunctor(
                emdash,
                'context_nd_whisker_identity_FL',
                shared.C1,
                shared.D,
                [L1, F]
            ),
            mappedDisplayedFunctor(
                emdash,
                'context_nd_whisker_identity_FL_target',
                shared.C1,
                shared.D,
                [L1, F]
            ),
            a => point(emdash, identity, map(emdash, L1, a))
        );
        assert.equal(
            emdash.inspect(postIdentity).abstractions.at(-1)?.rule,
            'categorical.displayed-transfor-context-whiskering'
        );
        assert.equal(
            emdash.inspect(preIdentity).abstractions.at(-1)?.rule,
            'categorical.displayed-transfor-context-whiskering'
        );
    });

    it('fails closed on family, orientation, and non-factorable mismatches',
        () => {
        const {
            emdash,
            K,
            E,
            Q,
            F,
            G,
            H0,
            eta
        } = shared;
        const postSource = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_negative_HF',
            E,
            Q,
            [F, H0]
        );
        const postTarget = mappedDisplayedFunctor(
            emdash,
            'context_nd_whisker_negative_HG',
            E,
            Q,
            [G, H0]
        );
        const Wrong = emdash.displayedFamily(
            'context_nd_whisker_Wrong',
            K
        );
        const wrongMapper = emdash.displayedFunctor(
            'context_nd_whisker_wrong_mapper',
            Wrong,
            Q
        );
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'wrongFamily',
                postSource,
                postTarget,
                a => point(
                    emdash,
                    wrongMapper,
                    point(emdash, eta, a)
                )
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'wrongOrientation',
                postSource,
                postTarget,
                a => point(emdash, eta, map(emdash, H0, a))
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'nonFactorable',
                postSource,
                postTarget,
                a => point(emdash, eta, emdash.fibrePair(a, a))
            ),
            error =>
                (
                    error instanceof CoreCategoricalFrontendError &&
                    (
                        error.code === 'CLASSIFIER_ARGUMENT_MISMATCH' ||
                        error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
                    )
                ) ||
                (
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'UNAVAILABLE_DISPLAYED_CONTEXT'
                )
        );
    });
});
