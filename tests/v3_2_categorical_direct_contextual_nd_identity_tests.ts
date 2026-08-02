/**
 * D-DTTLF-USABILITY-057 generic contextual point-identity slice.
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
    CoreCategoricalTerm,
    CoreLfComparisonResult
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

const runtimeRuleIds = (
    result: CoreLfComparisonResult
): readonly string[] => result.trace.flatMap(entry =>
    entry.reduction.kind === 'runtime'
        ? [entry.reduction.ruleId]
        : []
);

const fixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/categorical-direct-contextual-nd-identity.ts',
        profile: 'fibred-direct-mixed-introduction-1'
    });
    const K = emdash.category('context_nd_id_K');
    const opK = emdash.oppositeCategory(K);
    const E = emdash.displayedFamily('context_nd_id_E', K);
    const D = emdash.displayedFamily('context_nd_id_D', K);
    const Q = emdash.displayedFamily('context_nd_id_Q', K);
    const R = emdash.displayedFamily('context_nd_id_R', K);
    const S = emdash.displayedFamily('context_nd_id_S', K);
    const T = emdash.displayedFamily('context_nd_id_T', K);
    const F = emdash.displayedFunctor('context_nd_id_F', E, D);
    const G = emdash.displayedFunctor('context_nd_id_G', D, Q);
    const H = emdash.displayedFunctor('context_nd_id_H', Q, R);
    const I = emdash.displayedFunctor('context_nd_id_I', R, S);
    const J = emdash.displayedFunctor('context_nd_id_J', S, T);
    const FPrime = emdash.displayedFunctor(
        'context_nd_id_F_prime',
        E,
        D
    );
    const eta = emdash.displayedTransfor(
        'context_nd_id_eta',
        F,
        FPrime
    );
    const x = emdash.object('context_nd_id_x', K);
    const y = emdash.object('context_nd_id_y', K);
    const p = emdash.hom('context_nd_id_p', K, x, y);
    const u = emdash.object(
        'context_nd_id_u',
        emdash.fibre(E, x)
    );
    const A = emdash.displayedFamily('context_nd_id_A', opK);
    const B = emdash.displayedFamily('context_nd_id_B', K);
    const mixed = emdash.mixedDisplayedFunctorFamily(A, B);
    return {
        emdash,
        K,
        E,
        D,
        T,
        F,
        G,
        H,
        I,
        J,
        FPrime,
        eta,
        x,
        p,
        u,
        mixed
    };
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

describe('D-057 direct contextual displayed-natural identity', () => {
    const shared = fixture();

    it('constructs closed identity and factors lambda^nd a. id(a)', () => {
        const { emdash, E } = shared;
        const identityFunctor = emdash.displayedFunctorLambda(
            'aIdentity',
            E,
            E,
            a => a
        );
        const closed = emdash.identityCell(identityFunctor);
        let callbacks = 0;
        const contextual = emdash.displayedTransforContextLambda(
            'a',
            identityFunctor,
            identityFunctor,
            a => {
                callbacks += 1;
                return emdash.identityCell(a);
            }
        );

        assert.equal(callbacks, 1);
        assert.equal(emdash.compare(contextual, closed).status, 'equal');
        assert.equal(
            emdash.compile(closed).surfaceType.tag,
            'displayed-transfor'
        );
        assert.match(
            emdash.compile(contextual).explicitCore,
            /emdash_v3_2_scale_stress_3a2a_id/u
        );

        const evidence = emdash.inspect(contextual).abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-transfor-context-identity'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-context-identity'
        ) {
            assert.fail('Missing contextual point-identity evidence');
        }
        assert.deepEqual(evidence.bindingNames, ['aBase', 'a']);
        assert.deepEqual(evidence.bindingModes, ['natural', 'natural']);
        assert.equal(evidence.contextSize, 2);
        assert.equal(evidence.chainLength, 0);
        assert.equal(evidence.baseUsageCount, 0);
        assert.equal(evidence.fibreUsageCount, 1);
        assert.equal(evidence.body.tag, 'typed-cell-identity');
        if (evidence.body.tag !== 'typed-cell-identity') {
            assert.fail('Bare identity body was not retained');
        }
        assert.equal(evidence.body.endpoint.tag, 'slot-reference');
        assert.equal(evidence.body.type.tag, 'indexed-hom');
        assert.deepEqual(evidence.dependentPrerequisites, []);
        assertDeepFrozen(evidence);
    });

    it('shares one factorer for one map and a generated finite chain', () => {
        const {
            emdash,
            E,
            T,
            F,
            G,
            H,
            I,
            J
        } = shared;
        const one = emdash.displayedTransforContextLambda(
            'aOne',
            F,
            F,
            a => emdash.identityCell(
                emdash.apply(F, a, {
                    expectedShape: 'object-value'
                })
            )
        );
        assert.equal(
            emdash.compare(one, emdash.identityCell(F)).status,
            'equal'
        );
        const oneEvidence = emdash.inspect(one).abstractions.at(-1);
        assert.equal(oneEvidence?.rule,
            'categorical.displayed-transfor-context-identity');
        if (
            oneEvidence?.rule !==
                'categorical.displayed-transfor-context-identity'
        ) {
            assert.fail('Missing one-map identity evidence');
        }
        assert.equal(oneEvidence.chainLength, 1);
        assert.equal(oneEvidence.baseUsageCount, 1);

        const chain = [F, G, H, I, J] as const;
        const mappedEndpoint = (
            value: CoreCategoricalTerm
        ): CoreCategoricalTerm => chain.reduce(
            (current, functor) => emdash.apply(
                functor,
                current,
                { expectedShape: 'object-value' }
            ),
            value
        );
        const whole = emdash.displayedFunctorLambda(
            'aWhole',
            E,
            T,
            mappedEndpoint
        );
        let callbacks = 0;
        const contextual = emdash.displayedTransforContextLambda(
            'aChain',
            whole,
            whole,
            a => {
                callbacks += 1;
                return emdash.identityCell(mappedEndpoint(a));
            }
        );

        assert.equal(callbacks, 1);
        assert.equal(
            emdash.compare(
                contextual,
                emdash.identityCell(whole)
            ).status,
            'equal'
        );
        const evidence = emdash.inspect(contextual).abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-transfor-context-identity'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-context-identity'
        ) {
            assert.fail('Missing finite-chain identity evidence');
        }
        assert.equal(evidence.chainLength, chain.length);
        assert.equal(evidence.baseUsageCount, chain.length);
        assert.equal(evidence.fibreUsageCount, 1);
        assert.equal(evidence.body.tag, 'typed-cell-identity');
        if (evidence.body.tag !== 'typed-cell-identity') {
            assert.fail('Finite-chain identity body was not retained');
        }
        assert.equal(evidence.body.chainLength, chain.length);
    });

    it('recovers left and right identities inside point composition', () => {
        const {
            emdash,
            F,
            FPrime,
            eta
        } = shared;
        const left = emdash.displayedTransforContextLambda(
            'aLeft',
            F,
            FPrime,
            a => emdash.composeCells(
                emdash.identityCell(
                    emdash.apply(FPrime, a, {
                        expectedShape: 'object-value'
                    })
                ),
                point(emdash, eta, a)
            )
        );
        const right = emdash.displayedTransforContextLambda(
            'aRight',
            F,
            FPrime,
            a => emdash.composeCells(
                point(emdash, eta, a),
                emdash.identityCell(
                    emdash.apply(F, a, {
                        expectedShape: 'object-value'
                    })
                )
            )
        );

        const expectedLeft = emdash.composeDisplayedTransfor(
            emdash.identityCell(FPrime),
            eta
        );
        const expectedRight = emdash.composeDisplayedTransfor(
            eta,
            emdash.identityCell(F)
        );
        assert.equal(
            emdash.compare(left, expectedLeft).status,
            'equal'
        );
        assert.equal(
            emdash.compare(right, expectedRight).status,
            'equal'
        );
        const leftBody = emdash.inspect(left).abstractions.at(-1)?.body;
        const rightBody = emdash.inspect(right).abstractions.at(-1)?.body;
        assert.equal(leftBody?.tag, 'typed-cell-composition');
        assert.equal(rightBody?.tag, 'typed-cell-composition');
        if (
            leftBody?.tag !== 'typed-cell-composition' ||
            rightBody?.tag !== 'typed-cell-composition'
        ) {
            assert.fail('Identity composition lost its recursive body');
        }
        assert.equal(leftBody.outer.tag, 'typed-cell-identity');
        assert.equal(rightBody.inner.tag, 'typed-cell-identity');
    });

    it('computes points and internal base-arrow action through existing owners', () => {
        const {
            emdash,
            F,
            x,
            p,
            u
        } = shared;
        const closed = emdash.identityCell(F);
        const contextual = emdash.displayedTransforContextLambda(
            'aAction',
            F,
            F,
            a => emdash.identityCell(
                emdash.apply(F, a, {
                    expectedShape: 'object-value'
                })
            )
        );
        const actualPoint = emdash.displayedTransforPoint(
            contextual,
            x,
            u
        );
        const expectedPoint = emdash.displayedTransforPoint(
            closed,
            x,
            u
        );
        assert.equal(
            emdash.compare(actualPoint, expectedPoint).status,
            'equal'
        );
        assert.equal(
            emdash.compile(actualPoint).surfaceType.tag,
            'hom'
        );
        assert.match(
            emdash.compile(actualPoint).explicitCore,
            /transfor-component-capped/u
        );

        const actualCell = emdash.displayedTransforNaturality(
            contextual,
            p,
            u
        );
        const expectedCell = emdash.displayedFunctorInternalCell(
            F,
            p,
            u
        );
        const comparison = emdash.compare(
            actualCell,
            expectedCell,
            60_000
        );
        assert.equal(comparison.status, 'equal');
        assert.equal(
            runtimeRuleIds(comparison).includes(
                'categorical.displayed-chain.' +
                    'internal-cell-identity.direct'
            ),
            true
        );
        assert.match(
            emdash.compile(actualCell).explicitCore,
            /displayed-transfor-higher-cell/u
        );
    });

    it('uses the same bare-root identity for a mixed Functor_catd fibre', () => {
        const { emdash, mixed } = shared;
        const identityFunctor = emdash.displayedFunctorLambda(
            'mixedFunctor',
            mixed,
            mixed,
            functor => functor
        );
        const contextual = emdash.displayedTransforContextLambda(
            'boundFunctor',
            identityFunctor,
            identityFunctor,
            functor => emdash.identityCell(functor)
        );
        const compiled = emdash.compile(contextual);

        assert.equal(
            emdash.compare(
                contextual,
                emdash.identityCell(identityFunctor)
            ).status,
            'equal'
        );
        const evidence = emdash.inspect(contextual).abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-transfor-context-identity'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-context-identity'
        ) {
            assert.fail('Missing mixed-family identity evidence');
        }
        assert.equal(evidence.chainLength, 0);
        assert.equal(evidence.baseUsageCount, 0);
        assert.match(
            compiled.explicitExpectedType,
            /stable-functor-family/u
        );
        assert.doesNotMatch(compiled.explicitCore, /mixed_curry/u);
    });

    it('rejects non-factorable, mismatched, and non-displayed endpoints', () => {
        const {
            emdash,
            K,
            E,
            F,
            FPrime,
            eta
        } = shared;
        const identityFunctor = emdash.displayedFunctorLambda(
            'negativeIdentity',
            E,
            E,
            a => a
        );
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'nonFactorable',
                identityFunctor,
                identityFunctor,
                a => emdash.identityCell(
                    emdash.fibrePair(a, a)
                )
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'wrongEndpoint',
                F,
                F,
                a => emdash.identityCell(a)
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'badComposition',
                F,
                FPrime,
                a => emdash.composeCells(
                    emdash.identityCell(
                        emdash.apply(F, a, {
                            expectedShape: 'object-value'
                        })
                    ),
                    point(emdash, eta, a)
                )
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.throws(
            () => emdash.identityCell(emdash.identityFunctor(K)),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
    });

    it('rejects escaped/foreign slots and unavailable profiles', () => {
        const { emdash, E } = shared;
        const identityFunctor = emdash.displayedFunctorLambda(
            'scopeIdentity',
            E,
            E,
            a => a
        );
        let escaped: CoreCategoricalSlotToken | undefined;
        emdash.displayedTransforContextLambda(
            'escaped',
            identityFunctor,
            identityFunctor,
            a => {
                escaped = a;
                return emdash.identityCell(a);
            }
        );
        assert.throws(
            () => emdash.identityCell(
                escaped as CoreCategoricalSlotToken
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'ESCAPED_SLOT'
        );

        const foreign = new CoreCategoricalProgram();
        const foreignK = foreign.category('context_nd_id_foreign_K');
        const foreignTerm = foreign.object(
            'context_nd_id_foreign_x',
            foreignK
        );
        assert.throws(
            () => emdash.identityCell(foreignTerm),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'FOREIGN_TERM'
        );

        const legacy = new CoreCategoricalProgram({
            profile: 'fibred-binder-1'
        });
        const legacyK = legacy.category('context_nd_id_legacy_K');
        const legacyE = legacy.displayedFamily(
            'context_nd_id_legacy_E',
            legacyK
        );
        const legacyF = legacy.displayedFunctor(
            'context_nd_id_legacy_F',
            legacyE,
            legacyE
        );
        assert.throws(
            () => legacy.identityCell(legacyF),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_FIBRED_TRANSFD'
        );
    });
});
