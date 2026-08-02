/**
 * D-DTTLF-USABILITY-055 direct contextual displayed-natural eta slice.
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

const fixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/categorical-direct-contextual-nd-eta.ts',
        profile: 'fibred-transfd-1'
    });
    const K = emdash.category('context_nd_K', { line: 1 });
    const E = emdash.displayedFamily('context_nd_E', K, {
        line: 2
    });
    const D = emdash.displayedFamily('context_nd_D', K, {
        line: 3
    });
    const FF = emdash.displayedFunctor('context_nd_FF', E, D, {
        line: 4
    });
    const GG = emdash.displayedFunctor('context_nd_GG', E, D, {
        line: 5
    });
    const HH = emdash.displayedFunctor('context_nd_HH', E, D, {
        line: 6
    });
    const eta = emdash.displayedTransfor(
        'context_nd_eta',
        FF,
        GG,
        { line: 7 }
    );
    const theta = emdash.displayedTransfor(
        'context_nd_theta',
        GG,
        HH,
        { line: 8 }
    );
    const x = emdash.object('context_nd_x', K, { line: 9 });
    const y = emdash.object('context_nd_y', K, { line: 10 });
    const p = emdash.hom('context_nd_p', K, x, y, { line: 11 });
    const u = emdash.object(
        'context_nd_u',
        emdash.fibre(E, x),
        { line: 12 }
    );
    return {
        emdash,
        K,
        E,
        D,
        FF,
        GG,
        HH,
        eta,
        theta,
        x,
        y,
        p,
        u
    };
};

describe('D-055 direct contextual displayed-natural eta', () => {
    const shared = fixture();

    it('factors lambda^nd a. eta[a] after one callback', () => {
        const { emdash, FF, GG, eta } = shared;
        let callbacks = 0;
        const abstraction = emdash.displayedTransforContextLambda(
            'a',
            FF,
            GG,
            a => {
                callbacks += 1;
                return emdash.apply(eta, a, {
                    expectedShape: 'point-component'
                });
            },
            { source: { line: 20 } }
        );

        assert.equal(callbacks, 1);
        assert.equal(emdash.compare(abstraction, eta).status, 'equal');
        assert.equal(
            emdash.compile(abstraction).surfaceType.tag,
            'displayed-transfor'
        );
        assert.deepEqual(emdash.inspect(abstraction).usage, []);

        const evidence =
            emdash.inspect(abstraction).abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-transfor-context-eta'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-context-eta'
        ) {
            assert.fail('Missing direct contextual eta evidence');
        }
        assert.deepEqual(evidence.bindingNames, ['aBase', 'a']);
        assert.deepEqual(evidence.bindingModes, ['natural', 'natural']);
        assert.equal(evidence.contextSize, 2);
        assert.equal(
            evidence.contextRelation,
            'natural-base-then-natural-fibre-binder'
        );
        assert.equal(evidence.baseUsageCount, 1);
        assert.equal(evidence.fibreUsageCount, 1);
        assert.equal(evidence.body.tag, 'typed-application');
        if (evidence.body.tag !== 'typed-application') {
            assert.fail('Direct contextual eta lost its point body');
        }
        assert.equal(
            evidence.body.judgmentId,
            'indexed-fibre-transfor.object'
        );
        assert.equal(
            evidence.body.target,
            'indexed-fibre-transfor-point'
        );
        assert.equal(evidence.body.type.tag, 'indexed-hom');
        if (evidence.body.type.tag !== 'indexed-hom') {
            assert.fail('Direct contextual eta lost its indexed Hom');
        }
        assert.equal(evidence.body.type.baseIndex, 1);
        assert.equal(evidence.body.type.fibreIndex, 0);
        assert.equal(evidence.body.subject.tag, 'typed-application');
        assert.equal(evidence.body.argument.tag, 'slot-reference');
        assert.deepEqual(
            evidence.dependentPrerequisites,
            ['displayed-transfor-component-capped']
        );
        assertDeepFrozen(evidence);
    });

    it('preserves closed point and internal base-arrow action', () => {
        const {
            emdash,
            FF,
            GG,
            eta,
            x,
            p,
            u
        } = shared;
        const abstraction = emdash.displayedTransforContextLambda(
            'a',
            FF,
            GG,
            a => emdash.apply(eta, a)
        );
        const directPoint = emdash.displayedTransforPoint(
            abstraction,
            x,
            u
        );
        const etaPoint = emdash.displayedTransforPoint(eta, x, u);
        const directCell = emdash.displayedTransforNaturality(
            abstraction,
            p,
            u
        );
        const etaCell = emdash.displayedTransforNaturality(eta, p, u);

        assert.equal(
            emdash.compare(directPoint, etaPoint).status,
            'equal'
        );
        assert.equal(
            emdash.compare(directCell, etaCell).status,
            'equal'
        );
        assert.match(
            emdash.compile(directPoint).explicitCore,
            /transfor-component-capped/u
        );
        assert.match(
            emdash.compile(directCell).explicitCore,
            /displayed-transfor-higher-cell/u
        );
    });

    it('retains the whole-fibre eta and recursive composition API', () => {
        const {
            emdash,
            FF,
            HH,
            eta,
            theta
        } = shared;
        const retained = emdash.displayedTransforLambda(
            'k',
            FF,
            HH,
            k => emdash.composeCells(
                emdash.apply(theta, k),
                emdash.apply(eta, k)
            )
        );
        const expected = emdash.composeDisplayedTransfor(theta, eta);
        assert.equal(emdash.compare(retained, expected).status, 'equal');
    });

    it('rejects wrong endpoint and wrong-family point components', () => {
        const {
            emdash,
            K,
            FF,
            GG,
            theta
        } = shared;
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'a',
                FF,
                GG,
                a => emdash.apply(theta, a)
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );

        const Q = emdash.displayedFamily('context_nd_Q', K);
        const R = emdash.displayedFamily('context_nd_R', K);
        const JJ = emdash.displayedFunctor('context_nd_JJ', Q, R);
        const LL = emdash.displayedFunctor('context_nd_LL', Q, R);
        const zeta = emdash.displayedTransfor(
            'context_nd_zeta',
            JJ,
            LL
        );
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'a',
                FF,
                GG,
                a => emdash.apply(zeta, a)
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
    });

    it('rejects unsupported point data and wrong binder modes', () => {
        const {
            emdash,
            K,
            FF,
            GG,
            eta,
            x,
            y
        } = shared;
        const arbitrary = emdash.hom(
            'context_nd_arbitrary',
            K,
            x,
            y
        );
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'a',
                FF,
                GG,
                () => arbitrary
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'a',
                FF,
                GG,
                a => emdash.apply(eta, a),
                { variation: 'functorial' }
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
    });

    it('rejects escaped and foreign fibre tokens', () => {
        const { emdash, FF, GG, eta } = shared;
        let escaped: CoreCategoricalSlotToken | undefined;
        emdash.displayedTransforContextLambda(
            'a',
            FF,
            GG,
            a => {
                escaped = a;
                return emdash.apply(eta, a);
            }
        );
        assert.throws(
            () => emdash.apply(
                eta,
                escaped as CoreCategoricalSlotToken
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'ESCAPED_SLOT'
        );

        const foreign = new CoreCategoricalProgram();
        const foreignK = foreign.category('context_nd_foreign_K');
        const foreignTerm: CoreCategoricalTerm = foreign.object(
            'context_nd_foreign_x',
            foreignK
        );
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'a',
                FF,
                GG,
                () => foreignTerm
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'FOREIGN_TERM'
        );
    });

    it('remains unavailable outside the reviewed profile', () => {
        const legacy = new CoreCategoricalProgram({
            profile: 'fibred-binder-1'
        });
        const K = legacy.category('context_nd_legacy_K');
        const E = legacy.displayedFamily('context_nd_legacy_E', K);
        const F = legacy.displayedFunctor('context_nd_legacy_F', E, E);
        assert.throws(
            () => legacy.displayedTransforContextLambda(
                'a',
                F,
                F,
                a => a
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_FIBRED_TRANSFD'
        );
    });
});
