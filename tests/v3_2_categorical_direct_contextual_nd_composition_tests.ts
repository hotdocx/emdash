/**
 * D-DTTLF-USABILITY-056 recursive point-composition slice.
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
            'tests/fixtures/categorical-direct-contextual-nd-composition.ts',
        profile: 'fibred-transfd-1'
    });
    const K = emdash.category('context_nd_comp_K');
    const E = emdash.displayedFamily('context_nd_comp_E', K);
    const D = emdash.displayedFamily('context_nd_comp_D', K);
    const FF = emdash.displayedFunctor('context_nd_comp_FF', E, D);
    const GG = emdash.displayedFunctor('context_nd_comp_GG', E, D);
    const HH = emdash.displayedFunctor('context_nd_comp_HH', E, D);
    const II = emdash.displayedFunctor('context_nd_comp_II', E, D);
    const eta = emdash.displayedTransfor(
        'context_nd_comp_eta',
        FF,
        GG
    );
    const theta = emdash.displayedTransfor(
        'context_nd_comp_theta',
        GG,
        HH
    );
    const iota = emdash.displayedTransfor(
        'context_nd_comp_iota',
        HH,
        II
    );
    const x = emdash.object('context_nd_comp_x', K);
    const y = emdash.object('context_nd_comp_y', K);
    const p = emdash.hom('context_nd_comp_p', K, x, y);
    const u = emdash.object(
        'context_nd_comp_u',
        emdash.fibre(E, x)
    );
    return {
        emdash,
        K,
        E,
        D,
        FF,
        GG,
        HH,
        II,
        eta,
        theta,
        iota,
        x,
        p,
        u
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

describe('D-056 direct contextual displayed-natural composition', () => {
    const shared = fixture();

    it('recovers binary point composition after one callback', () => {
        const {
            emdash,
            FF,
            HH,
            eta,
            theta
        } = shared;
        let callbacks = 0;
        const abstraction = emdash.displayedTransforContextLambda(
            'a',
            FF,
            HH,
            a => {
                callbacks += 1;
                return emdash.composeCells(
                    point(emdash, theta, a),
                    point(emdash, eta, a)
                );
            }
        );
        const expected = emdash.composeDisplayedTransfor(theta, eta);

        assert.equal(callbacks, 1);
        assert.equal(emdash.compare(abstraction, expected).status, 'equal');
        assert.deepEqual(emdash.inspect(abstraction).usage, []);

        const evidence = emdash.inspect(abstraction).abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-transfor-context-composition'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-context-composition'
        ) {
            assert.fail('Missing direct contextual composition evidence');
        }
        assert.deepEqual(evidence.bindingNames, ['aBase', 'a']);
        assert.deepEqual(evidence.bindingModes, ['natural', 'natural']);
        assert.equal(evidence.baseUsageCount, 2);
        assert.equal(evidence.fibreUsageCount, 2);
        assert.equal(evidence.body.tag, 'typed-cell-composition');
        if (evidence.body.tag !== 'typed-cell-composition') {
            assert.fail('Point composition body was not retained');
        }
        assert.equal(evidence.body.type.tag, 'indexed-hom');
        if (evidence.body.type.tag !== 'indexed-hom') {
            assert.fail('Point composition lost its indexed Hom');
        }
        assert.equal(evidence.body.type.baseIndex, 1);
        assert.equal(evidence.body.type.fibreIndex, 0);
        assert.equal(evidence.body.outer.tag, 'typed-application');
        assert.equal(evidence.body.inner.tag, 'typed-application');
        assert.deepEqual(
            evidence.dependentPrerequisites,
            [
                'displayed-transfor-component-capped',
                'generic-category-composition'
            ]
        );
        assertDeepFrozen(evidence);
    });

    it('recursively recovers nested point composition', () => {
        const {
            emdash,
            FF,
            II,
            eta,
            theta,
            iota
        } = shared;
        const abstraction = emdash.displayedTransforContextLambda(
            'a',
            FF,
            II,
            a => emdash.composeCells(
                point(emdash, iota, a),
                emdash.composeCells(
                    point(emdash, theta, a),
                    point(emdash, eta, a)
                )
            )
        );
        const expected = emdash.composeDisplayedTransfor(
            iota,
            emdash.composeDisplayedTransfor(theta, eta)
        );

        assert.equal(emdash.compare(abstraction, expected).status, 'equal');
        const evidence = emdash.inspect(abstraction).abstractions.at(-1);
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-context-composition' ||
            evidence.body.tag !== 'typed-cell-composition'
        ) {
            assert.fail('Missing nested point-composition evidence');
        }
        assert.equal(evidence.body.inner.tag, 'typed-cell-composition');
        assert.equal(evidence.baseUsageCount, 3);
        assert.equal(evidence.fibreUsageCount, 3);
    });

    it('preserves point and internally owned base-arrow action', () => {
        const {
            emdash,
            FF,
            HH,
            eta,
            theta,
            x,
            p,
            u
        } = shared;
        const abstraction = emdash.displayedTransforContextLambda(
            'a',
            FF,
            HH,
            a => emdash.composeCells(
                point(emdash, theta, a),
                point(emdash, eta, a)
            )
        );
        const expected = emdash.composeDisplayedTransfor(theta, eta);
        const actualPoint = emdash.displayedTransforPoint(
            abstraction,
            x,
            u
        );
        const expectedPoint = emdash.displayedTransforPoint(
            expected,
            x,
            u
        );
        const actualCell = emdash.displayedTransforNaturality(
            abstraction,
            p,
            u
        );
        const expectedCell = emdash.displayedTransforNaturality(
            expected,
            p,
            u
        );

        assert.equal(emdash.compare(actualPoint, expectedPoint).status, 'equal');
        assert.equal(emdash.compare(actualCell, expectedCell).status, 'equal');
        assert.match(
            emdash.compile(actualCell).explicitCore,
            /displayed-transfor-higher-cell/u
        );
    });

    it('retains whole-fibre recursive composition unchanged', () => {
        const {
            emdash,
            FF,
            HH,
            eta,
            theta
        } = shared;
        const abstraction = emdash.displayedTransforLambda(
            'k',
            FF,
            HH,
            k => emdash.composeCells(
                emdash.apply(theta, k),
                emdash.apply(eta, k)
            )
        );
        const expected = emdash.composeDisplayedTransfor(theta, eta);
        assert.equal(emdash.compare(abstraction, expected).status, 'equal');
        assert.equal(
            emdash.inspect(abstraction).abstractions.at(-1)?.rule,
            'categorical.displayed-transfor-composition'
        );
    });

    it('rejects non-adjacent, non-point, and wrong-family bodies', () => {
        const {
            emdash,
            K,
            FF,
            HH,
            eta,
            theta
        } = shared;
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'a',
                FF,
                HH,
                a => emdash.composeCells(
                    point(emdash, eta, a),
                    point(emdash, theta, a)
                )
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.throws(
            () => emdash.composeCells(theta, eta),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );

        const Q = emdash.displayedFamily('context_nd_comp_Q', K);
        const R = emdash.displayedFamily('context_nd_comp_R', K);
        const JJ = emdash.displayedFunctor('context_nd_comp_JJ', Q, R);
        const LL = emdash.displayedFunctor('context_nd_comp_LL', Q, R);
        const zeta = emdash.displayedTransfor(
            'context_nd_comp_zeta',
            JJ,
            LL
        );
        assert.throws(
            () => emdash.displayedTransforContextLambda(
                'a',
                FF,
                HH,
                a => point(emdash, zeta, a)
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
    });

    it('remains unavailable outside the reviewed profile', () => {
        const legacy = new CoreCategoricalProgram({
            profile: 'fibred-binder-1'
        });
        const K = legacy.category('context_nd_comp_legacy_K');
        const E = legacy.displayedFamily('context_nd_comp_legacy_E', K);
        const F = legacy.displayedFunctor('context_nd_comp_legacy_F', E, E);
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
