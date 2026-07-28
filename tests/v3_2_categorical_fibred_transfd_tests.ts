/**
 * End-user FIBRED-TRANSFD-1 displayed-transfor usability slice.
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
    CoreCategoricalSlotToken
} from '../src/v3_2';

const fixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile: 'tests/fixtures/categorical-fibred-transfd.ts',
        profile: 'fibred-transfd-1'
    });
    const K = emdash.category('K', { line: 1 });
    const E = emdash.displayedFamily('E', K, { line: 2 });
    const D = emdash.displayedFamily('D', K, { line: 3 });
    const FF = emdash.displayedFunctor('FF', E, D, { line: 4 });
    const GG = emdash.displayedFunctor('GG', E, D, { line: 5 });
    const HH = emdash.displayedFunctor('HH', E, D, { line: 6 });
    const eta = emdash.displayedTransfor('eta', FF, GG, {
        line: 7
    });
    const theta = emdash.displayedTransfor('theta', GG, HH, {
        line: 8
    });
    const x = emdash.object('x', K, { line: 9 });
    const y = emdash.object('y', K, { line: 10 });
    const p = emdash.hom('p', K, x, y, { line: 11 });
    const u = emdash.object('u', emdash.fibre(E, x), {
        line: 12
    });
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

describe('FIBRED-TRANSFD-1 end-user usability', () => {
    it('eta-lowers λ k :^nd K. eta[k] after one callback', () => {
        const { emdash, FF, GG, eta } = fixture();
        let callbacks = 0;
        const abstraction = emdash.displayedTransforLambda(
            'k',
            FF,
            GG,
            k => {
                callbacks += 1;
                return emdash.apply(eta, k, {
                    expectedShape: 'displayed-component'
                });
            },
            { source: { line: 20 } }
        );
        assert.equal(callbacks, 1);
        assert.equal(emdash.compare(abstraction, eta).status, 'equal');
        const evidence =
            emdash.inspect(abstraction).abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-transfor-eta'
        );
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-eta'
        ) {
            assert.fail('Missing displayed-transfor eta evidence');
        }
        assert.equal(evidence.body.tag, 'typed-application');
        if (evidence.body.tag !== 'typed-application') {
            assert.fail('Displayed-transfor eta lost its component body');
        }
        assert.equal(
            evidence.body.judgmentId,
            'displayed-transfor.component.capped'
        );
        assert.equal(evidence.body.type.tag, 'indexed-transfor');
        assert.deepEqual(
            evidence.dependentPrerequisites,
            ['displayed-transfor-component-capped']
        );
        assert.equal(Object.isFrozen(evidence.body), true);
    });

    it('checks eta[x], eta[x][u], and eta[p][u]', () => {
        const { emdash, eta, x, p, u } = fixture();
        const component =
            emdash.displayedTransforComponent(eta, x);
        const point =
            emdash.displayedTransforPoint(eta, x, u);
        const higher =
            emdash.displayedTransforNaturality(eta, p, u);
        const componentCompilation = emdash.compile(component);
        const pointCompilation = emdash.compile(point);
        const higherCompilation = emdash.compile(higher);
        assert.equal(
            componentCompilation.surfaceType.tag,
            'transfor'
        );
        assert.equal(pointCompilation.surfaceType.tag, 'hom');
        assert.equal(higherCompilation.surfaceType.tag, 'hom');
        assert.match(
            componentCompilation.explicitCore,
            /displayed-component/u
        );
        assert.match(
            pointCompilation.explicitCore,
            /transfor-component-capped/u
        );
        assert.match(
            higherCompilation.explicitCore,
            /displayed-transfor-higher-cell/u
        );
        assert.match(
            higherCompilation.explicitExpectedType,
            /displayed-transport-lhs/u
        );
        assert.match(
            higherCompilation.explicitExpectedType,
            /displayed-transport-rhs/u
        );
    });

    it('composes coherent displayed transfors at Functord_cat', () => {
        const {
            emdash,
            eta,
            theta,
            x
        } = fixture();
        const composite =
            emdash.composeDisplayedTransfor(theta, eta);
        const component =
            emdash.displayedTransforComponent(composite, x);
        assert.equal(
            emdash.compile(composite).surfaceType.tag,
            'displayed-transfor'
        );
        assert.match(
            emdash.compile(composite).explicitCore,
            /generic-category-composition/u
        );
        assert.match(
            emdash.compile(component).explicitCore,
            /displayed-component/u
        );
    });

    it('fails closed outside the profile and on incoherent bodies', () => {
        const legacy = new CoreCategoricalProgram({
            profile: 'fibred-binder-1'
        });
        const legacyK = legacy.category('LegacyK');
        const legacyE = legacy.displayedFamily(
            'LegacyE',
            legacyK
        );
        const legacyFF = legacy.displayedFunctor(
            'LegacyFF',
            legacyE,
            legacyE
        );
        assert.throws(
            () => legacy.displayedTransfor(
                'legacyEta',
                legacyFF,
                legacyFF
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_FIBRED_TRANSFD'
        );

        const { emdash, K, FF, GG, eta } = fixture();
        assert.throws(
            () => emdash.displayedTransforLambda(
                'k',
                FF,
                GG,
                () => eta
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
        );
        assert.throws(
            () => emdash.displayedTransforLambda(
                'k',
                FF,
                GG,
                k => emdash.apply(eta, k),
                { variation: 'functorial' }
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        const otherK = emdash.category('OtherK');
        const wrongPoint = emdash.object('wrongPoint', otherK);
        assert.throws(
            () => emdash.displayedTransforComponent(
                eta,
                wrongPoint
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.ok(K);
    });

    it('rejects escaped direct base slots', () => {
        const { emdash, FF, GG, eta } = fixture();
        let escaped: CoreCategoricalSlotToken | undefined;
        emdash.displayedTransforLambda(
            'k',
            FF,
            GG,
            k => {
                escaped = k;
                return emdash.apply(eta, k);
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
    });
});
