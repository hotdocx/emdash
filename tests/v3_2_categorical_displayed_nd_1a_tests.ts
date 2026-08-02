/**
 * DISPLAYED-ND-1A recursive coherent component-composition corpus.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY,
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreCategoricalTerm,
    compileCoreCategoricalFibredTransfdTransfer
} from '../src/v3_2';

const fixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile: 'tests/fixtures/categorical-displayed-nd-1a.ts',
        profile: 'fibred-transfd-1'
    });
    const K = emdash.category('nd1a_K', { line: 1 });
    const E = emdash.displayedFamily('nd1a_E', K, { line: 2 });
    const D = emdash.displayedFamily('nd1a_D', K, { line: 3 });
    const FF = emdash.displayedFunctor('nd1a_FF', E, D, {
        line: 4
    });
    const GG = emdash.displayedFunctor('nd1a_GG', E, D, {
        line: 5
    });
    const HH = emdash.displayedFunctor('nd1a_HH', E, D, {
        line: 6
    });
    const II = emdash.displayedFunctor('nd1a_II', E, D, {
        line: 7
    });
    const eta = emdash.displayedTransfor('nd1a_eta', FF, GG, {
        line: 8
    });
    const theta = emdash.displayedTransfor(
        'nd1a_theta',
        GG,
        HH,
        { line: 9 }
    );
    const iota = emdash.displayedTransfor(
        'nd1a_iota',
        HH,
        II,
        { line: 10 }
    );
    const x = emdash.object('nd1a_x', K, { line: 11 });
    const y = emdash.object('nd1a_y', K, { line: 12 });
    const p = emdash.hom('nd1a_p', K, x, y, { line: 13 });
    const u = emdash.object('nd1a_u', emdash.fibre(E, x), {
        line: 14
    });
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
        y,
        p,
        u
    };
};

const component = (
    emdash: CoreCategoricalProgram,
    transformation: CoreCategoricalTerm,
    point: CoreCategoricalTerm
): CoreCategoricalTerm => emdash.apply(
    transformation,
    point,
    { expectedShape: 'displayed-component' }
);

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe('DISPLAYED-ND-1A recursive displayed coherence', () => {
    it('factors λ k :^nd K. theta[k] after eta[k] after one callback',
        () => {
            const {
                emdash,
                FF,
                HH,
                eta,
                theta
            } = fixture();
            let callbacks = 0;
            const abstraction = emdash.displayedTransforLambda(
                'k',
                FF,
                HH,
                k => {
                    callbacks += 1;
                    return emdash.composeCells(
                        component(emdash, theta, k),
                        component(emdash, eta, k)
                    );
                },
                { source: { line: 20 } }
            );
            const expected =
                emdash.composeDisplayedTransfor(theta, eta);
            assert.equal(callbacks, 1);
            assert.equal(
                emdash.compare(abstraction, expected).status,
                'equal'
            );
            assert.equal(
                emdash.compile(abstraction).surfaceType.tag,
                'displayed-transfor'
            );
            const evidence =
                emdash.inspect(abstraction).abstractions.at(-1);
            assert.equal(
                evidence?.rule,
                'categorical.displayed-transfor-composition'
            );
            if (
                evidence?.rule !==
                    'categorical.displayed-transfor-composition'
            ) {
                assert.fail('Missing recursive displayed composition');
            }
            assert.equal(evidence.body.tag, 'typed-cell-composition');
            if (evidence.body.tag !== 'typed-cell-composition') {
                assert.fail('Composition body was not reified');
            }
            assert.equal(evidence.body.outer.tag, 'typed-application');
            assert.equal(evidence.body.inner.tag, 'typed-application');
            assert.equal(evidence.body.type.tag, 'indexed-transfor');
            assert.equal(evidence.body.type.index, 0);
            assert.deepEqual(
                evidence.dependentPrerequisites,
                [
                    'displayed-transfor-component-capped',
                    'generic-category-composition'
                ]
            );
            assert.equal(Object.isFrozen(evidence), true);
            assertDeepFrozen(evidence.body);
        });

    it('recursively factors nested typed cell composition', () => {
        const {
            emdash,
            FF,
            II,
            eta,
            theta,
            iota
        } = fixture();
        const abstraction = emdash.displayedTransforLambda(
            'k',
            FF,
            II,
            k => emdash.composeCells(
                component(emdash, iota, k),
                emdash.composeCells(
                    component(emdash, theta, k),
                    component(emdash, eta, k)
                )
            )
        );
        const expected = emdash.composeDisplayedTransfor(
            iota,
            emdash.composeDisplayedTransfor(theta, eta)
        );
        assert.equal(
            emdash.compare(abstraction, expected).status,
            'equal'
        );
        const evidence =
            emdash.inspect(abstraction).abstractions.at(-1);
        if (
            evidence?.rule !==
                'categorical.displayed-transfor-composition' ||
            evidence.body.tag !== 'typed-cell-composition'
        ) {
            assert.fail('Missing nested displayed composition evidence');
        }
        assert.equal(
            evidence.body.inner.tag,
            'typed-cell-composition'
        );
        assert.deepEqual(
            evidence.dependentPrerequisites,
            [
                'displayed-transfor-component-capped',
                'generic-category-composition'
            ]
        );
    });

    it('computes the object component and typechecks the base-arrow cell',
        () => {
            const {
                emdash,
                FF,
                HH,
                eta,
                theta,
                x,
                p,
                u
            } = fixture();
            const abstraction = emdash.displayedTransforLambda(
                'k',
                FF,
                HH,
                k => emdash.composeCells(
                    component(emdash, theta, k),
                    component(emdash, eta, k)
                )
            );
            const projected =
                emdash.displayedTransforComponent(abstraction, x);
            const rewrite =
                compileCoreCategoricalFibredTransfdTransfer()
                    .composedRuntime
                    .rewriteHead(
                        emdash.compile(projected).explicitTerm
                    );
            assert.equal(rewrite.status, 'rewritten');
            if (rewrite.status !== 'rewritten') {
                assert.fail('Displayed composite component did not reduce');
            }
            assert.equal(
                rewrite.ruleId,
                'categorical.transfd.component-composition.direct'
            );
            const baseArrowCell =
                emdash.displayedTransforNaturality(
                    abstraction,
                    p,
                    u
                );
            const compiledCell = emdash.compile(baseArrowCell);
            assert.equal(compiledCell.surfaceType.tag, 'hom');
            assert.match(
                compiledCell.explicitCore,
                /displayed-transfor-higher-cell/u
            );
        });

    it('rejects non-adjacent transformation endpoints', () => {
        const {
            emdash,
            FF,
            HH,
            eta
        } = fixture();
        const rho = emdash.displayedTransfor(
            'nd1a_rho',
            FF,
            HH
        );
        assert.throws(
            () => emdash.displayedTransforLambda(
                'k',
                FF,
                HH,
                k => emdash.composeCells(
                    component(emdash, rho, k),
                    component(emdash, eta, k)
                )
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
        );
    });

    it('rejects different families and different contextual indices',
        () => {
            const {
                emdash,
                K,
                FF,
                HH,
                eta,
                theta
            } = fixture();
            const E2 = emdash.displayedFamily('nd1a_E2', K);
            const D2 = emdash.displayedFamily('nd1a_D2', K);
            const FF2 = emdash.displayedFunctor(
                'nd1a_FF2',
                E2,
                D2
            );
            const GG2 = emdash.displayedFunctor(
                'nd1a_GG2',
                E2,
                D2
            );
            const eta2 = emdash.displayedTransfor(
                'nd1a_eta2',
                FF2,
                GG2
            );
            assert.throws(
                () => emdash.displayedTransforLambda(
                    'k',
                    FF,
                    HH,
                    k => emdash.composeCells(
                        component(emdash, theta, k),
                        component(emdash, eta2, k)
                    )
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
            );
            assert.throws(
                () => emdash.displayedTransforLambda(
                    'k',
                    FF,
                    HH,
                    k => emdash.displayedTransforLambda(
                        'j',
                        FF,
                        HH,
                        j => emdash.composeCells(
                            component(emdash, theta, j),
                            component(emdash, eta, k)
                        )
                    )
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
            );
        });

    it('rejects escaped and foreign component terms', () => {
        const {
            emdash,
            FF,
            GG,
            HH,
            eta,
            theta
        } = fixture();
        let escaped: CoreCategoricalTerm | undefined;
        emdash.displayedTransforLambda(
            'k',
            FF,
            GG,
            k => {
                escaped = component(emdash, eta, k);
                return escaped;
            }
        );
        assert.throws(
            () => emdash.displayedTransforLambda(
                'j',
                FF,
                HH,
                j => emdash.composeCells(
                    component(emdash, theta, j),
                    escaped as CoreCategoricalTerm
                )
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'ESCAPED_SLOT'
        );

        const other = fixture();
        let foreign: CoreCategoricalTerm | undefined;
        other.emdash.displayedTransforLambda(
            'k',
            other.FF,
            other.GG,
            k => {
                foreign = component(other.emdash, other.eta, k);
                return foreign;
            }
        );
        assert.throws(
            () => emdash.displayedTransforLambda(
                'j',
                FF,
                HH,
                j => emdash.composeCells(
                    component(emdash, theta, j),
                    foreign as CoreCategoricalTerm
                )
            ),
            error =>
                error instanceof CoreCategoricalFrontendError &&
                error.code === 'FOREIGN_TERM'
        );
    });

    it('fails closed outside the profile and for unsupported bodies',
        () => {
            const {
                emdash,
                FF,
                GG,
                eta
            } = fixture();
            const legacy = new CoreCategoricalProgram({
                profile: 'fibred-binder-1'
            });
            assert.throws(
                () => legacy.composeCells(eta, eta),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'UNAVAILABLE_FIBRED_TRANSFD'
            );
            assert.throws(
                () => emdash.composeCells(eta, eta),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
            );
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
        });

    it('preserves the direct coherent eta route unchanged', () => {
        const {
            emdash,
            FF,
            GG,
            eta
        } = fixture();
        const abstraction = emdash.displayedTransforLambda(
            'k',
            FF,
            GG,
            k => component(emdash, eta, k)
        );
        assert.equal(
            emdash.compare(abstraction, eta).status,
            'equal'
        );
        const evidence =
            emdash.inspect(abstraction).abstractions.at(-1);
        assert.equal(
            evidence?.rule,
            'categorical.displayed-transfor-eta'
        );
        assert.deepEqual(
            evidence?.dependentPrerequisites,
            ['displayed-transfor-component-capped']
        );
    });

    it('inherits the D-061 transfer closure without a new owner or browser promotion',
        () => {
        const transfer =
            compileCoreCategoricalFibredTransfdTransfer();
        assert.equal(
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
                .declarationCount,
            8
        );
        assert.equal(transfer.runtime.rules.length, 17);
        assert.equal(
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
                .newMathematicalOwnerCount,
            0
        );
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /composeCells|identityCell|typed-cell-(?:composition|identity)/u
        );
    });
});
