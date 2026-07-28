/**
 * End-user FIBRED-BINDER-1 direct displayed-functor abstraction.
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

const program = (
    sourceFile = 'tests/fixtures/categorical-fibred-binder.ts'
) => new CoreCategoricalProgram({
    sourceFile,
    profile: 'fibred-binder-1'
});

const fixture = () => {
    const emdash = program();
    const K = emdash.category('K', { line: 1 });
    const E = emdash.displayedFamily('E', K, { line: 2 });
    const D = emdash.displayedFamily('D', K, { line: 3 });
    const Q = emdash.displayedFamily('Q', K, { line: 4 });
    const FF = emdash.displayedFunctor('FF', E, D, { line: 5 });
    const GG = emdash.displayedFunctor('GG', D, Q, { line: 6 });
    const x = emdash.object('x', K, { line: 7 });
    return { emdash, K, E, D, Q, FF, GG, x };
};

describe(
    'FIBRED-BINDER-1 direct displayed-functor abstraction',
    () => {
        it('lowers identity through the active displayed identity', () => {
            const { emdash, E, x } = fixture();
            let callbacks = 0;
            const identity = emdash.displayedFunctorLambda(
                'a',
                E,
                E,
                a => {
                    callbacks += 1;
                    return a;
                },
                {
                    variation: 'functorial',
                    dependency: 'displayed',
                    source: { line: 12 }
                }
            );
            assert.equal(callbacks, 1);
            const inspection = emdash.inspect(identity);
            const evidence = inspection.abstractions.at(-1);
            assert.equal(
                evidence?.rule,
                'categorical.displayed-functor-identity'
            );
            if (
                evidence?.rule !==
                    'categorical.displayed-functor-identity'
            ) {
                assert.fail('Missing displayed identity evidence');
            }
            assert.equal(evidence.chainLength, 0);
            assert.equal(evidence.body.tag, 'slot-reference');
            assert.equal(evidence.body.type.tag, 'indexed-object');
            if (evidence.body.type.tag !== 'indexed-object') {
                assert.fail('Identity input lost its indexed classifier');
            }
            assert.equal(evidence.body.index, 0);
            assert.equal(evidence.body.type.index, 1);
            assert.deepEqual(
                evidence.dependentPrerequisites,
                [
                    'sigma-projection-pullback',
                    'sigma-pi-uncurrying-proof',
                    'displayed-identity'
                ]
            );

            const fibreIdentity = emdash.apply(identity, x, {
                expectedShape: 'fibre-functor',
                source: { line: 20 }
            });
            const expected = emdash.identityFunctor(
                emdash.fibre(E, x),
                { line: 21 }
            );
            assert.equal(
                emdash.compare(fibreIdentity, expected, 4_000).status,
                'equal'
            );
            assert.match(
                emdash.compile(identity).explicitCore,
                /displayed-identity/u
            );
        });

        it('eta-lowers FF[a] to FF while retaining nested body evidence', () => {
            const { emdash, E, D, FF } = fixture();
            const eta = emdash.displayedFunctorLambda(
                'a',
                E,
                D,
                a => emdash.apply(FF, a, {
                    expectedShape: 'object-value',
                    source: { line: 31 }
                }),
                { source: { line: 30 } }
            );
            assert.equal(emdash.compare(eta, FF).status, 'equal');
            const evidence = emdash.inspect(eta).abstractions.at(-1);
            assert.equal(
                evidence?.rule,
                'categorical.displayed-functor-eta'
            );
            if (
                evidence?.rule !==
                    'categorical.displayed-functor-eta'
            ) {
                assert.fail('Missing displayed eta evidence');
            }
            assert.equal(evidence.chainLength, 1);
            assert.equal(evidence.body.tag, 'typed-application');
            if (evidence.body.tag !== 'typed-application') {
                assert.fail('Displayed eta lost its nested application');
            }
            assert.equal(
                evidence.body.judgmentId,
                'indexed-fibre-functor.object'
            );
            assert.equal(
                evidence.body.subject.tag,
                'typed-application'
            );
            if (
                evidence.body.subject.tag !== 'typed-application'
            ) {
                assert.fail('Displayed eta lost its base projection');
            }
            assert.equal(
                evidence.body.subject.judgmentId,
                'displayed-functor.fibre'
            );
            assert.equal(
                evidence.body.subject.argument.tag,
                'slot-reference'
            );
            if (
                evidence.body.subject.argument.tag !==
                    'slot-reference'
            ) {
                assert.fail('Displayed eta lost its hidden base slot');
            }
            assert.equal(evidence.body.subject.argument.index, 1);
            assert.equal(Object.isFrozen(evidence.body), true);
        });

        it('lowers a finite displayed composition chain through comp_fapp0', () => {
            const { emdash, E, D, Q, FF, GG, x } = fixture();
            const composition = emdash.displayedFunctorLambda(
                'a',
                E,
                Q,
                a => emdash.apply(
                    GG,
                    emdash.apply(FF, a, {
                        expectedShape: 'object-value'
                    }),
                    { expectedShape: 'object-value' }
                ),
                { source: { line: 50 } }
            );
            const evidence =
                emdash.inspect(composition).abstractions.at(-1);
            assert.equal(
                evidence?.rule,
                'categorical.displayed-functor-composition'
            );
            if (
                evidence?.rule !==
                    'categorical.displayed-functor-composition'
            ) {
                assert.fail('Missing displayed composition evidence');
            }
            assert.equal(evidence.chainLength, 2);
            assert.deepEqual(
                evidence.dependentPrerequisites,
                [
                    'sigma-projection-pullback',
                    'sigma-pi-uncurrying-proof',
                    'generic-category-composition',
                    'displayed-hom-classifier-reduction'
                ]
            );
            assert.match(
                emdash.compile(composition).explicitCore,
                /generic-category-composition/u
            );

            const atX = emdash.apply(composition, x, {
                expectedShape: 'fibre-functor'
            });
            const Ex = emdash.fibre(E, x);
            const FFx = emdash.apply(FF, x, {
                expectedShape: 'fibre-functor'
            });
            const GGx = emdash.apply(GG, x, {
                expectedShape: 'fibre-functor'
            });
            const u = emdash.object('u', Ex);
            const computed = emdash.apply(atX, u);
            const expected = emdash.apply(
                GGx,
                emdash.apply(FFx, u)
            );
            assert.equal(
                emdash.compare(computed, expected, 8_000).status,
                'equal'
            );
            assert.equal(
                emdash.compile(composition).surfaceType.tag,
                'displayed-functor'
            );
        });

        it('proves direct/nested compatibility without runtime collapse', () => {
            const { emdash, E, D } = fixture();
            const compatibility =
                emdash.displayedFunctorClassifierCompatibility(
                    E,
                    D
                );
            assert.equal(compatibility.proofTime.status, 'solved');
            assert.equal(compatibility.runtime.status, 'not-equal');
            assert.equal(
                compatibility.proofTime.ruleApplications[0]?.ruleId,
                'stress.sigma-pi.uncurrying'
            );
            assert.match(
                compatibility.explicitDirectClassifier,
                /displayed-functor-category/u
            );
            assert.match(
                compatibility.explicitNestedClassifier,
                /sigma-projection-pullback/u
            );
            assert.equal(compatibility.preservesPresentations, true);
        });

        it('fails closed outside the profile and on malformed bodies', () => {
            const legacy = new CoreCategoricalProgram();
            const legacyK = legacy.category('LegacyK');
            const legacyE = legacy.displayedFamily(
                'LegacyE',
                legacyK
            );
            assert.throws(
                () => legacy.displayedFunctorLambda(
                    'a',
                    legacyE,
                    legacyE,
                    a => a
                ),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'UNAVAILABLE_FIBRED_BINDER'
            );

            const { emdash, E, D, Q, FF } = fixture();
            assert.throws(
                () => emdash.displayedFunctorLambda(
                    'a',
                    E,
                    D,
                    a => a
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'CLASSIFIER_ARGUMENT_MISMATCH' &&
                    /target family/u.test(error.message)
            );
            const wrong = emdash.displayedFunctor('wrong', Q, D);
            assert.throws(
                () => emdash.displayedFunctorLambda(
                    'a',
                    E,
                    D,
                    a => emdash.apply(wrong, a)
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
            );
            assert.throws(
                () => emdash.displayedFunctorLambda(
                    'a',
                    E,
                    D,
                    a => emdash.apply(FF, a),
                    { variation: 'natural' }
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'CLASSIFIER_ARGUMENT_MISMATCH'
            );
        });

        it('rejects escaped and foreign direct fibre slots', () => {
            const { emdash, E, D, FF } = fixture();
            let escaped: CoreCategoricalSlotToken | undefined;
            emdash.displayedFunctorLambda(
                'a',
                E,
                E,
                a => {
                    escaped = a;
                    return a;
                }
            );
            assert.notEqual(escaped, undefined);
            assert.throws(
                () => emdash.apply(
                    FF,
                    escaped as CoreCategoricalSlotToken
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'ESCAPED_SLOT'
            );

            const foreign = program('foreign-fibred-binder.ts');
            const foreignK = foreign.category('ForeignK');
            const foreignE = foreign.displayedFamily(
                'ForeignE',
                foreignK
            );
            const foreignIdentity =
                foreign.displayedFunctorLambda(
                    'z',
                    foreignE,
                    foreignE,
                    z => z
                );
            assert.throws(
                () => emdash.displayedFunctorLambda(
                    'a',
                    E,
                    D,
                    _a => foreignIdentity
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'FOREIGN_TERM'
            );
        });
    }
);
