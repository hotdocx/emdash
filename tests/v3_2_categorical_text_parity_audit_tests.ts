/**
 * Focused executable SYNTAX-PARITY-0A inventory tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_PARITY_AUDIT,
    CORE_CATEGORICAL_TEXT_PARITY_METHOD_COVERAGE,
    CoreCategoricalProgram,
    CoreCategoricalTextError,
    CoreCategoricalTextParityAuditError,
    elaborateCoreCategoricalText,
    validateCoreCategoricalTextParityAudit
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

const cloneAudit = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_TEXT_PARITY_AUDIT
));

const assertAuditError = (
    mutate: (audit: any) => void,
    code: CoreCategoricalTextParityAuditError['code']
): void => {
    const audit = cloneAudit();
    mutate(audit);
    assert.throws(
        () => validateCoreCategoricalTextParityAudit(audit),
        error =>
            error instanceof CoreCategoricalTextParityAuditError &&
            error.code === code
    );
};

describe('SYNTAX-PARITY-0A executable capability inventory', () => {
    it('classifies every public categorical program method exactly once', () => {
        const audit = CORE_CATEGORICAL_TEXT_PARITY_AUDIT;
        const methods = audit.capabilities.flatMap(
            capability => capability.apiMethods
        );
        assert.equal(CORE_CATEGORICAL_TEXT_PARITY_METHOD_COVERAGE, true);
        assert.equal(methods.length, 68);
        assert.equal(new Set(methods).size, 68);
        assert.equal(audit.capabilities.length, 14);
        assert.deepEqual(audit.measuredCoverage.classificationRows, {
            alreadyTextComplete: 1,
            mechanicalSyntaxRoute: 1,
            typedResolverSeam: 9,
            semanticCapabilityAbsent: 1,
            deliberatelyNonTextualHostBehavior: 2
        });
    });

    it('retains ^f as the only implemented mode while parsing later modes', () => {
        const program = new CoreCategoricalProgram({
            sourceFile: 'tests/fixtures/text-parity-audit.emdash'
        });
        const A = program.category('parity_A');
        const B = program.category('parity_B');
        const b = program.object('parity_b', B);
        for (const mode of ['n', 'fd', 'nd']) {
            assert.throws(
                () => elaborateCoreCategoricalText(program, {
                    source: `λ^${mode} x. b`,
                    sourceFile:
                        'tests/fixtures/text-parity-audit.emdash',
                    environment: [
                        {
                            name: 'b',
                            kind: 'term',
                            value: b
                        }
                    ],
                    expected: {
                        kind: 'ordinary-functor',
                        source: A,
                        target: B
                    }
                }),
                error =>
                    error instanceof CoreCategoricalTextError &&
                    error.code === 'UNSUPPORTED_BINDER_MODE' &&
                    error.phase === 'resolution' &&
                    error.span.start.line === 1
            );
        }
    });

    it('executes every direct semantic target selected by the first proposal',
        () => {
            const natural = new CoreCategoricalProgram({
                profile: 'usability-dependent-1a'
            });
            const K = natural.category('parity_n_K');
            const E = natural.displayedFamily('parity_n_E', K);
            const D = natural.displayedFamily('parity_n_D', K);
            const FF = natural.displayedFunctor('parity_n_FF', E, D);
            const s = natural.section('parity_n_s', E);
            const naturalTerm = natural.dependentLambda(
                'k',
                D,
                k => natural.apply(
                    natural.apply(FF, k, {
                        expectedShape: 'fibre-functor'
                    }),
                    natural.apply(s, k, {
                        expectedShape: 'dependent-object'
                    }),
                    { expectedShape: 'object-value' }
                )
            );
            assert.equal(
                natural.inspect(naturalTerm).abstractions.at(-1)?.rule,
                'categorical.dependent-section-composition'
            );

            const functorial = new CoreCategoricalProgram({
                profile: 'fibred-binder-1'
            });
            const Kf = functorial.category('parity_fd_K');
            const Ef = functorial.displayedFamily('parity_fd_E', Kf);
            const Df = functorial.displayedFamily('parity_fd_D', Kf);
            const Qf = functorial.displayedFamily('parity_fd_Q', Kf);
            const Ff = functorial.displayedFunctor(
                'parity_fd_F',
                Ef,
                Df
            );
            const Gf = functorial.displayedFunctor(
                'parity_fd_G',
                Df,
                Qf
            );
            const functorialTerm = functorial.displayedFunctorLambda(
                'a',
                Ef,
                Qf,
                a => functorial.apply(
                    Gf,
                    functorial.apply(Ff, a, {
                        expectedShape: 'object-value'
                    }),
                    { expectedShape: 'object-value' }
                )
            );
            assert.equal(
                functorial.inspect(functorialTerm)
                    .abstractions.at(-1)?.rule,
                'categorical.displayed-functor-composition'
            );

            const displayedNatural = new CoreCategoricalProgram({
                profile: 'fibred-transfd-1'
            });
            const Kn = displayedNatural.category('parity_nd_K');
            const En = displayedNatural.displayedFamily(
                'parity_nd_E',
                Kn
            );
            const Dn = displayedNatural.displayedFamily(
                'parity_nd_D',
                Kn
            );
            const Fn = displayedNatural.displayedFunctor(
                'parity_nd_F',
                En,
                Dn
            );
            const Gn = displayedNatural.displayedFunctor(
                'parity_nd_G',
                En,
                Dn
            );
            const Hn = displayedNatural.displayedFunctor(
                'parity_nd_H',
                En,
                Dn
            );
            const eta = displayedNatural.displayedTransfor(
                'parity_nd_eta',
                Fn,
                Gn
            );
            const theta = displayedNatural.displayedTransfor(
                'parity_nd_theta',
                Gn,
                Hn
            );
            const displayedNaturalTerm =
                displayedNatural.displayedTransforLambda(
                    'k',
                    Fn,
                    Hn,
                    k => displayedNatural.composeCells(
                        displayedNatural.apply(theta, k, {
                            expectedShape: 'displayed-component'
                        }),
                        displayedNatural.apply(eta, k, {
                            expectedShape: 'displayed-component'
                        })
                    )
                );
            assert.equal(
                displayedNatural.inspect(displayedNaturalTerm)
                    .abstractions.at(-1)?.rule,
                'categorical.displayed-transfor-composition'
            );
        });

    it('freezes an exact modes-first proposal with later parity rows', () => {
        const proposal =
            CORE_CATEGORICAL_TEXT_PARITY_AUDIT.firstProposal;
        assert.equal(
            proposal.gate,
            'H-DTTLF-PRODUCT-SYNTAX-PARITY-01'
        );
        assert.equal(
            proposal.decision,
            'D-DTTLF-PRODUCT-SYNTAX-PARITY-001'
        );
        assert.deepEqual(proposal.selectedModes, ['n', 'fd', 'nd']);
        assert.deepEqual(proposal.requestContractAdditions.expectedKinds, [
            'dependent-section',
            'displayed-functor',
            'displayed-transfor'
        ]);
        assert.deepEqual(proposal.followingRows, [
            'SYNTAX-PARITY-1B-contexts-and-fibred-structure',
            'SYNTAX-PARITY-1C-remaining-mathematical-constructors',
            'SYNTAX-PARITY-GRADUATE-1'
        ]);
        assert.equal(
            proposal.exactPositiveSources[2],
            'λ^nd k : K. composeCells (theta k) (eta k)'
        );
    });

    it('is deeply frozen, validates, and installs no behavior', () => {
        assertDeepFrozen(CORE_CATEGORICAL_TEXT_PARITY_AUDIT);
        assert.doesNotThrow(
            () => validateCoreCategoricalTextParityAudit()
        );
        assert.equal(
            Object.values(
                CORE_CATEGORICAL_TEXT_PARITY_AUDIT.semanticDelta
            ).some(value => value !== 0),
            false
        );
    });

    it('fails closed on prerequisite, coverage, proposal, and boundary drift',
        () => {
            assertAuditError(
                audit => {
                    audit.prerequisite.textRevision = 'stale';
                },
                'TEXT_PARITY_PREREQUISITE_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.capabilities[0].apiMethods.push('apply');
                },
                'TEXT_PARITY_METHOD_COVERAGE_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.firstProposal.selectedModes = ['n', 'fd'];
                },
                'TEXT_PARITY_PROPOSAL_DRIFT'
            );
            assertAuditError(
                audit => {
                    audit.semanticDelta.resolverBranches = 1;
                },
                'TEXT_PARITY_BOUNDARY_DRIFT'
            );
        });
});
