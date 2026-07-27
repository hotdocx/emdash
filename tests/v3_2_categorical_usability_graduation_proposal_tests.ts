/**
 * Executable USABILITY-GRADUATE-1 architecture proposal evidence.
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
    CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL,
    CoreCategoricalUsabilityGraduationProposalError,
    validateCoreCategoricalUsabilityGraduationProposal
} from '../src/v3_2';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const assertProposalError = (
    mutate: (proposal: any) => void,
    expected:
        CoreCategoricalUsabilityGraduationProposalError['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCoreCategoricalUsabilityGraduationProposal(
            proposal
        ),
        error =>
            error instanceof
                CoreCategoricalUsabilityGraduationProposalError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 USABILITY-GRADUATE-1 proposal', () => {
    it('recommends only the exact qualified first-order envelope', () => {
        const proposal =
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL;
        assert.equal(proposal.revision, 'USABILITY-GRADUATE-1');
        assert.equal(
            proposal.status,
            'proposal-awaiting-h-dttlf-usability-graduate'
        );
        assert.equal(
            proposal.recommendation.architectureEnvelope,
            'outer-lf-plus-ordinary-bracket-plus-indexed-section-eta'
        );
        assert.equal(
            proposal.recommendation
                .mechanicallyReusableWithinEnvelope,
            true
        );
        assert.equal(
            proposal.recommendation.generalDependentBracketImplemented,
            false
        );
        assert.equal(
            proposal.recommendation.authorityAuthorized,
            false
        );
    });

    it('pins the callback-to-Core pipeline and implemented corpus', () => {
        const proposal =
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL;
        assert.deepEqual(proposal.compilationPipeline, [
            'one-shot-typed-typescript-callback',
            'opaque-slot-identities-and-classifiers',
            'immutable-first-order-locally-nameless-contextual-ir',
            'classifier-argument-expected-shape-selection',
            'categorical-bracket-or-qualified-dependent-eta-lowering',
            'backend-neutral-explicit-core',
            'generic-typescript-lf-infer-check-evaluate',
            'bounded-lambdapi-conformance'
        ]);
        assert.equal(
            proposal.implementedEnvelope
                .ordinaryCategorical.length,
            8
        );
        assert.equal(
            proposal.implementedEnvelope.indexedDisplayed.length,
            4
        );
        assert.equal(
            proposal.implementedEnvelope
                .facadeApplicationSelection.length,
            6
        );
        assert.deepEqual(proposal.abstractionCoverage, {
            outerLf:
                'available-general-dependent-lambda-pi',
            ordinaryFunctorial:
                'implemented-first-order-structural-bracket',
            naturalIndexed:
                'implemented-direct-slot-section-eta-only',
            objectOnly:
                'deferred-capability-and-notation-review'
        });
        assert.deepEqual(
            proposal.surfaceApplicationPartition,
            {
                eligibleOrQualified: [
                    'outer-lf-call',
                    'functor-object',
                    'functor-hom-full',
                    'functor-hom-capped',
                    'transfor-component-full',
                    'transfor-component-capped',
                    'section-object-evaluation',
                    'displayed-functor-fibre',
                    'displayed-functor-transport'
                ],
                reservedNaturality: [
                    'transfor-hom-full',
                    'transfor-hom-capped'
                ],
                activeButUntransferred: [
                    'section-hom-full',
                    'section-hom-capped',
                    'displayed-transfor-component-full',
                    'displayed-transfor-component-capped'
                ],
                inactiveAuthority: [
                    'displayed-functor-laxity'
                ],
                totalApplicationJudgments: 16
            }
        );
        assert.equal(
            proposal.implementedEnvelope
                .checkerOrEvaluatorOwnerSpecialCases,
            0
        );
    });

    it('states the exact mechanical reuse boundary', () => {
        const reuse =
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL
                .mechanicalReuse;
        assert.equal(
            reuse.ordinaryWithinCurrentIr,
            'typed-program-data-and-contextual-wiring-only'
        );
        assert.equal(
            reuse.indexedEtaWithinCurrentIr,
            'family-section-and-program-data-only'
        );
        assert.equal(reuse.newCheckerAlgorithmRequiredWithinEnvelope, false);
        assert.equal(
            reuse.newEvaluatorAlgorithmRequiredWithinEnvelope,
            false
        );
    });

    it('separates active transfers from mathematical authority gaps', () => {
        const proposal =
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL;
        assert.deepEqual(
            proposal.activeButUntransferred.map(entry => [
                entry.target,
                entry.authorityName
            ]),
            [
                ['section-hom-full', 'piapp1_func'],
                ['section-hom-capped', 'piapp1_fapp0'],
                [
                    'displayed-transfor-component-full',
                    'tdapp0_func'
                ],
                [
                    'displayed-transfor-component-capped',
                    'tdapp0_fapp0'
                ]
            ]
        );
        assert.deepEqual(proposal.authorityGaps, [
            {
                target: 'displayed-functor-laxity',
                authorityName: 'functord_laxity_transf',
                state: 'deliberately-inactive'
            },
            {
                target: 'general-displayed-bracket-basis',
                authorityName: 'no-qualified-complete-owner-basis',
                state: 'requires-consumer-led-owner-position-review'
            }
        ]);
    });

    it('withholds general dependent and whole-transfer claims', () => {
        const proposal =
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL;
        assert.equal(
            proposal.frontendAlgorithmGaps.includes(
                'general-non-eta-dependent-bracket-abstraction'
            ),
            true
        );
        assert.deepEqual(proposal.claimBoundary, {
            frontendArchitecture:
                'qualified-first-order-envelope-only',
            wholeDevelopmentTransfer: 'withheld',
            completeDisplayedStructuralLogic: 'withheld',
            completeGroupoidalDtt: 'withheld',
            standaloneSubjectReduction: 'withheld',
            termination: 'withheld',
            confluence: 'withheld',
            performance: 'withheld',
            finalTextualSyntax: 'withheld'
        });
    });

    it('keeps acquisition, parsing, notation, and product separate', () => {
        const proposal =
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL;
        assert.deepEqual(proposal.separateDeferredWork, {
            libraryCoverage:
                'measured-70-root-plus-83-extension-closure',
            acquisition:
                'direct-typed-default-parser-or-generator-only-if-measured',
            sourceNotation:
                'natural-settled-functorial-and-object-only-open',
            stringParser: 'optional-and-deferred',
            groupoidalClosure: 'separate-lambdapi-first-plan',
            browserPromotion: 'separate-product-gate'
        });
        assert.equal(
            proposal.nextWorkPolicy
                .graduationApprovalResumesBulkTransferAutomatically,
            false
        );
    });

    it('preserves the trust boundary and stays out of the browser', () => {
        const proposal =
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL;
        assert.equal(
            proposal.trustBoundary.productionLambdapiDependency,
            false
        );
        assert.equal(
            proposal.trustBoundary.frozenMvpProfile,
            'unchanged'
        );
        assert.equal(
            proposal.trustBoundary.reviewedDirectedProfile,
            'unchanged'
        );
        assert.equal(
            proposal.trustBoundary.browserEntryPoint,
            'excluded'
        );
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_usability_graduation|USABILITY_GRADUATE/u
        );
    });

    it('asks one exact yes-or-revise human question', () => {
        const proposal =
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL;
        assert.equal(
            proposal.reviewGate,
            'H-DTTLF-USABILITY-GRADUATE'
        );
        assert.equal(
            proposal.decisionId,
            'D-DTTLF-USABILITY-002'
        );
        assert.match(
            proposal.decisionQuestion,
            /^Approve H-DTTLF-USABILITY-GRADUATE\//u
        );
        assert.match(
            proposal.decisionQuestion,
            /only for the exact outer-LF, ordinary bracket, and indexed/u
        );
    });

    it('is deeply frozen and validates against current owners', () => {
        assertDeepFrozen(
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL
        );
        assert.equal(
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL
                .validation.rootGate,
            '655-tests-614-pass-41-opt-in-skip'
        );
        assert.doesNotThrow(
            () => validateCoreCategoricalUsabilityGraduationProposal()
        );
    });

    it('rejects implementation, owner, and recommendation drift', () => {
        assertProposalError(
            proposal => {
                proposal.validation.programRevision =
                    'USABILITY-2A0-CATEGORICAL-PROGRAM-1';
            },
            'GRADUATION_IMPLEMENTATION_DRIFT'
        );
        assertProposalError(
            proposal => {
                proposal.surfaceApplicationPartition
                    .activeButUntransferred.pop();
            },
            'GRADUATION_IMPLEMENTATION_DRIFT'
        );
        assertProposalError(
            proposal => {
                proposal.activeButUntransferred[1].authorityName =
                    'invented_pi_action';
            },
            'GRADUATION_OWNER_BOUNDARY_DRIFT'
        );
        assertProposalError(
            proposal => {
                proposal.recommendation.authorityAuthorized = true;
            },
            'GRADUATION_RECOMMENDATION_DRIFT'
        );
        assertProposalError(
            proposal => {
                proposal.frontendAlgorithmGaps.pop();
            },
            'GRADUATION_RECOMMENDATION_DRIFT'
        );
    });
});
