/**
 * Executable FIBRED-GRADUATE-1 proposal evidence.
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
    CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL,
    CoreCategoricalFibredGraduationProposalError,
    validateCoreCategoricalFibredGraduationProposal
} from '../src/v3_2';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL
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
        CoreCategoricalFibredGraduationProposalError['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCoreCategoricalFibredGraduationProposal(proposal),
        error =>
            error instanceof
                CoreCategoricalFibredGraduationProposalError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 FIBRED-GRADUATE-1 proposal', () => {
    it('recommends only the demonstrated qualified architecture', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL;
        assert.equal(
            proposal.reviewGate,
            'H-DTTLF-USABILITY-FIBRED-GRADUATE'
        );
        assert.equal(proposal.decisionId, 'D-DTTLF-USABILITY-008');
        assert.equal(
            proposal.recommendation.mechanicallyScalableWithinScope,
            true
        );
        assert.equal(
            proposal.recommendation
                .automaticWholeDevelopmentImportClaimed,
            false
        );
        assert.equal(
            proposal.recommendation.generalDisplayedBracketComplete,
            false
        );
    });

    it('pins the dependency-aware callback-to-Core pipeline', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL;
        assert.equal(proposal.compilationPipeline.length, 8);
        assert.deepEqual(
            proposal.demonstratedFrontendEnvelope.dependencyPlanning,
            [
                'finite-ordered-contexts',
                'genuine-dependency-chains',
                'independent-sibling-blocks',
                'sequential-pullback-intent',
                'grouped-displayed-product-intent',
                'dependency-sensitive-exchange-rejection'
            ]
        );
        assert.equal(
            proposal.demonstratedFrontendEnvelope.displayedBinders
                .includes('fd-identity-eta-and-finite-composition'),
            true
        );
        assert.equal(
            proposal.demonstratedFrontendEnvelope.dependentTarget
                .includes('genuinely-fibre-dependent-target-family'),
            true
        );
    });

    it('measures seven generic transfer closures without deduplicating', () => {
        const evidence =
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL
                .transferEvidence;
        assert.equal(evidence.rows.length, 7);
        assert.deepEqual(evidence.cumulativeSliceCounts, {
            representativeSlices: 7,
            declarationSlots: 36,
            runtimeRuleSlots: 69,
            proofRuleSlots: 3,
            newMathematicalOwners: 4,
            newMathematicalRuntimeRules: 15
        });
        assert.match(evidence.accounting, /not-unique-library-counts/u);
        assert.equal(
            evidence.rows.every(row => row.genericEnginesOnly),
            true
        );
    });

    it('separates generic transfer reuse from mathematical additions', () => {
        const evidence =
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL
                .transferEvidence;
        assert.equal(evidence.perOwnerCheckerBranchesAdded, 0);
        assert.equal(evidence.perOwnerEvaluatorBranchesAdded, 0);
        assert.equal(evidence.externalSubjectOracleRequired, false);
        assert.equal(
            evidence.genericMechanismsExercised.includes(
                'proof-assisted-runtime-subject-validation'
            ),
            true
        );
        assert.equal(
            evidence.genericMechanismsExercised.includes(
                'typed-pattern-wildcard-inferred-slots'
            ),
            true
        );
        assert.equal(
            evidence.entireRemainingCorpusThroughputBenchmarked,
            false
        );
    });

    it('retains the exact frontend and mathematical gaps', () => {
        const gaps =
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL
                .residualGaps;
        assert.equal(
            gaps.frontendAndErgonomics.includes(
                'general-dependent-displayed-bracket-and-coherence-synthesis'
            ),
            true
        );
        assert.equal(
            gaps.mathematicalOwnerOrTheoremWork.includes(
                'sigma-introduction-arrow-action'
            ),
            true
        );
        assert.equal(
            gaps.mathematicalOwnerOrTheoremWork.includes(
                'generic-total-category-pullback-or-comparison'
            ),
            true
        );
        assert.equal(
            gaps.mathematicalOwnerOrTheoremWork.includes(
                'groupoidal-specialization-and-closure'
            ),
            true
        );
    });

    it('keeps direct typed acquisition primary and parsing optional', () => {
        const boundary =
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL
                .acquisitionBoundary;
        assert.equal(
            boundary.default,
            'direct-typed-typescript-transcription-or-construction'
        );
        assert.equal(
            boundary.manualOrAgentTranscriptionFeasibleInPrinciple,
            true
        );
        assert.equal(
            boundary.lambdapiStringParserArchitecturallyRequired,
            false
        );
        assert.equal(boundary.bulkTransferAuthorizedByGraduation, false);
    });

    it('adds no semantic or product authority and stays root-only', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL;
        assert.equal(
            Object.entries(proposal.decisionEffects)
                .filter(([key]) => key !==
                    'recordsQualifiedArchitectureGraduation' &&
                    key !== 'nextImplementationStillRequiresBoundedPlanRow')
                .every(([, value]) => value === false),
            true
        );
        assert.equal(proposal.trustBoundary.browserEntryPoint, 'excluded');
        assert.equal(proposal.trustBoundary.proposalVisibility, 'root-only');
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_fibred_graduation|FIBRED-GRADUATE/u
        );
    });

    it('asks one exact qualified yes-or-revise question', () => {
        const proposal =
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL;
        assert.match(
            proposal.decisionQuestion,
            /^Approve H-DTTLF-USABILITY-FIBRED-GRADUATE\/D-DTTLF-/u
        );
        assert.match(
            proposal.decisionQuestion,
            /adds no semantic owner or rule/u
        );
        assert.match(
            proposal.decisionQuestion,
            /no profile promotion or bulk transfer/u
        );
    });

    it('is deeply frozen and fails closed on drift', () => {
        assertDeepFrozen(
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL
        );
        assertProposalError(
            proposal => {
                proposal.transferEvidence.rows[0].runtimeRuleSlots = 24;
            },
            'FIBRED_GRADUATION_EVIDENCE_DRIFT'
        );
        assertProposalError(
            proposal => {
                proposal.decisionEffects.addsLambdapiOwnerOrRule = true;
            },
            'FIBRED_GRADUATION_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                proposal.recommendation
                    .automaticWholeDevelopmentImportClaimed = true;
            },
            'FIBRED_GRADUATION_RECOMMENDATION_DRIFT'
        );
    });
});
