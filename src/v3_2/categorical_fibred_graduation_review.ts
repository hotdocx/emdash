/**
 * Separate immutable delegated-approval record for
 * H-DTTLF-USABILITY-FIBRED-GRADUATE/D-DTTLF-USABILITY-008.
 *
 * The pre-review FIBRED-GRADUATE-1 proposal remains unchanged and
 * non-self-authorizing. This artifact records the user's plan-specific
 * unattended delegation after no immediate human response to the exact
 * presented proposal. It installs no semantic authority and selects no
 * successor.
 */

import {
    CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL,
    CoreCategoricalFibredGraduationProposalInput,
    validateCoreCategoricalFibredGraduationProposal
} from './categorical_fibred_graduation_proposal';

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const proposal = CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL;

const rawReview = {
    revision: 'FIBRED-GRADUATE-1-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-DTTLF-USABILITY-FIBRED-GRADUATE',
        decisionId: 'D-DTTLF-USABILITY-008',
        decision: 'approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-response-after-presented-frozen-proposal',
        recordedOn: '2026-07-28',
        humanDecisionSupersedes: true,
        decisionEvidence:
            'The user authorized the coding agent to approve a frozen ' +
            'proposal during unattended continuation when no immediate ' +
            'human response follows, provided the Git checkpoint SOP is ' +
            'followed'
    },
    /**
     * Immutable snapshot of the exact pre-review proposal. Its
     * `semanticAuthorityAuthorized: false` field remains historical
     * evidence and is not mutated by approval.
     */
    recommendation:
        cloneData(proposal) as
            CoreCategoricalFibredGraduationProposalInput,
    authorization: {
        qualifiedArchitecture:
            'settled-demonstrated-existing-authority-envelope',
        settledClaim:
            proposal.recommendation.settledClaim,
        scope: proposal.recommendation.scope,
        mechanicallyScalableWithinScope: true,
        automaticWholeDevelopmentImportAuthorized: false,
        generalDisplayedBracketCompletionAuthorized: false,
        missingMathematicalOwnerWorkDeclaredComplete: false,
        additionalSemanticOwnerOrRuleAuthorized: false,
        browserOrDeployedProfilePromotionAuthorized: false,
        bulkTransferResumptionAuthorized: false,
        parserOrGeneratorSelected: false,
        successorImplementationAuthorized: false
    },
    retainedBoundaries: {
        settledArchitecture:
            cloneData(proposal.settledArchitecture),
        demonstratedFrontendEnvelope:
            cloneData(proposal.demonstratedFrontendEnvelope),
        transferEvidence:
            cloneData(proposal.transferEvidence),
        residualGaps:
            cloneData(proposal.residualGaps),
        acquisitionBoundary:
            cloneData(proposal.acquisitionBoundary),
        trustBoundary:
            cloneData(proposal.trustBoundary),
        claimBoundary:
            cloneData(proposal.claimBoundary),
        decisionEffects:
            cloneData(proposal.decisionEffects)
    },
    validation: {
        proposalRevision: 'FIBRED-GRADUATE-1-PROPOSAL-1',
        proposalCheckpoint:
            '517e64e67a411412b0300f05f910b8eb25b5f395',
        proposalLedgerCheckpoint:
            '6b38abe6aca557f6aed70484af6a6f7790c2e996',
        focusedProposalGate: '9-tests-pass',
        rootProposalGate:
            '804-tests-758-pass-46-intentional-skip-zero-fail',
        focusedReviewGate: '9-tests-pass',
        rootReviewGate:
            '813-tests-767-pass-46-intentional-skip-zero-fail',
        liveConformanceGate:
            '19-judgments-global-60-second-pass',
        activeKernelGate:
            '41-files-strict-0-47-29-audit-and-catalog-fresh'
    },
    gitBoundary: {
        rollbackEvidence:
            'proposal-and-ledger-checkpoints-recorded-before-delegation',
        localCheckpointRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false
    },
    nonEffects: [
        'does-not-mutate-the-pre-review-proposal',
        'does-not-add-or-authorize-a-semantic-owner-or-rule',
        'does-not-complete-general-displayed-bracket-or-coherence-synthesis',
        'does-not-complete-missing-arrow-total-or-groupoidal-mathematics',
        'does-not-claim-automatic-whole-development-transfer',
        'does-not-resume-the-remaining-library-inventory',
        'does-not-select-a-parser-generator-or-final-notation',
        'does-not-promote-a-browser-default-or-deployed-profile',
        'does-not-close-withheld-metatheory-or-performance-work',
        'does-not-authorize-a-successor-implementation',
        'does-not-broaden-local-checkpoint-git-authority'
    ],
    nextDependencyState:
        'requires-separate-bounded-successor-selection'
} as const;

export type CoreCategoricalFibredGraduationReviewInput =
    typeof rawReview;

export type CoreCategoricalFibredGraduationReviewErrorCode =
    | 'FIBRED_GRADUATION_REVIEW_DECISION_DRIFT'
    | 'FIBRED_GRADUATION_REVIEW_PREREQUISITE_DRIFT'
    | 'FIBRED_GRADUATION_REVIEW_PROPOSAL_DRIFT'
    | 'FIBRED_GRADUATION_REVIEW_AUTHORIZATION_DRIFT';

export class CoreCategoricalFibredGraduationReviewError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalFibredGraduationReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalFibredGraduationReviewError';
    }
}

export const CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW =
    deepFreeze(rawReview);

export function validateCoreCategoricalFibredGraduationReview(
    review: CoreCategoricalFibredGraduationReviewInput =
        CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW
): void {
    if (
        review.revision !== 'FIBRED-GRADUATE-1-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-FIBRED-GRADUATE' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-008' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-response-after-presented-frozen-proposal' ||
        review.approval.recordedOn !== '2026-07-28' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new CoreCategoricalFibredGraduationReviewError(
            'FIBRED_GRADUATION_REVIEW_DECISION_DRIFT',
            'The delegated review must preserve the exact D-DTTLF-' +
                'USABILITY-008 decision, authority, and supersession ' +
                'boundary'
        );
    }

    try {
        validateCoreCategoricalFibredGraduationProposal(proposal);
    } catch (error: unknown) {
        throw new CoreCategoricalFibredGraduationReviewError(
            'FIBRED_GRADUATION_REVIEW_PREREQUISITE_DRIFT',
            'The approved FIBRED-GRADUATE-1 proposal drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.recommendation
            .semanticAuthorityAuthorized !== false ||
        review.recommendation.recommendation
            .productProfilePromotionAuthorized !== false
    ) {
        throw new CoreCategoricalFibredGraduationReviewError(
            'FIBRED_GRADUATION_REVIEW_PROPOSAL_DRIFT',
            'The reviewed recommendation is not the exact immutable ' +
                'pre-review proposal'
        );
    }

    if (
        !review.authorization.mechanicallyScalableWithinScope ||
        review.authorization
            .automaticWholeDevelopmentImportAuthorized ||
        review.authorization
            .generalDisplayedBracketCompletionAuthorized ||
        review.authorization
            .missingMathematicalOwnerWorkDeclaredComplete ||
        review.authorization.additionalSemanticOwnerOrRuleAuthorized ||
        review.authorization
            .browserOrDeployedProfilePromotionAuthorized ||
        review.authorization.bulkTransferResumptionAuthorized ||
        review.authorization.parserOrGeneratorSelected ||
        review.authorization.successorImplementationAuthorized ||
        !review.gitBoundary.localCheckpointRequired ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        review.nextDependencyState !==
            'requires-separate-bounded-successor-selection'
    ) {
        throw new CoreCategoricalFibredGraduationReviewError(
            'FIBRED_GRADUATION_REVIEW_AUTHORIZATION_DRIFT',
            'The delegated approval exceeds its qualified architecture or ' +
                'Git boundary'
        );
    }

    if (
        !sameData(
            review.retainedBoundaries,
            rawReview.retainedBoundaries
        ) ||
        !sameData(review, rawReview)
    ) {
        throw new CoreCategoricalFibredGraduationReviewError(
            'FIBRED_GRADUATION_REVIEW_AUTHORIZATION_DRIFT',
            'The retained gaps, claims, or non-effects drifted'
        );
    }
}

validateCoreCategoricalFibredGraduationReview();
