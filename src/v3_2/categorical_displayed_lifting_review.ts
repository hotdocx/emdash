/**
 * Separate immutable delegated-approval record for
 * H-DTTLF-USABILITY-DISPLAYED-LIFTING-01/D-DTTLF-USABILITY-010.
 *
 * The pre-review DISPLAYED-LIFTING-0A proposal remains unchanged and
 * non-self-authorizing. This artifact records the user's plan-specific
 * unattended delegation after no immediate human response to the exact
 * presented proposal. It authorizes only the read-only DISPLAYED-EVAL-0B
 * owner-position and derived-construction investigation.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL,
    CoreCategoricalDisplayedLiftingProposalInput,
    validateCoreCategoricalDisplayedLiftingProposal
} from './categorical_displayed_lifting_proposal';

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

const proposal = CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL;

const rawReview = {
    revision: 'DISPLAYED-LIFTING-0A-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-DTTLF-USABILITY-DISPLAYED-LIFTING-01',
        decisionId: 'D-DTTLF-USABILITY-010',
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
     * Immutable snapshot of the exact pre-review proposal. Its pending
     * status remains historical evidence and is not mutated by approval.
     */
    recommendation:
        cloneData(proposal) as
            CoreCategoricalDisplayedLiftingProposalInput,
    authorization: {
        evidenceRow: 'DISPLAYED-EVAL-0B',
        evidenceRowAuthorized: true,
        investigationKind:
            'read-only-owner-position-and-derived-construction-probe',
        activeAuthorityInspectionAuthorized: true,
        boundedTemporaryLambdapiProbesAuthorized: true,
        profileMismatchIsolationAuthorized: true,
        resultMayFreezeExistingAuthorityProposal: true,
        resultMayFreezeMinimalOwnerProposal: true,
        semanticDisplayedLifting1AImplementationAuthorized: false,
        newLambdapiOrCoreOwnerAuthorized: false,
        newRuntimeOrProofRuleAuthorized: false,
        recursiveGrammarExtensionAuthorized: false,
        checkerOrSurfaceLayerAuthorized: false,
        profileJoinAuthorized: false,
        displayedChainImplementationAuthorized: false,
        generalNdCoherenceAuthorized: false,
        parserOrBulkTransferAuthorized: false,
        browserOrDeployedPromotionAuthorized: false
    },
    retainedBoundaries: {
        architectureCorrection:
            cloneData(proposal.architectureCorrection),
        migrationAssessment:
            cloneData(proposal.migrationAssessment),
        ordinaryMatrix:
            cloneData(proposal.ordinaryMatrix),
        displayedMatrix:
            cloneData(proposal.displayedMatrix),
        ownerAuditConclusion:
            cloneData(proposal.ownerAuditConclusion),
        recommendedNextRow:
            cloneData(proposal.recommendedNextRow),
        withheldRows:
            cloneData(proposal.withheldRows),
        semanticDelta:
            cloneData(proposal.semanticDelta),
        decisionEffects:
            cloneData(proposal.decisionEffects)
    },
    validation: {
        proposalRevision: 'DISPLAYED-LIFTING-0A-PROPOSAL-1',
        proposalCheckpoint:
            '29f2c5174c96c852f88a7a6ffa84c1ad502f21bd',
        proposalLedgerCheckpoint:
            '3c40fd2518e37c10f0e2eda30d4219189d59ed50',
        focusedProposalGate: '10-tests-pass',
        rootProposalGate:
            '851-tests-805-pass-46-intentional-skip-zero-fail',
        liveConformanceGate:
            '19-judgments-global-60-second-pass',
        activeKernelGate: 'bounded-make-check-pass',
        focusedReviewGate: '9-tests-required',
        rootReviewGate:
            '860-tests-814-pass-46-intentional-skip-zero-fail-required'
    },
    gitBoundary: {
        rollbackEvidence:
            'proposal-and-ledger-checkpoints-recorded-before-delegation',
        localCheckpointRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false,
        preservedTimeoutArtifactsUntouched: true
    },
    nonEffects: [
        'does-not-mutate-the-pre-review-proposal',
        'does-not-implement-displayed-lifting-1a',
        'does-not-add-or-authorize-a-lambdapi-owner-or-rule',
        'does-not-add-an-intrinsic-core-owner-or-checker-branch',
        'does-not-extend-the-recursive-contextual-grammar',
        'does-not-join-the-dependent-target-and-displayed-profiles',
        'does-not-authorize-displayed-chain-or-general-nd-work',
        'does-not-authorize-parser-acquisition-or-bulk-transfer',
        'does-not-authorize-browser-or-deployed-profile-promotion',
        'does-not-broaden-local-checkpoint-git-authority'
    ],
    nextDependencyState:
        'displayed-eval-0b-read-only-investigation-ready'
} as const;

export type CoreCategoricalDisplayedLiftingReviewInput =
    typeof rawReview;

export type CoreCategoricalDisplayedLiftingReviewErrorCode =
    | 'DISPLAYED_LIFTING_REVIEW_DECISION_DRIFT'
    | 'DISPLAYED_LIFTING_REVIEW_PREREQUISITE_DRIFT'
    | 'DISPLAYED_LIFTING_REVIEW_PROPOSAL_DRIFT'
    | 'DISPLAYED_LIFTING_REVIEW_AUTHORIZATION_DRIFT';

export class CoreCategoricalDisplayedLiftingReviewError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedLiftingReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDisplayedLiftingReviewError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW =
    deepFreeze(rawReview);

export function validateCoreCategoricalDisplayedLiftingReview(
    review: CoreCategoricalDisplayedLiftingReviewInput =
        CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW
): void {
    if (
        review.revision !== 'DISPLAYED-LIFTING-0A-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-DISPLAYED-LIFTING-01' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-010' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-response-after-presented-frozen-proposal' ||
        review.approval.recordedOn !== '2026-07-28' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new CoreCategoricalDisplayedLiftingReviewError(
            'DISPLAYED_LIFTING_REVIEW_DECISION_DRIFT',
            'The delegated review must preserve the exact D-DTTLF-' +
                'USABILITY-010 decision, authority, and supersession ' +
                'boundary'
        );
    }

    try {
        validateCoreCategoricalDisplayedLiftingProposal(proposal);
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedLiftingReviewError(
            'DISPLAYED_LIFTING_REVIEW_PREREQUISITE_DRIFT',
            'The approved DISPLAYED-LIFTING-0A proposal drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-lifting-01' ||
        review.recommendation.decisionId !==
            'D-DTTLF-USABILITY-010'
    ) {
        throw new CoreCategoricalDisplayedLiftingReviewError(
            'DISPLAYED_LIFTING_REVIEW_PROPOSAL_DRIFT',
            'The reviewed recommendation is not the exact immutable ' +
                'pre-review proposal'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.evidenceRow !== 'DISPLAYED-EVAL-0B' ||
        !authorization.evidenceRowAuthorized ||
        authorization.investigationKind !==
            'read-only-owner-position-and-derived-construction-probe' ||
        !authorization.activeAuthorityInspectionAuthorized ||
        !authorization.boundedTemporaryLambdapiProbesAuthorized ||
        !authorization.profileMismatchIsolationAuthorized ||
        !authorization.resultMayFreezeExistingAuthorityProposal ||
        !authorization.resultMayFreezeMinimalOwnerProposal ||
        authorization.semanticDisplayedLifting1AImplementationAuthorized ||
        authorization.newLambdapiOrCoreOwnerAuthorized ||
        authorization.newRuntimeOrProofRuleAuthorized ||
        authorization.recursiveGrammarExtensionAuthorized ||
        authorization.checkerOrSurfaceLayerAuthorized ||
        authorization.profileJoinAuthorized ||
        authorization.displayedChainImplementationAuthorized ||
        authorization.generalNdCoherenceAuthorized ||
        authorization.parserOrBulkTransferAuthorized ||
        authorization.browserOrDeployedPromotionAuthorized ||
        !review.gitBoundary.localCheckpointRequired ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        !review.gitBoundary.preservedTimeoutArtifactsUntouched ||
        review.nextDependencyState !==
            'displayed-eval-0b-read-only-investigation-ready'
    ) {
        throw new CoreCategoricalDisplayedLiftingReviewError(
            'DISPLAYED_LIFTING_REVIEW_AUTHORIZATION_DRIFT',
            'The delegated approval exceeds the frozen read-only row or ' +
                'its Git boundary'
        );
    }

    if (
        !sameData(
            review.retainedBoundaries,
            rawReview.retainedBoundaries
        ) ||
        !sameData(review, rawReview)
    ) {
        throw new CoreCategoricalDisplayedLiftingReviewError(
            'DISPLAYED_LIFTING_REVIEW_AUTHORIZATION_DRIFT',
            'The retained gaps, claims, or non-effects drifted'
        );
    }
}

validateCoreCategoricalDisplayedLiftingReview();
