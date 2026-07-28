/**
 * Separate immutable delegated-approval record for
 * H-DTTLF-USABILITY-DISPLAYED-BRACKET-01/D-DTTLF-USABILITY-009.
 *
 * The pre-review DISPLAYED-BRACKET-0A proposal remains unchanged and
 * non-self-authorizing. This artifact records the user's plan-specific
 * unattended delegation after no immediate human response to the exact
 * presented proposal. It authorizes only the frozen root-only
 * DISPLAYED-BRACKET-1A implementation row.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL,
    CoreCategoricalDisplayedBracketProposalInput,
    validateCoreCategoricalDisplayedBracketProposal
} from './categorical_displayed_bracket_proposal';

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

const proposal = CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL;

const rawReview = {
    revision: 'DISPLAYED-BRACKET-0A-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-DTTLF-USABILITY-DISPLAYED-BRACKET-01',
        decisionId: 'D-DTTLF-USABILITY-009',
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
            CoreCategoricalDisplayedBracketProposalInput,
    authorization: {
        selectedArchitecture:
            'generic-displayed-contextual-compiler',
        implementationRow: 'DISPLAYED-BRACKET-1A',
        implementationAuthorized: true,
        visibility: 'root-only',
        profile: 'fibred-displayed-bracket-1',
        contextScope:
            'finite-nonempty-independent-sibling-block-over-common-base',
        typedPairFrontendNodeAuthorized: true,
        existingDisplayedAuthorityOnly: true,
        additionalSemanticOwnerOrRuleAuthorized: false,
        displayedChainImplementationAuthorized: false,
        generalNdCoherenceAuthorized: false,
        sigmaArrowActionAuthorized: false,
        totalCategoryComparisonAuthorized: false,
        browserOrDeployedProfilePromotionAuthorized: false,
        parserOrBulkTransferAuthorized: false
    },
    retainedBoundaries: {
        firstImplementationRow:
            cloneData(proposal.firstImplementationRow),
        selectedArchitecture:
            cloneData(proposal.selectedArchitecture),
        scalabilityBoundary:
            cloneData(proposal.scalabilityBoundary),
        followOnRows:
            cloneData(proposal.followOnRows),
        decisionEffects:
            cloneData(proposal.decisionEffects)
    },
    validation: {
        proposalRevision: 'DISPLAYED-BRACKET-0A-PROPOSAL-1',
        proposalCheckpoint:
            'e4b743f70c0454d63a93587dc045a3e2d0273ee5',
        proposalLedgerCheckpoint:
            '6ee1b55b395eec4a9a9909afff0f1b0f693312f4',
        focusedProposalGate: '8-tests-pass',
        rootProposalGate:
            '821-tests-775-pass-46-intentional-skip-zero-fail',
        liveConformanceGate:
            '19-judgments-global-60-second-pass',
        focusedReviewGate: '9-tests-pass',
        rootReviewGate:
            '830-tests-784-pass-46-intentional-skip-zero-fail'
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
        'does-not-add-or-authorize-a-lambdapi-owner-or-rule',
        'does-not-add-an-intrinsic-core-semantic-owner',
        'does-not-authorize-displayed-chain-implementation',
        'does-not-authorize-general-nd-coherence-synthesis',
        'does-not-authorize-sigma-arrow-action-or-total-comparison',
        'does-not-authorize-browser-or-deployed-profile-promotion',
        'does-not-authorize-parsing-or-bulk-transfer',
        'does-not-broaden-local-checkpoint-git-authority'
    ],
    nextDependencyState:
        'displayed-bracket-1a-implementation-ready'
} as const;

export type CoreCategoricalDisplayedBracketReviewInput =
    typeof rawReview;

export type CoreCategoricalDisplayedBracketReviewErrorCode =
    | 'DISPLAYED_BRACKET_REVIEW_DECISION_DRIFT'
    | 'DISPLAYED_BRACKET_REVIEW_PREREQUISITE_DRIFT'
    | 'DISPLAYED_BRACKET_REVIEW_PROPOSAL_DRIFT'
    | 'DISPLAYED_BRACKET_REVIEW_AUTHORIZATION_DRIFT';

export class CoreCategoricalDisplayedBracketReviewError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedBracketReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDisplayedBracketReviewError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW =
    deepFreeze(rawReview);

export function validateCoreCategoricalDisplayedBracketReview(
    review: CoreCategoricalDisplayedBracketReviewInput =
        CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW
): void {
    if (
        review.revision !== 'DISPLAYED-BRACKET-0A-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-DISPLAYED-BRACKET-01' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-009' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-response-after-presented-frozen-proposal' ||
        review.approval.recordedOn !== '2026-07-28' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new CoreCategoricalDisplayedBracketReviewError(
            'DISPLAYED_BRACKET_REVIEW_DECISION_DRIFT',
            'The delegated review must preserve the exact D-DTTLF-' +
                'USABILITY-009 decision, authority, and supersession ' +
                'boundary'
        );
    }

    try {
        validateCoreCategoricalDisplayedBracketProposal(proposal);
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedBracketReviewError(
            'DISPLAYED_BRACKET_REVIEW_PREREQUISITE_DRIFT',
            'The approved DISPLAYED-BRACKET-0A proposal drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-bracket-01' ||
        review.recommendation.decisionId !==
            'D-DTTLF-USABILITY-009'
    ) {
        throw new CoreCategoricalDisplayedBracketReviewError(
            'DISPLAYED_BRACKET_REVIEW_PROPOSAL_DRIFT',
            'The reviewed recommendation is not the exact immutable ' +
                'pre-review proposal'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.selectedArchitecture !==
            'generic-displayed-contextual-compiler' ||
        authorization.implementationRow !== 'DISPLAYED-BRACKET-1A' ||
        !authorization.implementationAuthorized ||
        authorization.visibility !== 'root-only' ||
        authorization.profile !== 'fibred-displayed-bracket-1' ||
        !authorization.typedPairFrontendNodeAuthorized ||
        !authorization.existingDisplayedAuthorityOnly ||
        authorization.additionalSemanticOwnerOrRuleAuthorized ||
        authorization.displayedChainImplementationAuthorized ||
        authorization.generalNdCoherenceAuthorized ||
        authorization.sigmaArrowActionAuthorized ||
        authorization.totalCategoryComparisonAuthorized ||
        authorization.browserOrDeployedProfilePromotionAuthorized ||
        authorization.parserOrBulkTransferAuthorized ||
        !review.gitBoundary.localCheckpointRequired ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        review.nextDependencyState !==
            'displayed-bracket-1a-implementation-ready'
    ) {
        throw new CoreCategoricalDisplayedBracketReviewError(
            'DISPLAYED_BRACKET_REVIEW_AUTHORIZATION_DRIFT',
            'The delegated approval exceeds the frozen root-only row or ' +
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
        throw new CoreCategoricalDisplayedBracketReviewError(
            'DISPLAYED_BRACKET_REVIEW_AUTHORIZATION_DRIFT',
            'The retained gaps, claims, or non-effects drifted'
        );
    }
}

validateCoreCategoricalDisplayedBracketReview();
