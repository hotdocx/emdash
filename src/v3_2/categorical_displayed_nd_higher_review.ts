/**
 * Separate immutable delegated-approval record for
 * H-DTTLF-USABILITY-DISPLAYED-ND-HIGHER-01/D-DTTLF-USABILITY-019.
 *
 * The checkpointed audit remains unchanged and non-self-authorizing. This
 * record approves only its rule-free dependency foundation under the user's
 * standing unattended delegation, with human supersession.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT,
    CoreCategoricalDisplayedNdHigherAuditInput,
    validateCoreCategoricalDisplayedNdHigherAudit
} from './categorical_displayed_nd_higher_audit';

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

const proposal = CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT;
const continuation = proposal.recommendedContinuation;

const rawReview = {
    revision: 'DISPLAYED-ND-HIGHER-1B-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-DTTLF-USABILITY-DISPLAYED-ND-HIGHER-01',
        decisionId: 'D-DTTLF-USABILITY-019',
        decision: 'approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-presented-' +
            'checkpointed-proposal',
        recordedOn: '2026-07-29',
        humanDecisionSupersedes: true
    },
    recommendation:
        cloneData(proposal) as
            CoreCategoricalDisplayedNdHigherAuditInput,
    authorization: {
        implementationRow: continuation.row,
        implementationAuthorized: true,
        exactDeclarations:
            cloneData(continuation.exactDeclarations),
        exactPolicies:
            cloneData(continuation.exactPolicies),
        exactRuntimeRules:
            cloneData(continuation.exactRuntimeRules),
        exactProofRules:
            cloneData(continuation.exactProofRules),
        allEntriesUseGenericTransferEngines:
            continuation.allEntriesUseGenericTransferEngines,
        checkedTransparentDefinitionCount:
            continuation.checkedTransparentDefinitionCount,
        opaqueSignatureCount:
            continuation.opaqueSignatureCount,
        mandatoryStop: continuation.mandatoryStop,
        targetOwnersAuthorized: false,
        targetProjectionRulesAuthorized: false,
        richSurfaceConsumerAuthorized: false,
        newMathematicalOwnerAuthorized: false,
        intrinsicCoreOwnerAuthorized: false,
        ownerSpecificCheckerBranchAuthorized: false,
        parserOrSecondCheckerAuthorized: false,
        browserOrDeployedPromotionAuthorized: false,
        bulkTransferAuthorized: false,
        externalOrDestructiveGitActionAuthorized: false
    },
    validation: {
        proposalCheckpoint:
            '4db1ce8a80725c0030ac8908f416d412591620bd',
        proposalLedgerCheckpoint:
            '07ce033c34527f1e2cbd4b2f065634a1bb424eca',
        focusedProposalGate: '7-live-tests-pass',
        rootProposalGate:
            '1052-tests-1004-pass-48-intentional-skip-zero-fail',
        liveConformanceProposalGate:
            '19-judgments-global-60-second-pass',
        activeKernelProposalGate: 'bounded-make-check-pass'
    },
    gitBoundary: {
        rollbackEvidence:
            'proposal-and-ledger-checkpoints-recorded-before-delegation',
        localCheckpointRequired: true,
        exactStagedDiffReviewRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false
    },
    nonEffects: [
        'does-not-mutate-the-pre-review-audit-or-proposal',
        'does-not-itself-implement-the-foundation',
        'does-not-authorize-the-three-higher-action-target-owners',
        'does-not-authorize-the-two-target-projection-rules',
        'does-not-authorize-the-rich-typescript-surface-consumer',
        'does-not-authorize-a-new-mathematical-or-intrinsic-owner',
        'does-not-authorize-an-owner-specific-checker-or-evaluator-branch',
        'does-not-authorize-a-parser-or-second-checker',
        'does-not-authorize-browser-or-deployed-profile-promotion',
        'does-not-resume-bulk-or-whole-development-transfer',
        'does-not-broaden-local-checkpoint-git-authority'
    ],
    nextDependencyState:
        'displayed-nd-higher-foundation-1a-ready'
} as const;

export type CoreCategoricalDisplayedNdHigherReviewInput =
    typeof rawReview;

export type CoreCategoricalDisplayedNdHigherReviewErrorCode =
    | 'DISPLAYED_ND_HIGHER_REVIEW_DECISION_DRIFT'
    | 'DISPLAYED_ND_HIGHER_REVIEW_PROPOSAL_DRIFT'
    | 'DISPLAYED_ND_HIGHER_REVIEW_AUTHORIZATION_DRIFT';

export class CoreCategoricalDisplayedNdHigherReviewError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedNdHigherReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDisplayedNdHigherReviewError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_REVIEW =
    deepFreeze(rawReview);

export function validateCoreCategoricalDisplayedNdHigherReview(
    review: CoreCategoricalDisplayedNdHigherReviewInput =
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_REVIEW
): void {
    if (
        review.revision !==
            'DISPLAYED-ND-HIGHER-1B-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-DISPLAYED-ND-HIGHER-01' ||
        review.approval.decisionId !==
            'D-DTTLF-USABILITY-019' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-objection-after-presented-' +
            'checkpointed-proposal' ||
        review.approval.recordedOn !== '2026-07-29' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new CoreCategoricalDisplayedNdHigherReviewError(
            'DISPLAYED_ND_HIGHER_REVIEW_DECISION_DRIFT',
            'The delegated review decision or supersession boundary drifted'
        );
    }

    validateCoreCategoricalDisplayedNdHigherAudit(proposal);
    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.prerequisite
            .semanticImplementationAuthorized ||
        !review.recommendation.nonEffects.includes(
            'does-not-authorize-DISPLAYED-ND-HIGHER-FOUNDATION-1A'
        )
    ) {
        throw new CoreCategoricalDisplayedNdHigherReviewError(
            'DISPLAYED_ND_HIGHER_REVIEW_PROPOSAL_DRIFT',
            'The review must retain the exact non-authorizing proposal'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !==
            'DISPLAYED-ND-HIGHER-FOUNDATION-1A' ||
        !authorization.implementationAuthorized ||
        !sameData(
            authorization.exactDeclarations,
            continuation.exactDeclarations
        ) ||
        !sameData(
            authorization.exactPolicies,
            continuation.exactPolicies
        ) ||
        authorization.exactRuntimeRules.length !== 0 ||
        authorization.exactProofRules.length !== 0 ||
        !authorization.allEntriesUseGenericTransferEngines ||
        authorization.checkedTransparentDefinitionCount !== 5 ||
        authorization.opaqueSignatureCount !== 8 ||
        authorization.mandatoryStop !== continuation.mandatoryStop ||
        authorization.targetOwnersAuthorized ||
        authorization.targetProjectionRulesAuthorized ||
        authorization.richSurfaceConsumerAuthorized ||
        authorization.newMathematicalOwnerAuthorized ||
        authorization.intrinsicCoreOwnerAuthorized ||
        authorization.ownerSpecificCheckerBranchAuthorized ||
        authorization.parserOrSecondCheckerAuthorized ||
        authorization.browserOrDeployedPromotionAuthorized ||
        authorization.bulkTransferAuthorized ||
        authorization.externalOrDestructiveGitActionAuthorized ||
        !sameData(review.validation, rawReview.validation) ||
        !sameData(review.gitBoundary, rawReview.gitBoundary) ||
        !sameData(review.nonEffects, rawReview.nonEffects) ||
        review.nextDependencyState !==
            'displayed-nd-higher-foundation-1a-ready'
    ) {
        throw new CoreCategoricalDisplayedNdHigherReviewError(
            'DISPLAYED_ND_HIGHER_REVIEW_AUTHORIZATION_DRIFT',
            'The D-019 authorization exceeded or drifted from FOUNDATION-1A'
        );
    }
}
