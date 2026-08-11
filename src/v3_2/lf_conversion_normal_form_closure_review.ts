/**
 * Separate immutable review of the Core LF comparison normal-form closure
 * proposal frozen at checkpoint cf8ed76.
 */

import {
    CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL,
    CoreLfComparisonNormalFormClosureProposal,
    validateCoreLfComparisonNormalFormClosureProposal
} from './lf_conversion_normal_form_closure_proposal';

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

const deepFreeze = <T>(value: T): T => {
    if (value !== null && typeof value === 'object') {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        if (!Object.isFrozen(value)) Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const PROPOSAL_CHECKPOINT = 'cf8ed76';
const PROPOSAL_SHA256 =
    'b0711d2185b3f3fcf2ca35e6507c548f86c8f10d4252ab140f8b8ffa45bf7f4a';

const proposal = CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL;

const rawReview = {
    revision: 'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-REVIEWED-1',
    status: 'approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-01',
        decisionId:
            'D-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-001',
        decision: 'approve-exact-terminal-normal-form-closure',
        authority: 'user-delegated-unattended-approval',
        condition: 'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256
    },
    recommendation:
        cloneData(proposal) as
            CoreLfComparisonNormalFormClosureProposal,
    authorization: {
        implementationRow: 'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-1',
        implementationAuthorized: true,
        exactCorrection: cloneData(proposal.exactCorrection),
        exactBudgetAndFailureContract:
            cloneData(proposal.budgetAndFailureContract),
        exactRequiredEvidence: cloneData(proposal.requiredEvidence),
        terminalClosureOnlyAfterNotEqual: true,
        oneGlobalBudgetRequired: true,
        deterministicLeftThenRightRequired: true,
        traceSplicingRequired: true,
        exactKernelEqualityRequired: true,
        coherentFinalNegativeRequired: true,
        symmetricPositiveRegressionRequired: true,
        distinctNormalFormNegativeRequired: true,
        budgetExhaustionRegressionRequired: true,
        pathIndConsumerReplayRequired: true,
        newRuntimeRuleAuthorized: false,
        newProofRuleAuthorized: false,
        newCoreNodeAuthorized: false,
        checkerBranchAuthorized: false,
        unboundedNormalizationAuthorized: false,
        budgetResetAuthorized: false,
        proofSearchOrUnificationAuthorized: false,
        standaloneNormalizerChangeAuthorized: false,
        weakHeadChangeAuthorized: false,
        pathIndSpecificCommutingRewriteAuthorized: false,
        publicSurfaceChangeAuthorized: false,
        activeLambdapiSourceChangeAuthorized: false,
        externalIntegrationOrReleaseAuthorized: false
    },
    validation: {
        proposalCheckpoint: PROPOSAL_CHECKPOINT,
        proposalSha256: PROPOSAL_SHA256,
        rootTypecheck: 'passed',
        focusedLint: 'passed',
        focusedProposalGate: '5-tests-5-pass-zero-fail',
        LambdapiProposalGate: 'not-required-no-behavior',
        longAggregateGate:
            'intentionally-omitted-under-standing-proportional-policy'
    },
    gitBoundary: {
        localImplementationCheckpointAuthorized: true,
        exactStagedDiffReviewRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false
    },
    nonEffects: [
        'does-not-mutate-the-frozen-proposal',
        'does-not-itself-change-definitional-comparison',
        'does-not-authorize-new-runtime-or-proof-equations',
        'does-not-authorize-a-budget-reset-or-unbounded-normalization',
        'does-not-authorize-proof-search-unification-or-an-oracle',
        'does-not-authorize-a-PathInd-specific-outer-commuting-rewrite',
        'does-not-authorize-a-PathInd-v5-runtime-rule',
        'does-not-authorize-public-Lambdapi-or-release-effects'
    ],
    nextDependencyState:
        'comparison-normal-form-closure-implementation-ready'
} as const;

export type CoreLfComparisonNormalFormClosureReview = typeof rawReview;

export type CoreLfComparisonNormalFormClosureReviewErrorCode =
    | 'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_DECISION_DRIFT'
    | 'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_PROPOSAL_DRIFT'
    | 'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_AUTHORIZATION_DRIFT';

export class CoreLfComparisonNormalFormClosureReviewError extends Error {
    constructor(
        public readonly code:
            CoreLfComparisonNormalFormClosureReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfComparisonNormalFormClosureReviewError';
    }
}

export const CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW =
    deepFreeze(rawReview);

export function validateCoreLfComparisonNormalFormClosureReview(
    review: CoreLfComparisonNormalFormClosureReview =
        CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW
): CoreLfComparisonNormalFormClosureReview {
    validateCoreLfComparisonNormalFormClosureProposal();
    if (
        review.revision !==
            'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-REVIEWED-1' ||
        review.status !==
            'approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-01' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-001' ||
        review.approval.approvedProposalCheckpoint !==
            PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new CoreLfComparisonNormalFormClosureReviewError(
            'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_DECISION_DRIFT',
            'Comparison normal-form closure review decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        !sameData(review.authorization.exactCorrection,
            proposal.exactCorrection) ||
        !sameData(review.authorization.exactBudgetAndFailureContract,
            proposal.budgetAndFailureContract) ||
        !sameData(review.authorization.exactRequiredEvidence,
            proposal.requiredEvidence)
    ) {
        throw new CoreLfComparisonNormalFormClosureReviewError(
            'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_PROPOSAL_DRIFT',
            'Comparison normal-form closure reviewed proposal drifted'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !==
            'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-1' ||
        !authorization.implementationAuthorized ||
        !authorization.terminalClosureOnlyAfterNotEqual ||
        !authorization.oneGlobalBudgetRequired ||
        !authorization.deterministicLeftThenRightRequired ||
        !authorization.traceSplicingRequired ||
        !authorization.exactKernelEqualityRequired ||
        !authorization.coherentFinalNegativeRequired ||
        !authorization.symmetricPositiveRegressionRequired ||
        !authorization.distinctNormalFormNegativeRequired ||
        !authorization.budgetExhaustionRegressionRequired ||
        !authorization.pathIndConsumerReplayRequired ||
        authorization.newRuntimeRuleAuthorized ||
        authorization.newProofRuleAuthorized ||
        authorization.newCoreNodeAuthorized ||
        authorization.checkerBranchAuthorized ||
        authorization.unboundedNormalizationAuthorized ||
        authorization.budgetResetAuthorized ||
        authorization.proofSearchOrUnificationAuthorized ||
        authorization.standaloneNormalizerChangeAuthorized ||
        authorization.weakHeadChangeAuthorized ||
        authorization.pathIndSpecificCommutingRewriteAuthorized ||
        authorization.publicSurfaceChangeAuthorized ||
        authorization.activeLambdapiSourceChangeAuthorized ||
        authorization.externalIntegrationOrReleaseAuthorized
    ) {
        throw new CoreLfComparisonNormalFormClosureReviewError(
            'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_AUTHORIZATION_DRIFT',
            'Comparison normal-form closure review authorization drifted'
        );
    }
    return review;
}
