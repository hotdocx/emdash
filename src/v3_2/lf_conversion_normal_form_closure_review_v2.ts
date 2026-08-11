/**
 * Separate immutable review of corrected Core LF comparison closure v2.
 *
 * This approves only proposal checkpoint a42ffc9 under the user's standing
 * unattended delegation, with later human supersession.
 */

import {
    CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2,
    CoreLfComparisonNormalFormClosureProposalV2,
    validateCoreLfComparisonNormalFormClosureProposalV2
} from './lf_conversion_normal_form_closure_proposal_v2';

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

const proposal = CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2;

const PROPOSAL_CHECKPOINT = 'a42ffc9';
const PROPOSAL_SHA256 =
    'a79d5c632301456c395602d0a692af2c9dd21719969aa949289318efffa2f49c';

const rawReview = {
    revision: 'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-REVIEWED-2',
    status: 'approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-02',
        decisionId:
            'D-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-002',
        decision: 'approve-exact-terminal-source-root-replay',
        authority: 'user-delegated-unattended-approval',
        condition: 'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: 'cf8ed76',
        supersededReviewCheckpoint: '778da06',
        supersededLedgerCheckpoint: '2801a25'
    },
    recommendation:
        cloneData(proposal) as
            CoreLfComparisonNormalFormClosureProposalV2,
    authorization: {
        implementationRow: 'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-1',
        implementationAuthorized: true,
        exactCorrection: cloneData(proposal.exactCorrection),
        exactBudgetAndFailureContract:
            cloneData(proposal.budgetAndFailureContract),
        exactRequiredEvidence: cloneData(proposal.requiredEvidence),
        terminalClosureOnlyAfterNotEqual: true,
        originalSourceRootsRequired: true,
        pairedOutcomeRootsAsClosureInputsAuthorized: false,
        pairedOutcomeRetainedForFallbackDiagnostic: true,
        oneGlobalBudgetRequired: true,
        pairedConsumptionRetained: true,
        budgetResetAuthorized: false,
        deterministicLeftThenRightRequired: true,
        replayedTraceSplicingRequired: true,
        traceDeduplicationAuthorized: false,
        exactKernelEqualityRequired: true,
        coherentFinalNegativeRequired: true,
        symmetricPositiveRegressionRequired: true,
        overNormalizationRegressionRequired: true,
        directStructuralPlicityNegativeRequired: true,
        distinctNormalFormNegativeRequired: true,
        budgetExhaustionRegressionRequired: true,
        pathIndV5ConsumerReplayRequired: true,
        newRuntimeRuleAuthorized: false,
        newProofRuleAuthorized: false,
        newCoreNodeAuthorized: false,
        checkerBranchAuthorized: false,
        unboundedNormalizationAuthorized: false,
        memoizationOrCachingAuthorized: false,
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
        'does-not-mutate-proposal-v2-or-v1-history',
        'does-not-itself-change-definitional-comparison',
        'does-not-authorize-new-runtime-or-proof-equations',
        'does-not-reset-the-budget-before-source-root-replay',
        'does-not-discard-or-deduplicate-the-paired-trace',
        'does-not-authorize-memoization-caching-or-proof-search',
        'does-not-authorize-a-PathInd-specific-outer-commuting-rewrite',
        'does-not-authorize-a-new-PathInd-runtime-rule',
        'does-not-authorize-public-Lambdapi-or-release-effects'
    ],
    nextDependencyState:
        'comparison-normal-form-closure-v2-implementation-ready'
} as const;

export type CoreLfComparisonNormalFormClosureReviewV2 = typeof rawReview;

export type CoreLfComparisonNormalFormClosureReviewV2ErrorCode =
    | 'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2_DECISION_DRIFT'
    | 'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2_PROPOSAL_DRIFT'
    | 'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2_AUTHORIZATION_DRIFT';

export class CoreLfComparisonNormalFormClosureReviewV2Error extends Error {
    constructor(
        public readonly code:
            CoreLfComparisonNormalFormClosureReviewV2ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfComparisonNormalFormClosureReviewV2Error';
    }
}

export const CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2 =
    deepFreeze(rawReview);

export function validateCoreLfComparisonNormalFormClosureReviewV2(
    review: CoreLfComparisonNormalFormClosureReviewV2 =
        CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2
): CoreLfComparisonNormalFormClosureReviewV2 {
    validateCoreLfComparisonNormalFormClosureProposalV2();
    if (
        review.revision !==
            'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-REVIEWED-2' ||
        review.approval.gate !==
            'H-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-02' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-COMPARISON-NORMAL-FORM-CLOSURE-002' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !==
            PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== 'cf8ed76' ||
        review.approval.supersededReviewCheckpoint !== '778da06' ||
        review.approval.supersededLedgerCheckpoint !== '2801a25'
    ) {
        throw new CoreLfComparisonNormalFormClosureReviewV2Error(
            'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2_DECISION_DRIFT',
            'The exact delegated comparison-v2 decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        !sameData(
            review.authorization.exactCorrection,
            proposal.exactCorrection
        ) ||
        !sameData(
            review.authorization.exactBudgetAndFailureContract,
            proposal.budgetAndFailureContract
        ) ||
        !sameData(
            review.authorization.exactRequiredEvidence,
            proposal.requiredEvidence
        ) ||
        review.validation.proposalCheckpoint !== PROPOSAL_CHECKPOINT ||
        review.validation.proposalSha256 !== PROPOSAL_SHA256
    ) {
        throw new CoreLfComparisonNormalFormClosureReviewV2Error(
            'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2_PROPOSAL_DRIFT',
            'The review must retain exact non-authorizing proposal v2'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !==
            'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-1' ||
        !authorization.implementationAuthorized ||
        !authorization.terminalClosureOnlyAfterNotEqual ||
        !authorization.originalSourceRootsRequired ||
        authorization.pairedOutcomeRootsAsClosureInputsAuthorized ||
        !authorization.pairedOutcomeRetainedForFallbackDiagnostic ||
        !authorization.oneGlobalBudgetRequired ||
        !authorization.pairedConsumptionRetained ||
        authorization.budgetResetAuthorized ||
        !authorization.deterministicLeftThenRightRequired ||
        !authorization.replayedTraceSplicingRequired ||
        authorization.traceDeduplicationAuthorized ||
        !authorization.exactKernelEqualityRequired ||
        !authorization.coherentFinalNegativeRequired ||
        !authorization.symmetricPositiveRegressionRequired ||
        !authorization.overNormalizationRegressionRequired ||
        !authorization.directStructuralPlicityNegativeRequired ||
        !authorization.distinctNormalFormNegativeRequired ||
        !authorization.budgetExhaustionRegressionRequired ||
        !authorization.pathIndV5ConsumerReplayRequired ||
        authorization.newRuntimeRuleAuthorized ||
        authorization.newProofRuleAuthorized ||
        authorization.newCoreNodeAuthorized ||
        authorization.checkerBranchAuthorized ||
        authorization.unboundedNormalizationAuthorized ||
        authorization.memoizationOrCachingAuthorized ||
        authorization.proofSearchOrUnificationAuthorized ||
        authorization.standaloneNormalizerChangeAuthorized ||
        authorization.weakHeadChangeAuthorized ||
        authorization.pathIndSpecificCommutingRewriteAuthorized ||
        authorization.publicSurfaceChangeAuthorized ||
        authorization.activeLambdapiSourceChangeAuthorized ||
        authorization.externalIntegrationOrReleaseAuthorized ||
        !review.gitBoundary.localImplementationCheckpointAuthorized ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        review.nextDependencyState !==
            'comparison-normal-form-closure-v2-implementation-ready'
    ) {
        throw new CoreLfComparisonNormalFormClosureReviewV2Error(
            'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2_AUTHORIZATION_DRIFT',
            'The exact source-root replay authorization widened or weakened'
        );
    }
    return review;
}
