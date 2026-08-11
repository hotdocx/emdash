/**
 * Separate immutable review of declaration-checker budget propagation.
 *
 * This approves only proposal checkpoint 9238104 under the user's standing
 * unattended delegation, with later human supersession.
 */

import {
    CORE_LF_TRANSFER_DECLARATION_BUDGET_PROPOSAL,
    CoreLfTransferDeclarationBudgetProposal,
    validateCoreLfTransferDeclarationBudgetProposal
} from './lf_transfer_declaration_budget_proposal';

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

const proposal = CORE_LF_TRANSFER_DECLARATION_BUDGET_PROPOSAL;
const PROPOSAL_CHECKPOINT = '9238104';
const PROPOSAL_SHA256 =
    'b8903a21e8b66f49f498d81257399d502edf4d1278a709db3bba73fea78a5544';

const rawReview = {
    revision: 'CORE-LF-TRANSFER-DECLARATION-BUDGET-REVIEWED-1',
    status: 'approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-TS-EMDASH-LF-DECLARATION-BUDGET-01',
        decisionId: 'D-TS-EMDASH-LF-DECLARATION-BUDGET-001',
        decision: 'approve-exact-declaration-checker-budget-propagation',
        authority: 'user-delegated-unattended-approval',
        condition: 'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256
    },
    recommendation:
        cloneData(proposal) as CoreLfTransferDeclarationBudgetProposal,
    authorization: {
        implementationRow: 'CORE-LF-TRANSFER-DECLARATION-BUDGET-1',
        implementationAuthorized: true,
        exactCorrection: cloneData(proposal.exactCorrection),
        exactRequiredEvidence: cloneData(proposal.requiredEvidence),
        resolveAndValidateBeforeFactoryRequired: true,
        privateLimitAwareFactoryRequired: true,
        checkerConstraintLimitOverrideRequired: true,
        exactCallerSelectedLimitRequired: true,
        publicOptionNameMustRemainUnchanged: true,
        publicFactorySignatureMustRemainUnchanged: true,
        exportedDefaultMustRemain256: true,
        compiledModuleLimitContractMustRemainUnchanged: true,
        zeroVersusOneStepRegressionRequired: true,
        invalidLimitRegressionRequired: true,
        reviewedPathIndV6ReplayRequired: true,
        fullTypeScriptGateRequiredBeforeSemanticCheckpoint: true,
        unboundedBudgetAuthorized: false,
        adaptiveBudgetAuthorized: false,
        globalDefaultChangeAuthorized: false,
        pathIndSpecificBudgetAuthorized: false,
        newRuntimeRuleAuthorized: false,
        newProofRuleAuthorized: false,
        proofProgramIntegrationAuthorized: false,
        newCoreNodeAuthorized: false,
        newCheckerBranchAuthorized: false,
        newEvaluatorBranchAuthorized: false,
        publicBarrelChangeAuthorized: false,
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
        'does-not-mutate-the-proposal-or-prior-comparison-evidence',
        'does-not-itself-change-declaration-checking',
        'does-not-change-the-global-256-step-default',
        'does-not-authorize-unbounded-or-adaptive-comparison',
        'does-not-authorize-a-PathInd-specific-budget',
        'does-not-authorize-a-runtime-or-proof-equation',
        'does-not-authorize-proof-program-integration',
        'does-not-add-a-Core-node-checker-branch-or-evaluator-branch',
        'does-not-change-the-public-factory-signature-or-barrels',
        'does-not-change-active-Lambdapi-source',
        'does-not-authorize-push-merge-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'lf-transfer-declaration-budget-implementation-ready'
} as const;

export type CoreLfTransferDeclarationBudgetReview = typeof rawReview;

export type CoreLfTransferDeclarationBudgetReviewErrorCode =
    | 'LF_TRANSFER_DECLARATION_BUDGET_REVIEW_DECISION_DRIFT'
    | 'LF_TRANSFER_DECLARATION_BUDGET_REVIEW_PROPOSAL_DRIFT'
    | 'LF_TRANSFER_DECLARATION_BUDGET_REVIEW_AUTHORIZATION_DRIFT';

export class CoreLfTransferDeclarationBudgetReviewError extends Error {
    constructor(
        public readonly code:
            CoreLfTransferDeclarationBudgetReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfTransferDeclarationBudgetReviewError';
    }
}

export const CORE_LF_TRANSFER_DECLARATION_BUDGET_REVIEW =
    deepFreeze(rawReview);

export function validateCoreLfTransferDeclarationBudgetReview(
    review: CoreLfTransferDeclarationBudgetReview =
        CORE_LF_TRANSFER_DECLARATION_BUDGET_REVIEW
): CoreLfTransferDeclarationBudgetReview {
    validateCoreLfTransferDeclarationBudgetProposal();
    if (
        review.revision !==
            'CORE-LF-TRANSFER-DECLARATION-BUDGET-REVIEWED-1' ||
        review.approval.gate !==
            'H-TS-EMDASH-LF-DECLARATION-BUDGET-01' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-LF-DECLARATION-BUDGET-001' ||
        review.approval.decision !==
            'approve-exact-declaration-checker-budget-propagation' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !==
            PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256
    ) {
        throw new CoreLfTransferDeclarationBudgetReviewError(
            'LF_TRANSFER_DECLARATION_BUDGET_REVIEW_DECISION_DRIFT',
            'The exact delegated budget-propagation decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        !sameData(
            review.authorization.exactCorrection,
            proposal.exactCorrection
        ) ||
        !sameData(
            review.authorization.exactRequiredEvidence,
            proposal.requiredEvidence
        )
    ) {
        throw new CoreLfTransferDeclarationBudgetReviewError(
            'LF_TRANSFER_DECLARATION_BUDGET_REVIEW_PROPOSAL_DRIFT',
            'The reviewed declaration-budget proposal bytes drifted'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        !authorization.resolveAndValidateBeforeFactoryRequired ||
        !authorization.privateLimitAwareFactoryRequired ||
        !authorization.checkerConstraintLimitOverrideRequired ||
        !authorization.exactCallerSelectedLimitRequired ||
        !authorization.publicOptionNameMustRemainUnchanged ||
        !authorization.publicFactorySignatureMustRemainUnchanged ||
        !authorization.exportedDefaultMustRemain256 ||
        !authorization.compiledModuleLimitContractMustRemainUnchanged ||
        !authorization.zeroVersusOneStepRegressionRequired ||
        !authorization.invalidLimitRegressionRequired ||
        !authorization.reviewedPathIndV6ReplayRequired ||
        !authorization.fullTypeScriptGateRequiredBeforeSemanticCheckpoint ||
        authorization.unboundedBudgetAuthorized ||
        authorization.adaptiveBudgetAuthorized ||
        authorization.globalDefaultChangeAuthorized ||
        authorization.pathIndSpecificBudgetAuthorized ||
        authorization.newRuntimeRuleAuthorized ||
        authorization.newProofRuleAuthorized ||
        authorization.proofProgramIntegrationAuthorized ||
        authorization.newCoreNodeAuthorized ||
        authorization.newCheckerBranchAuthorized ||
        authorization.newEvaluatorBranchAuthorized ||
        authorization.publicBarrelChangeAuthorized ||
        authorization.activeLambdapiSourceChangeAuthorized ||
        authorization.externalIntegrationOrReleaseAuthorized ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized
    ) {
        throw new CoreLfTransferDeclarationBudgetReviewError(
            'LF_TRANSFER_DECLARATION_BUDGET_REVIEW_AUTHORIZATION_DRIFT',
            'The reviewed budget-propagation authorization widened'
        );
    }
    return review;
}
