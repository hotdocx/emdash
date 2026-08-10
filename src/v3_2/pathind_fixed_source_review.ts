/**
 * Separate immutable review of PATHIND-TRUSTED-PROFILE-1C proposal v1.
 *
 * The review approves only checkpointed proposal cc639fc under the user's
 * standing unattended delegation, with later human supersession.
 */

import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL,
    CorePathindFixedSource1cProposal,
    validateCorePathindFixedSource1cProposal
} from './pathind_fixed_source_proposal';

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

const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL;

const rawReview = {
    revision: 'PATHIND-TRUSTED-PROFILE-1C-REVIEWED-1',
    status: 'reviewed-proposal-v1-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-FIXED-SOURCE-01',
        decisionId: 'D-TS-EMDASH-PATHIND-FIXED-SOURCE-001',
        decision: 'proposal-v1-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-10',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: 'cc639fc'
    },
    recommendation:
        cloneData(proposal) as CorePathindFixedSource1cProposal,
    authorization: {
        implementationRow: 'PATHIND-TRUSTED-PROFILE-1C',
        implementationAuthorized: true,
        exactImplementation:
            cloneData(proposal.exactImplementation),
        exactDependencyClosure:
            cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor:
            cloneData(proposal.selectedPredecessor),
        trustedDeclarationCount: 5,
        runtimeRuleCount: 6,
        proofRuleCount: 0,
        transparentDefinitionCount: 6,
        typedLibraryConsumerCount: 1,
        negativeConsumerCount: 8,
        boundedOracleAssertionCount: 7,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        PathIndFuncAuthorized: false,
        PathIndTransfdAuthorized: false,
        internalizedPathInductionAuthorized: false,
        transitivityDefinitionsAuthorized: false,
        pathCategoryProofBridgeAuthorized: false,
        newCoreOrCheckerPrimitiveAuthorized: false,
        ordinarySafeLibraryRuleRegistrationAuthorized: false,
        textOrDeclarationParserAuthorized: false,
        browserOrPublicPackageExportAuthorized: false,
        activeLambdapiSourceChangeAuthorized: false,
        externalIntegrationOrReleaseAuthorized: false
    },
    validation: {
        proposalCheckpoint: 'cc639fc',
        rootTypecheck: 'passed',
        focusedLint: 'passed',
        focusedProposalGate: '8-tests-8-pass-zero-fail',
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
        'does-not-mutate-checkpointed-proposal-v1',
        'does-not-itself-implement-fixed-source-PathInd',
        'does-not-authorize-PathInd_func-or-PathInd_transfd',
        'does-not-authorize-varying-source-or-internalized-PathInd',
        'does-not-authorize-transitivity-definitions',
        'does-not-authorize-the-Path-category-proof-bridge',
        'does-not-add-a-Core-owner-checker-or-evaluator-branch',
        'does-not-authorize-safe-library-rule-registration',
        'does-not-authorize-text-browser-or-package-presentation',
        'does-not-authorize-active-Lambdapi-source-change',
        'does-not-authorize-push-merge-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'pathind-fixed-source-1c-implementation-ready'
} as const;

export type CorePathindFixedSource1cReview = typeof rawReview;

export type CorePathindFixedSource1cReviewErrorCode =
    | 'PATHIND_FIXED_SOURCE_REVIEW_DECISION_DRIFT'
    | 'PATHIND_FIXED_SOURCE_REVIEW_PROPOSAL_DRIFT'
    | 'PATHIND_FIXED_SOURCE_REVIEW_AUTHORIZATION_DRIFT';

export class CorePathindFixedSource1cReviewError extends Error {
    constructor(
        public readonly code: CorePathindFixedSource1cReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindFixedSource1cReviewError';
    }
}

export const CORE_PATHIND_FIXED_SOURCE_1C_REVIEW =
    deepFreeze(rawReview);

export function validateCorePathindFixedSource1cReview(
    review: CorePathindFixedSource1cReview =
        CORE_PATHIND_FIXED_SOURCE_1C_REVIEW
): CorePathindFixedSource1cReview {
    validateCorePathindFixedSource1cProposal(proposal);
    if (
        review.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-REVIEWED-1' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-FIXED-SOURCE-01' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-FIXED-SOURCE-001' ||
        review.approval.decision !==
            'proposal-v1-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-10' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== 'cc639fc'
    ) {
        throw new CorePathindFixedSource1cReviewError(
            'PATHIND_FIXED_SOURCE_REVIEW_DECISION_DRIFT',
            'The exact delegated fixed-source decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-1' ||
        review.recommendation.decision.status !== 'proposal-only' ||
        review.recommendation.decision.implementationAuthorized
    ) {
        throw new CorePathindFixedSource1cReviewError(
            'PATHIND_FIXED_SOURCE_REVIEW_PROPOSAL_DRIFT',
            'The review must retain exact non-authorizing proposal v1'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !==
            'PATHIND-TRUSTED-PROFILE-1C' ||
        !authorization.implementationAuthorized ||
        !sameData(
            authorization.exactImplementation,
            proposal.exactImplementation
        ) ||
        !sameData(
            authorization.exactDependencyClosure,
            proposal.dependencyClosure
        ) ||
        !sameData(
            authorization.exactSelectedPredecessor,
            proposal.selectedPredecessor
        ) ||
        authorization.trustedDeclarationCount !== 5 ||
        authorization.runtimeRuleCount !== 6 ||
        authorization.proofRuleCount !== 0 ||
        authorization.transparentDefinitionCount !== 6 ||
        authorization.typedLibraryConsumerCount !== 1 ||
        authorization.negativeConsumerCount !== 8 ||
        authorization.boundedOracleAssertionCount !== 7 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        authorization.PathIndFuncAuthorized ||
        authorization.PathIndTransfdAuthorized ||
        authorization.internalizedPathInductionAuthorized ||
        authorization.transitivityDefinitionsAuthorized ||
        authorization.pathCategoryProofBridgeAuthorized ||
        authorization.newCoreOrCheckerPrimitiveAuthorized ||
        authorization.ordinarySafeLibraryRuleRegistrationAuthorized ||
        authorization.textOrDeclarationParserAuthorized ||
        authorization.browserOrPublicPackageExportAuthorized ||
        authorization.activeLambdapiSourceChangeAuthorized ||
        authorization.externalIntegrationOrReleaseAuthorized ||
        !review.gitBoundary.localImplementationCheckpointAuthorized ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        review.nextDependencyState !==
            'pathind-fixed-source-1c-implementation-ready'
    ) {
        throw new CorePathindFixedSource1cReviewError(
            'PATHIND_FIXED_SOURCE_REVIEW_AUTHORIZATION_DRIFT',
            'The review widened or lost its exact 5/6/0/6 authorization'
        );
    }
    return review;
}
