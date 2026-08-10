/**
 * Separate immutable review of corrected PATHIND-TRUSTED-PROFILE-1C v2.
 *
 * The review approves only checkpointed proposal 7413dd6 under the user's
 * standing unattended delegation, with later human supersession.  It
 * supersedes review checkpoint 2deae91 rather than mutating its evidence.
 */

import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2,
    CorePathindFixedSource1cProposalV2,
    validateCorePathindFixedSource1cProposalV2
} from './pathind_fixed_source_proposal_v2';

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

const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2;

const rawReview = {
    revision: 'PATHIND-TRUSTED-PROFILE-1C-REVIEWED-2',
    status: 'reviewed-corrected-proposal-v2-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-FIXED-SOURCE-02',
        decisionId: 'D-TS-EMDASH-PATHIND-FIXED-SOURCE-002',
        decision: 'corrected-proposal-v2-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-10',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: '7413dd6',
        supersededProposalCheckpoint: 'cc639fc',
        supersededReviewCheckpoint: '2deae91'
    },
    recommendation:
        cloneData(proposal) as CorePathindFixedSource1cProposalV2,
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
        runtimeRuleCount: 7,
        proofRuleCount: 0,
        transparentDefinitionCount: 6,
        typedLibraryConsumerCount: 1,
        negativeConsumerCount: 8,
        selectedRuntimeObservationCount: 4,
        boundedOracleAssertionCount: 8,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        homConObjectProjectionAuthorized: true,
        genericCheckerChangeAuthorized: false,
        alternateFibCovBodyAuthorized: false,
        duplicateHomConDeclarationAuthorized: false,
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
        proposalCheckpoint: '7413dd6',
        rootTypecheck: 'passed',
        focusedLint: 'passed',
        focusedProposalGate: '6-tests-6-pass-zero-fail',
        historicalV1Gate: '13-tests-13-pass-zero-fail',
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
        'does-not-mutate-proposal-v2-or-v1-evidence',
        'does-not-itself-implement-fixed-source-PathInd',
        'does-not-authorize-a-generic-checker-change',
        'does-not-authorize-an-alternate-FibCov-body',
        'does-not-authorize-a-duplicate-hom_con-owner',
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
        'pathind-fixed-source-1c-corrected-implementation-ready'
} as const;

export type CorePathindFixedSource1cReviewV2 = typeof rawReview;

export type CorePathindFixedSource1cReviewV2ErrorCode =
    | 'PATHIND_FIXED_SOURCE_REVIEW_V2_DECISION_DRIFT'
    | 'PATHIND_FIXED_SOURCE_REVIEW_V2_PROPOSAL_DRIFT'
    | 'PATHIND_FIXED_SOURCE_REVIEW_V2_AUTHORIZATION_DRIFT';

export class CorePathindFixedSource1cReviewV2Error extends Error {
    constructor(
        public readonly code:
            CorePathindFixedSource1cReviewV2ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindFixedSource1cReviewV2Error';
    }
}

export const CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V2 =
    deepFreeze(rawReview);

export function validateCorePathindFixedSource1cReviewV2(
    review: CorePathindFixedSource1cReviewV2 =
        CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V2
): CorePathindFixedSource1cReviewV2 {
    validateCorePathindFixedSource1cProposalV2(proposal);
    if (
        review.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-REVIEWED-2' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-FIXED-SOURCE-02' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-FIXED-SOURCE-002' ||
        review.approval.decision !==
            'corrected-proposal-v2-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-10' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== '7413dd6' ||
        review.approval.supersededProposalCheckpoint !== 'cc639fc' ||
        review.approval.supersededReviewCheckpoint !== '2deae91'
    ) {
        throw new CorePathindFixedSource1cReviewV2Error(
            'PATHIND_FIXED_SOURCE_REVIEW_V2_DECISION_DRIFT',
            'The exact delegated corrected-v2 decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-2' ||
        review.recommendation.decision.status !== 'proposal-only' ||
        review.recommendation.decision.implementationAuthorized
    ) {
        throw new CorePathindFixedSource1cReviewV2Error(
            'PATHIND_FIXED_SOURCE_REVIEW_V2_PROPOSAL_DRIFT',
            'The review must retain exact non-authorizing proposal v2'
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
        authorization.runtimeRuleCount !== 7 ||
        authorization.proofRuleCount !== 0 ||
        authorization.transparentDefinitionCount !== 6 ||
        authorization.typedLibraryConsumerCount !== 1 ||
        authorization.negativeConsumerCount !== 8 ||
        authorization.selectedRuntimeObservationCount !== 4 ||
        authorization.boundedOracleAssertionCount !== 8 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        !authorization.homConObjectProjectionAuthorized ||
        authorization.genericCheckerChangeAuthorized ||
        authorization.alternateFibCovBodyAuthorized ||
        authorization.duplicateHomConDeclarationAuthorized ||
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
            'pathind-fixed-source-1c-corrected-implementation-ready'
    ) {
        throw new CorePathindFixedSource1cReviewV2Error(
            'PATHIND_FIXED_SOURCE_REVIEW_V2_AUTHORIZATION_DRIFT',
            'The review widened or lost its exact 5/7/0/6 authorization'
        );
    }
    return review;
}
