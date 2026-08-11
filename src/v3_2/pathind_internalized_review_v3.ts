/**
 * Separate immutable review of corrected
 * PATHOUT-LIBRARY-INTERNALIZED-1D proposal v3.
 *
 * The review approves only checkpoint 5a1d635 under the user's standing
 * unattended delegation, with later human supersession. It supersedes v2
 * implementation authority without mutating historical evidence.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3,
    CorePathindInternalized1dProposalV3,
    validateCorePathindInternalized1dProposalV3
} from './pathind_internalized_proposal_v3';

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

const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3;

const PROPOSAL_SHA256 =
    '4c9b60411a7b1c98b3da44fdd6919360a3cf65a18e862c163d5f911a214308e3';

const SUPPORT_RULE_ID =
    'pathind.internalized.' +
    'path-ind-functor-component-post-prefix-subject-fusion';

const rawReview = {
    revision: 'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-3',
    status:
        'reviewed-corrected-proposal-v3-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-03',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-003',
        decision: 'corrected-proposal-v3-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: '5a1d635',
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: 'fbfc4dd',
        supersededReviewCheckpoint: '2a250fb',
        supersededLedgerCheckpoint: '2ede000'
    },
    recommendation:
        cloneData(proposal) as CorePathindInternalized1dProposalV3,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
        implementationAuthorized: true,
        exactImplementation: cloneData(proposal.exactImplementation),
        exactDependencyClosure: cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor: cloneData(proposal.selectedPredecessor),
        trustedDeclarationCount: 4,
        runtimeRuleCount: 5,
        mathematicalRuntimeProjectionCount: 4,
        derivedRuntimeSupportRuleCount: 1,
        proofRuleCount: 0,
        transparentDefinitionCount: 10,
        typedLibraryConsumerCount: 2,
        negativeConsumerCount: 10,
        selectedRuntimeObservationCount: 9,
        boundedOracleAssertionCount: 11,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        sigmaTransfdOwnerAuthorized: true,
        sigmaTransfdObjectProjectionAuthorized: true,
        pathOutReflEvalOwnerAuthorized: true,
        pathOutReflEvalComponentAuthorized: true,
        pathIndFuncOwnerAuthorized: true,
        pathIndFuncComponentAuthorized: true,
        pathIndTransfdOwnerAuthorized: true,
        pathIndTransfdComponentAuthorized: true,
        componentPostPrefixSubjectFusionAuthorized: true,
        componentPostPrefixSubjectFusionRuleId: SUPPORT_RULE_ID,
        componentPostPrefixSubjectFusionMustSubjectCheck: true,
        componentPostPrefixSubjectFusionIsMathematicalRule: false,
        v2PrePrefixSubjectFusionRetained: false,
        additionalRuntimeRuleAuthorized: false,
        tenTransparentDefinitionsAuthorized: true,
        primaryTheoremIsPathIndTransfd: true,
        pathIndFuncdIsTransparentDerivedPresentation: true,
        sourceArrowMustRemainInternallyOwned: true,
        higherActionMustRemainInternallyOwned: true,
        genericRuntimeMatcherChangeAuthorized: false,
        genericCheckerChangeAuthorized: false,
        inheritedProofProgramDependencyAuthorized: false,
        genericFixedEvaluationRuntimeImportAuthorized: false,
        alternatePathIndTypeAuthorized: false,
        alternatePathIndComponentBodyAuthorized: false,
        retainedTemporaryObserverAuthorized: false,
        wholeScaleStress2b3ImportAuthorized: false,
        externalNaturalitySquareAuthorized: false,
        arbitraryNonCartesianSigmaNaturalityAuthorized: false,
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
        proposalCheckpoint: '5a1d635',
        proposalSha256: PROPOSAL_SHA256,
        rootTypecheck: 'passed',
        focusedLint: 'passed',
        focusedProposalGate: '20-tests-20-pass-zero-fail',
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
        'does-not-mutate-proposal-v3-or-historical-v1-v2-evidence',
        'does-not-itself-implement-internalized-PathInd',
        'does-not-authorize-retaining-the-v2-pre-prefix-fusion',
        'does-not-authorize-an-additional-runtime-rule',
        'does-not-authorize-a-generic-runtime-matcher-or-checker-change',
        'does-not-authorize-retaining-an-inherited-proof-program',
        'does-not-authorize-a-generic-fixed-evaluation-runtime-import',
        'does-not-authorize-alternate-PathInd-types-or-component-bodies',
        'does-not-retain-temporary-in-memory-diagnostic-observers',
        'does-not-classify-the-support-fusion-as-a-mathematical-rule',
        'does-not-authorize-whole-scale-stress-2b3-profile-import',
        'does-not-authorize-an-external-naturality-square',
        'does-not-authorize-arbitrary-non-cartesian-Sigma-naturality',
        'does-not-collapse-internally-owned-source-arrow-or-higher-action',
        'does-not-authorize-transitivity-definitions',
        'does-not-authorize-the-Path-category-proof-bridge',
        'does-not-add-a-Core-owner-checker-or-evaluator-branch',
        'does-not-authorize-safe-library-rule-registration',
        'does-not-authorize-text-browser-or-package-presentation',
        'does-not-authorize-active-Lambdapi-source-change',
        'does-not-authorize-push-merge-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'pathind-internalized-1d-corrected-v3-implementation-ready'
} as const;

export type CorePathindInternalized1dReviewV3 = typeof rawReview;

export type CorePathindInternalized1dReviewV3ErrorCode =
    | 'PATHIND_INTERNALIZED_REVIEW_V3_DECISION_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V3_PROPOSAL_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V3_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dReviewV3Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dReviewV3ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dReviewV3Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_REVIEW_V3 =
    deepFreeze(rawReview);

export function validateCorePathindInternalized1dReviewV3(
    review: CorePathindInternalized1dReviewV3 =
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V3
): CorePathindInternalized1dReviewV3 {
    validateCorePathindInternalized1dProposalV3(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-3' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-INTERNALIZED-03' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-INTERNALIZED-003' ||
        review.approval.decision !==
            'corrected-proposal-v3-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== '5a1d635' ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== 'fbfc4dd' ||
        review.approval.supersededReviewCheckpoint !== '2a250fb' ||
        review.approval.supersededLedgerCheckpoint !== '2ede000'
    ) {
        throw new CorePathindInternalized1dReviewV3Error(
            'PATHIND_INTERNALIZED_REVIEW_V3_DECISION_DRIFT',
            'The exact delegated corrected-v3 decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-3' ||
        review.recommendation.decision.status !== 'proposal-only' ||
        review.recommendation.decision.implementationAuthorized ||
        !sameData(
            review.authorization.exactImplementation,
            proposal.exactImplementation
        ) ||
        !sameData(
            review.authorization.exactDependencyClosure,
            proposal.dependencyClosure
        ) ||
        !sameData(
            review.authorization.exactSelectedPredecessor,
            proposal.selectedPredecessor
        ) ||
        review.validation.proposalCheckpoint !== '5a1d635' ||
        review.validation.proposalSha256 !==
            review.approval.approvedProposalSha256
    ) {
        throw new CorePathindInternalized1dReviewV3Error(
            'PATHIND_INTERNALIZED_REVIEW_V3_PROPOSAL_DRIFT',
            'The review must retain exact non-authorizing proposal v3'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D' ||
        !authorization.implementationAuthorized ||
        authorization.trustedDeclarationCount !== 4 ||
        authorization.runtimeRuleCount !== 5 ||
        authorization.mathematicalRuntimeProjectionCount !== 4 ||
        authorization.derivedRuntimeSupportRuleCount !== 1 ||
        authorization.proofRuleCount !== 0 ||
        authorization.transparentDefinitionCount !== 10 ||
        authorization.typedLibraryConsumerCount !== 2 ||
        authorization.negativeConsumerCount !== 10 ||
        authorization.selectedRuntimeObservationCount !== 9 ||
        authorization.boundedOracleAssertionCount !== 11 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        !authorization.sigmaTransfdOwnerAuthorized ||
        !authorization.sigmaTransfdObjectProjectionAuthorized ||
        !authorization.pathOutReflEvalOwnerAuthorized ||
        !authorization.pathOutReflEvalComponentAuthorized ||
        !authorization.pathIndFuncOwnerAuthorized ||
        !authorization.pathIndFuncComponentAuthorized ||
        !authorization.pathIndTransfdOwnerAuthorized ||
        !authorization.pathIndTransfdComponentAuthorized ||
        !authorization.componentPostPrefixSubjectFusionAuthorized ||
        authorization.componentPostPrefixSubjectFusionRuleId !==
            SUPPORT_RULE_ID ||
        !authorization.componentPostPrefixSubjectFusionMustSubjectCheck ||
        authorization.componentPostPrefixSubjectFusionIsMathematicalRule ||
        authorization.v2PrePrefixSubjectFusionRetained ||
        authorization.additionalRuntimeRuleAuthorized ||
        !authorization.tenTransparentDefinitionsAuthorized ||
        !authorization.primaryTheoremIsPathIndTransfd ||
        !authorization.pathIndFuncdIsTransparentDerivedPresentation ||
        !authorization.sourceArrowMustRemainInternallyOwned ||
        !authorization.higherActionMustRemainInternallyOwned ||
        authorization.genericRuntimeMatcherChangeAuthorized ||
        authorization.genericCheckerChangeAuthorized ||
        authorization.inheritedProofProgramDependencyAuthorized ||
        authorization.genericFixedEvaluationRuntimeImportAuthorized ||
        authorization.alternatePathIndTypeAuthorized ||
        authorization.alternatePathIndComponentBodyAuthorized ||
        authorization.retainedTemporaryObserverAuthorized ||
        authorization.wholeScaleStress2b3ImportAuthorized ||
        authorization.externalNaturalitySquareAuthorized ||
        authorization.arbitraryNonCartesianSigmaNaturalityAuthorized ||
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
            'pathind-internalized-1d-corrected-v3-implementation-ready'
    ) {
        throw new CorePathindInternalized1dReviewV3Error(
            'PATHIND_INTERNALIZED_REVIEW_V3_AUTHORIZATION_DRIFT',
            'The exact post-prefix 4/5/0/10 authorization widened'
        );
    }
    return review;
}
