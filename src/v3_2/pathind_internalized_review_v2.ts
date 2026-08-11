/**
 * Separate immutable review of corrected
 * PATHOUT-LIBRARY-INTERNALIZED-1D proposal v2.
 *
 * The review approves only checkpoint fbfc4dd under the user's standing
 * unattended delegation, with later human supersession. It supersedes v1
 * implementation authority without mutating either historical artifact.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2,
    CorePathindInternalized1dProposalV2,
    validateCorePathindInternalized1dProposalV2
} from './pathind_internalized_proposal_v2';

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

const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2;

const PROPOSAL_SHA256 =
    '9a4b6e9f863af1068518920c050f5cbfdaeddb5fcf2fccb2d58a9e8ef7dfb85e';

const SUPPORT_RULE_ID =
    'pathind.internalized.' +
    'path-ind-functor-component-subject-fusion';

const rawReview = {
    revision: 'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-2',
    status:
        'reviewed-corrected-proposal-v2-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-02',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-002',
        decision: 'corrected-proposal-v2-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: 'fbfc4dd',
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: '188b8e5',
        supersededReviewCheckpoint: 'd3a0f31',
        supersededLedgerCheckpoint: '0191db7'
    },
    recommendation:
        cloneData(proposal) as CorePathindInternalized1dProposalV2,
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
        componentSubjectPresentationFusionAuthorized: true,
        componentSubjectPresentationFusionRuleId: SUPPORT_RULE_ID,
        componentSubjectPresentationFusionMustSubjectCheck: true,
        componentSubjectPresentationFusionIsMathematicalRule: false,
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
        retainedTemporaryExperimentAuthorized: false,
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
        proposalCheckpoint: 'fbfc4dd',
        proposalSha256: PROPOSAL_SHA256,
        rootTypecheck: 'passed',
        focusedLint: 'passed',
        focusedProposalGate: '14-tests-14-pass-zero-fail',
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
        'does-not-mutate-proposal-v2-or-historical-v1-evidence',
        'does-not-itself-implement-internalized-PathInd',
        'does-not-authorize-a-generic-runtime-matcher-or-checker-change',
        'does-not-authorize-retaining-an-inherited-proof-program',
        'does-not-authorize-a-generic-fixed-evaluation-runtime-import',
        'does-not-authorize-alternate-PathInd-types-or-component-bodies',
        'does-not-retain-temporary-runtime-or-proof-experiments',
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
        'pathind-internalized-1d-corrected-v2-implementation-ready'
} as const;

export type CorePathindInternalized1dReviewV2 = typeof rawReview;

export type CorePathindInternalized1dReviewV2ErrorCode =
    | 'PATHIND_INTERNALIZED_REVIEW_V2_DECISION_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V2_PROPOSAL_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V2_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dReviewV2Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dReviewV2ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dReviewV2Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_REVIEW_V2 =
    deepFreeze(rawReview);

export function validateCorePathindInternalized1dReviewV2(
    review: CorePathindInternalized1dReviewV2 =
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V2
): CorePathindInternalized1dReviewV2 {
    validateCorePathindInternalized1dProposalV2(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-2' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-INTERNALIZED-02' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-INTERNALIZED-002' ||
        review.approval.decision !==
            'corrected-proposal-v2-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== 'fbfc4dd' ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== '188b8e5' ||
        review.approval.supersededReviewCheckpoint !== 'd3a0f31' ||
        review.approval.supersededLedgerCheckpoint !== '0191db7'
    ) {
        throw new CorePathindInternalized1dReviewV2Error(
            'PATHIND_INTERNALIZED_REVIEW_V2_DECISION_DRIFT',
            'The exact delegated corrected-v2 decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-2' ||
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
        review.validation.proposalCheckpoint !== 'fbfc4dd' ||
        review.validation.proposalSha256 !==
            review.approval.approvedProposalSha256
    ) {
        throw new CorePathindInternalized1dReviewV2Error(
            'PATHIND_INTERNALIZED_REVIEW_V2_PROPOSAL_DRIFT',
            'The review must retain exact non-authorizing proposal v2'
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
        !authorization.componentSubjectPresentationFusionAuthorized ||
        authorization.componentSubjectPresentationFusionRuleId !==
            SUPPORT_RULE_ID ||
        !authorization.componentSubjectPresentationFusionMustSubjectCheck ||
        authorization.componentSubjectPresentationFusionIsMathematicalRule ||
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
        authorization.retainedTemporaryExperimentAuthorized ||
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
            'pathind-internalized-1d-corrected-v2-implementation-ready'
    ) {
        throw new CorePathindInternalized1dReviewV2Error(
            'PATHIND_INTERNALIZED_REVIEW_V2_AUTHORIZATION_DRIFT',
            'The exact 4/5/0/10 authorization widened or weakened'
        );
    }
    return review;
}
