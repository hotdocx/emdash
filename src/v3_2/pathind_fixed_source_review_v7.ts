/**
 * Separate immutable review of corrected PATHIND-TRUSTED-PROFILE-1C v7.
 *
 * The review approves only checkpointed proposal f0fd4a6 under the user's
 * standing unattended delegation, with later human supersession. It
 * supersedes review checkpoint 9b22034 without mutating earlier evidence.
 */

import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7,
    CorePathindFixedSource1cProposalV7,
    validateCorePathindFixedSource1cProposalV7
} from './pathind_fixed_source_proposal_v7';

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

const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7;

const rawReview = {
    revision: 'PATHIND-TRUSTED-PROFILE-1C-REVIEWED-7',
    status: 'reviewed-corrected-proposal-v7-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-FIXED-SOURCE-07',
        decisionId: 'D-TS-EMDASH-PATHIND-FIXED-SOURCE-007',
        decision: 'corrected-proposal-v7-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-10',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: 'f0fd4a6',
        supersededProposalCheckpoint: 'b41c3b0',
        supersededReviewCheckpoint: '9b22034'
    },
    recommendation:
        cloneData(proposal) as CorePathindFixedSource1cProposalV7,
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
        runtimeRuleCount: 12,
        proofRuleCount: 0,
        transparentDefinitionCount: 6,
        typedLibraryConsumerCount: 1,
        negativeConsumerCount: 8,
        selectedRuntimeObservationCount: 5,
        boundedOracleAssertionCount: 9,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        exactActiveFibreSignaturesRequired: true,
        homConObjectProjectionAuthorized: true,
        displayedFunctorObjectProjectionAuthorized: true,
        displayedHomObjectFusionAuthorized: true,
        displayedHomObjectFusionAuthorityLines: [5481, 9177],
        transforClassifierDeltaAuthorized: true,
        transforClassifierDeltaAuthorityLines: [9150, 9151],
        fibreCovariantTargetSectionFusionAuthorized: true,
        fibreCovariantTargetSectionFusionAuthorityLines: [
            5481,
            7865,
            8419,
            9177,
            13765,
            13767,
            13773,
            13775,
            13923,
            13928
        ],
        fixedEvaluationSourcePresentationFusionAuthorized: true,
        fixedEvaluationSourcePresentationFusionAuthorityLines: [
            5457,
            19067,
            19068,
            19069,
            19072
        ],
        fixedEvaluationSourcePresentationFusionMustSubjectCheck: true,
        directRuntimeFunctorCategoryCollapseAuthorized: false,
        genericDeclarationProofIntegrationAuthorized: false,
        genericDeclarationUnfoldingAuthorized: false,
        retainedCheckerDiagnosticAuthorized: false,
        genericNestedRuntimeNormalizationAuthorized: false,
        wholeFibredProductRuntimeImportAuthorized: false,
        reversedTransforDeltaAuthorized: false,
        genericCheckerChangeAuthorized: false,
        alternateFibCovBodyAuthorized: false,
        canonicalSignatureSubstitutionAuthorized: false,
        duplicateClassifierDeclarationAuthorized: false,
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
        proposalCheckpoint: 'f0fd4a6',
        rootTypecheck: 'passed',
        focusedLint: 'passed',
        focusedProposalGate: '6-tests-6-pass-zero-fail',
        historicalV6AndV7Gate: '12-tests-12-pass-zero-fail',
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
        'does-not-mutate-proposal-v7-or-earlier-evidence',
        'does-not-itself-implement-fixed-source-PathInd',
        'does-not-authorize-a-runtime-Functor_cat-to-Catd_cat-collapse',
        'does-not-authorize-proof-program-integration-into-declaration-checking',
        'does-not-authorize-generic-declaration-unfolding',
        'does-not-authorize-retaining-a-checker-diagnostic-hook',
        'does-not-authorize-generic-nested-runtime-normalization',
        'does-not-authorize-whole-fibred-product-runtime-import',
        'does-not-authorize-reversing-the-active-Transf-delta',
        'does-not-authorize-a-generic-checker-change',
        'does-not-authorize-an-alternate-FibCov-body',
        'does-not-authorize-canonical-signature-substitution',
        'does-not-authorize-a-duplicate-classifier-owner',
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
        'pathind-fixed-source-1c-corrected-v7-implementation-ready'
} as const;

export type CorePathindFixedSource1cReviewV7 = typeof rawReview;

export type CorePathindFixedSource1cReviewV7ErrorCode =
    | 'PATHIND_FIXED_SOURCE_REVIEW_V7_DECISION_DRIFT'
    | 'PATHIND_FIXED_SOURCE_REVIEW_V7_PROPOSAL_DRIFT'
    | 'PATHIND_FIXED_SOURCE_REVIEW_V7_AUTHORIZATION_DRIFT';

export class CorePathindFixedSource1cReviewV7Error extends Error {
    constructor(
        public readonly code:
            CorePathindFixedSource1cReviewV7ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindFixedSource1cReviewV7Error';
    }
}

export const CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V7 =
    deepFreeze(rawReview);

export function validateCorePathindFixedSource1cReviewV7(
    review: CorePathindFixedSource1cReviewV7 =
        CORE_PATHIND_FIXED_SOURCE_1C_REVIEW_V7
): CorePathindFixedSource1cReviewV7 {
    validateCorePathindFixedSource1cProposalV7(proposal);
    if (
        review.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-REVIEWED-7' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-FIXED-SOURCE-07' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-FIXED-SOURCE-007' ||
        review.approval.decision !==
            'corrected-proposal-v7-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-10' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== 'f0fd4a6' ||
        review.approval.supersededProposalCheckpoint !== 'b41c3b0' ||
        review.approval.supersededReviewCheckpoint !== '9b22034'
    ) {
        throw new CorePathindFixedSource1cReviewV7Error(
            'PATHIND_FIXED_SOURCE_REVIEW_V7_DECISION_DRIFT',
            'The exact delegated corrected-v7 decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-7' ||
        review.recommendation.decision.status !== 'proposal-only' ||
        review.recommendation.decision.implementationAuthorized
    ) {
        throw new CorePathindFixedSource1cReviewV7Error(
            'PATHIND_FIXED_SOURCE_REVIEW_V7_PROPOSAL_DRIFT',
            'The review must retain exact non-authorizing proposal v7'
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
        authorization.runtimeRuleCount !== 12 ||
        authorization.proofRuleCount !== 0 ||
        authorization.transparentDefinitionCount !== 6 ||
        authorization.typedLibraryConsumerCount !== 1 ||
        authorization.negativeConsumerCount !== 8 ||
        authorization.selectedRuntimeObservationCount !== 5 ||
        authorization.boundedOracleAssertionCount !== 9 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        !authorization.exactActiveFibreSignaturesRequired ||
        !authorization.homConObjectProjectionAuthorized ||
        !authorization.displayedFunctorObjectProjectionAuthorized ||
        !authorization.displayedHomObjectFusionAuthorized ||
        !authorization.transforClassifierDeltaAuthorized ||
        !authorization.fibreCovariantTargetSectionFusionAuthorized ||
        !authorization
            .fixedEvaluationSourcePresentationFusionAuthorized ||
        !authorization
            .fixedEvaluationSourcePresentationFusionMustSubjectCheck ||
        !sameData(
            authorization
                .fixedEvaluationSourcePresentationFusionAuthorityLines,
            [5457, 19067, 19068, 19069, 19072]
        ) ||
        authorization.directRuntimeFunctorCategoryCollapseAuthorized ||
        authorization.genericDeclarationProofIntegrationAuthorized ||
        authorization.genericDeclarationUnfoldingAuthorized ||
        authorization.retainedCheckerDiagnosticAuthorized ||
        authorization.genericNestedRuntimeNormalizationAuthorized ||
        authorization.wholeFibredProductRuntimeImportAuthorized ||
        authorization.reversedTransforDeltaAuthorized ||
        authorization.genericCheckerChangeAuthorized ||
        authorization.alternateFibCovBodyAuthorized ||
        authorization.canonicalSignatureSubstitutionAuthorized ||
        authorization.duplicateClassifierDeclarationAuthorized ||
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
            'pathind-fixed-source-1c-corrected-v7-implementation-ready'
    ) {
        throw new CorePathindFixedSource1cReviewV7Error(
            'PATHIND_FIXED_SOURCE_REVIEW_V7_AUTHORIZATION_DRIFT',
            'The review widened or lost its exact 5/12/0/6 authorization'
        );
    }
    return review;
}
