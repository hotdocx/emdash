/**
 * Separate immutable review of corrected
 * PATHOUT-LIBRARY-INTERNALIZED-1D proposal v13.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13,
    CorePathindInternalized1dProposalV13,
    validateCorePathindInternalized1dProposalV13
} from './pathind_internalized_proposal_v13';

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

const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13;

const PROPOSAL_CHECKPOINT = 'd77f0d7';
const PROPOSAL_SHA256 =
    '555b3d3f656a52d89ddbbd1a76f030d522b673b07918d2b0ed9bf708b313f2e1';

const PATHOUT_PI_TRANSPORT_POST_DELTA_FUSION_ID =
    'pathind.internalized.' +
    'pathout-pi-transport-post-delta-presentation-fusion';

const rawReview = {
    revision: 'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-13',
    status:
        'reviewed-corrected-proposal-v13-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-13',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-013',
        decision: 'corrected-proposal-v13-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: '39abb02',
        supersededReviewCheckpoint: '8833f8f',
        supersededLedgerCheckpoint: null
    },
    recommendation:
        cloneData(proposal) as CorePathindInternalized1dProposalV13,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
        implementationAuthorized: true,
        exactImplementation: cloneData(proposal.exactImplementation),
        exactDependencyClosure: cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor: cloneData(proposal.selectedPredecessor),
        trustedDeclarationCount: 4,
        runtimeRuleCount: 12,
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 7,
        proofRuleCount: 0,
        transparentDefinitionCount: 10,
        typedLibraryConsumerCount: 2,
        negativeConsumerCount: 10,
        selectedRuntimeObservationCount: 10,
        boundedOracleAssertionCount: 12,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        stagedRuntimePartitionAuthorized: true,
        baseRuntimeRuleCount: 9,
        prefixTransparentDefinitionCount: 3,
        extensionRuntimeRuleCount: 3,
        suffixTransparentDefinitionCount: 4,
        declarationOrderPreserved: true,
        semanticCountDeltaFromV12: 0,
        directSourceFibreFusionRetained: true,
        transportedMotiveReflexiveFibreFusionRetained: true,
        v12PreDeltaFusionRetained: false,
        pathoutPiTransportPostDeltaFusionAuthorized: true,
        pathoutPiTransportPostDeltaFusionRuleId:
            PATHOUT_PI_TRANSPORT_POST_DELTA_FUSION_ID,
        pathoutPiTransportFusionMustRemainLocal: true,
        pathoutPiTransportFusionMustSubjectCheck: true,
        pathoutPiTransportFusionMustCompileAfterPrefix: true,
        pathoutPiTransportFusionClosesCompleteFunctorParent: true,
        pathoutPiTransportFusionUsesStablePostDeltaType: true,
        pathoutPiTransportFusionUsesActiveSectionFacadeOnly: true,
        pathoutPiTransportFusionUsesActiveSectionPullbackOnly: true,
        genericPrerequisites: {
            comparisonRow:
                'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-1',
            declarationBudgetRow:
                'CORE-LF-TRANSFER-DECLARATION-BUDGET-1',
            sharedSemanticCheckpoint: 'e560551',
            bothComplete: true,
            originalSourceRootReplayRequired: true,
            exactRequestedBudgetPropagationRequired: true
        },
        newMathematicalRuntimeEquationAuthorized: false,
        additionalRuntimeRuleAuthorized: false,
        newProofRuleAuthorized: false,
        declarationBodyOrTypeChangeAuthorized: false,
        declarationSourceOrderChangeAuthorized: false,
        underlyingCategoryEqualityAuthorized: false,
        genericSectionCategoryRuntimeRuleAuthorized: false,
        genericPullbackRuleChangeAuthorized: false,
        genericComparisonChangeAuthorized: false,
        genericDeclarationProofIntegrationAuthorized: false,
        genericRuntimeMatcherChangeAuthorized: false,
        genericCheckerChangeAuthorized: false,
        pathIndSpecificComparisonBudgetAuthorized: false,
        inheritedProofProgramDependencyAuthorized: false,
        genericFixedEvaluationRuntimeImportAuthorized: false,
        alternatePathIndTypeAuthorized: false,
        alternatePathIndTransfdTypeAuthorized: false,
        alternatePathIndComponentBodyAuthorized: false,
        alternatePathIndTransfdComponentBodyAuthorized: false,
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
        proposalCheckpoint: PROPOSAL_CHECKPOINT,
        proposalSha256: PROPOSAL_SHA256,
        rootTypecheck: 'passed',
        focusedLint: 'passed',
        focusedProposalGate: '12-tests-12-pass-zero-fail',
        genericSemanticCheckpoint: 'e560551',
        genericFullTypeScriptGate:
            '1923-tests-1867-pass-56-skip-zero-fail',
        LambdapiProposalGate: 'not-required-no-behavior',
        longAggregateGate:
            'carried-forward-from-e560551-no-rerun-for-root-local-review'
    },
    gitBoundary: {
        localImplementationCheckpointAuthorized: true,
        exactStagedDiffReviewRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false
    },
    nonEffects: [
        'does-not-mutate-proposal-v13-or-historical-evidence',
        'does-not-itself-implement-internalized-PathInd',
        'does-not-authorize-an-equation-beyond-active-v3.2',
        'does-not-change-any-selected-declaration-body-or-type',
        'does-not-change-the-order-of-the-seven-derived-declarations',
        'does-not-retain-the-unreachable-v12-pre-delta-fusion',
        'does-not-add-a-thirteenth-runtime-rule',
        'does-not-install-a-generic-Pi-cat-to-Functord-cat-runtime-rule',
        'does-not-equate-section-and-displayed-functor-categories',
        'does-not-change-the-generic-pullback-fibre-rule',
        'does-not-authorize-proof-program-integration',
        'does-not-authorize-a-PathInd-specific-comparison-budget',
        'does-not-authorize-generic-runtime-matcher-or-checker-widening',
        'does-not-authorize-whole-scale-stress-2b3-profile-import',
        'does-not-authorize-external-or-arbitrary-Sigma-naturality',
        'does-not-authorize-transitivity-or-the-Path-category-bridge',
        'does-not-add-a-Core-owner-checker-or-evaluator-branch',
        'does-not-authorize-safe-library-rule-registration',
        'does-not-authorize-text-browser-or-package-presentation',
        'does-not-authorize-active-Lambdapi-source-change',
        'does-not-authorize-push-merge-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'pathind-internalized-1d-corrected-v13-implementation-ready'
} as const;

export type CorePathindInternalized1dReviewV13 = typeof rawReview;

export type CorePathindInternalized1dReviewV13ErrorCode =
    | 'PATHIND_INTERNALIZED_REVIEW_V13_DECISION_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V13_PROPOSAL_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V13_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dReviewV13Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dReviewV13ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dReviewV13Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_REVIEW_V13 =
    deepFreeze(rawReview);

export function validateCorePathindInternalized1dReviewV13(
    review: CorePathindInternalized1dReviewV13 =
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V13
): CorePathindInternalized1dReviewV13 {
    validateCorePathindInternalized1dProposalV13(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-13' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-INTERNALIZED-13' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-INTERNALIZED-013' ||
        review.approval.decision !==
            'corrected-proposal-v13-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== '39abb02' ||
        review.approval.supersededReviewCheckpoint !== '8833f8f' ||
        review.approval.supersededLedgerCheckpoint !== null
    ) {
        throw new CorePathindInternalized1dReviewV13Error(
            'PATHIND_INTERNALIZED_REVIEW_V13_DECISION_DRIFT',
            'The exact delegated corrected-v13 decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
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
        )
    ) {
        throw new CorePathindInternalized1dReviewV13Error(
            'PATHIND_INTERNALIZED_REVIEW_V13_PROPOSAL_DRIFT',
            'The reviewed proposal v13 bytes drifted'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        authorization.trustedDeclarationCount !== 4 ||
        authorization.runtimeRuleCount !== 12 ||
        authorization.mathematicalRuntimeProjectionCount !== 5 ||
        authorization.derivedRuntimeSupportRuleCount !== 7 ||
        authorization.proofRuleCount !== 0 ||
        authorization.transparentDefinitionCount !== 10 ||
        authorization.typedLibraryConsumerCount !== 2 ||
        authorization.negativeConsumerCount !== 10 ||
        authorization.selectedRuntimeObservationCount !== 10 ||
        authorization.boundedOracleAssertionCount !== 12 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        !authorization.stagedRuntimePartitionAuthorized ||
        authorization.baseRuntimeRuleCount !== 9 ||
        authorization.prefixTransparentDefinitionCount !== 3 ||
        authorization.extensionRuntimeRuleCount !== 3 ||
        authorization.suffixTransparentDefinitionCount !== 4 ||
        !authorization.declarationOrderPreserved ||
        authorization.semanticCountDeltaFromV12 !== 0 ||
        !authorization.directSourceFibreFusionRetained ||
        !authorization.transportedMotiveReflexiveFibreFusionRetained ||
        authorization.v12PreDeltaFusionRetained ||
        !authorization.pathoutPiTransportPostDeltaFusionAuthorized ||
        authorization.pathoutPiTransportPostDeltaFusionRuleId !==
            PATHOUT_PI_TRANSPORT_POST_DELTA_FUSION_ID ||
        !authorization.pathoutPiTransportFusionMustRemainLocal ||
        !authorization.pathoutPiTransportFusionMustSubjectCheck ||
        !authorization.pathoutPiTransportFusionMustCompileAfterPrefix ||
        !authorization.pathoutPiTransportFusionClosesCompleteFunctorParent ||
        !authorization.pathoutPiTransportFusionUsesStablePostDeltaType ||
        !authorization.pathoutPiTransportFusionUsesActiveSectionFacadeOnly ||
        !authorization.pathoutPiTransportFusionUsesActiveSectionPullbackOnly ||
        authorization.genericPrerequisites.sharedSemanticCheckpoint !==
            'e560551' ||
        !authorization.genericPrerequisites.bothComplete ||
        authorization.newMathematicalRuntimeEquationAuthorized ||
        authorization.additionalRuntimeRuleAuthorized ||
        authorization.newProofRuleAuthorized ||
        authorization.declarationBodyOrTypeChangeAuthorized ||
        authorization.declarationSourceOrderChangeAuthorized ||
        authorization.underlyingCategoryEqualityAuthorized ||
        authorization.genericSectionCategoryRuntimeRuleAuthorized ||
        authorization.genericPullbackRuleChangeAuthorized ||
        authorization.genericComparisonChangeAuthorized ||
        authorization.genericDeclarationProofIntegrationAuthorized ||
        authorization.genericRuntimeMatcherChangeAuthorized ||
        authorization.genericCheckerChangeAuthorized ||
        authorization.pathIndSpecificComparisonBudgetAuthorized ||
        authorization.retainedTemporaryObserverAuthorized ||
        authorization.wholeScaleStress2b3ImportAuthorized ||
        authorization.transitivityDefinitionsAuthorized ||
        authorization.newCoreOrCheckerPrimitiveAuthorized ||
        authorization.browserOrPublicPackageExportAuthorized ||
        authorization.activeLambdapiSourceChangeAuthorized ||
        authorization.externalIntegrationOrReleaseAuthorized ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized
    ) {
        throw new CorePathindInternalized1dReviewV13Error(
            'PATHIND_INTERNALIZED_REVIEW_V13_AUTHORIZATION_DRIFT',
            'The reviewed one-for-one 4/12/0/10 authorization drifted'
        );
    }
    return review;
}
