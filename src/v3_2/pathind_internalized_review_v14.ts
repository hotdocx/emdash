/**
 * Separate immutable review of corrected
 * PATHOUT-LIBRARY-INTERNALIZED-1D proposal v14.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14,
    CorePathindInternalized1dProposalV14,
    validateCorePathindInternalized1dProposalV14
} from './pathind_internalized_proposal_v14';

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

const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14;

const PROPOSAL_CHECKPOINT = '4244b54';
const PROPOSAL_SHA256 =
    '6ddf101160ab62b5209eb6c416e732c00b69025cfba8ffa562f7fffc43140e34';

const TARGET_FIBRE_FUSION_ID =
    'pathind.internalized.' +
    'path-ind-target-fibre-at-sigma-pair-presentation-fusion';

const rawReview = {
    revision: 'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-14',
    status:
        'reviewed-corrected-proposal-v14-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-14',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-014',
        decision: 'corrected-proposal-v14-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: 'd77f0d7',
        supersededReviewCheckpoint: 'a8aff88',
        supersededLedgerCheckpoint: null
    },
    recommendation:
        cloneData(proposal) as CorePathindInternalized1dProposalV14,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
        implementationAuthorized: true,
        exactImplementation: cloneData(proposal.exactImplementation),
        exactDependencyClosure: cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor: cloneData(proposal.selectedPredecessor),
        trustedDeclarationCount: 4,
        runtimeRuleCount: 13,
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 8,
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
        extensionRuntimeRuleCount: 4,
        suffixTransparentDefinitionCount: 4,
        declarationOrderPreserved: true,
        semanticCountDeltaFromV13: 1,
        directSourceFibreFusionRetained: true,
        transportedMotiveReflexiveFibreFusionRetained: true,
        pathoutPiTransportPostDeltaFusionRetained: true,
        pathoutPiTransportCompiledBeforeTargetAlias: true,
        pathInductionTargetFibreFusionAuthorized: true,
        pathInductionTargetFibreFusionRuleId: TARGET_FIBRE_FUSION_ID,
        targetFibreFusionMustRemainLocal: true,
        targetFibreFusionMustSubjectCheck: true,
        targetFibreFusionMustCompileAfterPreludeAndPrefix: true,
        targetFibreFusionCoversBothAliasEndpoints: true,
        targetFibreFusionUsesActivePathIndTgtOnly: true,
        targetFibreFusionUsesActiveSectionFacadeOnly: true,
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
        newProofRuleAuthorized: false,
        declarationBodyOrTypeChangeAuthorized: false,
        declarationSourceOrderChangeAuthorized: false,
        underlyingCategoryEqualityAuthorized: false,
        genericSigmaFibreRuntimeRuleAuthorized: false,
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
        'does-not-mutate-proposal-v14-or-historical-evidence',
        'does-not-itself-implement-internalized-PathInd',
        'does-not-authorize-an-equation-beyond-active-v3.2',
        'does-not-change-any-selected-declaration-body-or-type',
        'does-not-change-the-order-of-the-seven-derived-declarations',
        'does-not-add-a-fourteenth-runtime-rule',
        'does-not-install-a-generic-Sigma-fibre-runtime-rule',
        'does-not-install-a-generic-Pi-cat-to-Functord-cat-runtime-rule',
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
        'pathind-internalized-1d-corrected-v14-implementation-ready'
} as const;

export type CorePathindInternalized1dReviewV14 = typeof rawReview;

export type CorePathindInternalized1dReviewV14ErrorCode =
    | 'PATHIND_INTERNALIZED_REVIEW_V14_DECISION_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V14_PROPOSAL_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V14_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dReviewV14Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dReviewV14ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dReviewV14Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_REVIEW_V14 =
    deepFreeze(rawReview);

export function validateCorePathindInternalized1dReviewV14(
    review: CorePathindInternalized1dReviewV14 =
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V14
): CorePathindInternalized1dReviewV14 {
    validateCorePathindInternalized1dProposalV14(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-14' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-INTERNALIZED-14' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-INTERNALIZED-014' ||
        review.approval.decision !==
            'corrected-proposal-v14-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== 'd77f0d7' ||
        review.approval.supersededReviewCheckpoint !== 'a8aff88' ||
        review.approval.supersededLedgerCheckpoint !== null
    ) {
        throw new CorePathindInternalized1dReviewV14Error(
            'PATHIND_INTERNALIZED_REVIEW_V14_DECISION_DRIFT',
            'The exact delegated corrected-v14 decision drifted'
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
        throw new CorePathindInternalized1dReviewV14Error(
            'PATHIND_INTERNALIZED_REVIEW_V14_PROPOSAL_DRIFT',
            'The reviewed proposal v14 bytes drifted'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        authorization.trustedDeclarationCount !== 4 ||
        authorization.runtimeRuleCount !== 13 ||
        authorization.mathematicalRuntimeProjectionCount !== 5 ||
        authorization.derivedRuntimeSupportRuleCount !== 8 ||
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
        authorization.extensionRuntimeRuleCount !== 4 ||
        authorization.suffixTransparentDefinitionCount !== 4 ||
        !authorization.declarationOrderPreserved ||
        authorization.semanticCountDeltaFromV13 !== 1 ||
        !authorization.directSourceFibreFusionRetained ||
        !authorization.transportedMotiveReflexiveFibreFusionRetained ||
        !authorization.pathoutPiTransportPostDeltaFusionRetained ||
        !authorization.pathoutPiTransportCompiledBeforeTargetAlias ||
        !authorization.pathInductionTargetFibreFusionAuthorized ||
        authorization.pathInductionTargetFibreFusionRuleId !==
            TARGET_FIBRE_FUSION_ID ||
        !authorization.targetFibreFusionMustRemainLocal ||
        !authorization.targetFibreFusionMustSubjectCheck ||
        !authorization.targetFibreFusionMustCompileAfterPreludeAndPrefix ||
        !authorization.targetFibreFusionCoversBothAliasEndpoints ||
        !authorization.targetFibreFusionUsesActivePathIndTgtOnly ||
        !authorization.targetFibreFusionUsesActiveSectionFacadeOnly ||
        authorization.genericPrerequisites.sharedSemanticCheckpoint !==
            'e560551' ||
        !authorization.genericPrerequisites.bothComplete ||
        authorization.newMathematicalRuntimeEquationAuthorized ||
        authorization.newProofRuleAuthorized ||
        authorization.declarationBodyOrTypeChangeAuthorized ||
        authorization.declarationSourceOrderChangeAuthorized ||
        authorization.underlyingCategoryEqualityAuthorized ||
        authorization.genericSigmaFibreRuntimeRuleAuthorized ||
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
        throw new CorePathindInternalized1dReviewV14Error(
            'PATHIND_INTERNALIZED_REVIEW_V14_AUTHORIZATION_DRIFT',
            'The reviewed staged 4/13/0/10 authorization drifted'
        );
    }
    return review;
}
