/**
 * Separate immutable review of corrected
 * PATHOUT-LIBRARY-INTERNALIZED-1D proposal v11.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11,
    CorePathindInternalized1dProposalV11,
    validateCorePathindInternalized1dProposalV11
} from './pathind_internalized_proposal_v11';

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

const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11;

const PROPOSAL_CHECKPOINT = '2e1e593';
const PROPOSAL_SHA256 =
    '82fb6f02cf2be16b2dfe8b240ee6d4abcdacc2bfb2cb135b03affdc8bd3097d2';

const TARGET_FIBRE_FUSION_ID =
    'pathind.internalized.' +
    'transported-motive-reflexive-fibre-presentation-fusion';

const rawReview = {
    revision: 'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-11',
    status:
        'reviewed-corrected-proposal-v11-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-11',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-011',
        decision: 'corrected-proposal-v11-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: '270da40',
        supersededReviewCheckpoint: '302c4a9',
        supersededLedgerCheckpoint: null
    },
    recommendation:
        cloneData(proposal) as CorePathindInternalized1dProposalV11,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
        implementationAuthorized: true,
        exactImplementation: cloneData(proposal.exactImplementation),
        exactDependencyClosure: cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor: cloneData(proposal.selectedPredecessor),
        trustedDeclarationCount: 4,
        runtimeRuleCount: 11,
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 6,
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
        extensionRuntimeRuleCount: 2,
        suffixTransparentDefinitionCount: 4,
        declarationOrderPreserved: true,
        semanticCountDeltaFromV10: 1,
        directSourceFibreFusionRetained: true,
        transportedMotiveReflexiveFibreFusionAuthorized: true,
        transportedMotiveReflexiveFibreFusionRuleId:
            TARGET_FIBRE_FUSION_ID,
        targetFibreFusionMustRemainLocal: true,
        targetFibreFusionMustSubjectCheck: true,
        targetFibreFusionMustCompileAfterPrefix: true,
        targetFibreFusionUsesActivePullbackFibreOnly: true,
        targetFibreFusionUsesQualifiedPathoutActionOnly: true,
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
        focusedProposalGate: '6-tests-6-pass-zero-fail',
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
        'does-not-mutate-proposal-v11-or-historical-evidence',
        'does-not-itself-implement-internalized-PathInd',
        'does-not-authorize-an-equation-beyond-active-v3.2',
        'does-not-change-any-selected-declaration-body-or-type',
        'does-not-change-the-order-of-the-seven-derived-declarations',
        'does-not-add-a-twelfth-runtime-rule',
        'does-not-equate-PathOut-cat-with-the-total-motive-category',
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
        'pathind-internalized-1d-corrected-v11-implementation-ready'
} as const;

export type CorePathindInternalized1dReviewV11 = typeof rawReview;

export type CorePathindInternalized1dReviewV11ErrorCode =
    | 'PATHIND_INTERNALIZED_REVIEW_V11_DECISION_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V11_PROPOSAL_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V11_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dReviewV11Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dReviewV11ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dReviewV11Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_REVIEW_V11 =
    deepFreeze(rawReview);

export function validateCorePathindInternalized1dReviewV11(
    review: CorePathindInternalized1dReviewV11 =
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V11
): CorePathindInternalized1dReviewV11 {
    validateCorePathindInternalized1dProposalV11(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-11' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-INTERNALIZED-11' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-INTERNALIZED-011' ||
        review.approval.decision !==
            'corrected-proposal-v11-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== '270da40' ||
        review.approval.supersededReviewCheckpoint !== '302c4a9' ||
        review.approval.supersededLedgerCheckpoint !== null
    ) {
        throw new CorePathindInternalized1dReviewV11Error(
            'PATHIND_INTERNALIZED_REVIEW_V11_DECISION_DRIFT',
            'The exact delegated corrected-v11 decision drifted'
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
        throw new CorePathindInternalized1dReviewV11Error(
            'PATHIND_INTERNALIZED_REVIEW_V11_PROPOSAL_DRIFT',
            'The reviewed proposal v11 bytes drifted'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        authorization.trustedDeclarationCount !== 4 ||
        authorization.runtimeRuleCount !== 11 ||
        authorization.mathematicalRuntimeProjectionCount !== 5 ||
        authorization.derivedRuntimeSupportRuleCount !== 6 ||
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
        authorization.extensionRuntimeRuleCount !== 2 ||
        authorization.suffixTransparentDefinitionCount !== 4 ||
        !authorization.declarationOrderPreserved ||
        authorization.semanticCountDeltaFromV10 !== 1 ||
        !authorization.directSourceFibreFusionRetained ||
        !authorization.transportedMotiveReflexiveFibreFusionAuthorized ||
        authorization.transportedMotiveReflexiveFibreFusionRuleId !==
            TARGET_FIBRE_FUSION_ID ||
        !authorization.targetFibreFusionMustRemainLocal ||
        !authorization.targetFibreFusionMustSubjectCheck ||
        !authorization.targetFibreFusionMustCompileAfterPrefix ||
        !authorization.targetFibreFusionUsesActivePullbackFibreOnly ||
        !authorization.targetFibreFusionUsesQualifiedPathoutActionOnly ||
        authorization.genericPrerequisites.sharedSemanticCheckpoint !==
            'e560551' ||
        !authorization.genericPrerequisites.bothComplete ||
        !authorization.genericPrerequisites.originalSourceRootReplayRequired ||
        !authorization.genericPrerequisites
            .exactRequestedBudgetPropagationRequired ||
        authorization.newMathematicalRuntimeEquationAuthorized ||
        authorization.newProofRuleAuthorized ||
        authorization.declarationBodyOrTypeChangeAuthorized ||
        authorization.declarationSourceOrderChangeAuthorized ||
        authorization.underlyingCategoryEqualityAuthorized ||
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
        throw new CorePathindInternalized1dReviewV11Error(
            'PATHIND_INTERNALIZED_REVIEW_V11_AUTHORIZATION_DRIFT',
            'The reviewed staged 4/11/0/10 authorization drifted'
        );
    }
    return review;
}
