/**
 * Separate immutable review of corrected
 * PATHOUT-LIBRARY-INTERNALIZED-1D proposal v7.
 *
 * The review approves only checkpoint ef761e4 under the user's standing
 * unattended delegation, with later human supersession. The completed
 * generic checkpoint e560551 is a fixed prerequisite, not new authority.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7,
    CorePathindInternalized1dProposalV7,
    validateCorePathindInternalized1dProposalV7
} from './pathind_internalized_proposal_v7';

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

const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7;

const PROPOSAL_CHECKPOINT = 'ef761e4';
const PROPOSAL_SHA256 =
    'e56b79f367dd7d92cae10a649a6f9cb5e13c563ddc39f4e4812b32ed2a270313';

const ACTION_PRESENTATION_FUSION_ID =
    'pathind.internalized.' +
    'motive-transport-action-category-presentation-fusion';

const rawReview = {
    revision: 'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-7',
    status:
        'reviewed-corrected-proposal-v7-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-07',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-007',
        decision: 'corrected-proposal-v7-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: '19eb941',
        supersededReviewCheckpoint: '2112543',
        supersededLedgerCheckpoint: null
    },
    recommendation:
        cloneData(proposal) as CorePathindInternalized1dProposalV7,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
        implementationAuthorized: true,
        exactImplementation: cloneData(proposal.exactImplementation),
        exactDependencyClosure: cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor: cloneData(proposal.selectedPredecessor),
        trustedDeclarationCount: 4,
        runtimeRuleCount: 9,
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 4,
        proofRuleCount: 0,
        transparentDefinitionCount: 10,
        typedLibraryConsumerCount: 2,
        negativeConsumerCount: 10,
        selectedRuntimeObservationCount: 10,
        boundedOracleAssertionCount: 12,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        exactFiveMathematicalProjectionsAuthorized: true,
        exactFourDerivedSupportRulesAuthorized: true,
        motiveTransportActionCategoryPresentationFusionAuthorized: true,
        motiveTransportActionCategoryPresentationFusionRuleId:
            ACTION_PRESENTATION_FUSION_ID,
        motiveTransportActionFusionMustRemainLocal: true,
        motiveTransportActionFusionMustSubjectCheck: true,
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
        tenTransparentDefinitionsAuthorized: true,
        allEightV6RuntimeRulesRetained: true,
        newRuntimeEquationAuthorized: false,
        newProofRuleAuthorized: false,
        underlyingCategoryCollapseAuthorized: false,
        genericActionCategoryFusionAuthorized: false,
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
        'does-not-mutate-proposal-v7-or-historical-evidence',
        'does-not-itself-implement-internalized-PathInd',
        'does-not-authorize-an-equation-beyond-active-v3.2',
        'does-not-authorize-an-underlying-category-collapse',
        'does-not-authorize-a-generic-action-category-fusion',
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
        'pathind-internalized-1d-corrected-v7-implementation-ready'
} as const;

export type CorePathindInternalized1dReviewV7 = typeof rawReview;

export type CorePathindInternalized1dReviewV7ErrorCode =
    | 'PATHIND_INTERNALIZED_REVIEW_V7_DECISION_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V7_PROPOSAL_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V7_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dReviewV7Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dReviewV7ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dReviewV7Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_REVIEW_V7 =
    deepFreeze(rawReview);

export function validateCorePathindInternalized1dReviewV7(
    review: CorePathindInternalized1dReviewV7 =
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V7
): CorePathindInternalized1dReviewV7 {
    validateCorePathindInternalized1dProposalV7(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-7' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-INTERNALIZED-07' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-INTERNALIZED-007' ||
        review.approval.decision !==
            'corrected-proposal-v7-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !==
            PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== '19eb941' ||
        review.approval.supersededReviewCheckpoint !== '2112543' ||
        review.approval.supersededLedgerCheckpoint !== null
    ) {
        throw new CorePathindInternalized1dReviewV7Error(
            'PATHIND_INTERNALIZED_REVIEW_V7_DECISION_DRIFT',
            'The exact delegated corrected-v7 decision drifted'
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
        throw new CorePathindInternalized1dReviewV7Error(
            'PATHIND_INTERNALIZED_REVIEW_V7_PROPOSAL_DRIFT',
            'The reviewed proposal v7 bytes drifted'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        authorization.trustedDeclarationCount !== 4 ||
        authorization.runtimeRuleCount !== 9 ||
        authorization.mathematicalRuntimeProjectionCount !== 5 ||
        authorization.derivedRuntimeSupportRuleCount !== 4 ||
        authorization.proofRuleCount !== 0 ||
        authorization.transparentDefinitionCount !== 10 ||
        authorization.typedLibraryConsumerCount !== 2 ||
        authorization.negativeConsumerCount !== 10 ||
        authorization.selectedRuntimeObservationCount !== 10 ||
        authorization.boundedOracleAssertionCount !== 12 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        !authorization.exactFiveMathematicalProjectionsAuthorized ||
        !authorization.exactFourDerivedSupportRulesAuthorized ||
        !authorization
            .motiveTransportActionCategoryPresentationFusionAuthorized ||
        authorization
            .motiveTransportActionCategoryPresentationFusionRuleId !==
            ACTION_PRESENTATION_FUSION_ID ||
        !authorization.motiveTransportActionFusionMustRemainLocal ||
        !authorization.motiveTransportActionFusionMustSubjectCheck ||
        authorization.genericPrerequisites.sharedSemanticCheckpoint !==
            'e560551' ||
        !authorization.genericPrerequisites.bothComplete ||
        !authorization.genericPrerequisites.originalSourceRootReplayRequired ||
        !authorization.genericPrerequisites
            .exactRequestedBudgetPropagationRequired ||
        !authorization.allEightV6RuntimeRulesRetained ||
        authorization.newRuntimeEquationAuthorized ||
        authorization.newProofRuleAuthorized ||
        authorization.underlyingCategoryCollapseAuthorized ||
        authorization.genericActionCategoryFusionAuthorized ||
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
        throw new CorePathindInternalized1dReviewV7Error(
            'PATHIND_INTERNALIZED_REVIEW_V7_AUTHORIZATION_DRIFT',
            'The reviewed 4/9/0/10 authorization widened or drifted'
        );
    }
    return review;
}
