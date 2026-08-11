/**
 * Separate immutable review of corrected
 * PATHOUT-LIBRARY-INTERNALIZED-1D proposal v10.
 *
 * The review authorizes only the staged 4/10/0/10 boundary checkpointed at
 * 270da40. In particular, the tenth runtime rule may be compiled only after
 * the three-definition prefix has declared PathIndSrc_catd.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10,
    CorePathindInternalized1dProposalV10,
    validateCorePathindInternalized1dProposalV10
} from './pathind_internalized_proposal_v10';

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

const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10;

const PROPOSAL_CHECKPOINT = '270da40';
const PROPOSAL_SHA256 =
    '898cbcd3d56859ae69c0b8646f45bc5792ff5205739720289c22699f3435324b';

const STAGED_SOURCE_FIBRE_FUSION_ID =
    'pathind.internalized.' +
    'path-ind-source-fibre-at-sigma-pair-presentation-fusion';

const rawReview = {
    revision: 'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-10',
    status:
        'reviewed-corrected-proposal-v10-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-10',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-010',
        decision: 'corrected-proposal-v10-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: 'a735c40',
        supersededReviewCheckpoint: '7b466d5',
        supersededLedgerCheckpoint: null
    },
    recommendation:
        cloneData(proposal) as CorePathindInternalized1dProposalV10,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
        implementationAuthorized: true,
        exactImplementation: cloneData(proposal.exactImplementation),
        exactDependencyClosure: cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor: cloneData(proposal.selectedPredecessor),
        trustedDeclarationCount: 4,
        runtimeRuleCount: 10,
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 5,
        proofRuleCount: 0,
        transparentDefinitionCount: 10,
        typedLibraryConsumerCount: 2,
        negativeConsumerCount: 10,
        selectedRuntimeObservationCount: 10,
        boundedOracleAssertionCount: 12,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        exactFiveMathematicalProjectionsAuthorized: true,
        exactFiveDerivedSupportRulesAuthorized: true,
        stagedRuntimePartitionAuthorized: true,
        baseRuntimeRuleCount: 9,
        prefixTransparentDefinitionCount: 3,
        extensionRuntimeRuleCount: 1,
        suffixTransparentDefinitionCount: 4,
        declarationOrderPreserved: true,
        semanticCountDelta: 0,
        stagedSourceFibreFusionAuthorized: true,
        stagedSourceFibreFusionRuleId: STAGED_SOURCE_FIBRE_FUSION_ID,
        sourceFibreFusionMustRemainLocal: true,
        sourceFibreFusionMustSubjectCheck: true,
        sourceFibreFusionMustCompileAfterPrefix: true,
        sourceFibreFusionUsesDeclaredPathIndSrcAtItsStage: true,
        sourceFibreFusionBeforePrefixAuthorized: false,
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
        allNineV7RuntimeRulesRetainedInBase: true,
        newMathematicalRuntimeEquationAuthorized: false,
        newProofRuleAuthorized: false,
        declarationBodyOrTypeChangeAuthorized: false,
        declarationSourceOrderChangeAuthorized: false,
        underlyingCategoryEqualityAuthorized: false,
        genericSigmaFibreRuleAuthorized: false,
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
        'does-not-mutate-proposal-v10-or-historical-evidence',
        'does-not-itself-implement-internalized-PathInd',
        'does-not-authorize-an-equation-beyond-active-v3.2',
        'does-not-change-any-selected-declaration-body-or-type',
        'does-not-change-the-order-of-the-seven-derived-declarations',
        'does-not-add-an-eleventh-runtime-rule',
        'does-not-equate-PathOut-cat-with-the-total-motive-category',
        'does-not-authorize-a-generic-Sigma-fibre-shortcut',
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
        'pathind-internalized-1d-corrected-v10-implementation-ready'
} as const;

export type CorePathindInternalized1dReviewV10 = typeof rawReview;

export type CorePathindInternalized1dReviewV10ErrorCode =
    | 'PATHIND_INTERNALIZED_REVIEW_V10_DECISION_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V10_PROPOSAL_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V10_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dReviewV10Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dReviewV10ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dReviewV10Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_REVIEW_V10 =
    deepFreeze(rawReview);

export function validateCorePathindInternalized1dReviewV10(
    review: CorePathindInternalized1dReviewV10 =
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V10
): CorePathindInternalized1dReviewV10 {
    validateCorePathindInternalized1dProposalV10(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-10' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-INTERNALIZED-10' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-INTERNALIZED-010' ||
        review.approval.decision !==
            'corrected-proposal-v10-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== 'a735c40' ||
        review.approval.supersededReviewCheckpoint !== '7b466d5' ||
        review.approval.supersededLedgerCheckpoint !== null
    ) {
        throw new CorePathindInternalized1dReviewV10Error(
            'PATHIND_INTERNALIZED_REVIEW_V10_DECISION_DRIFT',
            'The exact delegated corrected-v10 decision drifted'
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
        throw new CorePathindInternalized1dReviewV10Error(
            'PATHIND_INTERNALIZED_REVIEW_V10_PROPOSAL_DRIFT',
            'The reviewed proposal v10 bytes drifted'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        authorization.trustedDeclarationCount !== 4 ||
        authorization.runtimeRuleCount !== 10 ||
        authorization.mathematicalRuntimeProjectionCount !== 5 ||
        authorization.derivedRuntimeSupportRuleCount !== 5 ||
        authorization.proofRuleCount !== 0 ||
        authorization.transparentDefinitionCount !== 10 ||
        authorization.typedLibraryConsumerCount !== 2 ||
        authorization.negativeConsumerCount !== 10 ||
        authorization.selectedRuntimeObservationCount !== 10 ||
        authorization.boundedOracleAssertionCount !== 12 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        !authorization.exactFiveMathematicalProjectionsAuthorized ||
        !authorization.exactFiveDerivedSupportRulesAuthorized ||
        !authorization.stagedRuntimePartitionAuthorized ||
        authorization.baseRuntimeRuleCount !== 9 ||
        authorization.prefixTransparentDefinitionCount !== 3 ||
        authorization.extensionRuntimeRuleCount !== 1 ||
        authorization.suffixTransparentDefinitionCount !== 4 ||
        !authorization.declarationOrderPreserved ||
        authorization.semanticCountDelta !== 0 ||
        !authorization.stagedSourceFibreFusionAuthorized ||
        authorization.stagedSourceFibreFusionRuleId !==
            STAGED_SOURCE_FIBRE_FUSION_ID ||
        !authorization.sourceFibreFusionMustRemainLocal ||
        !authorization.sourceFibreFusionMustSubjectCheck ||
        !authorization.sourceFibreFusionMustCompileAfterPrefix ||
        !authorization.sourceFibreFusionUsesDeclaredPathIndSrcAtItsStage ||
        authorization.sourceFibreFusionBeforePrefixAuthorized ||
        authorization.genericPrerequisites.sharedSemanticCheckpoint !==
            'e560551' ||
        !authorization.genericPrerequisites.bothComplete ||
        !authorization.genericPrerequisites.originalSourceRootReplayRequired ||
        !authorization.genericPrerequisites
            .exactRequestedBudgetPropagationRequired ||
        !authorization.allNineV7RuntimeRulesRetainedInBase ||
        authorization.newMathematicalRuntimeEquationAuthorized ||
        authorization.newProofRuleAuthorized ||
        authorization.declarationBodyOrTypeChangeAuthorized ||
        authorization.declarationSourceOrderChangeAuthorized ||
        authorization.underlyingCategoryEqualityAuthorized ||
        authorization.genericSigmaFibreRuleAuthorized ||
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
        throw new CorePathindInternalized1dReviewV10Error(
            'PATHIND_INTERNALIZED_REVIEW_V10_AUTHORIZATION_DRIFT',
            'The reviewed staged 4/10/0/10 authorization drifted'
        );
    }
    return review;
}
