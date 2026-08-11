/**
 * Separate immutable review of corrected
 * PATHOUT-LIBRARY-INTERNALIZED-1D proposal v5.
 *
 * The review approves only checkpoint fe0306d under the user's standing
 * unattended delegation, with later human supersession. PathInd semantic
 * checkpointing remains conditional on the separately reviewed generic
 * comparison closure reaching its own green semantic checkpoint.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5,
    CorePathindInternalized1dProposalV5,
    validateCorePathindInternalized1dProposalV5
} from './pathind_internalized_proposal_v5';

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

const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5;

const PROPOSAL_CHECKPOINT = 'fe0306d';
const PROPOSAL_SHA256 =
    '9a9adef53c4d682def1528ff194fce11838bb4899de94169fa7fbe21f67eccda';

const PI_PULLBACK_COMPONENT_RULE_ID =
    'pathind.internalized.pi-pullback-component';

const rawReview = {
    revision: 'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-5',
    status:
        'reviewed-corrected-proposal-v5-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-05',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-005',
        decision: 'corrected-proposal-v5-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: '001a899',
        supersededReviewCheckpoint: '7984efb',
        supersededLedgerCheckpoint: '5d1851f'
    },
    recommendation:
        cloneData(proposal) as CorePathindInternalized1dProposalV5,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
        implementationAuthorized: true,
        exactImplementation: cloneData(proposal.exactImplementation),
        exactDependencyClosure: cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor: cloneData(proposal.selectedPredecessor),
        trustedDeclarationCount: 4,
        runtimeRuleCount: 7,
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 2,
        proofRuleCount: 0,
        transparentDefinitionCount: 10,
        typedLibraryConsumerCount: 2,
        negativeConsumerCount: 10,
        selectedRuntimeObservationCount: 10,
        boundedOracleAssertionCount: 12,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        exactFourOwnersAuthorized: true,
        exactFiveMathematicalProjectionsAuthorized: true,
        exactTwoDerivedSupportRulesAuthorized: true,
        piPullbackComponentProjectionAuthorized: true,
        piPullbackComponentProjectionRuleId:
            PI_PULLBACK_COMPONENT_RULE_ID,
        piPullbackInferredFamilySlotsMustRemainTypedWildcards: true,
        piPullbackComponentMustSubjectCheck: true,
        genericComparisonPrerequisite: {
            row: 'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-1',
            proposalCheckpoint: 'cf8ed76',
            reviewCheckpoint: '778da06',
            semanticCheckpointRequiredBeforePathIndCheckpoint: true
        },
        tenTransparentDefinitionsAuthorized: true,
        primaryTheoremIsPathIndTransfd: true,
        pathIndFuncdIsTransparentDerivedPresentation: true,
        sourceArrowMustRemainInternallyOwned: true,
        higherActionMustRemainInternallyOwned: true,
        newRuntimeEquationAuthorized: false,
        newProofRuleAuthorized: false,
        pathIndSpecificOuterCommutingRuleAuthorized: false,
        overSpecifiedInferredFamilySlotsAuthorized: false,
        genericCategoryCollapseAuthorized: false,
        genericRuntimeMatcherChangeAuthorized: false,
        genericCheckerChangeAuthorized: false,
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
        'does-not-mutate-proposal-v5-or-historical-evidence',
        'does-not-itself-implement-internalized-PathInd',
        'does-not-authorize-a-new-equation-beyond-active-v3.2',
        'does-not-authorize-over-specified-inferred-family-slots',
        'does-not-authorize-a-PathInd-specific-outer-commuting-rule',
        'does-not-authorize-generic-runtime-matcher-or-checker-widening',
        'does-not-bypass-the-generic-comparison-semantic-checkpoint',
        'does-not-authorize-proof-program-integration',
        'does-not-authorize-whole-scale-stress-2b3-profile-import',
        'does-not-authorize-external-or-arbitrary-Sigma-naturality',
        'does-not-collapse-internally-owned-source-arrow-or-higher-action',
        'does-not-authorize-transitivity-or-the-Path-category-bridge',
        'does-not-add-a-Core-owner-checker-or-evaluator-branch',
        'does-not-authorize-safe-library-rule-registration',
        'does-not-authorize-text-browser-or-package-presentation',
        'does-not-authorize-active-Lambdapi-source-change',
        'does-not-authorize-push-merge-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'pathind-internalized-1d-corrected-v5-implementation-ready-after-' +
        'generic-comparison-semantic-checkpoint'
} as const;

export type CorePathindInternalized1dReviewV5 = typeof rawReview;

export type CorePathindInternalized1dReviewV5ErrorCode =
    | 'PATHIND_INTERNALIZED_REVIEW_V5_DECISION_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V5_PROPOSAL_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V5_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dReviewV5Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dReviewV5ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dReviewV5Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_REVIEW_V5 =
    deepFreeze(rawReview);

export function validateCorePathindInternalized1dReviewV5(
    review: CorePathindInternalized1dReviewV5 =
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V5
): CorePathindInternalized1dReviewV5 {
    validateCorePathindInternalized1dProposalV5();
    if (
        review.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-5' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-INTERNALIZED-05' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-INTERNALIZED-005' ||
        review.approval.decision !==
            'corrected-proposal-v5-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !==
            PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== '001a899' ||
        review.approval.supersededReviewCheckpoint !== '7984efb' ||
        review.approval.supersededLedgerCheckpoint !== '5d1851f'
    ) {
        throw new CorePathindInternalized1dReviewV5Error(
            'PATHIND_INTERNALIZED_REVIEW_V5_DECISION_DRIFT',
            'The exact delegated corrected-v5 decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-5' ||
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
        review.validation.proposalCheckpoint !== PROPOSAL_CHECKPOINT ||
        review.validation.proposalSha256 !==
            review.approval.approvedProposalSha256
    ) {
        throw new CorePathindInternalized1dReviewV5Error(
            'PATHIND_INTERNALIZED_REVIEW_V5_PROPOSAL_DRIFT',
            'The review must retain exact non-authorizing proposal v5'
        );
    }

    const authorization = review.authorization;
    const prerequisite = authorization.genericComparisonPrerequisite;
    if (
        authorization.implementationRow !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D' ||
        !authorization.implementationAuthorized ||
        authorization.trustedDeclarationCount !== 4 ||
        authorization.runtimeRuleCount !== 7 ||
        authorization.mathematicalRuntimeProjectionCount !== 5 ||
        authorization.derivedRuntimeSupportRuleCount !== 2 ||
        authorization.proofRuleCount !== 0 ||
        authorization.transparentDefinitionCount !== 10 ||
        authorization.typedLibraryConsumerCount !== 2 ||
        authorization.negativeConsumerCount !== 10 ||
        authorization.selectedRuntimeObservationCount !== 10 ||
        authorization.boundedOracleAssertionCount !== 12 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        !authorization.exactFourOwnersAuthorized ||
        !authorization.exactFiveMathematicalProjectionsAuthorized ||
        !authorization.exactTwoDerivedSupportRulesAuthorized ||
        !authorization.piPullbackComponentProjectionAuthorized ||
        authorization.piPullbackComponentProjectionRuleId !==
            PI_PULLBACK_COMPONENT_RULE_ID ||
        !authorization
            .piPullbackInferredFamilySlotsMustRemainTypedWildcards ||
        !authorization.piPullbackComponentMustSubjectCheck ||
        prerequisite.row !==
            'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-1' ||
        prerequisite.proposalCheckpoint !== 'cf8ed76' ||
        prerequisite.reviewCheckpoint !== '778da06' ||
        !prerequisite.semanticCheckpointRequiredBeforePathIndCheckpoint ||
        authorization.newRuntimeEquationAuthorized ||
        authorization.newProofRuleAuthorized ||
        authorization.pathIndSpecificOuterCommutingRuleAuthorized ||
        authorization.overSpecifiedInferredFamilySlotsAuthorized ||
        authorization.genericCategoryCollapseAuthorized ||
        authorization.genericRuntimeMatcherChangeAuthorized ||
        authorization.genericCheckerChangeAuthorized ||
        authorization.inheritedProofProgramDependencyAuthorized ||
        authorization.genericFixedEvaluationRuntimeImportAuthorized ||
        authorization.alternatePathIndTypeAuthorized ||
        authorization.alternatePathIndTransfdTypeAuthorized ||
        authorization.alternatePathIndComponentBodyAuthorized ||
        authorization.alternatePathIndTransfdComponentBodyAuthorized ||
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
            'pathind-internalized-1d-corrected-v5-implementation-ready-' +
            'after-generic-comparison-semantic-checkpoint'
    ) {
        throw new CorePathindInternalized1dReviewV5Error(
            'PATHIND_INTERNALIZED_REVIEW_V5_AUTHORIZATION_DRIFT',
            'The exact 4/7/0/10 authorization widened or weakened'
        );
    }
    return review;
}
