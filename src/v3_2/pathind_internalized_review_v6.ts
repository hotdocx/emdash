/**
 * Separate immutable review of corrected
 * PATHOUT-LIBRARY-INTERNALIZED-1D proposal v6.
 *
 * The review approves only checkpoint 19eb941 under the user's standing
 * unattended delegation, with later human supersession. PathInd semantic
 * checkpointing remains conditional on the separately reviewed generic
 * comparison-v2 implementation reaching its own green checkpoint.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6,
    CorePathindInternalized1dProposalV6,
    validateCorePathindInternalized1dProposalV6
} from './pathind_internalized_proposal_v6';

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

const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6;

const PROPOSAL_CHECKPOINT = '19eb941';
const PROPOSAL_SHA256 =
    '5f9181e4db004e4a1922d2d5ec72ee6862c7dbeaa40a44ecb88423355bffcf17';

const MOTIVE_TRANSPORT_FUSION_ID =
    'pathind.internalized.' +
    'motive-transport-functor-category-presentation-fusion';

const rawReview = {
    revision: 'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-6',
    status:
        'reviewed-corrected-proposal-v6-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-06',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-006',
        decision: 'corrected-proposal-v6-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: 'fe0306d',
        supersededReviewCheckpoint: 'a94c2f7',
        supersededLedgerCheckpoint: null
    },
    recommendation:
        cloneData(proposal) as CorePathindInternalized1dProposalV6,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
        implementationAuthorized: true,
        exactImplementation: cloneData(proposal.exactImplementation),
        exactDependencyClosure: cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor: cloneData(proposal.selectedPredecessor),
        trustedDeclarationCount: 4,
        runtimeRuleCount: 8,
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 3,
        proofRuleCount: 0,
        transparentDefinitionCount: 10,
        typedLibraryConsumerCount: 2,
        negativeConsumerCount: 10,
        selectedRuntimeObservationCount: 10,
        boundedOracleAssertionCount: 12,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        exactFiveMathematicalProjectionsAuthorized: true,
        exactThreeDerivedSupportRulesAuthorized: true,
        motiveTransportCategoryPresentationFusionAuthorized: true,
        motiveTransportCategoryPresentationFusionRuleId:
            MOTIVE_TRANSPORT_FUSION_ID,
        motiveTransportFusionMustRemainTwoSidedAndDecoded: true,
        motiveTransportFusionMustSubjectCheck: true,
        genericComparisonPrerequisite: {
            row: 'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-1',
            proposalCheckpoint: 'a42ffc9',
            reviewCheckpoint: '5277885',
            semanticCheckpointRequiredBeforePathIndCheckpoint: true,
            originalSourceRootReplayRequired: true
        },
        tenTransparentDefinitionsAuthorized: true,
        allSevenV5RuntimeRulesRetained: true,
        newRuntimeEquationAuthorized: false,
        newProofRuleAuthorized: false,
        underlyingCategoryCollapseAuthorized: false,
        genericTwoSidedCategoryFusionAuthorized: false,
        genericDeclarationProofIntegrationAuthorized: false,
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
        'does-not-mutate-proposal-v6-or-historical-evidence',
        'does-not-itself-implement-internalized-PathInd',
        'does-not-authorize-an-equation-beyond-active-v3.2',
        'does-not-authorize-an-underlying-category-collapse',
        'does-not-authorize-a-generic-two-sided-category-fusion',
        'does-not-authorize-proof-program-integration',
        'does-not-authorize-generic-runtime-matcher-or-checker-widening',
        'does-not-bypass-the-generic-comparison-semantic-checkpoint',
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
        'pathind-internalized-1d-corrected-v6-implementation-ready-after-' +
        'comparison-v2-semantic-checkpoint'
} as const;

export type CorePathindInternalized1dReviewV6 = typeof rawReview;

export type CorePathindInternalized1dReviewV6ErrorCode =
    | 'PATHIND_INTERNALIZED_REVIEW_V6_DECISION_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V6_PROPOSAL_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V6_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dReviewV6Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dReviewV6ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dReviewV6Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_REVIEW_V6 =
    deepFreeze(rawReview);

export function validateCorePathindInternalized1dReviewV6(
    review: CorePathindInternalized1dReviewV6 =
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V6
): CorePathindInternalized1dReviewV6 {
    validateCorePathindInternalized1dProposalV6();
    if (
        review.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-6' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-INTERNALIZED-06' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-INTERNALIZED-006' ||
        review.approval.decision !==
            'corrected-proposal-v6-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !==
            PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== 'fe0306d' ||
        review.approval.supersededReviewCheckpoint !== 'a94c2f7' ||
        review.approval.supersededLedgerCheckpoint !== null
    ) {
        throw new CorePathindInternalized1dReviewV6Error(
            'PATHIND_INTERNALIZED_REVIEW_V6_DECISION_DRIFT',
            'The exact delegated corrected-v6 decision drifted'
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
        throw new CorePathindInternalized1dReviewV6Error(
            'PATHIND_INTERNALIZED_REVIEW_V6_PROPOSAL_DRIFT',
            'The reviewed proposal v6 bytes drifted'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        authorization.trustedDeclarationCount !== 4 ||
        authorization.runtimeRuleCount !== 8 ||
        authorization.mathematicalRuntimeProjectionCount !== 5 ||
        authorization.derivedRuntimeSupportRuleCount !== 3 ||
        authorization.proofRuleCount !== 0 ||
        authorization.transparentDefinitionCount !== 10 ||
        authorization.typedLibraryConsumerCount !== 2 ||
        authorization.negativeConsumerCount !== 10 ||
        authorization.selectedRuntimeObservationCount !== 10 ||
        authorization.boundedOracleAssertionCount !== 12 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        !authorization.exactFiveMathematicalProjectionsAuthorized ||
        !authorization.exactThreeDerivedSupportRulesAuthorized ||
        !authorization.motiveTransportCategoryPresentationFusionAuthorized ||
        authorization.motiveTransportCategoryPresentationFusionRuleId !==
            MOTIVE_TRANSPORT_FUSION_ID ||
        !authorization.motiveTransportFusionMustRemainTwoSidedAndDecoded ||
        !authorization.motiveTransportFusionMustSubjectCheck ||
        authorization.genericComparisonPrerequisite.proposalCheckpoint !==
            'a42ffc9' ||
        authorization.genericComparisonPrerequisite.reviewCheckpoint !==
            '5277885' ||
        !authorization.genericComparisonPrerequisite
            .semanticCheckpointRequiredBeforePathIndCheckpoint ||
        !authorization.genericComparisonPrerequisite
            .originalSourceRootReplayRequired ||
        !authorization.allSevenV5RuntimeRulesRetained ||
        authorization.newRuntimeEquationAuthorized ||
        authorization.newProofRuleAuthorized ||
        authorization.underlyingCategoryCollapseAuthorized ||
        authorization.genericTwoSidedCategoryFusionAuthorized ||
        authorization.genericDeclarationProofIntegrationAuthorized ||
        authorization.genericRuntimeMatcherChangeAuthorized ||
        authorization.genericCheckerChangeAuthorized ||
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
        throw new CorePathindInternalized1dReviewV6Error(
            'PATHIND_INTERNALIZED_REVIEW_V6_AUTHORIZATION_DRIFT',
            'The reviewed 4/8/0/10 authorization widened or drifted'
        );
    }
    return review;
}
