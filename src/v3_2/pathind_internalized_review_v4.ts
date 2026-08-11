/**
 * Separate immutable review of corrected
 * PATHOUT-LIBRARY-INTERNALIZED-1D proposal v4.
 *
 * The review approves only checkpoint 001a899 under the user's standing
 * unattended delegation, with later human supersession.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4,
    CorePathindInternalized1dProposalV4,
    validateCorePathindInternalized1dProposalV4
} from './pathind_internalized_proposal_v4';

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

const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4;

const PROPOSAL_SHA256 =
    '6d30ede357b09900667904549ab1f4a0f6246ae21b5eb578a4cf57bdeb6127fe';

const POST_PREFIX_RULE_ID =
    'pathind.internalized.' +
    'path-ind-functor-component-post-prefix-subject-fusion';

const TRANSFD_SUBJECT_RULE_ID =
    'pathind.internalized.' +
    'path-ind-transfd-component-subject-fusion';

const rawReview = {
    revision: 'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-4',
    status:
        'reviewed-corrected-proposal-v4-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-04',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-004',
        decision: 'corrected-proposal-v4-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: '001a899',
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: '5a1d635',
        supersededReviewCheckpoint: '6694c87',
        supersededLedgerCheckpoint: 'e26091d'
    },
    recommendation:
        cloneData(proposal) as CorePathindInternalized1dProposalV4,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
        implementationAuthorized: true,
        exactImplementation: cloneData(proposal.exactImplementation),
        exactDependencyClosure: cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor: cloneData(proposal.selectedPredecessor),
        trustedDeclarationCount: 4,
        runtimeRuleCount: 6,
        mathematicalRuntimeProjectionCount: 4,
        derivedRuntimeSupportRuleCount: 2,
        proofRuleCount: 0,
        transparentDefinitionCount: 10,
        typedLibraryConsumerCount: 2,
        negativeConsumerCount: 10,
        selectedRuntimeObservationCount: 9,
        boundedOracleAssertionCount: 11,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        exactFourOwnersAuthorized: true,
        exactFourMathematicalProjectionsAuthorized: true,
        componentPostPrefixSubjectFusionAuthorized: true,
        componentPostPrefixSubjectFusionRuleId: POST_PREFIX_RULE_ID,
        transfdComponentSubjectFusionAuthorized: true,
        transfdComponentSubjectFusionRuleId: TRANSFD_SUBJECT_RULE_ID,
        transfdComponentSubjectFusionMustSubjectCheck: true,
        bothSupportFusionsAreNonMathematical: true,
        seventhRuntimeRuleAuthorized: false,
        tenTransparentDefinitionsAuthorized: true,
        primaryTheoremIsPathIndTransfd: true,
        pathIndFuncdIsTransparentDerivedPresentation: true,
        sourceArrowMustRemainInternallyOwned: true,
        higherActionMustRemainInternallyOwned: true,
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
        proposalCheckpoint: '001a899',
        proposalSha256: PROPOSAL_SHA256,
        rootTypecheck: 'passed',
        focusedLint: 'passed',
        focusedProposalGate: '26-tests-26-pass-zero-fail',
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
        'does-not-mutate-proposal-v4-or-historical-evidence',
        'does-not-itself-implement-internalized-PathInd',
        'does-not-authorize-a-seventh-runtime-rule',
        'does-not-authorize-a-generic-Catd_cat-to-Functor_cat-collapse',
        'does-not-authorize-a-generic-runtime-matcher-or-checker-change',
        'does-not-authorize-proof-program-integration',
        'does-not-authorize-a-generic-fixed-evaluation-runtime-import',
        'does-not-authorize-alternate-PathInd-signatures-or-bodies',
        'does-not-retain-temporary-in-memory-diagnostic-observers',
        'does-not-classify-either-support-fusion-as-mathematics',
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
        'pathind-internalized-1d-corrected-v4-implementation-ready'
} as const;

export type CorePathindInternalized1dReviewV4 = typeof rawReview;

export type CorePathindInternalized1dReviewV4ErrorCode =
    | 'PATHIND_INTERNALIZED_REVIEW_V4_DECISION_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V4_PROPOSAL_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_V4_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dReviewV4Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dReviewV4ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dReviewV4Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_REVIEW_V4 =
    deepFreeze(rawReview);

export function validateCorePathindInternalized1dReviewV4(
    review: CorePathindInternalized1dReviewV4 =
        CORE_PATHIND_INTERNALIZED_1D_REVIEW_V4
): CorePathindInternalized1dReviewV4 {
    validateCorePathindInternalized1dProposalV4(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-4' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-INTERNALIZED-04' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-INTERNALIZED-004' ||
        review.approval.decision !==
            'corrected-proposal-v4-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== '001a899' ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== '5a1d635' ||
        review.approval.supersededReviewCheckpoint !== '6694c87' ||
        review.approval.supersededLedgerCheckpoint !== 'e26091d'
    ) {
        throw new CorePathindInternalized1dReviewV4Error(
            'PATHIND_INTERNALIZED_REVIEW_V4_DECISION_DRIFT',
            'The exact delegated corrected-v4 decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-4' ||
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
        review.validation.proposalCheckpoint !== '001a899' ||
        review.validation.proposalSha256 !==
            review.approval.approvedProposalSha256
    ) {
        throw new CorePathindInternalized1dReviewV4Error(
            'PATHIND_INTERNALIZED_REVIEW_V4_PROPOSAL_DRIFT',
            'The review must retain exact non-authorizing proposal v4'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D' ||
        !authorization.implementationAuthorized ||
        authorization.trustedDeclarationCount !== 4 ||
        authorization.runtimeRuleCount !== 6 ||
        authorization.mathematicalRuntimeProjectionCount !== 4 ||
        authorization.derivedRuntimeSupportRuleCount !== 2 ||
        authorization.proofRuleCount !== 0 ||
        authorization.transparentDefinitionCount !== 10 ||
        authorization.typedLibraryConsumerCount !== 2 ||
        authorization.negativeConsumerCount !== 10 ||
        authorization.selectedRuntimeObservationCount !== 9 ||
        authorization.boundedOracleAssertionCount !== 11 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        !authorization.exactFourOwnersAuthorized ||
        !authorization.exactFourMathematicalProjectionsAuthorized ||
        !authorization.componentPostPrefixSubjectFusionAuthorized ||
        authorization.componentPostPrefixSubjectFusionRuleId !==
            POST_PREFIX_RULE_ID ||
        !authorization.transfdComponentSubjectFusionAuthorized ||
        authorization.transfdComponentSubjectFusionRuleId !==
            TRANSFD_SUBJECT_RULE_ID ||
        !authorization.transfdComponentSubjectFusionMustSubjectCheck ||
        !authorization.bothSupportFusionsAreNonMathematical ||
        authorization.seventhRuntimeRuleAuthorized ||
        !authorization.tenTransparentDefinitionsAuthorized ||
        !authorization.primaryTheoremIsPathIndTransfd ||
        !authorization.pathIndFuncdIsTransparentDerivedPresentation ||
        !authorization.sourceArrowMustRemainInternallyOwned ||
        !authorization.higherActionMustRemainInternallyOwned ||
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
            'pathind-internalized-1d-corrected-v4-implementation-ready'
    ) {
        throw new CorePathindInternalized1dReviewV4Error(
            'PATHIND_INTERNALIZED_REVIEW_V4_AUTHORIZATION_DRIFT',
            'The exact 4/6/0/10 authorization widened or weakened'
        );
    }
    return review;
}
