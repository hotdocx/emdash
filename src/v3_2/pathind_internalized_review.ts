/**
 * Separate immutable review of PATHOUT-LIBRARY-INTERNALIZED-1D proposal v1.
 *
 * The review approves only checkpoint 188b8e5 under the user's standing
 * unattended delegation, with later human supersession. It does not mutate
 * the proposal or itself implement any declaration or rule.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL,
    CorePathindInternalized1dProposal,
    validateCorePathindInternalized1dProposal
} from './pathind_internalized_proposal';

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

const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL;

const rawReview = {
    revision: 'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-1',
    status: 'reviewed-proposal-v1-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-01',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-001',
        decision: 'proposal-v1-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-10',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: '188b8e5',
        approvedProposalSha256:
            'da30d4fc2a9d54737e8fce9b0256e9b066b6b4f463d054d0d38741cdaedddd63'
    },
    recommendation:
        cloneData(proposal) as CorePathindInternalized1dProposal,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-INTERNALIZED-1D',
        implementationAuthorized: true,
        exactImplementation: cloneData(proposal.exactImplementation),
        exactDependencyClosure: cloneData(proposal.dependencyClosure),
        exactSelectedPredecessor: cloneData(proposal.selectedPredecessor),
        trustedDeclarationCount: 4,
        runtimeRuleCount: 4,
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
        tenTransparentDefinitionsAuthorized: true,
        primaryTheoremIsPathIndTransfd: true,
        pathIndFuncdIsTransparentDerivedPresentation: true,
        sourceArrowMustRemainInternallyOwned: true,
        higherActionMustRemainInternallyOwned: true,
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
        proposalCheckpoint: '188b8e5',
        proposalSha256:
            'da30d4fc2a9d54737e8fce9b0256e9b066b6b4f463d054d0d38741cdaedddd63',
        rootTypecheck: 'passed',
        focusedLint: 'passed',
        focusedProposalGate: '8-tests-8-pass-zero-fail',
        authorityAndProviderGate:
            'active-positions-and-exact-provider-groups-green',
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
        'does-not-mutate-proposal-v1-or-predecessor-evidence',
        'does-not-itself-implement-internalized-PathInd',
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
        'pathind-internalized-1d-proposal-v1-implementation-ready'
} as const;

export type CorePathindInternalized1dReview = typeof rawReview;

export type CorePathindInternalized1dReviewErrorCode =
    | 'PATHIND_INTERNALIZED_REVIEW_DECISION_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_PROPOSAL_DRIFT'
    | 'PATHIND_INTERNALIZED_REVIEW_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dReviewError extends Error {
    constructor(
        public readonly code: CorePathindInternalized1dReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dReviewError';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_REVIEW = deepFreeze(rawReview);

export function validateCorePathindInternalized1dReview(
    review: CorePathindInternalized1dReview =
        CORE_PATHIND_INTERNALIZED_1D_REVIEW
): CorePathindInternalized1dReview {
    validateCorePathindInternalized1dProposal(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-1' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHIND-INTERNALIZED-01' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHIND-INTERNALIZED-001' ||
        review.approval.decision !== 'proposal-v1-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.recordedOn !== '2026-08-10' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== '188b8e5' ||
        review.approval.approvedProposalSha256 !==
            'da30d4fc2a9d54737e8fce9b0256e9b066b6b4f463d054d0d38741cdaedddd63'
    ) {
        throw new CorePathindInternalized1dReviewError(
            'PATHIND_INTERNALIZED_REVIEW_DECISION_DRIFT',
            'The delegated decision or exact proposal checkpoint drifted'
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
        ) ||
        review.validation.proposalCheckpoint !== '188b8e5' ||
        review.validation.proposalSha256 !==
            review.approval.approvedProposalSha256
    ) {
        throw new CorePathindInternalized1dReviewError(
            'PATHIND_INTERNALIZED_REVIEW_PROPOSAL_DRIFT',
            'The review no longer embeds the exact checkpointed proposal'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        authorization.trustedDeclarationCount !== 4 ||
        authorization.runtimeRuleCount !== 4 ||
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
        !authorization.tenTransparentDefinitionsAuthorized ||
        !authorization.primaryTheoremIsPathIndTransfd ||
        !authorization.pathIndFuncdIsTransparentDerivedPresentation ||
        !authorization.sourceArrowMustRemainInternallyOwned ||
        !authorization.higherActionMustRemainInternallyOwned ||
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
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        review.nextDependencyState !==
            'pathind-internalized-1d-proposal-v1-implementation-ready'
    ) {
        throw new CorePathindInternalized1dReviewError(
            'PATHIND_INTERNALIZED_REVIEW_AUTHORIZATION_DRIFT',
            'The exact 4/4/0/10 authorization widened or weakened'
        );
    }
    return review;
}
