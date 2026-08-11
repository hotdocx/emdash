/**
 * Separate immutable review of the root-only PathOut transitivity proposal.
 */

import {
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL,
    CorePathoutTransitivity1eProposal,
    validateCorePathoutTransitivity1eProposal
} from './pathout_transitivity_proposal';

export const CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_REVISION =
    'PATHOUT-LIBRARY-TRANSITIVITY-1E-REVIEWED-1' as const;

const PROPOSAL_CHECKPOINT = '50b9a56';
const PROPOSAL_SHA256 =
    '1951ff30d42ab95dfa9d77fadb747be9eca3c4bf760a99ab283da07fc1351bfb';

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const proposal = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL;

const rawReview = {
    revision: CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_REVISION,
    status: 'reviewed-proposal-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHOUT-TRANSITIVITY-01',
        decisionId: 'D-TS-EMDASH-PATHOUT-TRANSITIVITY-001',
        decision: 'proposal-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256
    },
    recommendation:
        cloneData(proposal) as CorePathoutTransitivity1eProposal,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-TRANSITIVITY-1E',
        implementationAuthorized: true,
        exactImplementation: cloneData(proposal.exactImplementation),
        exactRequiredExistingProviders:
            cloneData(proposal.requiredExistingProviders),
        exactTypedLibraryConsumers:
            cloneData(proposal.typedLibraryConsumers),
        exactSelectedDefinitionalObservations:
            cloneData(proposal.selectedDefinitionalObservations),
        exactNegativeConsumers: cloneData(proposal.negativeConsumers),
        exactBoundedOracle: cloneData(proposal.boundedOracle),
        trustedDeclarationCount: 0,
        runtimeRuleCount: 0,
        proofRuleCount: 0,
        transparentDefinitionCount: 5,
        requiredExistingProviderCount: 11,
        typedLibraryConsumerCount: 2,
        selectedDefinitionalObservationCount: 8,
        negativeConsumerCount: 8,
        boundedOracleAssertionCount: 8,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        checkedTransparentDefinitionPolicyRequired: true,
        freeDeclarationLinksRequired: true,
        sourceOrderRequired: true,
        comparisonStepLimit: 512,
        sourceInjectiveModifierIsMetadataOnly: true,
        transitivityStopsAtStablePrecomposition: true,
        typescriptInjectivityOrUnificationAuthorized: false,
        intrinsicCoreOwnerAuthorized: false,
        genericCheckerChangeAuthorized: false,
        genericEvaluatorChangeAuthorized: false,
        runtimeRuleAuthorized: false,
        proofRuleAuthorized: false,
        pathCategoryBridgeAuthorized: false,
        rawCompositionRuntimeCollapseAuthorized: false,
        textSyntaxAuthorized: false,
        browserOrPublicPackageExportAuthorized: false,
        activeLambdapiSourceChangeAuthorized: false,
        externalIntegrationOrReleaseAuthorized: false
    },
    validation: {
        proposalCheckpoint: PROPOSAL_CHECKPOINT,
        proposalSha256: PROPOSAL_SHA256,
        rootTypecheck: 'passed',
        focusedLint: 'passed',
        focusedProposalGate: '7-tests-7-pass-zero-fail',
        LambdapiProposalGate: 'not-required-no-behavior',
        carriedAggregateCheckpoint: 'e560551',
        carriedAggregateGate:
            '1923-tests-1867-pass-56-skip-zero-fail',
        longAggregateGate:
            'carried-forward-no-rerun-for-root-local-review'
    },
    gitBoundary: {
        localImplementationCheckpointAuthorized: true,
        exactStagedDiffReviewRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false
    },
    nonEffects: [
        'does-not-mutate-the-checkpointed-proposal',
        'does-not-itself-implement-transitivity',
        'does-not-add-an-opaque-owner-runtime-rule-or-proof-rule',
        'does-not-turn-source-injective-metadata-into-TypeScript-behavior',
        'does-not-add-a-Core-checker-evaluator-or-unification-branch',
        'does-not-authorize-the-Path-category-comparison-library',
        'does-not-add-a-runtime-collapse-to-raw-composition',
        'does-not-authorize-text-browser-or-package-presentation',
        'does-not-authorize-active-Lambdapi-source-change',
        'does-not-authorize-push-merge-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'pathout-transitivity-1e-exact-implementation-ready'
} as const;

export type CorePathoutTransitivity1eReview = typeof rawReview;

export type CorePathoutTransitivity1eReviewErrorCode =
    | 'PATHOUT_TRANSITIVITY_REVIEW_DECISION_DRIFT'
    | 'PATHOUT_TRANSITIVITY_REVIEW_PROPOSAL_DRIFT'
    | 'PATHOUT_TRANSITIVITY_REVIEW_AUTHORIZATION_DRIFT';

export class CorePathoutTransitivity1eReviewError extends Error {
    constructor(
        public readonly code: CorePathoutTransitivity1eReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutTransitivity1eReviewError';
    }
}

export const CORE_PATHOUT_TRANSITIVITY_1E_REVIEW =
    deepFreeze(rawReview);

export function validateCorePathoutTransitivity1eReview(
    review: CorePathoutTransitivity1eReview =
        CORE_PATHOUT_TRANSITIVITY_1E_REVIEW
): CorePathoutTransitivity1eReview {
    validateCorePathoutTransitivity1eProposal(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-TRANSITIVITY-1E-REVIEWED-1' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHOUT-TRANSITIVITY-01' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHOUT-TRANSITIVITY-001' ||
        review.approval.decision !== 'proposal-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-objection-after-proposal-checkpoint' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !==
            PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256
    ) {
        throw new CorePathoutTransitivity1eReviewError(
            'PATHOUT_TRANSITIVITY_REVIEW_DECISION_DRIFT',
            'The exact delegated transitivity decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        !sameData(
            review.authorization.exactImplementation,
            proposal.exactImplementation
        ) ||
        !sameData(
            review.authorization.exactRequiredExistingProviders,
            proposal.requiredExistingProviders
        ) ||
        !sameData(
            review.authorization.exactTypedLibraryConsumers,
            proposal.typedLibraryConsumers
        ) ||
        !sameData(
            review.authorization.exactSelectedDefinitionalObservations,
            proposal.selectedDefinitionalObservations
        ) ||
        !sameData(
            review.authorization.exactNegativeConsumers,
            proposal.negativeConsumers
        ) ||
        !sameData(
            review.authorization.exactBoundedOracle,
            proposal.boundedOracle
        )
    ) {
        throw new CorePathoutTransitivity1eReviewError(
            'PATHOUT_TRANSITIVITY_REVIEW_PROPOSAL_DRIFT',
            'The reviewed transitivity proposal bytes drifted'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        authorization.trustedDeclarationCount !== 0 ||
        authorization.runtimeRuleCount !== 0 ||
        authorization.proofRuleCount !== 0 ||
        authorization.transparentDefinitionCount !== 5 ||
        authorization.requiredExistingProviderCount !== 11 ||
        authorization.typedLibraryConsumerCount !== 2 ||
        authorization.selectedDefinitionalObservationCount !== 8 ||
        authorization.negativeConsumerCount !== 8 ||
        authorization.boundedOracleAssertionCount !== 8 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        !authorization.checkedTransparentDefinitionPolicyRequired ||
        !authorization.freeDeclarationLinksRequired ||
        !authorization.sourceOrderRequired ||
        authorization.comparisonStepLimit !== 512 ||
        !authorization.sourceInjectiveModifierIsMetadataOnly ||
        !authorization.transitivityStopsAtStablePrecomposition ||
        authorization.typescriptInjectivityOrUnificationAuthorized ||
        authorization.intrinsicCoreOwnerAuthorized ||
        authorization.genericCheckerChangeAuthorized ||
        authorization.genericEvaluatorChangeAuthorized ||
        authorization.runtimeRuleAuthorized ||
        authorization.proofRuleAuthorized ||
        authorization.pathCategoryBridgeAuthorized ||
        authorization.rawCompositionRuntimeCollapseAuthorized ||
        authorization.textSyntaxAuthorized ||
        authorization.browserOrPublicPackageExportAuthorized ||
        authorization.activeLambdapiSourceChangeAuthorized ||
        authorization.externalIntegrationOrReleaseAuthorized ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized
    ) {
        throw new CorePathoutTransitivity1eReviewError(
            'PATHOUT_TRANSITIVITY_REVIEW_AUTHORIZATION_DRIFT',
            'The exact 0/0/0/5 transitivity authorization drifted'
        );
    }
    return review;
}

export const cloneCorePathoutTransitivity1eReview = ():
CorePathoutTransitivity1eReview => cloneData(
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW
);
