/**
 * Separate immutable review of corrected PathOut transitivity proposal v2.
 */

import {
    CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2,
    CorePathoutTransitivity1eProposalV2,
    validateCorePathoutTransitivity1eProposalV2
} from './pathout_transitivity_proposal_v2';

export const CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2_REVISION =
    'PATHOUT-LIBRARY-TRANSITIVITY-1E-REVIEWED-2' as const;

const PROPOSAL_CHECKPOINT = 'b1e6f0f';
const PROPOSAL_SHA256 =
    '139dbc75984f229e879ac93ee01e2dafc8b39982ca19f5ea9120836b0f9c2b1c';
const INHERITED_PROOF_RULE_ID = 'stress.sigma-pi.uncurrying';

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

const proposal = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2;

const rawReview = {
    revision: CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2_REVISION,
    status: 'corrected-v2-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHOUT-TRANSITIVITY-02',
        decisionId: 'D-TS-EMDASH-PATHOUT-TRANSITIVITY-002',
        decision: 'corrected-proposal-v2-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: '50b9a56',
        supersededReviewCheckpoint: 'f60b36a',
        supersededLedgerCheckpoint: '150e315'
    },
    recommendation:
        cloneData(proposal) as CorePathoutTransitivity1eProposalV2,
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
        exactSelectedObservationPartition:
            cloneData(
                proposal.exactImplementation.selectedObservationPartition
            ),
        exactNegativeConsumers: cloneData(proposal.negativeConsumers),
        exactBoundedOracle: cloneData(proposal.boundedOracle),
        trustedDeclarationCount: 0,
        localRuntimeSupportRuleCount: 1,
        localProofRuleCount: 0,
        transparentDefinitionCount: 5,
        inheritedProofProviderCount: 1,
        requiredExistingProviderCount: 11,
        typedLibraryConsumerCount: 2,
        runtimeDefinitionalObservationCount: 7,
        inheritedProofTimeObservationCount: 1,
        negativeConsumerCount: 8,
        boundedOracleAssertionCount: 8,
        genericEnginesOnly: true,
        rootOnlyQualification: true,
        checkedTransparentDefinitionPolicyRequired: true,
        freeDeclarationLinksRequired: true,
        sourceOrderRequired: true,
        comparisonStepLimit: 512,
        sourceInjectiveModifierIsMetadataOnly: true,
        exactLocalRuntimeSupportRuleAuthorized: true,
        exactLocalRuntimeSupportRuleId:
            CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
        localRuntimeSupportMustRemainDerived: true,
        localRuntimeSupportMustRemainCompleteParent: true,
        localRuntimeSupportMustSubjectCheck: true,
        localRuntimeSupportMustCompileAfterFiveDefinitions: true,
        inheritedProofProviderReuseAuthorized: true,
        inheritedProofProviderId: INHERITED_PROOF_RULE_ID,
        inheritedProofProviderMustRecheckAgainstFinalEnvironment: true,
        genericRuntimeRuleAuthorized: false,
        newProofRuleAuthorized: false,
        broadHomConRuntimeImportAuthorized: false,
        wholeDisplayedIdentityDeltaAuthorized: false,
        genericPiToFunctordRuntimeCollapseAuthorized: false,
        typescriptInjectivityOrUnificationAuthorized: false,
        intrinsicCoreOwnerAuthorized: false,
        genericRuntimeMatcherChangeAuthorized: false,
        genericCheckerChangeAuthorized: false,
        genericEvaluatorChangeAuthorized: false,
        genericComparisonChangeAuthorized: false,
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
        focusedProposalGate: '20-tests-20-pass-zero-fail',
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
        'does-not-mutate-v1-or-corrected-v2-proposal-evidence',
        'does-not-itself-implement-transitivity',
        'does-not-add-an-opaque-owner-or-proof-rule',
        'does-not-import-the-generic-hom-con-arrow-ladder',
        'does-not-import-the-whole-displayed-identity-delta',
        'does-not-install-a-runtime-Pi-cat-to-Functord-cat-collapse',
        'does-not-turn-source-injective-metadata-into-TypeScript-behavior',
        'does-not-add-a-Core-checker-evaluator-or-comparison-branch',
        'does-not-authorize-the-Path-category-comparison-library',
        'does-not-add-a-runtime-collapse-to-raw-composition',
        'does-not-authorize-text-browser-or-package-presentation',
        'does-not-authorize-active-Lambdapi-source-change',
        'does-not-authorize-push-merge-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'pathout-transitivity-1e-corrected-v2-implementation-ready'
} as const;

export type CorePathoutTransitivity1eReviewV2 = typeof rawReview;

export type CorePathoutTransitivity1eReviewV2ErrorCode =
    | 'PATHOUT_TRANSITIVITY_REVIEW_V2_DECISION_DRIFT'
    | 'PATHOUT_TRANSITIVITY_REVIEW_V2_PROPOSAL_DRIFT'
    | 'PATHOUT_TRANSITIVITY_REVIEW_V2_AUTHORIZATION_DRIFT';

export class CorePathoutTransitivity1eReviewV2Error extends Error {
    constructor(
        public readonly code: CorePathoutTransitivity1eReviewV2ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutTransitivity1eReviewV2Error';
    }
}

export const CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2 =
    deepFreeze(rawReview);

export function validateCorePathoutTransitivity1eReviewV2(
    review: CorePathoutTransitivity1eReviewV2 =
        CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2
): CorePathoutTransitivity1eReviewV2 {
    validateCorePathoutTransitivity1eProposalV2(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-TRANSITIVITY-1E-REVIEWED-2' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHOUT-TRANSITIVITY-02' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHOUT-TRANSITIVITY-002' ||
        review.approval.decision !==
            'corrected-proposal-v2-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-objection-after-proposal-checkpoint' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== '50b9a56' ||
        review.approval.supersededReviewCheckpoint !== 'f60b36a' ||
        review.approval.supersededLedgerCheckpoint !== '150e315'
    ) {
        throw new CorePathoutTransitivity1eReviewV2Error(
            'PATHOUT_TRANSITIVITY_REVIEW_V2_DECISION_DRIFT',
            'The delegated corrected-v2 transitivity decision drifted'
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
            review.authorization.exactSelectedObservationPartition,
            proposal.exactImplementation.selectedObservationPartition
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
        throw new CorePathoutTransitivity1eReviewV2Error(
            'PATHOUT_TRANSITIVITY_REVIEW_V2_PROPOSAL_DRIFT',
            'The reviewed corrected-v2 proposal bytes drifted'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        authorization.trustedDeclarationCount !== 0 ||
        authorization.localRuntimeSupportRuleCount !== 1 ||
        authorization.localProofRuleCount !== 0 ||
        authorization.transparentDefinitionCount !== 5 ||
        authorization.inheritedProofProviderCount !== 1 ||
        authorization.requiredExistingProviderCount !== 11 ||
        authorization.typedLibraryConsumerCount !== 2 ||
        authorization.runtimeDefinitionalObservationCount !== 7 ||
        authorization.inheritedProofTimeObservationCount !== 1 ||
        authorization.negativeConsumerCount !== 8 ||
        authorization.boundedOracleAssertionCount !== 8 ||
        !authorization.genericEnginesOnly ||
        !authorization.rootOnlyQualification ||
        !authorization.checkedTransparentDefinitionPolicyRequired ||
        !authorization.freeDeclarationLinksRequired ||
        !authorization.sourceOrderRequired ||
        authorization.comparisonStepLimit !== 512 ||
        !authorization.sourceInjectiveModifierIsMetadataOnly ||
        !authorization.exactLocalRuntimeSupportRuleAuthorized ||
        authorization.exactLocalRuntimeSupportRuleId !==
            CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID ||
        !authorization.localRuntimeSupportMustRemainDerived ||
        !authorization.localRuntimeSupportMustRemainCompleteParent ||
        !authorization.localRuntimeSupportMustSubjectCheck ||
        !authorization.localRuntimeSupportMustCompileAfterFiveDefinitions ||
        !authorization.inheritedProofProviderReuseAuthorized ||
        authorization.inheritedProofProviderId !== INHERITED_PROOF_RULE_ID ||
        !authorization
            .inheritedProofProviderMustRecheckAgainstFinalEnvironment ||
        authorization.genericRuntimeRuleAuthorized ||
        authorization.newProofRuleAuthorized ||
        authorization.broadHomConRuntimeImportAuthorized ||
        authorization.wholeDisplayedIdentityDeltaAuthorized ||
        authorization.genericPiToFunctordRuntimeCollapseAuthorized ||
        authorization.typescriptInjectivityOrUnificationAuthorized ||
        authorization.intrinsicCoreOwnerAuthorized ||
        authorization.genericRuntimeMatcherChangeAuthorized ||
        authorization.genericCheckerChangeAuthorized ||
        authorization.genericEvaluatorChangeAuthorized ||
        authorization.genericComparisonChangeAuthorized ||
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
        throw new CorePathoutTransitivity1eReviewV2Error(
            'PATHOUT_TRANSITIVITY_REVIEW_V2_AUTHORIZATION_DRIFT',
            'The exact corrected 0/1/0/5 authorization drifted'
        );
    }
    return review;
}

export const cloneCorePathoutTransitivity1eReviewV2 = ():
CorePathoutTransitivity1eReviewV2 => cloneData(
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2
);
