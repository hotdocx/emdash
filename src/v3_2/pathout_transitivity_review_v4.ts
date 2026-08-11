/**
 * Separate immutable review of corrected PathOut transitivity proposal v4.
 */

import {
    CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID
} from './pathout_transitivity_proposal_v3';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4,
    CorePathoutTransitivity1eProposalV4,
    validateCorePathoutTransitivity1eProposalV4
} from './pathout_transitivity_proposal_v4';

export const CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V4_REVISION =
    'PATHOUT-LIBRARY-TRANSITIVITY-1E-REVIEWED-4' as const;

const PROPOSAL_CHECKPOINT = '2498053';
const PROPOSAL_SHA256 =
    '820df96e9a0b889172c2e74fbcdc77cd16329dcaf36105d3c53076807e76394b';
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

const proposal = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4;

const rawReview = {
    revision: CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V4_REVISION,
    status: 'corrected-v4-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHOUT-TRANSITIVITY-04',
        decisionId: 'D-TS-EMDASH-PATHOUT-TRANSITIVITY-004',
        decision: 'corrected-proposal-v4-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: 'fe1a9b7',
        supersededReviewCheckpoint: '0834d00',
        supersededLedgerCheckpoint: '5d0dad5'
    },
    recommendation:
        cloneData(proposal) as CorePathoutTransitivity1eProposalV4,
    authorization: {
        implementationRow: 'PATHOUT-LIBRARY-TRANSITIVITY-1E',
        implementationAuthorized: true,
        exactImplementation: cloneData(proposal.exactImplementation),
        exactRequiredExistingProviders:
            cloneData(proposal.requiredExistingProviders),
        exactTypedLibraryConsumers:
            cloneData(proposal.typedLibraryConsumers),
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
        comparisonStepLimit: 512,
        sourceInjectiveModifierIsMetadataOnly: true,
        exactConsumerParentRuntimeSupportRuleAuthorized: true,
        exactConsumerParentRuntimeSupportRuleId:
            CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID,
        exactSupersededPostDeltaRuleId:
            CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
        postDeltaRuntimeSupportRetained: false,
        secondLocalRuntimeSupportRuleAuthorized: false,
        localRuntimeSupportMustRemainDerived: true,
        localRuntimeSupportMustRemainCompleteParent: true,
        localRuntimeSupportMustMatchOriginalConsumerParent: true,
        localRuntimeSupportMustBeConsultedBeforeDescendantDelta: true,
        localRuntimeSupportMustSubjectCheck: true,
        localRuntimeSupportMustCompileAfterFiveDefinitions: true,
        inheritedProofProviderReuseAuthorized: true,
        inheritedProofProviderId: INHERITED_PROOF_RULE_ID,
        inheritedProofProviderMustRecheckAgainstFinalEnvironment: true,
        inheritedProofHelperExplicitDescendantEnvironmentAuthorized: true,
        canonicalPredecessorCoreNameTestRepairAuthorized: true,
        genericRuntimeRuleAuthorized: false,
        newProofRuleAuthorized: false,
        broadHomConRuntimeImportAuthorized: false,
        wholeDisplayedIdentityDeltaAuthorized: false,
        wholeRepresentableFamilyDeltaAuthorized: false,
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
        focusedProposalGate: '47-tests-47-pass-zero-fail',
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
        'does-not-mutate-v1-v2-v3-or-v4-proposal-evidence',
        'does-not-itself-implement-transitivity',
        'does-not-retain-v3-or-add-a-second-runtime-rule',
        'does-not-add-an-opaque-owner-or-proof-rule',
        'does-not-import-the-generic-hom-con-arrow-ladder',
        'does-not-import-whole-Rep-catd-or-id-funcd-delta',
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
        'pathout-transitivity-1e-corrected-v4-implementation-ready'
} as const;

export type CorePathoutTransitivity1eReviewV4 = typeof rawReview;

export type CorePathoutTransitivity1eReviewV4ErrorCode =
    | 'PATHOUT_TRANSITIVITY_REVIEW_V4_DECISION_DRIFT'
    | 'PATHOUT_TRANSITIVITY_REVIEW_V4_PROPOSAL_DRIFT'
    | 'PATHOUT_TRANSITIVITY_REVIEW_V4_AUTHORIZATION_DRIFT';

export class CorePathoutTransitivity1eReviewV4Error extends Error {
    constructor(
        public readonly code: CorePathoutTransitivity1eReviewV4ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutTransitivity1eReviewV4Error';
    }
}

export const CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V4 =
    deepFreeze(rawReview);

export function validateCorePathoutTransitivity1eReviewV4(
    review: CorePathoutTransitivity1eReviewV4 =
        CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V4
): CorePathoutTransitivity1eReviewV4 {
    validateCorePathoutTransitivity1eProposalV4(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-TRANSITIVITY-1E-REVIEWED-4' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHOUT-TRANSITIVITY-04' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHOUT-TRANSITIVITY-004' ||
        review.approval.decision !==
            'corrected-proposal-v4-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-objection-after-proposal-checkpoint' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== 'fe1a9b7' ||
        review.approval.supersededReviewCheckpoint !== '0834d00' ||
        review.approval.supersededLedgerCheckpoint !== '5d0dad5'
    ) {
        throw new CorePathoutTransitivity1eReviewV4Error(
            'PATHOUT_TRANSITIVITY_REVIEW_V4_DECISION_DRIFT',
            'The delegated corrected-v4 transitivity decision drifted'
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
        throw new CorePathoutTransitivity1eReviewV4Error(
            'PATHOUT_TRANSITIVITY_REVIEW_V4_PROPOSAL_DRIFT',
            'The reviewed corrected-v4 proposal bytes drifted'
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
        authorization.comparisonStepLimit !== 512 ||
        !authorization.sourceInjectiveModifierIsMetadataOnly ||
        !authorization.exactConsumerParentRuntimeSupportRuleAuthorized ||
        authorization.exactConsumerParentRuntimeSupportRuleId !==
            CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID ||
        authorization.exactSupersededPostDeltaRuleId !==
            CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID ||
        authorization.postDeltaRuntimeSupportRetained ||
        authorization.secondLocalRuntimeSupportRuleAuthorized ||
        !authorization.localRuntimeSupportMustRemainDerived ||
        !authorization.localRuntimeSupportMustRemainCompleteParent ||
        !authorization.localRuntimeSupportMustMatchOriginalConsumerParent ||
        !authorization
            .localRuntimeSupportMustBeConsultedBeforeDescendantDelta ||
        !authorization.localRuntimeSupportMustSubjectCheck ||
        !authorization.localRuntimeSupportMustCompileAfterFiveDefinitions ||
        !authorization.inheritedProofProviderReuseAuthorized ||
        authorization.inheritedProofProviderId !== INHERITED_PROOF_RULE_ID ||
        !authorization
            .inheritedProofProviderMustRecheckAgainstFinalEnvironment ||
        !authorization
            .inheritedProofHelperExplicitDescendantEnvironmentAuthorized ||
        !authorization.canonicalPredecessorCoreNameTestRepairAuthorized ||
        authorization.genericRuntimeRuleAuthorized ||
        authorization.newProofRuleAuthorized ||
        authorization.broadHomConRuntimeImportAuthorized ||
        authorization.wholeDisplayedIdentityDeltaAuthorized ||
        authorization.wholeRepresentableFamilyDeltaAuthorized ||
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
        throw new CorePathoutTransitivity1eReviewV4Error(
            'PATHOUT_TRANSITIVITY_REVIEW_V4_AUTHORIZATION_DRIFT',
            'The exact corrected-v4 0/1/0/5 authorization drifted'
        );
    }
    return review;
}

export const cloneCorePathoutTransitivity1eReviewV4 = ():
CorePathoutTransitivity1eReviewV4 => cloneData(
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V4
);
