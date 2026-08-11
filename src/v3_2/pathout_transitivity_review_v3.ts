/**
 * Separate immutable review of corrected PathOut transitivity proposal v3.
 */

import {
    CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID
} from './pathout_transitivity_proposal_v2';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3,
    CorePathoutTransitivity1eProposalV3,
    validateCorePathoutTransitivity1eProposalV3
} from './pathout_transitivity_proposal_v3';

export const CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3_REVISION =
    'PATHOUT-LIBRARY-TRANSITIVITY-1E-REVIEWED-3' as const;

const PROPOSAL_CHECKPOINT = 'fe1a9b7';
const PROPOSAL_SHA256 =
    '0d7448ae68d9aa6ae3bf91b9010a676f8ca3c9101976e1de2c88816a94e68dd9';
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

const proposal = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3;

const rawReview = {
    revision: CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3_REVISION,
    status: 'corrected-v3-approved-under-delegated-authority',
    approval: {
        gate: 'H-TS-EMDASH-PATHOUT-TRANSITIVITY-03',
        decisionId: 'D-TS-EMDASH-PATHOUT-TRANSITIVITY-003',
        decision: 'corrected-proposal-v3-approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-proposal-checkpoint',
        recordedOn: '2026-08-11',
        humanDecisionSupersedes: true,
        approvedProposalCheckpoint: PROPOSAL_CHECKPOINT,
        approvedProposalSha256: PROPOSAL_SHA256,
        supersededProposalCheckpoint: 'b1e6f0f',
        supersededReviewCheckpoint: '31f23db',
        supersededLedgerCheckpoint: '8668764'
    },
    recommendation:
        cloneData(proposal) as CorePathoutTransitivity1eProposalV3,
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
        exactPostDeltaRuntimeSupportRuleAuthorized: true,
        exactPostDeltaRuntimeSupportRuleId:
            CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
        exactSupersededPreDeltaRuleId:
            CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
        preDeltaRuntimeSupportRetained: false,
        secondLocalRuntimeSupportRuleAuthorized: false,
        localRuntimeSupportMustRemainDerived: true,
        localRuntimeSupportMustRemainCompleteParent: true,
        localRuntimeSupportMustRemainStablePostCompTargetDelta: true,
        localRuntimeSupportMustSubjectCheck: true,
        localRuntimeSupportMustCompileAfterFiveDefinitions: true,
        inheritedProofProviderReuseAuthorized: true,
        inheritedProofProviderId: INHERITED_PROOF_RULE_ID,
        inheritedProofProviderMustRecheckAgainstFinalEnvironment: true,
        inheritedProofHelperExplicitDescendantEnvironmentAuthorized: true,
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
        focusedProposalGate: '34-tests-34-pass-zero-fail',
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
        'does-not-mutate-v1-v2-or-v3-proposal-evidence',
        'does-not-itself-implement-transitivity',
        'does-not-retain-v2-or-add-a-second-runtime-rule',
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
        'pathout-transitivity-1e-corrected-v3-implementation-ready'
} as const;

export type CorePathoutTransitivity1eReviewV3 = typeof rawReview;

export type CorePathoutTransitivity1eReviewV3ErrorCode =
    | 'PATHOUT_TRANSITIVITY_REVIEW_V3_DECISION_DRIFT'
    | 'PATHOUT_TRANSITIVITY_REVIEW_V3_PROPOSAL_DRIFT'
    | 'PATHOUT_TRANSITIVITY_REVIEW_V3_AUTHORIZATION_DRIFT';

export class CorePathoutTransitivity1eReviewV3Error extends Error {
    constructor(
        public readonly code: CorePathoutTransitivity1eReviewV3ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutTransitivity1eReviewV3Error';
    }
}

export const CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3 =
    deepFreeze(rawReview);

export function validateCorePathoutTransitivity1eReviewV3(
    review: CorePathoutTransitivity1eReviewV3 =
        CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3
): CorePathoutTransitivity1eReviewV3 {
    validateCorePathoutTransitivity1eProposalV3(proposal);
    if (
        review.revision !==
            'PATHOUT-LIBRARY-TRANSITIVITY-1E-REVIEWED-3' ||
        review.approval.gate !==
            'H-TS-EMDASH-PATHOUT-TRANSITIVITY-03' ||
        review.approval.decisionId !==
            'D-TS-EMDASH-PATHOUT-TRANSITIVITY-003' ||
        review.approval.decision !==
            'corrected-proposal-v3-approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-objection-after-proposal-checkpoint' ||
        review.approval.recordedOn !== '2026-08-11' ||
        !review.approval.humanDecisionSupersedes ||
        review.approval.approvedProposalCheckpoint !== PROPOSAL_CHECKPOINT ||
        review.approval.approvedProposalSha256 !== PROPOSAL_SHA256 ||
        review.approval.supersededProposalCheckpoint !== 'b1e6f0f' ||
        review.approval.supersededReviewCheckpoint !== '31f23db' ||
        review.approval.supersededLedgerCheckpoint !== '8668764'
    ) {
        throw new CorePathoutTransitivity1eReviewV3Error(
            'PATHOUT_TRANSITIVITY_REVIEW_V3_DECISION_DRIFT',
            'The delegated corrected-v3 transitivity decision drifted'
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
        throw new CorePathoutTransitivity1eReviewV3Error(
            'PATHOUT_TRANSITIVITY_REVIEW_V3_PROPOSAL_DRIFT',
            'The reviewed corrected-v3 proposal bytes drifted'
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
        !authorization.exactPostDeltaRuntimeSupportRuleAuthorized ||
        authorization.exactPostDeltaRuntimeSupportRuleId !==
            CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID ||
        authorization.exactSupersededPreDeltaRuleId !==
            CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID ||
        authorization.preDeltaRuntimeSupportRetained ||
        authorization.secondLocalRuntimeSupportRuleAuthorized ||
        !authorization.localRuntimeSupportMustRemainDerived ||
        !authorization.localRuntimeSupportMustRemainCompleteParent ||
        !authorization
            .localRuntimeSupportMustRemainStablePostCompTargetDelta ||
        !authorization.localRuntimeSupportMustSubjectCheck ||
        !authorization.localRuntimeSupportMustCompileAfterFiveDefinitions ||
        !authorization.inheritedProofProviderReuseAuthorized ||
        authorization.inheritedProofProviderId !== INHERITED_PROOF_RULE_ID ||
        !authorization
            .inheritedProofProviderMustRecheckAgainstFinalEnvironment ||
        !authorization
            .inheritedProofHelperExplicitDescendantEnvironmentAuthorized ||
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
        throw new CorePathoutTransitivity1eReviewV3Error(
            'PATHOUT_TRANSITIVITY_REVIEW_V3_AUTHORIZATION_DRIFT',
            'The exact corrected-v3 0/1/0/5 authorization drifted'
        );
    }
    return review;
}

export const cloneCorePathoutTransitivity1eReviewV3 = ():
CorePathoutTransitivity1eReviewV3 => cloneData(
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3
);
