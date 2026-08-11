/**
 * Corrected, non-authorizing PathOut transitivity proposal v3.
 *
 * Reviewed v2 proved that its one local rule is well typed and fires at its
 * proposed redex, but the live observation unfolds CompTarget_catd before
 * consulting that fragment. V3 replaces the pre-delta rule one-for-one with
 * the measured stable post-delta parent. The 0/1/0/5 boundary is unchanged.
 */

import {
    CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2,
    validateCorePathoutTransitivity1eProposalV2
} from './pathout_transitivity_proposal_v2';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2,
    validateCorePathoutTransitivity1eReviewV2
} from './pathout_transitivity_review_v2';

export const CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3_REVISION =
    'PATHOUT-LIBRARY-TRANSITIVITY-1E-PROPOSAL-3' as const;

export const CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID = (
    'pathout.transitivity.fixed-source-section-component-post-delta-presentation-fusion'
) as const;

const V2_PROPOSAL_CHECKPOINT = 'b1e6f0f';
const V2_PROPOSAL_SHA256 =
    '139dbc75984f229e879ac93ee01e2dafc8b39982ca19f5ea9120836b0f9c2b1c';
const V2_REVIEW_CHECKPOINT = '31f23db';
const V2_REVIEW_SHA256 =
    'b24b2e0dfd77b541b52b7eb6f1388a045f01ed7f08c2f9b6b137da57bb2a4d0a';
const V2_LEDGER_CHECKPOINT = '8668764';

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

const proposalV2 = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2;
const reviewV2 = CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2;

const postDeltaSectionComponentPresentationFusion = {
    order: 0,
    id: CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
    replaces: CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
    authority:
        'derived-transitivity-stable-post-delta-complete-parent-fusion',
    authorityPositions: [
        'emdash2/emdash3_2.lp:5484-5497',
        'emdash2/emdash3_2.lp:7955-7972',
        'emdash2/emdash3_2.lp:8445-8453',
        'emdash2/emdash3_2.lp:19363-19413',
        'emdash2/emdash3_2.lp:19687-19710'
    ],
    sourceOwner: 'functor-object',
    policy: 'runtime-rewrite-derived-support',
    mathematicalRule: false,
    variables: ['Z', 'x', 'y', 'p'],
    left:
        'fapp0(Functord_cat(Z,Rep_x,Rep_x),' +
        'Functord_cat(Z,Rep_y,Rep_x),' +
        'fapp0(Hom_cat(Z,x,y),' +
        'Functor_cat(Functord_cat(Z,Rep_x,Rep_x),' +
        'Functord_cat(Z,Rep_y,Rep_x)),' +
        'fapp1_func(Z,Cat_cat,' +
        'hom_con(Catd_cat(Z),Rep_x,Op_cat(Z),Rep_catd_func(Z)),x,y),p),' +
        'id_funcd(Z,Rep_x))',
    right: 'path_comp_func(Z,x,y,p)',
    compileAfterTransparentDefinitionCount: 5,
    completeParentOnly: true,
    stableAfterCompTargetDelta: true,
    mustSubjectCheck: true
} as const;

const correctedModuleStages = proposalV2.exactImplementation.moduleStages
    .map(stage => stage.id ===
        'derived-transitivity-local-runtime-support'
        ? {
            ...cloneData(stage),
            rules: [
                CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID
            ]
        }
        : cloneData(stage)
    );

const rawProposal = {
    ...cloneData(proposalV2),
    revision: CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3_REVISION,
    status: 'corrected-proposal-v3-awaiting-separate-immutable-review',
    parent: {
        ...cloneData(proposalV2.parent),
        supersededProposalRevision: proposalV2.revision,
        supersededProposalCheckpoint: V2_PROPOSAL_CHECKPOINT,
        supersededProposalSha256: V2_PROPOSAL_SHA256,
        supersededReviewRevision: reviewV2.revision,
        supersededReviewCheckpoint: V2_REVIEW_CHECKPOINT,
        supersededReviewSha256: V2_REVIEW_SHA256,
        supersededLedgerCheckpoint: V2_LEDGER_CHECKPOINT,
        priorCounterevidence: cloneData(proposalV2.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'reviewed-v2-cold-focused-TypeScript-semantic-replay',
            coldFocusedGate: '9-tests-6-pass-2-fail-1-skip',
            coldFocusedDurationMs: 213_114,
            allFiveTransparentDefinitionsAdmitted: true,
            v2LocalRuntimeRuleSubjectChecked: true,
            v2LocalRuntimeRuleFiredAtExactInstantiatedRedex: true,
            bothTypedConsumersAccepted: true,
            allEightNegativeConsumersRejected: true,
            capabilityAndNonExportClosurePassed: true,
            genericCompilerDiffEmpty: true,
            failureCount: 2,
            inheritedProofAdapterResidual: {
                observation:
                    'CompMotive-sections-compare-with-' +
                    'CompTarget-representable-sections',
                errorCode: 'UNBOUND_FREE_REFERENCE',
                missingName: 'pathout_transitivity_test_Z',
                cause:
                    'proof-helper-used-compiled-environment-before-' +
                    'fixture-descendant-assumptions',
                boundaryChangeRequired: false,
                explicitDescendantEnvironmentParameterRequired: true,
                newProofRuleRequired: false,
                runtimeCategoryCollapseRequired: false
            },
            sectionComponentResidual: {
                observation: 'path-comp-sec-component-is-path-comp-func',
                mismatch: 'TAG_MISMATCH-at-root',
                normalizedLeftOwner: 'functor-object',
                normalizedLeftFamilyOwner: 'hom_con',
                normalizedRightOwner: 'hom_int_precomp_func',
                compTargetDeltaFiredBeforeLocalRuleConsulted: true,
                v2PreDeltaRuleAppliedInObservation: false,
                postDeltaCompleteParentReplacementRequired: true,
                additionalRuntimeRuleRequired: false,
                broadHomConRuleImportRequired: false,
                wholeDisplayedIdentityDeltaRequired: false,
                genericEngineChangeRequired: false,
                mathematicalRuleRequired: false
            }
        }
    },
    exactImplementation: {
        ...cloneData(proposalV2.exactImplementation),
        runtimeRules: [postDeltaSectionComponentPresentationFusion],
        moduleStages: correctedModuleStages,
        exactBoundary: '0/1/0/5',
        localRuntimeSupportRuleCount: 1,
        localProofRuleCount: 0,
        inheritedProofProviderCount: 1,
        semanticCountDeltaFromV2: 0,
        v2PreDeltaSupportRetained: false,
        v3PostDeltaSupportSelected: true,
        inheritedProofHelperAcceptsExplicitDescendantEnvironment: true,
        genericRuntimeOrProofRuleAdded: false,
        broadHomConRuntimeImportAdded: false,
        wholeDisplayedIdentityDeltaAdded: false
    },
    profileSealing: {
        ...cloneData(proposalV2.profileSealing),
        exactReviewedLocalRuntimeSupportRuleAuthorized: true,
        preDeltaLocalRuntimeSupportRuleAuthorized: false,
        stablePostDeltaLocalRuntimeSupportRuleAuthorized: true,
        inheritedProofProviderReuseAuthorized: true,
        inheritedProofProviderMustBeRechecked: true,
        inheritedProofHelperMayAcceptDescendantEnvironment: true,
        secondLocalRuntimeSupportRuleAuthorized: false,
        genericPiToFunctordRuntimeCollapseAuthorized: false,
        broadHomConRuntimeImportAuthorized: false,
        wholeDisplayedIdentityDeltaAuthorized: false
    },
    validation: {
        ...cloneData(proposalV2.validation),
        v2ProposalCheckpointRequired: V2_PROPOSAL_CHECKPOINT,
        v2ReviewCheckpointRequired: V2_REVIEW_CHECKPOINT,
        v2LedgerCheckpointRequired: V2_LEDGER_CHECKPOINT,
        reasonLongAggregateOmitted:
            'v3-is-immutable-one-for-one-root-only-boundary-data-and-' +
            'e560551-is-carried-forward'
    },
    decision: {
        question:
            'Approve only the one-for-one post-delta correction at the ' +
            'unchanged root-only 0/1/0/5 transitivity boundary?',
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-TRANSITIVITY-1E-corrected-v3-implementation',
        'retaining-v2-pre-delta-support-or-adding-a-second-runtime-rule',
        'new-opaque-owner-proof-rule-or-Core-node',
        'generic-checker-evaluator-comparison-or-runtime-matcher-change',
        'broad-hom-con-runtime-rule-import',
        'whole-id-funcd-delta-import',
        'runtime-Pi-cat-to-Functord-cat-collapse',
        'TypeScript-injectivity-or-unification-from-Lambdapi-metadata',
        'path-category-reflexive-component-join',
        'path-category-structured-versus-J-comparison-library',
        'public-browser-package-or-text-presentation',
        'active-Lambdapi-source-change',
        'integration-push-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'pathout-transitivity-1e-v3-awaiting-separate-immutable-review'
} as const;

export type CorePathoutTransitivity1eProposalV3 = typeof rawProposal;

export type CorePathoutTransitivity1eProposalV3ErrorCode =
    | 'PATHOUT_TRANSITIVITY_PROPOSAL_V3_AUTHORITY_DRIFT'
    | 'PATHOUT_TRANSITIVITY_PROPOSAL_V3_SCOPE_DRIFT'
    | 'PATHOUT_TRANSITIVITY_PROPOSAL_V3_AUTHORIZATION_DRIFT';

export class CorePathoutTransitivity1eProposalV3Error extends Error {
    constructor(
        public readonly code:
            CorePathoutTransitivity1eProposalV3ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutTransitivity1eProposalV3Error';
    }
}

export const CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3 =
    deepFreeze(rawProposal);

export function validateCorePathoutTransitivity1eProposalV3(
    proposal: CorePathoutTransitivity1eProposalV3 =
        CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3
): CorePathoutTransitivity1eProposalV3 {
    validateCorePathoutTransitivity1eProposalV2(proposalV2);
    validateCorePathoutTransitivity1eReviewV2(reviewV2);
    const evidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-TRANSITIVITY-1E-PROPOSAL-3' ||
        proposal.parent.supersededProposalRevision !== proposalV2.revision ||
        proposal.parent.supersededProposalCheckpoint !==
            V2_PROPOSAL_CHECKPOINT ||
        proposal.parent.supersededProposalSha256 !== V2_PROPOSAL_SHA256 ||
        proposal.parent.supersededReviewRevision !== reviewV2.revision ||
        proposal.parent.supersededReviewCheckpoint !== V2_REVIEW_CHECKPOINT ||
        proposal.parent.supersededReviewSha256 !== V2_REVIEW_SHA256 ||
        proposal.parent.supersededLedgerCheckpoint !== V2_LEDGER_CHECKPOINT ||
        evidence.coldFocusedGate !== '9-tests-6-pass-2-fail-1-skip' ||
        !evidence.allFiveTransparentDefinitionsAdmitted ||
        !evidence.v2LocalRuntimeRuleSubjectChecked ||
        !evidence.v2LocalRuntimeRuleFiredAtExactInstantiatedRedex ||
        !evidence.bothTypedConsumersAccepted ||
        !evidence.allEightNegativeConsumersRejected ||
        !evidence.capabilityAndNonExportClosurePassed ||
        !evidence.genericCompilerDiffEmpty ||
        evidence.failureCount !== 2 ||
        evidence.inheritedProofAdapterResidual.errorCode !==
            'UNBOUND_FREE_REFERENCE' ||
        evidence.inheritedProofAdapterResidual.boundaryChangeRequired ||
        !evidence.inheritedProofAdapterResidual
            .explicitDescendantEnvironmentParameterRequired ||
        evidence.inheritedProofAdapterResidual.newProofRuleRequired ||
        evidence.inheritedProofAdapterResidual.runtimeCategoryCollapseRequired ||
        !evidence.sectionComponentResidual
            .compTargetDeltaFiredBeforeLocalRuleConsulted ||
        evidence.sectionComponentResidual.v2PreDeltaRuleAppliedInObservation ||
        !evidence.sectionComponentResidual
            .postDeltaCompleteParentReplacementRequired ||
        evidence.sectionComponentResidual.additionalRuntimeRuleRequired ||
        evidence.sectionComponentResidual.broadHomConRuleImportRequired ||
        evidence.sectionComponentResidual.wholeDisplayedIdentityDeltaRequired ||
        evidence.sectionComponentResidual.genericEngineChangeRequired ||
        evidence.sectionComponentResidual.mathematicalRuleRequired
    ) {
        throw new CorePathoutTransitivity1eProposalV3Error(
            'PATHOUT_TRANSITIVITY_PROPOSAL_V3_AUTHORITY_DRIFT',
            'The measured v2 counterevidence or predecessor pins drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const rule = implementation.runtimeRules[0];
    if (
        implementation.exactBoundary !== '0/1/0/5' ||
        implementation.trustedDeclarations.length !== 0 ||
        implementation.runtimeRules.length !== 1 ||
        rule?.id !==
            CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID ||
        rule?.replaces !== CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID ||
        !rule?.stableAfterCompTargetDelta ||
        !rule?.completeParentOnly ||
        !rule?.mustSubjectCheck ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 5 ||
        implementation.localRuntimeSupportRuleCount !== 1 ||
        implementation.localProofRuleCount !== 0 ||
        implementation.inheritedProofProviderCount !== 1 ||
        implementation.semanticCountDeltaFromV2 !== 0 ||
        implementation.v2PreDeltaSupportRetained ||
        !implementation.v3PostDeltaSupportSelected ||
        !implementation
            .inheritedProofHelperAcceptsExplicitDescendantEnvironment ||
        implementation.genericRuntimeOrProofRuleAdded ||
        implementation.broadHomConRuntimeImportAdded ||
        implementation.wholeDisplayedIdentityDeltaAdded ||
        !sameData(
            implementation.transparentDefinitions,
            proposalV2.exactImplementation.transparentDefinitions
        ) ||
        !sameData(
            implementation.inheritedProofProviders,
            proposalV2.exactImplementation.inheritedProofProviders
        ) ||
        !sameData(
            implementation.selectedObservationPartition,
            proposalV2.exactImplementation.selectedObservationPartition
        ) ||
        !sameData(
            proposal.requiredExistingProviders,
            proposalV2.requiredExistingProviders
        ) ||
        !sameData(
            proposal.typedLibraryConsumers,
            proposalV2.typedLibraryConsumers
        ) ||
        !sameData(proposal.negativeConsumers, proposalV2.negativeConsumers) ||
        !sameData(proposal.boundedOracle, proposalV2.boundedOracle) ||
        proposal.profileSealing
            .preDeltaLocalRuntimeSupportRuleAuthorized ||
        !proposal.profileSealing
            .stablePostDeltaLocalRuntimeSupportRuleAuthorized ||
        proposal.profileSealing.secondLocalRuntimeSupportRuleAuthorized ||
        !proposal.profileSealing
            .inheritedProofHelperMayAcceptDescendantEnvironment ||
        proposal.profileSealing
            .genericPiToFunctordRuntimeCollapseAuthorized ||
        proposal.profileSealing.broadHomConRuntimeImportAuthorized ||
        proposal.profileSealing.wholeDisplayedIdentityDeltaAuthorized ||
        proposal.profileSealing.pathCategoryBridgeAuthorized ||
        proposal.profileSealing.browserOrPublicPackageExportAuthorized
    ) {
        throw new CorePathoutTransitivity1eProposalV3Error(
            'PATHOUT_TRANSITIVITY_PROPOSAL_V3_SCOPE_DRIFT',
            'The one-for-one corrected 0/1/0/5 transitivity scope drifted'
        );
    }

    if (
        proposal.status !==
            'corrected-proposal-v3-awaiting-separate-immutable-review' ||
        proposal.decision.status !== 'proposal-only' ||
        proposal.decision.implementationAuthorized ||
        !proposal.decision.separateImmutableReviewRequired ||
        proposal.gitBoundary.pushMergePublishAuthorized ||
        proposal.gitBoundary.historyRewriteAuthorized ||
        proposal.gitBoundary.cleanupAuthorized ||
        proposal.nextDependencyState !==
            'pathout-transitivity-1e-v3-awaiting-separate-immutable-review'
    ) {
        throw new CorePathoutTransitivity1eProposalV3Error(
            'PATHOUT_TRANSITIVITY_PROPOSAL_V3_AUTHORIZATION_DRIFT',
            'The corrected-v3 transitivity proposal became self-authorizing'
        );
    }
    return proposal;
}

export const cloneCorePathoutTransitivity1eProposalV3 = ():
CorePathoutTransitivity1eProposalV3 => cloneData(
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3
);
