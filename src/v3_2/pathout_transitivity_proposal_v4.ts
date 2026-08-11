/**
 * Corrected, non-authorizing PathOut transitivity proposal v4.
 *
 * Reviewed v3 reaches the intended post-CompTarget mathematical shape, but
 * transparent Rep_catd descendants have already delta-expanded before that
 * local pattern is consulted. V4 replaces the v3 rule one-for-one with the
 * original complete consumer parent, before any descendant delta. The exact
 * root-only boundary remains 0/1/0/5.
 */

import {
    CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3,
    validateCorePathoutTransitivity1eProposalV3
} from './pathout_transitivity_proposal_v3';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3,
    validateCorePathoutTransitivity1eReviewV3
} from './pathout_transitivity_review_v3';

export const CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4_REVISION =
    'PATHOUT-LIBRARY-TRANSITIVITY-1E-PROPOSAL-4' as const;

export const CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID = (
    'pathout.transitivity.fixed-source-selected-component-consumer-parent-fusion'
) as const;

const V3_PROPOSAL_CHECKPOINT = 'fe1a9b7';
const V3_PROPOSAL_SHA256 =
    '0d7448ae68d9aa6ae3bf91b9010a676f8ca3c9101976e1de2c88816a94e68dd9';
const V3_REVIEW_CHECKPOINT = '0834d00';
const V3_REVIEW_SHA256 =
    '064e36392e6e7962912237d4f0d1abc27ae0184e1f0b6e94009ce1b7842664f6';
const V3_LEDGER_CHECKPOINT = '5d0dad5';

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

const proposalV3 = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3;
const reviewV3 = CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3;

const selectedComponentConsumerParentFusion = {
    order: 0,
    id: CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID,
    replaces: CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
    authority:
        'derived-transitivity-original-complete-consumer-parent-fusion',
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
        'fapp0(Hom_cat(Z,x,y),Functord_cat(Z,Rep_y,Rep_x),' +
        'component(Z,Rep_x,CompTarget_catd(Z,x),y,' +
        'path_comp_sec(Z,x)),p)',
    right: 'path_comp_func(Z,x,y,p)',
    compileAfterTransparentDefinitionCount: 5,
    completeParentOnly: true,
    originalConsumerParent: true,
    consultedBeforeDescendantDelta: true,
    mustSubjectCheck: true
} as const;

const correctedModuleStages = proposalV3.exactImplementation.moduleStages
    .map(stage => stage.id ===
        'derived-transitivity-local-runtime-support'
        ? {
            ...cloneData(stage),
            rules: [
                CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID
            ]
        }
        : cloneData(stage)
    );

const rawProposal = {
    ...cloneData(proposalV3),
    revision: CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4_REVISION,
    status: 'corrected-proposal-v4-awaiting-separate-immutable-review',
    parent: {
        ...cloneData(proposalV3.parent),
        supersededProposalRevision: proposalV3.revision,
        supersededProposalCheckpoint: V3_PROPOSAL_CHECKPOINT,
        supersededProposalSha256: V3_PROPOSAL_SHA256,
        supersededReviewRevision: reviewV3.revision,
        supersededReviewCheckpoint: V3_REVIEW_CHECKPOINT,
        supersededReviewSha256: V3_REVIEW_SHA256,
        supersededLedgerCheckpoint: V3_LEDGER_CHECKPOINT,
        priorCounterevidence: cloneData(proposalV3.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'reviewed-v3-cold-focused-TypeScript-semantic-replay',
            coldFocusedGate: '9-tests-6-pass-2-fail-1-skip',
            coldFocusedDurationMs: 210_148,
            isolatedObservationGate: '1-test-0-pass-1-fail',
            isolatedObservationTestDurationMs: 194_177,
            allFiveTransparentDefinitionsAdmitted: true,
            v3LocalRuntimeRuleSubjectChecked: true,
            v3LocalRuntimeRuleFiredAtExactInstantiatedRedex: true,
            bothTypedConsumersAccepted: true,
            allEightNegativeConsumersRejected: true,
            capabilityAndNonExportClosurePassed: true,
            genericCompilerDiffEmpty: true,
            failureCount: 2,
            inheritedProofCorrection: {
                explicitDescendantEnvironmentUsed: true,
                providerId: 'stress.sigma-pi.uncurrying',
                providerSolved: true,
                newProofRuleRequired: false,
                boundaryChangeRequired: false
            },
            predecessorTestLinkageResidual: {
                error: 'No transitivity link for path_ind_sec',
                cause:
                    'test-helper-asked-local-linkage-for-predecessor-symbol',
                correction:
                    'use-canonical-fixed-source-Core-name',
                semanticBoundaryChangeRequired: false
            },
            sectionComponentResidual: {
                observation: 'path-comp-sec-component-is-path-comp-func',
                mismatch: 'TAG_MISMATCH-at-root',
                normalizedLeftOwner: 'functor-object',
                normalizedRightOwner: 'hom_int_precomp_func',
                representableSubtermsNormalizedOwner: 'hom_',
                representableFamilyDeltaFiredBeforeV3PatternMatch: true,
                v3PostDeltaRuleAppliedInObservation: false,
                originalConsumerParent:
                    'fapp0(Hom_cat,Functord_cat,component,p)',
                originalConsumerParentReplacementRequired: true,
                additionalRuntimeRuleRequired: false,
                genericEngineChangeRequired: false,
                mathematicalRuleRequired: false
            }
        }
    },
    exactImplementation: {
        ...cloneData(proposalV3.exactImplementation),
        runtimeRules: [selectedComponentConsumerParentFusion],
        moduleStages: correctedModuleStages,
        exactBoundary: '0/1/0/5',
        localRuntimeSupportRuleCount: 1,
        localProofRuleCount: 0,
        inheritedProofProviderCount: 1,
        semanticCountDeltaFromV3: 0,
        v2PreDeltaSupportRetained: false,
        v3PostDeltaSupportRetained: false,
        v4ConsumerParentSupportSelected: true,
        inheritedProofHelperAcceptsExplicitDescendantEnvironment: true,
        genericRuntimeOrProofRuleAdded: false,
        broadHomConRuntimeImportAdded: false,
        wholeDisplayedIdentityDeltaAdded: false
    },
    profileSealing: {
        ...cloneData(proposalV3.profileSealing),
        exactReviewedLocalRuntimeSupportRuleAuthorized: true,
        preDeltaLocalRuntimeSupportRuleAuthorized: false,
        stablePostDeltaLocalRuntimeSupportRuleAuthorized: false,
        originalConsumerParentLocalRuntimeSupportRuleAuthorized: true,
        inheritedProofProviderReuseAuthorized: true,
        inheritedProofProviderMustBeRechecked: true,
        inheritedProofHelperMayAcceptDescendantEnvironment: true,
        secondLocalRuntimeSupportRuleAuthorized: false,
        genericPiToFunctordRuntimeCollapseAuthorized: false,
        broadHomConRuntimeImportAuthorized: false,
        wholeDisplayedIdentityDeltaAuthorized: false
    },
    validation: {
        ...cloneData(proposalV3.validation),
        v3ProposalCheckpointRequired: V3_PROPOSAL_CHECKPOINT,
        v3ReviewCheckpointRequired: V3_REVIEW_CHECKPOINT,
        v3LedgerCheckpointRequired: V3_LEDGER_CHECKPOINT,
        reasonLongAggregateOmitted:
            'v4-is-immutable-one-for-one-root-only-boundary-data-and-' +
            'e560551-is-carried-forward'
    },
    decision: {
        question:
            'Approve only the one-for-one original consumer-parent ' +
            'correction at the unchanged root-only 0/1/0/5 boundary?',
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-TRANSITIVITY-1E-corrected-v4-implementation',
        'retaining-v3-post-delta-support-or-adding-a-second-runtime-rule',
        'new-opaque-owner-proof-rule-or-Core-node',
        'generic-checker-evaluator-comparison-or-runtime-matcher-change',
        'broad-hom-con-runtime-rule-import',
        'whole-id-funcd-or-Rep-catd-delta-import',
        'runtime-Pi-cat-to-Functord-cat-collapse',
        'TypeScript-injectivity-or-unification-from-Lambdapi-metadata',
        'path-category-reflexive-component-join',
        'path-category-structured-versus-J-comparison-library',
        'public-browser-package-or-text-presentation',
        'active-Lambdapi-source-change',
        'integration-push-publication-deployment-or-cleanup'
    ],
    nextDependencyState:
        'pathout-transitivity-1e-v4-awaiting-separate-immutable-review'
} as const;

export type CorePathoutTransitivity1eProposalV4 = typeof rawProposal;

export type CorePathoutTransitivity1eProposalV4ErrorCode =
    | 'PATHOUT_TRANSITIVITY_PROPOSAL_V4_AUTHORITY_DRIFT'
    | 'PATHOUT_TRANSITIVITY_PROPOSAL_V4_SCOPE_DRIFT'
    | 'PATHOUT_TRANSITIVITY_PROPOSAL_V4_AUTHORIZATION_DRIFT';

export class CorePathoutTransitivity1eProposalV4Error extends Error {
    constructor(
        public readonly code:
            CorePathoutTransitivity1eProposalV4ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutTransitivity1eProposalV4Error';
    }
}

export const CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4 =
    deepFreeze(rawProposal);

export function validateCorePathoutTransitivity1eProposalV4(
    proposal: CorePathoutTransitivity1eProposalV4 =
        CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4
): CorePathoutTransitivity1eProposalV4 {
    validateCorePathoutTransitivity1eProposalV3(proposalV3);
    validateCorePathoutTransitivity1eReviewV3(reviewV3);
    const evidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-TRANSITIVITY-1E-PROPOSAL-4' ||
        proposal.parent.supersededProposalRevision !== proposalV3.revision ||
        proposal.parent.supersededProposalCheckpoint !==
            V3_PROPOSAL_CHECKPOINT ||
        proposal.parent.supersededProposalSha256 !== V3_PROPOSAL_SHA256 ||
        proposal.parent.supersededReviewRevision !== reviewV3.revision ||
        proposal.parent.supersededReviewCheckpoint !== V3_REVIEW_CHECKPOINT ||
        proposal.parent.supersededReviewSha256 !== V3_REVIEW_SHA256 ||
        proposal.parent.supersededLedgerCheckpoint !== V3_LEDGER_CHECKPOINT ||
        evidence.coldFocusedGate !== '9-tests-6-pass-2-fail-1-skip' ||
        evidence.isolatedObservationGate !== '1-test-0-pass-1-fail' ||
        !evidence.allFiveTransparentDefinitionsAdmitted ||
        !evidence.v3LocalRuntimeRuleSubjectChecked ||
        !evidence.v3LocalRuntimeRuleFiredAtExactInstantiatedRedex ||
        !evidence.bothTypedConsumersAccepted ||
        !evidence.allEightNegativeConsumersRejected ||
        !evidence.capabilityAndNonExportClosurePassed ||
        !evidence.genericCompilerDiffEmpty ||
        evidence.failureCount !== 2 ||
        !evidence.inheritedProofCorrection.explicitDescendantEnvironmentUsed ||
        !evidence.inheritedProofCorrection.providerSolved ||
        evidence.inheritedProofCorrection.newProofRuleRequired ||
        evidence.predecessorTestLinkageResidual
            .semanticBoundaryChangeRequired ||
        !evidence.sectionComponentResidual
            .representableFamilyDeltaFiredBeforeV3PatternMatch ||
        evidence.sectionComponentResidual.v3PostDeltaRuleAppliedInObservation ||
        !evidence.sectionComponentResidual
            .originalConsumerParentReplacementRequired ||
        evidence.sectionComponentResidual.additionalRuntimeRuleRequired ||
        evidence.sectionComponentResidual.genericEngineChangeRequired ||
        evidence.sectionComponentResidual.mathematicalRuleRequired
    ) {
        throw new CorePathoutTransitivity1eProposalV4Error(
            'PATHOUT_TRANSITIVITY_PROPOSAL_V4_AUTHORITY_DRIFT',
            'The measured v3 counterevidence or predecessor pins drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const rule = implementation.runtimeRules[0];
    if (
        implementation.exactBoundary !== '0/1/0/5' ||
        implementation.trustedDeclarations.length !== 0 ||
        implementation.runtimeRules.length !== 1 ||
        rule?.id !==
            CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID ||
        rule?.replaces !==
            CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID ||
        !rule?.originalConsumerParent ||
        !rule?.consultedBeforeDescendantDelta ||
        !rule?.completeParentOnly ||
        !rule?.mustSubjectCheck ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 5 ||
        implementation.localRuntimeSupportRuleCount !== 1 ||
        implementation.localProofRuleCount !== 0 ||
        implementation.inheritedProofProviderCount !== 1 ||
        implementation.semanticCountDeltaFromV3 !== 0 ||
        implementation.v2PreDeltaSupportRetained ||
        implementation.v3PostDeltaSupportRetained ||
        !implementation.v4ConsumerParentSupportSelected ||
        !implementation
            .inheritedProofHelperAcceptsExplicitDescendantEnvironment ||
        implementation.genericRuntimeOrProofRuleAdded ||
        implementation.broadHomConRuntimeImportAdded ||
        implementation.wholeDisplayedIdentityDeltaAdded ||
        !sameData(
            implementation.transparentDefinitions,
            proposalV3.exactImplementation.transparentDefinitions
        ) ||
        !sameData(
            implementation.inheritedProofProviders,
            proposalV3.exactImplementation.inheritedProofProviders
        ) ||
        !sameData(
            implementation.selectedObservationPartition,
            proposalV3.exactImplementation.selectedObservationPartition
        ) ||
        !sameData(
            proposal.requiredExistingProviders,
            proposalV3.requiredExistingProviders
        ) ||
        !sameData(
            proposal.typedLibraryConsumers,
            proposalV3.typedLibraryConsumers
        ) ||
        !sameData(proposal.negativeConsumers, proposalV3.negativeConsumers) ||
        !sameData(proposal.boundedOracle, proposalV3.boundedOracle) ||
        proposal.profileSealing.preDeltaLocalRuntimeSupportRuleAuthorized ||
        proposal.profileSealing.stablePostDeltaLocalRuntimeSupportRuleAuthorized ||
        !proposal.profileSealing
            .originalConsumerParentLocalRuntimeSupportRuleAuthorized ||
        proposal.profileSealing.secondLocalRuntimeSupportRuleAuthorized ||
        !proposal.profileSealing
            .inheritedProofHelperMayAcceptDescendantEnvironment ||
        proposal.profileSealing.genericPiToFunctordRuntimeCollapseAuthorized ||
        proposal.profileSealing.broadHomConRuntimeImportAuthorized ||
        proposal.profileSealing.wholeDisplayedIdentityDeltaAuthorized ||
        proposal.profileSealing.pathCategoryBridgeAuthorized ||
        proposal.profileSealing.browserOrPublicPackageExportAuthorized
    ) {
        throw new CorePathoutTransitivity1eProposalV4Error(
            'PATHOUT_TRANSITIVITY_PROPOSAL_V4_SCOPE_DRIFT',
            'The one-for-one corrected 0/1/0/5 transitivity scope drifted'
        );
    }

    if (
        proposal.status !==
            'corrected-proposal-v4-awaiting-separate-immutable-review' ||
        proposal.decision.status !== 'proposal-only' ||
        proposal.decision.implementationAuthorized ||
        !proposal.decision.separateImmutableReviewRequired ||
        proposal.gitBoundary.pushMergePublishAuthorized ||
        proposal.gitBoundary.historyRewriteAuthorized ||
        proposal.gitBoundary.cleanupAuthorized ||
        proposal.nextDependencyState !==
            'pathout-transitivity-1e-v4-awaiting-separate-immutable-review'
    ) {
        throw new CorePathoutTransitivity1eProposalV4Error(
            'PATHOUT_TRANSITIVITY_PROPOSAL_V4_AUTHORIZATION_DRIFT',
            'The corrected-v4 transitivity proposal became self-authorizing'
        );
    }
    return proposal;
}

export const cloneCorePathoutTransitivity1eProposalV4 = ():
CorePathoutTransitivity1eProposalV4 => cloneData(
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4
);
