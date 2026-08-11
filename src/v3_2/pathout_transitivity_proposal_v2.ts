/**
 * Corrected, non-authorizing PathOut transitivity proposal v2.
 *
 * A cold replay of reviewed v1 admitted all five transparent declarations
 * and isolated two presentation boundaries. The Sigma/Pi category boundary
 * is already owned by an inherited proof-time provider. The section
 * component boundary needs one local, subject-checked complete-parent
 * presentation rule after the five declarations have been compiled.
 */

import {
    CORE_CATEGORICAL_FIBRED_BINDER_TRANSFER_BOUNDARY
} from './categorical_fibred_binder_transfer';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL,
    validateCorePathoutTransitivity1eProposal
} from './pathout_transitivity_proposal';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW,
    validateCorePathoutTransitivity1eReview
} from './pathout_transitivity_review';

export const CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2_REVISION =
    'PATHOUT-LIBRARY-TRANSITIVITY-1E-PROPOSAL-2' as const;

export const CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID = (
    'pathout.transitivity.fixed-source-section-component-presentation-fusion'
) as const;

const V1_PROPOSAL_CHECKPOINT = '50b9a56';
const V1_PROPOSAL_SHA256 =
    '1951ff30d42ab95dfa9d77fadb747be9eca3c4bf760a99ab283da07fc1351bfb';
const V1_REVIEW_CHECKPOINT = 'f60b36a';
const V1_REVIEW_SHA256 =
    'cd1fead66d6447e0ed73fe5eaa6cbc67ef0a9dbb606897dbad4c6e7c0b6c76ca';
const V1_LEDGER_CHECKPOINT = '150e315';
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

const proposalV1 = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL;
const reviewV1 = CORE_PATHOUT_TRANSITIVITY_1E_REVIEW;

const localSectionComponentPresentationFusion = {
    order: 0,
    id: CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
    authority: 'derived-transitivity-complete-parent-presentation-fusion',
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
        'fapp1_func(Z,Cat_cat,CompTarget_catd(Z,x),x,y),p),' +
        'id_funcd(Z,Rep_x))',
    right: 'path_comp_func(Z,x,y,p)',
    compileAfterTransparentDefinitionCount: 5,
    completeParentOnly: true,
    mustSubjectCheck: true
} as const;

const inheritedSigmaPiProofProvider = {
    order: 0,
    id: INHERITED_PROOF_RULE_ID,
    module: 'categorical_fibred_binder_transfer',
    authorityPosition: 'emdash2/emdash3_2.lp:13049-13055',
    phase: 'proof-time-unification',
    role: 'sigma-pullback-section-category-to-displayed-functor-category',
    localRuleDelta: 0,
    recheckAgainstDescendantEnvironment: true,
    runtimeClassifierCollapseAuthorized: false
} as const;

const runtimeObservationIds = proposalV1.selectedDefinitionalObservations
    .filter(id =>
        id !==
            'CompMotive-sections-compare-with-CompTarget-representable-sections'
    );

const rawProposal = {
    ...cloneData(proposalV1),
    revision: CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2_REVISION,
    status: 'corrected-proposal-v2-awaiting-separate-immutable-review',
    parent: {
        ...cloneData(proposalV1.parent),
        supersededProposalRevision: proposalV1.revision,
        supersededProposalCheckpoint: V1_PROPOSAL_CHECKPOINT,
        supersededProposalSha256: V1_PROPOSAL_SHA256,
        supersededReviewRevision: reviewV1.revision,
        supersededReviewCheckpoint: V1_REVIEW_CHECKPOINT,
        supersededReviewSha256: V1_REVIEW_SHA256,
        supersededLedgerCheckpoint: V1_LEDGER_CHECKPOINT,
        counterevidence: {
            measuredDuring:
                'reviewed-v1-cold-focused-TypeScript-semantic-replay',
            coldFocusedGate: '8-tests-5-pass-2-fail-1-skip',
            allFiveTransparentDefinitionsAdmitted: true,
            bothTypedConsumersAccepted: true,
            allEightNegativeConsumersRejected: true,
            capabilityAndNonExportClosurePassed: true,
            genericCompilerDiffEmpty: true,
            failureCount: 2,
            sectionCategoryResidual: {
                observation:
                    'CompMotive-sections-compare-with-' +
                    'CompTarget-representable-sections',
                mismatch: 'TAG_MISMATCH-at-root',
                normalizedLeft:
                    'Pi_cat(Sigma_cat(Z,Rep_catd(Z,x)),' +
                    'Sigma_proj1_pullback_catd(Z,Rep_catd(Z,x),' +
                    'CompTarget_catd(Z,x)))',
                normalizedRight:
                    'Functord_cat(Z,Rep_catd(Z,x),CompTarget_catd(Z,x))',
                existingProvider: INHERITED_PROOF_RULE_ID,
                newRuntimeRuleRequired: false,
                newProofRuleRequired: false
            },
            sectionComponentResidual: {
                observation: 'path-comp-sec-component-is-path-comp-func',
                mismatch: 'TAG_MISMATCH-at-root',
                normalizedLeftOwner: 'functor-object',
                normalizedLeftFunctorOwner: 'functor-object',
                normalizedLeftArrowOwner: 'functor-hom-full',
                normalizedLeftObjectOwner: 'id_funcd',
                normalizedRightOwner: 'hom_int_precomp_func',
                normalizedRight:
                    'hom_int_precomp_func(Z,Z,id_func(Z),y,x,p)',
                completeParentLocalFusionRequired: true,
                broadHomConRuleImportRequired: false,
                wholeDisplayedIdentityDeltaRequired: false,
                genericEngineChangeRequired: false,
                mathematicalRuleRequired: false
            }
        }
    },
    exactImplementation: {
        ...cloneData(proposalV1.exactImplementation),
        exactBoundary: '0/1/0/5',
        runtimeRules: [localSectionComponentPresentationFusion],
        proofRules: [] as const,
        inheritedProofProviders: [inheritedSigmaPiProofProvider],
        localRuntimeSupportRuleCount: 1,
        localProofRuleCount: 0,
        inheritedProofProviderCount: 1,
        moduleStages: [
            {
                order: 0,
                id: 'derived-transitivity-declarations',
                declarations:
                    proposalV1.exactImplementation.transparentDefinitions
                        .map(entry => entry.name)
            },
            {
                order: 1,
                id: 'derived-transitivity-local-runtime-support',
                rules: [
                    CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID
                ]
            }
        ],
        selectedObservationPartition: {
            runtimeDefinitional: runtimeObservationIds,
            inheritedProofTime: [
                'CompMotive-sections-compare-with-' +
                'CompTarget-representable-sections'
            ]
        },
        genericRuntimeOrProofRuleAdded: false,
        broadHomConRuntimeImportAdded: false,
        wholeDisplayedIdentityDeltaAdded: false
    },
    profileSealing: {
        ...cloneData(proposalV1.profileSealing),
        exactReviewedLocalRuntimeSupportRuleAuthorized: true,
        inheritedProofProviderReuseAuthorized: true,
        inheritedProofProviderMustBeRechecked: true,
        genericPiToFunctordRuntimeCollapseAuthorized: false,
        broadHomConRuntimeImportAuthorized: false,
        wholeDisplayedIdentityDeltaAuthorized: false
    },
    validation: {
        ...cloneData(proposalV1.validation),
        v1ProposalCheckpointRequired: V1_PROPOSAL_CHECKPOINT,
        v1ReviewCheckpointRequired: V1_REVIEW_CHECKPOINT,
        v1LedgerCheckpointRequired: V1_LEDGER_CHECKPOINT,
        reasonLongAggregateOmitted:
            'v2-is-immutable-root-only-boundary-data-and-e560551-is-' +
            'carried-forward'
    },
    decision: {
        question:
            'Approve only the corrected root-only 0/1/0/5 transitivity ' +
            'boundary with one inherited proof provider?',
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-TRANSITIVITY-1E-corrected-v2-implementation',
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
        'pathout-transitivity-1e-v2-awaiting-separate-immutable-review'
} as const;

export type CorePathoutTransitivity1eProposalV2 = typeof rawProposal;

export type CorePathoutTransitivity1eProposalV2ErrorCode =
    | 'PATHOUT_TRANSITIVITY_PROPOSAL_V2_AUTHORITY_DRIFT'
    | 'PATHOUT_TRANSITIVITY_PROPOSAL_V2_SCOPE_DRIFT'
    | 'PATHOUT_TRANSITIVITY_PROPOSAL_V2_AUTHORIZATION_DRIFT';

export class CorePathoutTransitivity1eProposalV2Error extends Error {
    constructor(
        public readonly code:
            CorePathoutTransitivity1eProposalV2ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathoutTransitivity1eProposalV2Error';
    }
}

export const CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2 =
    deepFreeze(rawProposal);

export function validateCorePathoutTransitivity1eProposalV2(
    proposal: CorePathoutTransitivity1eProposalV2 =
        CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2
): CorePathoutTransitivity1eProposalV2 {
    validateCorePathoutTransitivity1eProposal(proposalV1);
    validateCorePathoutTransitivity1eReview(reviewV1);
    const evidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-TRANSITIVITY-1E-PROPOSAL-2' ||
        proposal.parent.supersededProposalRevision !== proposalV1.revision ||
        proposal.parent.supersededProposalCheckpoint !==
            V1_PROPOSAL_CHECKPOINT ||
        proposal.parent.supersededProposalSha256 !== V1_PROPOSAL_SHA256 ||
        proposal.parent.supersededReviewRevision !== reviewV1.revision ||
        proposal.parent.supersededReviewCheckpoint !== V1_REVIEW_CHECKPOINT ||
        proposal.parent.supersededReviewSha256 !== V1_REVIEW_SHA256 ||
        proposal.parent.supersededLedgerCheckpoint !== V1_LEDGER_CHECKPOINT ||
        evidence.coldFocusedGate !== '8-tests-5-pass-2-fail-1-skip' ||
        !evidence.allFiveTransparentDefinitionsAdmitted ||
        !evidence.bothTypedConsumersAccepted ||
        !evidence.allEightNegativeConsumersRejected ||
        !evidence.capabilityAndNonExportClosurePassed ||
        !evidence.genericCompilerDiffEmpty ||
        evidence.failureCount !== 2 ||
        evidence.sectionCategoryResidual.existingProvider !==
            INHERITED_PROOF_RULE_ID ||
        evidence.sectionCategoryResidual.newRuntimeRuleRequired ||
        evidence.sectionCategoryResidual.newProofRuleRequired ||
        !evidence.sectionComponentResidual
            .completeParentLocalFusionRequired ||
        evidence.sectionComponentResidual.broadHomConRuleImportRequired ||
        evidence.sectionComponentResidual.wholeDisplayedIdentityDeltaRequired ||
        evidence.sectionComponentResidual.genericEngineChangeRequired ||
        evidence.sectionComponentResidual.mathematicalRuleRequired ||
        !CORE_CATEGORICAL_FIBRED_BINDER_TRANSFER_BOUNDARY.proofRuleIds
            .includes(INHERITED_PROOF_RULE_ID)
    ) {
        throw new CorePathoutTransitivity1eProposalV2Error(
            'PATHOUT_TRANSITIVITY_PROPOSAL_V2_AUTHORITY_DRIFT',
            'The measured v1 counterevidence or inherited authority drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const runtimeIds = implementation.runtimeRules.map(rule => rule.id);
    const partition = implementation.selectedObservationPartition;
    const partitionedObservations = [
        ...partition.runtimeDefinitional,
        ...partition.inheritedProofTime
    ];
    if (
        implementation.exactBoundary !== '0/1/0/5' ||
        implementation.trustedDeclarations.length !== 0 ||
        implementation.runtimeRules.length !== 1 ||
        !sameData(runtimeIds, [
            CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID
        ]) ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 5 ||
        implementation.localRuntimeSupportRuleCount !== 1 ||
        implementation.localProofRuleCount !== 0 ||
        implementation.inheritedProofProviderCount !== 1 ||
        implementation.inheritedProofProviders[0]?.id !==
            INHERITED_PROOF_RULE_ID ||
        implementation.inheritedProofProviders[0]
            ?.runtimeClassifierCollapseAuthorized ||
        !sameData(
            implementation.transparentDefinitions,
            proposalV1.exactImplementation.transparentDefinitions
        ) ||
        partition.runtimeDefinitional.length !== 7 ||
        partition.inheritedProofTime.length !== 1 ||
        new Set(partitionedObservations).size !== 8 ||
        !proposalV1.selectedDefinitionalObservations.every(id =>
            partitionedObservations.includes(id)
        ) ||
        !sameData(
            proposal.requiredExistingProviders,
            proposalV1.requiredExistingProviders
        ) ||
        !sameData(
            proposal.typedLibraryConsumers,
            proposalV1.typedLibraryConsumers
        ) ||
        !sameData(proposal.negativeConsumers, proposalV1.negativeConsumers) ||
        !sameData(proposal.boundedOracle, proposalV1.boundedOracle) ||
        implementation.genericRuntimeOrProofRuleAdded ||
        implementation.broadHomConRuntimeImportAdded ||
        implementation.wholeDisplayedIdentityDeltaAdded ||
        !proposal.profileSealing
            .exactReviewedLocalRuntimeSupportRuleAuthorized ||
        !proposal.profileSealing.inheritedProofProviderReuseAuthorized ||
        !proposal.profileSealing.inheritedProofProviderMustBeRechecked ||
        proposal.profileSealing
            .genericPiToFunctordRuntimeCollapseAuthorized ||
        proposal.profileSealing.broadHomConRuntimeImportAuthorized ||
        proposal.profileSealing.wholeDisplayedIdentityDeltaAuthorized ||
        proposal.profileSealing.pathCategoryBridgeAuthorized ||
        proposal.profileSealing.browserOrPublicPackageExportAuthorized
    ) {
        throw new CorePathoutTransitivity1eProposalV2Error(
            'PATHOUT_TRANSITIVITY_PROPOSAL_V2_SCOPE_DRIFT',
            'The exact corrected 0/1/0/5 transitivity scope drifted'
        );
    }

    if (
        proposal.status !==
            'corrected-proposal-v2-awaiting-separate-immutable-review' ||
        proposal.decision.status !== 'proposal-only' ||
        proposal.decision.implementationAuthorized ||
        !proposal.decision.separateImmutableReviewRequired ||
        proposal.gitBoundary.pushMergePublishAuthorized ||
        proposal.gitBoundary.historyRewriteAuthorized ||
        proposal.gitBoundary.cleanupAuthorized ||
        proposal.nextDependencyState !==
            'pathout-transitivity-1e-v2-awaiting-separate-immutable-review'
    ) {
        throw new CorePathoutTransitivity1eProposalV2Error(
            'PATHOUT_TRANSITIVITY_PROPOSAL_V2_AUTHORIZATION_DRIFT',
            'The corrected transitivity proposal became self-authorizing'
        );
    }
    return proposal;
}

export const cloneCorePathoutTransitivity1eProposalV2 = ():
CorePathoutTransitivity1eProposalV2 => cloneData(
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2
);
