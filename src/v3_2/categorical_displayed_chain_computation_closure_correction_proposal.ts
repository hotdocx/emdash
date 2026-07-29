/**
 * Executable DISPLAYED-CHAIN-COMPUTATION-CLOSURE-CORRECTION-0A proposal.
 *
 * D-012 through D-014 froze the mathematical closure and completed the
 * declaration-linkage inventory. Subject-checking the selected rules then
 * exposed a distinct omission: several pre-existing transparent definitions
 * and runtime equations had deliberately been imported only as signatures.
 * This proposal freezes the smallest computation-closed correction and
 * authorizes nothing by itself.
 */

import {
    validateCoreCategoricalDisplayedChainConstantFunctorCorrectionReview
} from './categorical_displayed_chain_constant_functor_correction_review';

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

const semanticRuleIds = [
    'categorical.displayed-chain.sigma-first-projection-structured-arrow',
    'categorical.displayed-chain.sigma-projection-pullback-structured-arrow',
    'categorical.displayed-chain.sigma-functord-section-object',
    'categorical.displayed-chain.sigma-functord-section-structured-arrow',
    'categorical.displayed-chain.section-pullback-direct-object',
    'categorical.displayed-chain.section-pullback-direct-arrow'
] as const;

const rawProposal = {
    revision:
        'DISPLAYED-CHAIN-COMPUTATION-CLOSURE-CORRECTION-0A-PROPOSAL-1',
    status:
        'proposal-awaiting-h-dttlf-usability-displayed-chain-04',
    reviewGate: 'H-DTTLF-USABILITY-DISPLAYED-CHAIN-04',
    decisionId: 'D-DTTLF-USABILITY-015',
    prerequisite: {
        d012ReviewRevision: 'DISPLAYED-CHAIN-0A-REVIEWED-1',
        d013ReviewRevision:
            'DISPLAYED-CHAIN-TRANSFER-CORRECTION-0A-REVIEWED-1',
        d014ReviewRevision:
            'DISPLAYED-CHAIN-CONST-FUNCTOR-CORRECTION-0A-REVIEWED-1',
        d014ReviewCheckpoint:
            'b05c84a4e67c13f5c9f136b98ebb7bdae5ce41ff',
        approvedMathematicalOwnerCount: 1,
        approvedMathematicalRuntimeRuleCount: 6,
        approvedSemanticRuleIds: semanticRuleIds
    },
    compilationAudit: {
        method:
            'compile-each-selected-rule-after-generic-declaration-linkage-and-stop-at-first-subject-error',
        linkageResidualAfterD014: [],
        stagedFailures: [
            {
                stage: 'sigma-map-structured-arrow-subject',
                cause:
                    'functord_transport_lhs_func-and-rhs_func-bodies-omitted'
            },
            {
                stage: 'sigma-functord-section-object-and-arrow-subject',
                cause:
                    'sigma-projection-pullback-object-action-omitted'
            },
            {
                stage: 'sigma-functord-section-arrow-conversion',
                cause:
                    'Obj_func-body-and-Const_func-object-action-omitted'
            },
            {
                stage: 'section-pullback-direct-arrow-subject',
                cause:
                    'Const_catd-arrow-action-and-piapp0-delta-closure-omitted'
            },
            {
                stage: 'section-pullback-direct-arrow-pattern',
                cause:
                    'inferred-source-fibre-slot-was-represented-as-a-type-wildcard-instead-of-a-typed-term-capture'
            }
        ],
        allApprovedSemanticRulesCompileAfterCandidateCorrection: true,
        compiledSemanticRuleIds: semanticRuleIds,
        furtherComputationResidualExpected: false,
        newMathematicsDiscovered: false,
        activeLambdapiEditRequired: false
    },
    authorityCorrections: {
        restoredTransparentDefinitions: [
            {
                owner: 'functord_transport_lhs_func',
                activeBody:
                    'D[p] o Fibre_func(FF,x)',
                owningTransfer:
                    'categorical_fibred_transfd_transfer'
            },
            {
                owner: 'functord_transport_rhs_func',
                activeBody:
                    'Fibre_func(FF,y) o E[p]',
                owningTransfer:
                    'categorical_fibred_transfd_transfer'
            }
        ],
        restoredTransparentDefinitionCount: 2,
        checkedTransparentMirrors: [
            {
                owner: 'Obj_func',
                activeBody:
                    'Const_func(Terminal_cat,Y,y)',
                localCoreSymbol:
                    'Obj_func__displayed_chain_mirror',
                backendName: 'Obj_func',
                owningTransfer:
                    'categorical_displayed_chain_transfer',
                priorCompletedTransferMutated: false
            }
        ],
        checkedTransparentMirrorCount: 1,
        exactExistingRuntimeEquations: [
            'sigma_map_func-object-action',
            'sigma_map_func-structured-arrow-action',
            'Sigma_proj1_pullback_catd-object-action',
            'Const_func-object-action',
            'Const_catd-base-arrow-action'
        ],
        exactExistingRuntimeEquationCount: 5,
        normalFormSpecialization: {
            id:
                'categorical.displayed-chain.section-object.delta-normalize',
            owner: 'piapp0',
            left: 'piapp0(K,E,s,k)',
            right:
                'fapp0(tapp0_fapp0(Const_catd(K,Terminal_cat),E,k,s),Terminal_obj)',
            derivation: [
                'unfold-active-transparent-piapp0',
                'unfold-active-transparent-piapp0_func',
                'apply-existing-composition-object-action',
                'apply-existing-fapp0_func-object-action',
                'retain-explicit-tapp0_fapp0-component'
            ],
            typedExplicitCoreSpecialization: true,
            activeLambdapiRuleAdded: false,
            globalDirected1cOpacityRetained: true
        },
        normalFormSpecializationCount: 1,
        patternRepresentationCorrection: {
            activeSlot: 'section-pullback-direct-arrow-source-fibre-object',
            from: 'type-wildcard-used-as-term-witness',
            to: 'typed-captured-term-unused-on-rhs',
            matcherBroadening: false,
            selectedNormalFormChanged: false
        },
        dependencyPlacementPreservation: {
            owner: 'Const_func',
            d014AuthorizationRetained: true,
            selectedPlacement: 'chain-local-ambient-declaration',
            declarationTransferredExactlyOnce: true,
            authorityBroadened: false,
            completedWeakeningTransferMutated: false
        }
    },
    alternatives: [
        {
            id: 'fully-transfer-piapp0-and-piapp0_func-now',
            disposition: 'defer',
            reason:
                'Faithful but needlessly reopens the reviewed DIRECTED-1C ' +
                'closure and imports a larger evaluation-functor dependency ' +
                'graph than this consumer needs'
        },
        {
            id: 'make-directed-1c-globally-transparent-in-place',
            disposition: 'reject',
            reason:
                'It mutates a frozen reviewed catalog and still requires the ' +
                'larger piapp0_func closure'
        },
        {
            id: 'mutate-completed-weakening-transfer-to-restore-obj-body',
            disposition: 'viable-fallback-not-selected',
            reason:
                'It is faithful in isolation but changes the frozen ' +
                'declaration and rule counts used by the completed fibred ' +
                'graduation evidence'
        },
        {
            id: 'local-obj-point-normal-form-only',
            disposition: 'reject',
            reason:
                'It reduces fapp0 of Obj_func but does not provide the ' +
                'transparent category conversion required while checking ' +
                'the direct displayed-arrow subject'
        },
        {
            id: 'specialize-or-rewrite-the-six-semantic-rules',
            disposition: 'reject',
            reason:
                'It duplicates or changes the approved mathematics instead ' +
                'of restoring its pre-existing computation dependencies'
        },
        {
            id: 'external-subject-reduction-oracle',
            disposition: 'reject',
            reason:
                'The generic TypeScript checker must validate every rule ' +
                'subject and template itself'
        },
        {
            id:
                'hybrid-transport-bodies-local-obj-mirror-and-one-piapp0-normal-form',
            disposition: 'recommend',
            reason:
                'It restores the two transport bodies at their owner, uses ' +
                'the established checked-mirror seam for Obj_func without ' +
                'mutating a completed transfer, and specializes only the ' +
                'intentionally opaque larger piapp0 closure'
        }
    ],
    proposedCorrection: {
        localChainSpecificDeclarationPrerequisiteCountRemains: 3,
        localAmbientDeclarationPrerequisites: [
            'Terminal_obj',
            'Const_func'
        ],
        checkedTransparentMirrorDeclarations: [
            'Obj_func__displayed_chain_mirror'
        ],
        totalAmbientDeclarationPrerequisiteCountRemains: 2,
        approvedExistingDeclarationPrerequisiteCountRemains: 5,
        totalGenericTransferDeclarationCount: 6,
        restoredTransparentDefinitionCount: 2,
        checkedTransparentMirrorCount: 1,
        localPrerequisiteRuntimeClauseCount: 6,
        inheritedPrerequisiteRuntimeClauseCount: 0,
        totalPrerequisiteRuntimeClauseCount: 6,
        exactExistingRuntimeEquationCount: 5,
        typedNormalFormSpecializationCount: 1,
        mathematicalOwnerCountRemains: 1,
        mathematicalRuntimeRuleCountRemains: 6,
        mathematicalProofRuleCountRemains: 0,
        activeLambdapiEditCount: 0,
        intrinsicCoreOwnerCountRemains: 0,
        externalOracleCount: 0,
        parserOrCheckerLayerCount: 0,
        compiler:
            'generic-lf-declaration-and-runtime-compilers'
    },
    validationPlan: {
        exactDeclarationPartition:
            'three-chain-specific-plus-two-local-ambient-plus-one-checked-transparent-mirror',
        exactRuntimePartition:
            'five-exact-existing-plus-one-typed-normal-form-plus-six-semantic',
        allDeclarationsAndRuleSubjectsChecked: true,
        finalDependentDeclarationsRecompiledAgainstComposedRuntime: true,
        exactSemanticRuleIdsRequired: semanticRuleIds,
        diagnosticRuleNameForbiddenInFinalTransfer: true,
        objectAndInternalizedArrowEvidenceRequired: true,
        recursiveConsumerStillRequiredAfterTransfer: true,
        activeSourceHashRequired: true,
        rootTypecheckLintAndTestsRequired: true,
        boundedKernelCheckRequired: true,
        browserExclusionRequired: true
    },
    nonEffects: [
        'does-not-mutate-the-frozen-d-012-through-d-014-records',
        'does-not-add-or-edit-an-active-lambdapi-owner-or-rule',
        'does-not-add-a-new-mathematical-owner-or-rule',
        'does-not-change-any-of-the-six-approved-semantic-normal-forms',
        'does-not-make-directed-1c-globally-transparent',
        'does-not-mutate-the-completed-weakening-reindexing-transfer',
        'does-not-add-an-intrinsic-core-owner',
        'does-not-add-an-external-subject-reduction-oracle',
        'does-not-add-a-parser-rawexpr-or-second-checker',
        'does-not-authorize-general-nd-or-arbitrary-telescope-depth',
        'does-not-authorize-browser-promotion-or-bulk-transfer',
        'does-not-broaden-git-authority'
    ],
    decisionEffects: {
        authorityAuthorized: false,
        implementationAuthorized: false,
        nextIfApproved:
            'displayed-chain-1a-computation-closed-generic-transfer',
        nextIfRejected:
            'displayed-chain-1a-typescript-transfer-blocked-on-pre-existing-computation-closure'
    }
} as const;

export type CoreCategoricalDisplayedChainComputationClosureCorrectionProposalInput =
    typeof rawProposal;

export type CoreCategoricalDisplayedChainComputationClosureCorrectionProposalErrorCode =
    | 'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_PREREQUISITE_DRIFT'
    | 'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_BOUNDARY_DRIFT'
    | 'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_AUTHORITY_DRIFT';

export class
CoreCategoricalDisplayedChainComputationClosureCorrectionProposalError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedChainComputationClosureCorrectionProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreCategoricalDisplayedChainComputationClosureCorrectionProposalError';
    }
}

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_PROPOSAL =
    deepFreeze(rawProposal);

export function
validateCoreCategoricalDisplayedChainComputationClosureCorrectionProposal(
    proposal:
        CoreCategoricalDisplayedChainComputationClosureCorrectionProposalInput =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_PROPOSAL
): void {
    try {
        validateCoreCategoricalDisplayedChainConstantFunctorCorrectionReview();
    } catch (error: unknown) {
        throw new
        CoreCategoricalDisplayedChainComputationClosureCorrectionProposalError(
            'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_PREREQUISITE_DRIFT',
            'The reviewed D-014 prerequisite drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        proposal.revision !==
            'DISPLAYED-CHAIN-COMPUTATION-CLOSURE-CORRECTION-0A-PROPOSAL-1' ||
        proposal.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-chain-04' ||
        proposal.reviewGate !==
            'H-DTTLF-USABILITY-DISPLAYED-CHAIN-04' ||
        proposal.decisionId !== 'D-DTTLF-USABILITY-015' ||
        proposal.prerequisite.approvedMathematicalOwnerCount !== 1 ||
        proposal.prerequisite.approvedMathematicalRuntimeRuleCount !== 6 ||
        proposal.prerequisite.approvedSemanticRuleIds.join(',') !==
            semanticRuleIds.join(',') ||
        proposal.compilationAudit.linkageResidualAfterD014.length !== 0 ||
        proposal.compilationAudit.stagedFailures.length !== 5 ||
        !proposal.compilationAudit
            .allApprovedSemanticRulesCompileAfterCandidateCorrection ||
        proposal.compilationAudit.compiledSemanticRuleIds.join(',') !==
            semanticRuleIds.join(',') ||
        proposal.compilationAudit.furtherComputationResidualExpected ||
        proposal.compilationAudit.newMathematicsDiscovered ||
        proposal.compilationAudit.activeLambdapiEditRequired
    ) {
        throw new
        CoreCategoricalDisplayedChainComputationClosureCorrectionProposalError(
            'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_PREREQUISITE_DRIFT',
            'The staged computation-closure diagnosis drifted'
        );
    }

    const authority = proposal.authorityCorrections;
    const correction = proposal.proposedCorrection;
    if (
        authority.restoredTransparentDefinitions.map(
            entry => entry.owner
        ).join(',') !==
            'functord_transport_lhs_func,' +
            'functord_transport_rhs_func' ||
        authority.restoredTransparentDefinitionCount !== 2 ||
        authority.checkedTransparentMirrors.map(
            entry => entry.owner
        ).join(',') !== 'Obj_func' ||
        authority.checkedTransparentMirrors[0].localCoreSymbol !==
            'Obj_func__displayed_chain_mirror' ||
        authority.checkedTransparentMirrors[0].backendName !== 'Obj_func' ||
        authority.checkedTransparentMirrors[0]
            .priorCompletedTransferMutated ||
        authority.checkedTransparentMirrorCount !== 1 ||
        authority.exactExistingRuntimeEquationCount !== 5 ||
        authority.normalFormSpecialization.owner !== 'piapp0' ||
        !authority.normalFormSpecialization
            .typedExplicitCoreSpecialization ||
        authority.normalFormSpecialization.activeLambdapiRuleAdded ||
        !authority.normalFormSpecialization.globalDirected1cOpacityRetained ||
        authority.normalFormSpecializationCount !== 1 ||
        authority.patternRepresentationCorrection.matcherBroadening ||
        authority.patternRepresentationCorrection.selectedNormalFormChanged ||
        !authority.dependencyPlacementPreservation.d014AuthorizationRetained ||
        authority.dependencyPlacementPreservation.selectedPlacement !==
            'chain-local-ambient-declaration' ||
        !authority.dependencyPlacementPreservation
            .declarationTransferredExactlyOnce ||
        authority.dependencyPlacementPreservation.authorityBroadened ||
        authority.dependencyPlacementPreservation
            .completedWeakeningTransferMutated ||
        correction.localChainSpecificDeclarationPrerequisiteCountRemains !==
            3 ||
        correction.localAmbientDeclarationPrerequisites.join(',') !==
            'Terminal_obj,Const_func' ||
        correction.checkedTransparentMirrorDeclarations.join(',') !==
            'Obj_func__displayed_chain_mirror' ||
        correction.totalAmbientDeclarationPrerequisiteCountRemains !== 2 ||
        correction.approvedExistingDeclarationPrerequisiteCountRemains !==
            5 ||
        correction.totalGenericTransferDeclarationCount !== 6 ||
        correction.restoredTransparentDefinitionCount !== 2 ||
        correction.checkedTransparentMirrorCount !== 1 ||
        correction.localPrerequisiteRuntimeClauseCount !== 6 ||
        correction.inheritedPrerequisiteRuntimeClauseCount !== 0 ||
        correction.totalPrerequisiteRuntimeClauseCount !== 6 ||
        correction.exactExistingRuntimeEquationCount !== 5 ||
        correction.typedNormalFormSpecializationCount !== 1 ||
        correction.mathematicalOwnerCountRemains !== 1 ||
        correction.mathematicalRuntimeRuleCountRemains !== 6 ||
        correction.mathematicalProofRuleCountRemains !== 0 ||
        correction.activeLambdapiEditCount !== 0 ||
        correction.intrinsicCoreOwnerCountRemains !== 0 ||
        correction.externalOracleCount !== 0 ||
        correction.parserOrCheckerLayerCount !== 0 ||
        proposal.alternatives.filter(
            alternative => alternative.disposition === 'recommend'
        ).map(alternative => alternative.id).join(',') !==
            'hybrid-transport-bodies-local-obj-mirror-and-one-piapp0-normal-form'
    ) {
        throw new
        CoreCategoricalDisplayedChainComputationClosureCorrectionProposalError(
            'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_BOUNDARY_DRIFT',
            'The bounded computation-closure correction drifted'
        );
    }

    if (
        proposal.decisionEffects.authorityAuthorized ||
        proposal.decisionEffects.implementationAuthorized ||
        proposal.nonEffects.length !== 12
    ) {
        throw new
        CoreCategoricalDisplayedChainComputationClosureCorrectionProposalError(
            'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_AUTHORITY_DRIFT',
            'The proposal must remain non-self-authorizing'
        );
    }
}

validateCoreCategoricalDisplayedChainComputationClosureCorrectionProposal();
