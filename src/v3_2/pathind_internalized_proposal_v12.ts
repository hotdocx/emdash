/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v12.
 *
 * V12 retains the reviewed v11 staged fibre closure and adds one exact
 * complete-parent presentation rule for the active section-pullback body of
 * `pathout_pi_transport_func`. It deliberately does not expose the active
 * proof-time `Pi_cat` comparison as a category-level runtime equality.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11,
    validateCorePathindInternalized1dProposalV11
} from './pathind_internalized_proposal_v11';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-12' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-12/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-012 as proposed.';

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

const proposalV11 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11;

const pathoutPiTransportFunctorPresentationFusion = {
    order: 11,
    id:
        'pathind.internalized.' +
        'pathout-pi-transport-functor-presentation-fusion',
    authority:
        'derived-complete-parent-section-pullback-presentation-fusion',
    authorityPositions: [
        'emdash2/emdash3_2.lp:12554-12561',
        'emdash2/emdash3_2.lp:16502-16506',
        'emdash2/emdash3_2.lp:19139-19153',
        'emdash2/emdash3_2.lp:19734-19744'
    ],
    sourceOwner: 'decode',
    policy: 'runtime-rewrite-derived-support',
    mathematicalRule: false,
    variables: ['Z', 'x', 'y', 'p', 'E'],
    left:
        'τ(Functor(' +
        'Functord_cat(PathOut_Z(x),Const(PathOut_Z(x),Terminal),E),' +
        'Functord_cat(PathOut_Z(y),Const(PathOut_Z(y),Terminal),' +
        'Pullback_catd(E,PathOut_transport(p)))))',
    right:
        'τ(Functor(Pi_cat(PathOut_Z(x),E),' +
        'Pi_cat(PathOut_Z(y),' +
        'pathout_motive_transport_obj(Z,x,y,p,E))))'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV11.exactImplementation.runtimeRules.map(rule =>
        cloneData(rule)
    ),
    pathoutPiTransportFunctorPresentationFusion
]);

const correctedExtensionRuntimeRuleIds = Object.freeze([
    ...proposalV11.exactImplementation.stagedModulePartition
        .extensionRuntimeRuleIds,
    pathoutPiTransportFunctorPresentationFusion.id
]);

const correctedStages = Object.freeze(
    proposalV11.exactImplementation.implementationStages.map(stage => {
        const cloned = cloneData(stage) as Record<string, unknown>;
        return cloned.id ===
            'internalized-runtime-source-fibre-extension'
            ? {
                ...cloned,
                rules: cloneData(correctedExtensionRuntimeRuleIds)
            }
            : cloned;
    })
);

const rawProposal = {
    ...cloneData(proposalV11),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12_REVISION,
    status: 'corrected-proposal-v12-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV11.parent),
        supersededProposalRevision: proposalV11.revision,
        supersededProposalCheckpoint: '2e1e593',
        supersededReviewCheckpoint: '731dc32',
        supersededLedgerCheckpoint: null,
        priorCounterevidence:
            cloneData(proposalV11.parent.counterevidence),
        counterevidence: {
            measuredDuring: 'reviewed-v11-cold-semantic-replay-with-trace',
            allElevenRuntimeRulesSubjectChecked: true,
            allThreePrefixTransparentDefinitionsCompiled: true,
            compiledPrefixTransparentDefinitions: [
                'pathout_motive_transport_obj',
                'pathout_motive_transport_arrow',
                'PathIndSrc_catd'
            ],
            bothPostPrefixExtensionRulesSubjectChecked: true,
            pathInductionSourceTransportCompiled: true,
            pathInductionTotalFunctorCompiled: true,
            compiledDerivedTransparentDefinitionCount: 5,
            selectedDerivedTransparentDefinitionCount: 7,
            failingDeclaration: 'pathout_pi_transport_func',
            failingDeclarationOrder: 5,
            failingAuthorityPosition:
                'emdash2/emdash3_2.lp:19734-19744',
            requestedComparisonStepLimit: 512,
            effectiveComparisonStepLimit: 512,
            comparisonStepLimitExceeded: false,
            comparisonSteps: [318, 326, 54],
            comparisonMismatchCodes: [
                'TAG_MISMATCH',
                'TAG_MISMATCH',
                'TAG_MISMATCH'
            ],
            primaryMismatchPath: [
                '$',
                'application:decode:argument:0',
                'application:object-classifier:argument:0',
                'call:argument:0'
            ],
            primaryMismatchLeft:
                'call:reference:dttlf_Functord_cat',
            primaryMismatchRight: 'application:section-category',
            terminalMismatchLeft:
                'call:reference:dttlf_Functord_cat',
            terminalMismatchRight: 'application:section-category',
            activeSectionCategoryFacadeIsOpaque: true,
            activeSectionCategoryComparisonIsProofTimeOnly: true,
            activeSectionPullbackBodyUsesDisplayedFunctorCategories: true,
            declaredTypeUsesSectionCategoryFacades: true,
            completeFunctorParentFusionRequired: true,
            underlyingCategoryRuntimeEqualityRequired: false,
            declarationBodyOrTypeChangeRequired: false,
            declarationSourceOrderChangeRequired: false,
            genericComparisonChangeRequired: false,
            genericRuntimeMatcherChangeRequired: false,
            mathematicalRuleRequired: false,
            proofRuleRequired: false,
            temporaryObserverRetained: false
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-12',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-012',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV11.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/12/0/10',
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 7,
        stagedModulePartition: {
            ...cloneData(
                proposalV11.exactImplementation.stagedModulePartition
            ),
            extensionRuntimeRuleIds: correctedExtensionRuntimeRuleIds,
            semanticCountDelta: 1
        }
    },
    selectedPredecessor: {
        ...cloneData(proposalV11.selectedPredecessor),
        v11TransportedMotiveReflexiveFibreFusionRetained: true,
        v11TransportedMotiveReflexiveFibreFusionInsufficientAlone: true,
        v12PathoutPiTransportFunctorPresentationFusionSelected: true
    },
    dependencyClosure: {
        ...cloneData(proposalV11.dependencyClosure),
        pathoutPiTransportFunctorPresentationFusion: {
            ruleId: pathoutPiTransportFunctorPresentationFusion.id,
            authorityPositions:
                pathoutPiTransportFunctorPresentationFusion
                    .authorityPositions,
            left: pathoutPiTransportFunctorPresentationFusion.left,
            right: pathoutPiTransportFunctorPresentationFusion.right,
            exactPathoutPiTransportParentSelected: true,
            sourceAndTargetCategoriesClosedTogether: true,
            prefixDeclaresMotiveTransportBeforeRuleCompilation: true,
            extensionRetainsBothFibreSupportRules: true,
            activeSectionFacadeComparisonOnly: true,
            activeSectionPullbackSignatureOnly: true,
            underlyingCategoryRuntimeEqualitySelected: false,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            activeMathematicalRuleDelta: 0,
            derivedSupportRuleDelta: 1,
            proofRuleDelta: 0,
            declarationBodyOrTypeChangeAuthorized: false,
            declarationSourceOrderChangeAuthorized: false,
            genericSectionCategoryRuleAuthorized: false,
            genericComparisonChangeAuthorized: false,
            genericRuntimeMatcherChangeAuthorized: false,
            genericCheckerChangeAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV11.validation),
        v11ProposalCheckpointRequired: '2e1e593',
        v11ReviewCheckpointRequired: '731dc32',
        reasonLongAggregateOmitted:
            'v12-is-immutable-boundary-data-and-e560551-is-carried-forward'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v12-implementation',
        ...cloneData(proposalV11.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v11-implementation' &&
            entry !== 'adding-a-twelfth-runtime-rule'
        ),
        'changing-any-selected-declaration-body-or-type',
        'changing-the-order-of-the-seven-derived-declarations',
        'adding-a-thirteenth-runtime-rule',
        'adding-a-generic-Pi-cat-to-Functord-cat-runtime-equality'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v12-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV12 = typeof rawProposal;

export type CorePathindInternalized1dProposalV12ErrorCode =
    | 'PATHIND_INTERNALIZED_V12_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V12_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V12_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV12Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV12ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV12Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV12(
    proposal: CorePathindInternalized1dProposalV12 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12
): CorePathindInternalized1dProposalV12 {
    validateCorePathindInternalized1dProposalV11(proposalV11);
    const evidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-12' ||
        proposal.parent.supersededProposalRevision !== proposalV11.revision ||
        proposal.parent.supersededProposalCheckpoint !== '2e1e593' ||
        proposal.parent.supersededReviewCheckpoint !== '731dc32' ||
        proposal.parent.supersededLedgerCheckpoint !== null ||
        !evidence.allElevenRuntimeRulesSubjectChecked ||
        !evidence.allThreePrefixTransparentDefinitionsCompiled ||
        evidence.compiledPrefixTransparentDefinitions.length !== 3 ||
        !evidence.bothPostPrefixExtensionRulesSubjectChecked ||
        !evidence.pathInductionSourceTransportCompiled ||
        !evidence.pathInductionTotalFunctorCompiled ||
        evidence.compiledDerivedTransparentDefinitionCount !== 5 ||
        evidence.selectedDerivedTransparentDefinitionCount !== 7 ||
        evidence.failingDeclaration !== 'pathout_pi_transport_func' ||
        evidence.failingDeclarationOrder !== 5 ||
        evidence.requestedComparisonStepLimit !== 512 ||
        evidence.effectiveComparisonStepLimit !== 512 ||
        evidence.comparisonStepLimitExceeded ||
        !sameData(evidence.comparisonSteps, [318, 326, 54]) ||
        !sameData(evidence.comparisonMismatchCodes, [
            'TAG_MISMATCH',
            'TAG_MISMATCH',
            'TAG_MISMATCH'
        ]) ||
        evidence.primaryMismatchLeft !==
            'call:reference:dttlf_Functord_cat' ||
        evidence.primaryMismatchRight !== 'application:section-category' ||
        evidence.terminalMismatchLeft !==
            'call:reference:dttlf_Functord_cat' ||
        evidence.terminalMismatchRight !== 'application:section-category' ||
        !evidence.activeSectionCategoryFacadeIsOpaque ||
        !evidence.activeSectionCategoryComparisonIsProofTimeOnly ||
        !evidence.activeSectionPullbackBodyUsesDisplayedFunctorCategories ||
        !evidence.declaredTypeUsesSectionCategoryFacades ||
        !evidence.completeFunctorParentFusionRequired ||
        evidence.underlyingCategoryRuntimeEqualityRequired ||
        evidence.declarationBodyOrTypeChangeRequired ||
        evidence.declarationSourceOrderChangeRequired ||
        evidence.genericComparisonChangeRequired ||
        evidence.genericRuntimeMatcherChangeRequired ||
        evidence.mathematicalRuleRequired ||
        evidence.proofRuleRequired ||
        evidence.temporaryObserverRetained
    ) {
        throw new CorePathindInternalized1dProposalV12Error(
            'PATHIND_INTERNALIZED_V12_AUTHORITY_DRIFT',
            'The reviewed-v11 section-category trace or authority drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const partition = implementation.stagedModulePartition;
    const fusion = proposal.dependencyClosure
        .pathoutPiTransportFunctorPresentationFusion;
    if (
        implementation.trustedDeclarations.length !== 4 ||
        implementation.runtimeRules.length !== 12 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 10 ||
        implementation.exactBoundary !== '4/12/0/10' ||
        implementation.mathematicalRuntimeProjectionCount !== 5 ||
        implementation.derivedRuntimeSupportRuleCount !== 7 ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        partition.baseRuntimeRuleIds.length !== 9 ||
        partition.prefixTransparentDefinitions.length !== 3 ||
        !sameData(
            partition.extensionRuntimeRuleIds,
            correctedExtensionRuntimeRuleIds
        ) ||
        partition.suffixTransparentDefinitions.length !== 4 ||
        !partition.declarationOrderPreserved ||
        partition.semanticCountDelta !== 1 ||
        !proposal.selectedPredecessor
            .v11TransportedMotiveReflexiveFibreFusionRetained ||
        !proposal.selectedPredecessor
            .v11TransportedMotiveReflexiveFibreFusionInsufficientAlone ||
        !proposal.selectedPredecessor
            .v12PathoutPiTransportFunctorPresentationFusionSelected ||
        fusion.ruleId !== pathoutPiTransportFunctorPresentationFusion.id ||
        !fusion.exactPathoutPiTransportParentSelected ||
        !fusion.sourceAndTargetCategoriesClosedTogether ||
        !fusion.prefixDeclaresMotiveTransportBeforeRuleCompilation ||
        !fusion.extensionRetainsBothFibreSupportRules ||
        !fusion.activeSectionFacadeComparisonOnly ||
        !fusion.activeSectionPullbackSignatureOnly ||
        fusion.underlyingCategoryRuntimeEqualitySelected ||
        !fusion.subjectCheckRequiredBeforeImplementationCheckpoint ||
        fusion.activeMathematicalRuleDelta !== 0 ||
        fusion.derivedSupportRuleDelta !== 1 ||
        fusion.proofRuleDelta !== 0 ||
        fusion.declarationBodyOrTypeChangeAuthorized ||
        fusion.declarationSourceOrderChangeAuthorized ||
        fusion.genericSectionCategoryRuleAuthorized ||
        fusion.genericComparisonChangeAuthorized ||
        fusion.genericRuntimeMatcherChangeAuthorized ||
        fusion.genericCheckerChangeAuthorized
    ) {
        throw new CorePathindInternalized1dProposalV12Error(
            'PATHIND_INTERNALIZED_V12_SCOPE_DRIFT',
            'The exact staged 4/12/0/10 boundary drifted'
        );
    }

    if (
        proposal.decision.question !== DECISION_QUESTION ||
        proposal.decision.status !== 'proposal-only' ||
        proposal.decision.implementationAuthorized ||
        !proposal.decision.separateImmutableReviewRequired ||
        proposal.profileSealing.packageOrBrowserExportAuthorized ||
        proposal.gitBoundary.pushMergePublishAuthorized ||
        proposal.gitBoundary.historyRewriteAuthorized ||
        proposal.gitBoundary.cleanupAuthorized ||
        proposal.nextDependencyState !==
            'pathind-internalized-1d-v12-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV12Error(
            'PATHIND_INTERNALIZED_V12_AUTHORIZATION_DRIFT',
            'Corrected proposal v12 became self-authorizing or widened'
        );
    }
    return proposal;
}
