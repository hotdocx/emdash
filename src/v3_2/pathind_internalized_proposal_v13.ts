/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v13.
 *
 * V13 preserves the reviewed v12 boundary but replaces its unreachable
 * pre-delta Functor-classifier fusion with the exact stable decoded object
 * type reached after the dependency runtime's active Functor delta. It adds
 * no rule and retains the absence of a category-level Pi/Functord rewrite.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12,
    validateCorePathindInternalized1dProposalV12
} from './pathind_internalized_proposal_v12';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-13' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-13/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-013 as proposed.';

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

const proposalV12 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12;

const v12FusionId =
    'pathind.internalized.' +
    'pathout-pi-transport-functor-presentation-fusion';

const pathoutPiTransportPostDeltaPresentationFusion = {
    order: 11,
    id:
        'pathind.internalized.' +
        'pathout-pi-transport-post-delta-presentation-fusion',
    authority:
        'derived-complete-parent-post-delta-section-pullback-fusion',
    authorityPositions: [
        'emdash2/emdash3_2.lp:3316-3317',
        'emdash2/emdash3_2.lp:12554-12561',
        'emdash2/emdash3_2.lp:16502-16506',
        'emdash2/emdash3_2.lp:19139-19153',
        'emdash2/emdash3_2.lp:19734-19744'
    ],
    sourceOwner: 'decode',
    policy: 'runtime-rewrite-derived-post-delta-type-fusion',
    mathematicalRule: false,
    variables: ['Z', 'x', 'y', 'p', 'E'],
    left:
        'τ(Obj(Functor_cat(' +
        'Functord_cat(PathOut_Z(x),Const(PathOut_Z(x),Terminal),E),' +
        'Functord_cat(PathOut_Z(y),Const(PathOut_Z(y),Terminal),' +
        'Pullback_catd(E,PathOut_transport(p))))))',
    right:
        'τ(Obj(Functor_cat(Pi_cat(PathOut_Z(x),E),' +
        'Pi_cat(PathOut_Z(y),' +
        'pathout_motive_transport_obj(Z,x,y,p,E)))))'
} as const;

const correctedRuntimeRules = Object.freeze(
    proposalV12.exactImplementation.runtimeRules.map(rule =>
        rule.id === v12FusionId
            ? pathoutPiTransportPostDeltaPresentationFusion
            : cloneData(rule)
    )
);

const correctedExtensionRuntimeRuleIds = Object.freeze(
    proposalV12.exactImplementation.stagedModulePartition
        .extensionRuntimeRuleIds.map(ruleId =>
            ruleId === v12FusionId
                ? pathoutPiTransportPostDeltaPresentationFusion.id
                : ruleId
        )
);

const correctedStages = Object.freeze(
    proposalV12.exactImplementation.implementationStages.map(stage => {
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
    ...cloneData(proposalV12),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13_REVISION,
    status: 'corrected-proposal-v13-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV12.parent),
        supersededProposalRevision: proposalV12.revision,
        supersededProposalCheckpoint: '39abb02',
        supersededReviewCheckpoint: '8833f8f',
        supersededLedgerCheckpoint: null,
        priorCounterevidence:
            cloneData(proposalV12.parent.counterevidence),
        counterevidence: {
            measuredDuring: 'reviewed-v12-cold-semantic-replay',
            compiledRuntimeRuleCount: 12,
            allSelectedRuntimeRulesSubjectChecked: true,
            compiledDerivedTransparentDefinitionCount: 5,
            selectedDerivedTransparentDefinitionCount: 7,
            failingDeclaration: 'pathout_pi_transport_func',
            failingDeclarationOrder: 5,
            failingPhase: 'transparent-body-type-conversion',
            predecessorRuleAppliedFirst:
                'categorical.mixed-action.functor-classifier-definition',
            predecessorRuleAuthorityPositions: [
                'emdash2/emdash3_2.lp:3316-3317'
            ],
            v12PreDeltaFusionSubjectChecked: true,
            v12PreDeltaFusionMatched: false,
            v12PreDeltaFusionShadowedByEarlierFragment: true,
            exactStableLeft:
                'τ(Obj(Functor_cat(' +
                'Functord_cat(PathOut_Z(x),Const(PathOut_Z(x),Terminal),E),' +
                'Functord_cat(PathOut_Z(y),Const(PathOut_Z(y),Terminal),' +
                'Pullback_catd(E,PathOut_transport(p))))))',
            exactStableRight:
                'τ(Obj(Functor_cat(Pi_cat(PathOut_Z(x),E),' +
                'Pi_cat(PathOut_Z(y),' +
                'pathout_motive_transport_obj(Z,x,y,p,E)))))',
            replacementRuleRequired: true,
            additionalRuntimeRuleRequired: false,
            underlyingCategoryRuntimeEqualityRequired: false,
            declarationBodyOrTypeChangeRequired: false,
            declarationSourceOrderChangeRequired: false,
            genericComparisonChangeRequired: false,
            genericRuntimeMatcherChangeRequired: false,
            mathematicalRuleRequired: false,
            proofRuleRequired: false,
            temporaryObserverRetained: false,
            genericCheckerDiffEmpty: true
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-13',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-013',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV12.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/12/0/10',
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 7,
        stagedModulePartition: {
            ...cloneData(
                proposalV12.exactImplementation.stagedModulePartition
            ),
            extensionRuntimeRuleIds: correctedExtensionRuntimeRuleIds,
            semanticCountDelta: 0
        }
    },
    selectedPredecessor: {
        ...cloneData(proposalV12.selectedPredecessor),
        v12PathoutPiTransportFunctorPresentationFusionSelected: false,
        v12PreDeltaFusionRetained: false,
        v13PostDeltaFusionSelected: true
    },
    dependencyClosure: {
        ...cloneData(proposalV12.dependencyClosure),
        pathoutPiTransportFunctorPresentationFusion: {
            ruleId: pathoutPiTransportPostDeltaPresentationFusion.id,
            authorityPositions:
                pathoutPiTransportPostDeltaPresentationFusion
                    .authorityPositions,
            left: pathoutPiTransportPostDeltaPresentationFusion.left,
            right: pathoutPiTransportPostDeltaPresentationFusion.right,
            replacesUnreachableV12PreDeltaFusion: true,
            wrapsStablePresentationUnderDecodedObjectClassifier: true,
            exactPathoutPiTransportParentSelected: true,
            sourceAndTargetCategoriesClosedTogether: true,
            prefixDeclaresMotiveTransportBeforeRuleCompilation: true,
            extensionRetainsBothFibreSupportRules: true,
            activeFunctorClassifierDeltaOnly: true,
            activeSectionFacadeComparisonOnly: true,
            activeSectionPullbackSignatureOnly: true,
            underlyingCategoryRuntimeEqualitySelected: false,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            activeMathematicalRuleDelta: 0,
            derivedSupportRuleDelta: 0,
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
        ...cloneData(proposalV12.validation),
        v12ProposalCheckpointRequired: '39abb02',
        v12ReviewCheckpointRequired: '8833f8f',
        reasonLongAggregateOmitted:
            'v13-is-one-for-one-immutable-boundary-data-and-' +
            'e560551-is-carried-forward'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v13-implementation',
        ...cloneData(proposalV12.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v12-implementation'
        ),
        'retaining-the-unreachable-v12-pre-delta-fusion',
        'adding-a-thirteenth-runtime-rule',
        'adding-a-generic-Pi-cat-to-Functord-cat-runtime-equality'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v13-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV13 = typeof rawProposal;

export type CorePathindInternalized1dProposalV13ErrorCode =
    | 'PATHIND_INTERNALIZED_V13_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V13_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V13_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV13Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV13ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV13Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV13(
    proposal: CorePathindInternalized1dProposalV13 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13
): CorePathindInternalized1dProposalV13 {
    validateCorePathindInternalized1dProposalV12(proposalV12);
    const evidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-13' ||
        proposal.parent.supersededProposalRevision !== proposalV12.revision ||
        proposal.parent.supersededProposalCheckpoint !== '39abb02' ||
        proposal.parent.supersededReviewCheckpoint !== '8833f8f' ||
        proposal.parent.supersededLedgerCheckpoint !== null ||
        evidence.compiledRuntimeRuleCount !== 12 ||
        !evidence.allSelectedRuntimeRulesSubjectChecked ||
        evidence.compiledDerivedTransparentDefinitionCount !== 5 ||
        evidence.selectedDerivedTransparentDefinitionCount !== 7 ||
        evidence.failingDeclaration !== 'pathout_pi_transport_func' ||
        evidence.failingDeclarationOrder !== 5 ||
        evidence.predecessorRuleAppliedFirst !==
            'categorical.mixed-action.functor-classifier-definition' ||
        !evidence.v12PreDeltaFusionSubjectChecked ||
        evidence.v12PreDeltaFusionMatched ||
        !evidence.v12PreDeltaFusionShadowedByEarlierFragment ||
        !evidence.replacementRuleRequired ||
        evidence.additionalRuntimeRuleRequired ||
        evidence.underlyingCategoryRuntimeEqualityRequired ||
        evidence.declarationBodyOrTypeChangeRequired ||
        evidence.declarationSourceOrderChangeRequired ||
        evidence.genericComparisonChangeRequired ||
        evidence.genericRuntimeMatcherChangeRequired ||
        evidence.mathematicalRuleRequired ||
        evidence.proofRuleRequired ||
        evidence.temporaryObserverRetained ||
        !evidence.genericCheckerDiffEmpty
    ) {
        throw new CorePathindInternalized1dProposalV13Error(
            'PATHIND_INTERNALIZED_V13_AUTHORITY_DRIFT',
            'The reviewed-v12 post-delta evidence or authority drifted'
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
        partition.semanticCountDelta !== 0 ||
        proposal.selectedPredecessor
            .v12PathoutPiTransportFunctorPresentationFusionSelected ||
        proposal.selectedPredecessor.v12PreDeltaFusionRetained ||
        !proposal.selectedPredecessor.v13PostDeltaFusionSelected ||
        fusion.ruleId !== pathoutPiTransportPostDeltaPresentationFusion.id ||
        !fusion.replacesUnreachableV12PreDeltaFusion ||
        !fusion.wrapsStablePresentationUnderDecodedObjectClassifier ||
        !fusion.exactPathoutPiTransportParentSelected ||
        !fusion.sourceAndTargetCategoriesClosedTogether ||
        !fusion.prefixDeclaresMotiveTransportBeforeRuleCompilation ||
        !fusion.extensionRetainsBothFibreSupportRules ||
        !fusion.activeFunctorClassifierDeltaOnly ||
        !fusion.activeSectionFacadeComparisonOnly ||
        !fusion.activeSectionPullbackSignatureOnly ||
        fusion.underlyingCategoryRuntimeEqualitySelected ||
        !fusion.subjectCheckRequiredBeforeImplementationCheckpoint ||
        fusion.activeMathematicalRuleDelta !== 0 ||
        fusion.derivedSupportRuleDelta !== 0 ||
        fusion.proofRuleDelta !== 0 ||
        fusion.declarationBodyOrTypeChangeAuthorized ||
        fusion.declarationSourceOrderChangeAuthorized ||
        fusion.genericSectionCategoryRuleAuthorized ||
        fusion.genericComparisonChangeAuthorized ||
        fusion.genericRuntimeMatcherChangeAuthorized ||
        fusion.genericCheckerChangeAuthorized
    ) {
        throw new CorePathindInternalized1dProposalV13Error(
            'PATHIND_INTERNALIZED_V13_SCOPE_DRIFT',
            'The exact one-for-one staged 4/12/0/10 boundary drifted'
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
            'pathind-internalized-1d-v13-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV13Error(
            'PATHIND_INTERNALIZED_V13_AUTHORIZATION_DRIFT',
            'Corrected proposal v13 became self-authorizing or widened'
        );
    }
    return proposal;
}
