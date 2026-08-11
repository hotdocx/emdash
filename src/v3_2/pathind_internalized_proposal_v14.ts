/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v14.
 *
 * V14 retains reviewed v13 and adds one staged complete-parent rule for the
 * already-declared total target family at a Sigma pair. This exposes the
 * section-category presentation needed by the seventh and final derived
 * declaration without changing PathIndTgt, Pi, or generic Sigma computation.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13,
    validateCorePathindInternalized1dProposalV13
} from './pathind_internalized_proposal_v13';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-14' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-14/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-014 as proposed.';

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

const proposalV13 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13;

const pathInductionTargetFibreStagedParentFusion = {
    order: 12,
    id:
        'pathind.internalized.' +
        'path-ind-target-fibre-at-sigma-pair-presentation-fusion',
    authority: 'derived-staged-complete-parent-target-fibre-fusion',
    authorityPositions: [
        'emdash2/emdash3_2.lp:12554-12561',
        'emdash2/emdash3_2.lp:13297-13314',
        'emdash2/emdash3_2.lp:19018-19041',
        'emdash2/emdash3_2.lp:19751-19759'
    ],
    sourceOwner: 'functor-object',
    policy: 'runtime-rewrite-derived-support',
    mathematicalRule: false,
    variables: ['Z', 'x', 'E'],
    left: 'Fibre_cat(PathIndTgt_catd(Z),Struct_sigma(x,E))',
    right: 'Pi_cat(PathOut_cat(Z,x),E)'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV13.exactImplementation.runtimeRules.map(rule =>
        cloneData(rule)
    ),
    pathInductionTargetFibreStagedParentFusion
]);

const correctedExtensionRuntimeRuleIds = Object.freeze([
    ...proposalV13.exactImplementation.stagedModulePartition
        .extensionRuntimeRuleIds,
    pathInductionTargetFibreStagedParentFusion.id
]);

const correctedStages = Object.freeze(
    proposalV13.exactImplementation.implementationStages.map(stage => {
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
    ...cloneData(proposalV13),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14_REVISION,
    status: 'corrected-proposal-v14-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV13.parent),
        supersededProposalRevision: proposalV13.revision,
        supersededProposalCheckpoint: 'd77f0d7',
        supersededReviewCheckpoint: 'a8aff88',
        supersededLedgerCheckpoint: null,
        priorCounterevidence:
            cloneData(proposalV13.parent.counterevidence),
        counterevidence: {
            measuredDuring: 'reviewed-v13-cold-semantic-replay-with-trace',
            allTwelveRuntimeRulesSubjectChecked: true,
            pathoutPiTransportPostDeltaFusionSubjectChecked: true,
            pathoutPiTransportCompiled: true,
            compiledDerivedTransparentDefinitionCount: 6,
            selectedDerivedTransparentDefinitionCount: 7,
            failingDeclaration: 'PathIndTgt_transport_func',
            failingDeclarationOrder: 6,
            failingAuthorityPosition:
                'emdash2/emdash3_2.lp:19751-19759',
            requestedComparisonStepLimit: 512,
            effectiveComparisonStepLimit: 512,
            comparisonStepLimitExceeded: false,
            comparisonSteps: [464, 472, 96],
            comparisonMismatchCodes: [
                'OWNER_MISMATCH',
                'OWNER_MISMATCH',
                'OWNER_MISMATCH'
            ],
            primaryMismatchPath: [
                '$',
                'application:decode:argument:0',
                'application:object-classifier:argument:0',
                'call:argument:0'
            ],
            primaryMismatchLeft: 'application:section-category',
            primaryMismatchRight: 'application:functor-object',
            terminalMismatchLeft: 'application:section-category',
            terminalMismatchRight: 'application:functor-object',
            pathInductionTargetFamilyDeclaredInPrelude: true,
            pathoutPiBodyHasQualifiedSectionCategoryType: true,
            totalTargetFibreRetainsFunctorObjectPresentation: true,
            stagedDirectTargetFibreParentRequired: true,
            genericSigmaFibreRuleRequired: false,
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
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-14',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-014',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV13.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/13/0/10',
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 8,
        stagedModulePartition: {
            ...cloneData(
                proposalV13.exactImplementation.stagedModulePartition
            ),
            extensionRuntimeRuleIds: correctedExtensionRuntimeRuleIds,
            semanticCountDelta: 1
        }
    },
    selectedPredecessor: {
        ...cloneData(proposalV13.selectedPredecessor),
        v13PostDeltaFusionRetained: true,
        v13PostDeltaFusionClosesPathoutPiTransport: true,
        v13PostDeltaFusionInsufficientForTotalTargetAlias: true,
        v14PathInductionTargetFibreStagedParentFusionSelected: true
    },
    dependencyClosure: {
        ...cloneData(proposalV13.dependencyClosure),
        pathInductionTargetFibreStagedParentFusion: {
            ruleId: pathInductionTargetFibreStagedParentFusion.id,
            authorityPositions:
                pathInductionTargetFibreStagedParentFusion
                    .authorityPositions,
            left: pathInductionTargetFibreStagedParentFusion.left,
            right: pathInductionTargetFibreStagedParentFusion.right,
            exactCompleteParentPairSelected: true,
            pathIndTgtDeclaredByPreludeBeforeRuleCompilation: true,
            prefixStillCompiledBeforeExtension: true,
            extensionRetainsSourceAndTransportSupportRules: true,
            sourceAndTargetFinalAliasFibresCoveredByOneRule: true,
            targetFibrePresentationOnly: true,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            activeMathematicalRuleDelta: 0,
            derivedSupportRuleDelta: 1,
            proofRuleDelta: 0,
            declarationBodyOrTypeChangeAuthorized: false,
            declarationSourceOrderChangeAuthorized: false,
            underlyingCategoryEqualityAuthorized: false,
            genericSigmaFibreRuleAuthorized: false,
            genericComparisonChangeAuthorized: false,
            genericRuntimeMatcherChangeAuthorized: false,
            genericCheckerChangeAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV13.validation),
        v13ProposalCheckpointRequired: 'd77f0d7',
        v13ReviewCheckpointRequired: 'a8aff88',
        reasonLongAggregateOmitted:
            'v14-is-immutable-boundary-data-and-e560551-is-carried-forward'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v14-implementation',
        ...cloneData(proposalV13.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v13-implementation' &&
            entry !== 'adding-a-thirteenth-runtime-rule'
        ),
        'changing-any-selected-declaration-body-or-type',
        'changing-the-order-of-the-seven-derived-declarations',
        'adding-a-fourteenth-runtime-rule',
        'adding-a-generic-Sigma-fibre-runtime-rule'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v14-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV14 = typeof rawProposal;

export type CorePathindInternalized1dProposalV14ErrorCode =
    | 'PATHIND_INTERNALIZED_V14_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V14_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V14_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV14Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV14ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV14Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV14(
    proposal: CorePathindInternalized1dProposalV14 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14
): CorePathindInternalized1dProposalV14 {
    validateCorePathindInternalized1dProposalV13(proposalV13);
    const evidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-14' ||
        proposal.parent.supersededProposalRevision !== proposalV13.revision ||
        proposal.parent.supersededProposalCheckpoint !== 'd77f0d7' ||
        proposal.parent.supersededReviewCheckpoint !== 'a8aff88' ||
        proposal.parent.supersededLedgerCheckpoint !== null ||
        !evidence.allTwelveRuntimeRulesSubjectChecked ||
        !evidence.pathoutPiTransportPostDeltaFusionSubjectChecked ||
        !evidence.pathoutPiTransportCompiled ||
        evidence.compiledDerivedTransparentDefinitionCount !== 6 ||
        evidence.selectedDerivedTransparentDefinitionCount !== 7 ||
        evidence.failingDeclaration !== 'PathIndTgt_transport_func' ||
        evidence.failingDeclarationOrder !== 6 ||
        evidence.requestedComparisonStepLimit !== 512 ||
        evidence.effectiveComparisonStepLimit !== 512 ||
        evidence.comparisonStepLimitExceeded ||
        !sameData(evidence.comparisonSteps, [464, 472, 96]) ||
        !sameData(evidence.comparisonMismatchCodes, [
            'OWNER_MISMATCH',
            'OWNER_MISMATCH',
            'OWNER_MISMATCH'
        ]) ||
        evidence.primaryMismatchLeft !== 'application:section-category' ||
        evidence.primaryMismatchRight !== 'application:functor-object' ||
        evidence.terminalMismatchLeft !== 'application:section-category' ||
        evidence.terminalMismatchRight !== 'application:functor-object' ||
        !evidence.pathInductionTargetFamilyDeclaredInPrelude ||
        !evidence.pathoutPiBodyHasQualifiedSectionCategoryType ||
        !evidence.totalTargetFibreRetainsFunctorObjectPresentation ||
        !evidence.stagedDirectTargetFibreParentRequired ||
        evidence.genericSigmaFibreRuleRequired ||
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
        throw new CorePathindInternalized1dProposalV14Error(
            'PATHIND_INTERNALIZED_V14_AUTHORITY_DRIFT',
            'The reviewed-v13 target-fibre trace or authority drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const partition = implementation.stagedModulePartition;
    const fusion = proposal.dependencyClosure
        .pathInductionTargetFibreStagedParentFusion;
    if (
        implementation.trustedDeclarations.length !== 4 ||
        implementation.runtimeRules.length !== 13 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 10 ||
        implementation.exactBoundary !== '4/13/0/10' ||
        implementation.mathematicalRuntimeProjectionCount !== 5 ||
        implementation.derivedRuntimeSupportRuleCount !== 8 ||
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
        !proposal.selectedPredecessor.v13PostDeltaFusionRetained ||
        !proposal.selectedPredecessor
            .v13PostDeltaFusionClosesPathoutPiTransport ||
        !proposal.selectedPredecessor
            .v13PostDeltaFusionInsufficientForTotalTargetAlias ||
        !proposal.selectedPredecessor
            .v14PathInductionTargetFibreStagedParentFusionSelected ||
        fusion.ruleId !== pathInductionTargetFibreStagedParentFusion.id ||
        !fusion.exactCompleteParentPairSelected ||
        !fusion.pathIndTgtDeclaredByPreludeBeforeRuleCompilation ||
        !fusion.prefixStillCompiledBeforeExtension ||
        !fusion.extensionRetainsSourceAndTransportSupportRules ||
        !fusion.sourceAndTargetFinalAliasFibresCoveredByOneRule ||
        !fusion.targetFibrePresentationOnly ||
        !fusion.subjectCheckRequiredBeforeImplementationCheckpoint ||
        fusion.activeMathematicalRuleDelta !== 0 ||
        fusion.derivedSupportRuleDelta !== 1 ||
        fusion.proofRuleDelta !== 0 ||
        fusion.declarationBodyOrTypeChangeAuthorized ||
        fusion.declarationSourceOrderChangeAuthorized ||
        fusion.underlyingCategoryEqualityAuthorized ||
        fusion.genericSigmaFibreRuleAuthorized ||
        fusion.genericComparisonChangeAuthorized ||
        fusion.genericRuntimeMatcherChangeAuthorized ||
        fusion.genericCheckerChangeAuthorized
    ) {
        throw new CorePathindInternalized1dProposalV14Error(
            'PATHIND_INTERNALIZED_V14_SCOPE_DRIFT',
            'The exact staged 4/13/0/10 target-fibre boundary drifted'
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
            'pathind-internalized-1d-v14-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV14Error(
            'PATHIND_INTERNALIZED_V14_AUTHORIZATION_DRIFT',
            'Corrected proposal v14 became self-authorizing or widened'
        );
    }
    return proposal;
}
