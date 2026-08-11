/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v11.
 *
 * V11 retains the reviewed v10 staging and adds one complete-parent support
 * rule for the already-active pullback-fibre and PathOut reflexive-action
 * computation exposed by the first suffix declaration.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10,
    validateCorePathindInternalized1dProposalV10
} from './pathind_internalized_proposal_v10';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-11' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-11/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-011 as proposed.';

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

const proposalV10 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10;

const transportedMotiveReflexiveFibreFusion = {
    order: 10,
    id:
        'pathind.internalized.' +
        'transported-motive-reflexive-fibre-presentation-fusion',
    authority:
        'derived-complete-parent-pullback-fibre-and-pathout-action-fusion',
    authorityPositions: [
        'emdash2/emdash3_2.lp:12034-12035',
        'emdash2/emdash3_2.lp:18981-18992',
        'emdash2/emdash3_2.lp:19046-19058',
        'emdash2/emdash3_2.lp:19132-19154',
        'emdash2/emdash3_2.lp:19309-19318'
    ],
    sourceOwner: 'functor-object',
    policy: 'runtime-rewrite-derived-support',
    mathematicalRule: false,
    variables: ['Z', 'x', 'y', 'p', 'E'],
    left:
        'Fibre_cat(pathout_motive_transport_obj(Z,x,y,p,E),' +
        'pathout_refl_obj(Z,y))',
    right: 'Fibre_cat(E,pathout_obj(Z,x,y,p))'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV10.exactImplementation.runtimeRules.map(rule =>
        cloneData(rule)
    ),
    transportedMotiveReflexiveFibreFusion
]);

const correctedExtensionRuntimeRuleIds = Object.freeze([
    ...proposalV10.exactImplementation.stagedModulePartition
        .extensionRuntimeRuleIds,
    transportedMotiveReflexiveFibreFusion.id
]);

const correctedStages = Object.freeze(
    proposalV10.exactImplementation.implementationStages.map(stage => {
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
    ...cloneData(proposalV10),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11_REVISION,
    status: 'corrected-proposal-v11-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV10.parent),
        supersededProposalRevision: proposalV10.revision,
        supersededProposalCheckpoint: '270da40',
        supersededReviewCheckpoint: '302c4a9',
        supersededLedgerCheckpoint: null,
        priorCounterevidence:
            cloneData(proposalV10.parent.counterevidence),
        counterevidence: {
            measuredDuring: 'reviewed-v10-cold-semantic-replay-with-trace',
            allNineBaseRuntimeRulesSubjectChecked: true,
            allThreePrefixTransparentDefinitionsCompiled: true,
            compiledPrefixTransparentDefinitions: [
                'pathout_motive_transport_obj',
                'pathout_motive_transport_arrow',
                'PathIndSrc_catd'
            ],
            directSourceFibreExtensionRuleSubjectChecked: true,
            extensionLocalClauseOrderRestartRequired: true,
            extensionLocalClauseOrderRestartSemanticDelta: false,
            directSourceFibreRuleFiredOnSource: true,
            directSourceFibreRuleFiredOnTarget: true,
            failingDeclaration: 'PathIndSrc_transport_func',
            failingAuthorityPosition:
                'emdash2/emdash3_2.lp:19309-19318',
            requestedComparisonStepLimit: 512,
            effectiveComparisonStepLimit: 512,
            comparisonStepLimitExceeded: false,
            primaryComparisonStepsBeforeMismatch: 336,
            primaryMismatchCode: 'BOUND_VARIABLE_MISMATCH',
            primaryMismatchPath: [
                '$',
                'application:decode:argument:0',
                'application:object-classifier:argument:0',
                'call:argument:1',
                'application:functor-object:argument:0',
                'call:argument:1',
                'call:argument:3'
            ],
            primaryMismatchLeft: 'bound:3',
            primaryMismatchRight: 'bound:2',
            boundVariableMeaning: 'fixed-source-x-versus-transport-target-y',
            recursiveComparisonSteps: [344, 230, 32, 14],
            recursiveMismatchCodes: [
                'BOUND_VARIABLE_MISMATCH',
                'BOUND_VARIABLE_MISMATCH',
                'TAG_MISMATCH',
                'TAG_MISMATCH'
            ],
            finalStructuralDiagnostic:
                'PathOut_cat-free-name-versus-Sigma_cat-free-name',
            pullbackFibreRuleActive: true,
            pathoutTransportOnReflexiveObjectAlreadyQualified: true,
            completeParentTargetFibreNotExposedBeforeBaseChild: true,
            targetTransportCompleteParentFusionRequired: true,
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
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-11',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-011',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV10.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/11/0/10',
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 6,
        stagedModulePartition: {
            ...cloneData(
                proposalV10.exactImplementation.stagedModulePartition
            ),
            extensionRuntimeRuleIds: correctedExtensionRuntimeRuleIds,
            semanticCountDelta: 1
        }
    },
    selectedPredecessor: {
        ...cloneData(proposalV10.selectedPredecessor),
        v10StagedDirectSourceFibreFusionRetained: true,
        v10StagedDirectSourceFibreFusionInsufficientAlone: true,
        v11TransportedMotiveReflexiveFibreFusionSelected: true
    },
    dependencyClosure: {
        ...cloneData(proposalV10.dependencyClosure),
        transportedMotiveReflexiveFibreFusion: {
            ruleId: transportedMotiveReflexiveFibreFusion.id,
            authorityPositions:
                transportedMotiveReflexiveFibreFusion.authorityPositions,
            left: transportedMotiveReflexiveFibreFusion.left,
            right: transportedMotiveReflexiveFibreFusion.right,
            exactCompleteParentPairSelected: true,
            prefixDeclaresMotiveTransportBeforeRuleCompilation: true,
            extensionContainsDirectAndTargetFibreSupportRules: true,
            activePullbackFibreComputationOnly: true,
            activePathoutReflexiveActionOnly: true,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            activeMathematicalRuleDelta: 0,
            derivedSupportRuleDelta: 1,
            proofRuleDelta: 0,
            declarationBodyOrTypeChangeAuthorized: false,
            declarationSourceOrderChangeAuthorized: false,
            genericPullbackRuleChangeAuthorized: false,
            genericComparisonChangeAuthorized: false,
            genericRuntimeMatcherChangeAuthorized: false,
            genericCheckerChangeAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV10.validation),
        v10ProposalCheckpointRequired: '270da40',
        v10ReviewCheckpointRequired: '302c4a9',
        reasonLongAggregateOmitted:
            'v11-is-immutable-boundary-data-and-e560551-is-carried-forward'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v11-implementation',
        ...cloneData(proposalV10.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v10-implementation' &&
            entry !== 'adding-an-eleventh-runtime-rule'
        ),
        'changing-any-selected-declaration-body-or-type',
        'changing-the-order-of-the-seven-derived-declarations',
        'adding-a-twelfth-runtime-rule'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v11-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV11 = typeof rawProposal;

export type CorePathindInternalized1dProposalV11ErrorCode =
    | 'PATHIND_INTERNALIZED_V11_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V11_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V11_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV11Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV11ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV11Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV11(
    proposal: CorePathindInternalized1dProposalV11 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11
): CorePathindInternalized1dProposalV11 {
    validateCorePathindInternalized1dProposalV10(proposalV10);
    const evidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-11' ||
        proposal.parent.supersededProposalRevision !== proposalV10.revision ||
        proposal.parent.supersededProposalCheckpoint !== '270da40' ||
        proposal.parent.supersededReviewCheckpoint !== '302c4a9' ||
        proposal.parent.supersededLedgerCheckpoint !== null ||
        !evidence.allNineBaseRuntimeRulesSubjectChecked ||
        !evidence.allThreePrefixTransparentDefinitionsCompiled ||
        evidence.compiledPrefixTransparentDefinitions.length !== 3 ||
        !evidence.directSourceFibreExtensionRuleSubjectChecked ||
        !evidence.extensionLocalClauseOrderRestartRequired ||
        evidence.extensionLocalClauseOrderRestartSemanticDelta ||
        !evidence.directSourceFibreRuleFiredOnSource ||
        !evidence.directSourceFibreRuleFiredOnTarget ||
        evidence.failingDeclaration !== 'PathIndSrc_transport_func' ||
        evidence.requestedComparisonStepLimit !== 512 ||
        evidence.effectiveComparisonStepLimit !== 512 ||
        evidence.comparisonStepLimitExceeded ||
        evidence.primaryComparisonStepsBeforeMismatch !== 336 ||
        evidence.primaryMismatchCode !== 'BOUND_VARIABLE_MISMATCH' ||
        evidence.primaryMismatchLeft !== 'bound:3' ||
        evidence.primaryMismatchRight !== 'bound:2' ||
        evidence.boundVariableMeaning !==
            'fixed-source-x-versus-transport-target-y' ||
        !sameData(evidence.recursiveComparisonSteps, [344, 230, 32, 14]) ||
        !sameData(evidence.recursiveMismatchCodes, [
            'BOUND_VARIABLE_MISMATCH',
            'BOUND_VARIABLE_MISMATCH',
            'TAG_MISMATCH',
            'TAG_MISMATCH'
        ]) ||
        !evidence.pullbackFibreRuleActive ||
        !evidence.pathoutTransportOnReflexiveObjectAlreadyQualified ||
        !evidence.completeParentTargetFibreNotExposedBeforeBaseChild ||
        !evidence.targetTransportCompleteParentFusionRequired ||
        evidence.declarationBodyOrTypeChangeRequired ||
        evidence.declarationSourceOrderChangeRequired ||
        evidence.genericComparisonChangeRequired ||
        evidence.genericRuntimeMatcherChangeRequired ||
        evidence.mathematicalRuleRequired ||
        evidence.proofRuleRequired ||
        evidence.temporaryObserverRetained
    ) {
        throw new CorePathindInternalized1dProposalV11Error(
            'PATHIND_INTERNALIZED_V11_AUTHORITY_DRIFT',
            'The reviewed-v10 target-fibre trace or authority drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const partition = implementation.stagedModulePartition;
    const fusion = proposal.dependencyClosure
        .transportedMotiveReflexiveFibreFusion;
    if (
        implementation.trustedDeclarations.length !== 4 ||
        implementation.runtimeRules.length !== 11 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 10 ||
        implementation.exactBoundary !== '4/11/0/10' ||
        implementation.mathematicalRuntimeProjectionCount !== 5 ||
        implementation.derivedRuntimeSupportRuleCount !== 6 ||
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
            .v10StagedDirectSourceFibreFusionRetained ||
        !proposal.selectedPredecessor
            .v10StagedDirectSourceFibreFusionInsufficientAlone ||
        !proposal.selectedPredecessor
            .v11TransportedMotiveReflexiveFibreFusionSelected ||
        fusion.ruleId !== transportedMotiveReflexiveFibreFusion.id ||
        !fusion.exactCompleteParentPairSelected ||
        !fusion.prefixDeclaresMotiveTransportBeforeRuleCompilation ||
        !fusion.extensionContainsDirectAndTargetFibreSupportRules ||
        !fusion.activePullbackFibreComputationOnly ||
        !fusion.activePathoutReflexiveActionOnly ||
        !fusion.subjectCheckRequiredBeforeImplementationCheckpoint ||
        fusion.activeMathematicalRuleDelta !== 0 ||
        fusion.derivedSupportRuleDelta !== 1 ||
        fusion.proofRuleDelta !== 0 ||
        fusion.declarationBodyOrTypeChangeAuthorized ||
        fusion.declarationSourceOrderChangeAuthorized ||
        fusion.genericPullbackRuleChangeAuthorized ||
        fusion.genericComparisonChangeAuthorized ||
        fusion.genericRuntimeMatcherChangeAuthorized ||
        fusion.genericCheckerChangeAuthorized
    ) {
        throw new CorePathindInternalized1dProposalV11Error(
            'PATHIND_INTERNALIZED_V11_SCOPE_DRIFT',
            'The exact staged 4/11/0/10 boundary drifted'
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
            'pathind-internalized-1d-v11-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV11Error(
            'PATHIND_INTERNALIZED_V11_AUTHORIZATION_DRIFT',
            'Corrected proposal v11 became self-authorizing or widened'
        );
    }
    return proposal;
}
