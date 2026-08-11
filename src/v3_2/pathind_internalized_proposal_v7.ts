/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v7.
 *
 * V7 preserves v6 and adds one local action-level category-presentation
 * fusion required by pathout_motive_transport_arrow after the generic
 * comparison and declaration-budget prerequisites completed. It adds no
 * mathematical equation, category collapse, or proof-program integration.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6,
    validateCorePathindInternalized1dProposalV6
} from './pathind_internalized_proposal_v6';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-7' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-07/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-007 as proposed.';

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

const proposalV6 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6;

const motiveTransportActionCategoryPresentationFusion = {
    order: 8,
    id:
        'pathind.internalized.' +
        'motive-transport-action-category-presentation-fusion',
    authority: 'derived-action-level-category-presentation-fusion',
    authorityPositions: [
        'emdash2/emdash3_2.lp:3316-3317',
        'emdash2/emdash3_2.lp:5452-5457',
        'emdash2/emdash3_2.lp:19139-19178'
    ],
    sourceOwner: 'functor-object',
    policy: 'runtime-rewrite-derived-support',
    mathematicalRule: false,
    variables: ['K', 'L', 'F', 'E'],
    left:
        'fapp0(Functor_cat(K,Cat_cat),' +
        'Functor_cat(L,Cat_cat),F,E)',
    right: 'fapp0(Catd_cat(K),Catd_cat(L),F,E)'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV6.exactImplementation.runtimeRules
        .map(rule => cloneData(rule)),
    motiveTransportActionCategoryPresentationFusion
]);

const correctedStages = proposalV6.exactImplementation
    .implementationStages.map(stage =>
        stage.id === 'internalized-runtime-projections'
            ? {
                ...cloneData(stage),
                rules: correctedRuntimeRules.map(rule => rule.id)
            }
            : cloneData(stage)
    );

const rawProposal = {
    ...cloneData(proposalV6),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7_REVISION,
    status: 'corrected-proposal-v7-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV6.parent),
        supersededProposalRevision: proposalV6.revision,
        supersededProposalCheckpoint: '19eb941',
        supersededReviewCheckpoint: '2112543',
        supersededLedgerCheckpoint: null,
        priorCounterevidence:
            cloneData(proposalV6.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'reviewed-v6-cold-replay-after-generic-checkpoint-e560551',
            allEightLocalRuntimeRulesCompiled: true,
            firstTransparentDefinitionCompiled: true,
            compiledTransparentDefinition:
                'pathout_motive_transport_obj',
            failingPhase: 'transparent-library-declaration-one',
            failingDeclaration: 'pathout_motive_transport_arrow',
            failingAuthorityPosition:
                'emdash2/emdash3_2.lp:19159-19178',
            failingComparisonPath:
                'application:functor-object:argument:0',
            requestedComparisonStepLimit: 512,
            effectiveComparisonStepLimit: 512,
            comparisonStepLimitExceeded: false,
            comparisonStepsBeforeMismatch: 284,
            mismatchCode: 'TAG_MISMATCH',
            exactNormalizedLeft:
                'fapp0(Functor_cat(K,Cat_cat),' +
                'Functor_cat(L,Cat_cat),F,E)',
            exactNormalizedRight:
                'fapp0(Catd_cat(K),Catd_cat(L),F,E)',
            v6ClassifierPresentationFusionAlreadyCompiled: true,
            localActionCategoryPresentationFusionRequired: true,
            genericCategoryCollapseRequired: false,
            genericDeclarationProofIntegrationRequired: false,
            additionalActiveMathematicalRuleRequired: false,
            additionalDerivedSupportRuleRequired: true,
            proofRuleRequired: false,
            temporaryObserverRetained: false
        },
        genericComparisonPrerequisite: {
            ...cloneData(proposalV6.parent
                .genericComparisonPrerequisite),
            semanticCheckpoint: 'e560551',
            semanticCheckpointComplete: true
        },
        declarationBudgetPrerequisite: {
            row: 'CORE-LF-TRANSFER-DECLARATION-BUDGET-1',
            proposalCheckpoint: '9238104',
            reviewCheckpoint: 'a4d61a9',
            semanticCheckpoint: 'e560551',
            semanticCheckpointComplete: true,
            requestedLimitAppliedExactly: true,
            defaultLimitRetained: 256,
            publicFactorySignatureRetained: true,
            adaptiveOrUnboundedBudgetAuthorized: false
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-07',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-007',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV6.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/9/0/10',
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 4
    },
    selectedPredecessor: {
        ...cloneData(proposalV6.selectedPredecessor),
        localImplementationDeltaIsFourEightZeroTen: false,
        localImplementationDeltaIsFourNineZeroTen: true,
        v6MotiveTransportCategoryPresentationFusionRetained: true,
        v7MotiveTransportActionCategoryPresentationFusionSelected: true
    },
    dependencyClosure: {
        ...cloneData(proposalV6.dependencyClosure),
        motiveTransportActionCategoryPresentationFusion: {
            ruleId: motiveTransportActionCategoryPresentationFusion.id,
            authorityPositions:
                motiveTransportActionCategoryPresentationFusion
                    .authorityPositions,
            left: motiveTransportActionCategoryPresentationFusion.left,
            right: motiveTransportActionCategoryPresentationFusion.right,
            exactStablePostDeltaPairSelected: true,
            actionLevelPresentationOnly: true,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            activeMathematicalRuleDelta: 0,
            derivedSupportRuleDelta: 1,
            proofRuleDelta: 0,
            underlyingCategoryCollapseAuthorized: false,
            genericActionFusionAuthorized: false,
            genericDeclarationProofIntegrationAuthorized: false,
            genericRuntimeMatcherChangeAuthorized: false,
            genericCheckerChangeAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV6.validation),
        genericComparisonSemanticCheckpointRequired: 'e560551',
        declarationBudgetSemanticCheckpointRequired: 'e560551',
        reasonLongAggregateOmitted:
            'v7-is-immutable-boundary-data-and-e560551-is-carried-forward'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v7-implementation',
        ...cloneData(proposalV6.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v6-implementation'
        ),
        'a-generic-functor-object-category-presentation-runtime-rule',
        'a-PathInd-specific-comparison-budget'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v7-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV7 = typeof rawProposal;

export type CorePathindInternalized1dProposalV7ErrorCode =
    | 'PATHIND_INTERNALIZED_V7_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V7_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V7_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV7Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV7ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV7Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV7(
    proposal: CorePathindInternalized1dProposalV7 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7
): CorePathindInternalized1dProposalV7 {
    validateCorePathindInternalized1dProposalV6(proposalV6);
    const evidence = proposal.parent.counterevidence;
    const generic = proposal.parent.genericComparisonPrerequisite;
    const budget = proposal.parent.declarationBudgetPrerequisite;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-7' ||
        proposal.parent.supersededProposalRevision !== proposalV6.revision ||
        proposal.parent.supersededProposalCheckpoint !== '19eb941' ||
        proposal.parent.supersededReviewCheckpoint !== '2112543' ||
        proposal.parent.supersededLedgerCheckpoint !== null ||
        !evidence.allEightLocalRuntimeRulesCompiled ||
        !evidence.firstTransparentDefinitionCompiled ||
        evidence.compiledTransparentDefinition !==
            'pathout_motive_transport_obj' ||
        evidence.failingDeclaration !== 'pathout_motive_transport_arrow' ||
        evidence.failingComparisonPath !==
            'application:functor-object:argument:0' ||
        evidence.requestedComparisonStepLimit !== 512 ||
        evidence.effectiveComparisonStepLimit !== 512 ||
        evidence.comparisonStepLimitExceeded ||
        evidence.comparisonStepsBeforeMismatch !== 284 ||
        !evidence.v6ClassifierPresentationFusionAlreadyCompiled ||
        !evidence.localActionCategoryPresentationFusionRequired ||
        evidence.genericCategoryCollapseRequired ||
        evidence.genericDeclarationProofIntegrationRequired ||
        evidence.additionalActiveMathematicalRuleRequired ||
        !evidence.additionalDerivedSupportRuleRequired ||
        evidence.proofRuleRequired ||
        evidence.temporaryObserverRetained ||
        generic.semanticCheckpoint !== 'e560551' ||
        !generic.semanticCheckpointComplete ||
        budget.semanticCheckpoint !== 'e560551' ||
        !budget.semanticCheckpointComplete ||
        !budget.requestedLimitAppliedExactly ||
        budget.defaultLimitRetained !== 256 ||
        !budget.publicFactorySignatureRetained ||
        budget.adaptiveOrUnboundedBudgetAuthorized
    ) {
        throw new CorePathindInternalized1dProposalV7Error(
            'PATHIND_INTERNALIZED_V7_AUTHORITY_DRIFT',
            'The v6 boundary, action mismatch, or generic checkpoints drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const fusion = proposal.dependencyClosure
        .motiveTransportActionCategoryPresentationFusion;
    if (
        implementation.trustedDeclarations.length !== 4 ||
        implementation.runtimeRules.length !== 9 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 10 ||
        implementation.exactBoundary !== '4/9/0/10' ||
        implementation.mathematicalRuntimeProjectionCount !== 5 ||
        implementation.derivedRuntimeSupportRuleCount !== 4 ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[8].id !==
            motiveTransportActionCategoryPresentationFusion.id ||
        proposal.selectedPredecessor
            .localImplementationDeltaIsFourEightZeroTen ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFourNineZeroTen ||
        !proposal.selectedPredecessor
            .v6MotiveTransportCategoryPresentationFusionRetained ||
        !proposal.selectedPredecessor
            .v7MotiveTransportActionCategoryPresentationFusionSelected ||
        fusion.ruleId !==
            motiveTransportActionCategoryPresentationFusion.id ||
        !fusion.exactStablePostDeltaPairSelected ||
        !fusion.actionLevelPresentationOnly ||
        !fusion.subjectCheckRequiredBeforeImplementationCheckpoint ||
        fusion.activeMathematicalRuleDelta !== 0 ||
        fusion.derivedSupportRuleDelta !== 1 ||
        fusion.proofRuleDelta !== 0 ||
        fusion.underlyingCategoryCollapseAuthorized ||
        fusion.genericActionFusionAuthorized ||
        fusion.genericDeclarationProofIntegrationAuthorized ||
        fusion.genericRuntimeMatcherChangeAuthorized ||
        fusion.genericCheckerChangeAuthorized ||
        proposal.typedLibraryConsumers.length !== 2 ||
        proposal.selectedRuntimeObservations.length !== 10 ||
        proposal.negativeConsumers.length !== 10 ||
        proposal.boundedOracle.assertions.length !== 12
    ) {
        throw new CorePathindInternalized1dProposalV7Error(
            'PATHIND_INTERNALIZED_V7_SCOPE_DRIFT',
            'The exact 4/9/0/10 local action boundary drifted'
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
            'pathind-internalized-1d-v7-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV7Error(
            'PATHIND_INTERNALIZED_V7_AUTHORIZATION_DRIFT',
            'Corrected proposal v7 became self-authorizing or widened'
        );
    }
    return proposal;
}
