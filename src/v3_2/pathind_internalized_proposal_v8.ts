/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v8.
 *
 * V8 preserves v7 and adds one complete-parent source-fibre presentation
 * fusion required by PathIndSrc_transport_func. The rule composes the active
 * Sigma-telescope fibre projection with reflexive-evaluation projection; it
 * does not identify PathOut_cat with the total motive category.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7,
    validateCorePathindInternalized1dProposalV7
} from './pathind_internalized_proposal_v7';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-8' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-08/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-008 as proposed.';

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

const proposalV7 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7;

const pathInductionSourceFibrePresentationFusion = {
    order: 9,
    id:
        'pathind.internalized.' +
        'path-ind-source-fibre-at-sigma-pair-presentation-fusion',
    authority: 'derived-complete-parent-source-fibre-presentation-fusion',
    authorityPositions: [
        'emdash2/emdash3_2.lp:13297-13314',
        'emdash2/emdash3_2.lp:19080-19091',
        'emdash2/emdash3_2.lp:19296-19317'
    ],
    sourceOwner: 'functor-object',
    policy: 'runtime-rewrite-derived-support',
    mathematicalRule: false,
    variables: ['Z', 'x', 'E'],
    left:
        'Fibre_cat(PathIndSrc_catd(Z),Struct_sigma(x,E))',
    right: 'Fibre_cat(E,pathout_refl_obj(Z,x))'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV7.exactImplementation.runtimeRules
        .map(rule => cloneData(rule)),
    pathInductionSourceFibrePresentationFusion
]);

const correctedStages = proposalV7.exactImplementation
    .implementationStages.map(stage =>
        stage.id === 'internalized-runtime-projections'
            ? {
                ...cloneData(stage),
                rules: correctedRuntimeRules.map(rule => rule.id)
            }
            : cloneData(stage)
    );

const rawProposal = {
    ...cloneData(proposalV7),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8_REVISION,
    status: 'corrected-proposal-v8-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV7.parent),
        supersededProposalRevision: proposalV7.revision,
        supersededProposalCheckpoint: 'ef761e4',
        supersededReviewCheckpoint: '8cdff35',
        supersededLedgerCheckpoint: null,
        priorCounterevidence:
            cloneData(proposalV7.parent.counterevidence),
        counterevidence: {
            measuredDuring: 'reviewed-v7-cold-semantic-replay',
            allNineLocalRuntimeRulesCompiled: true,
            compiledTransparentDefinitionCount: 3,
            compiledTransparentDefinitions: [
                'pathout_motive_transport_obj',
                'pathout_motive_transport_arrow',
                'PathIndSrc_catd'
            ],
            failingPhase: 'transparent-library-declaration-three',
            failingDeclaration: 'PathIndSrc_transport_func',
            failingAuthorityPosition:
                'emdash2/emdash3_2.lp:19309-19317',
            failingComparisonPath: [
                '$',
                'application:decode:argument:0',
                'application:object-classifier:argument:0',
                'call:argument:0',
                'application:functor-object:argument:0',
                'call:argument:1'
            ],
            requestedComparisonStepLimit: 512,
            effectiveComparisonStepLimit: 512,
            comparisonStepLimitExceeded: false,
            comparisonStepsBeforeMismatch: 360,
            mismatchCode: 'TAG_MISMATCH',
            normalizedNestedLeftCategory:
                'PathOut_cat(Z,x)=' +
                'Sigma_cat(Z,hom_(Z,Z,id(Cat_cat,Z),x))',
            normalizedNestedRightCategory:
                'Sigma_cat(Z,PathOutMotives_catd(Z))',
            completeParentLeft:
                pathInductionSourceFibrePresentationFusion.left,
            completeParentRight:
                pathInductionSourceFibrePresentationFusion.right,
            v7ActionPresentationFusionCompiled: true,
            sourceFibreParentPresentationFusionRequired: true,
            underlyingCategoryEqualityRequired: false,
            genericSigmaFibreEquationRequired: false,
            genericComparisonChangeRequired: false,
            genericDeclarationProofIntegrationRequired: false,
            additionalActiveMathematicalRuleRequired: false,
            additionalDerivedSupportRuleRequired: true,
            proofRuleRequired: false,
            temporaryObserverRetained: false
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-08',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-008',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV7.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/10/0/10',
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 5
    },
    selectedPredecessor: {
        ...cloneData(proposalV7.selectedPredecessor),
        localImplementationDeltaIsFourNineZeroTen: false,
        localImplementationDeltaIsFourTenZeroTen: true,
        v7MotiveTransportActionCategoryPresentationFusionRetained: true,
        v8PathInductionSourceFibrePresentationFusionSelected: true
    },
    dependencyClosure: {
        ...cloneData(proposalV7.dependencyClosure),
        pathInductionSourceFibrePresentationFusion: {
            ruleId: pathInductionSourceFibrePresentationFusion.id,
            authorityPositions:
                pathInductionSourceFibrePresentationFusion
                    .authorityPositions,
            left: pathInductionSourceFibrePresentationFusion.left,
            right: pathInductionSourceFibrePresentationFusion.right,
            exactCompleteParentPairSelected: true,
            sourceFibrePresentationOnly: true,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            activeMathematicalRuleDelta: 0,
            derivedSupportRuleDelta: 1,
            proofRuleDelta: 0,
            underlyingCategoryEqualityAuthorized: false,
            genericSigmaFibreRuleAuthorized: false,
            genericComparisonChangeAuthorized: false,
            genericDeclarationProofIntegrationAuthorized: false,
            genericRuntimeMatcherChangeAuthorized: false,
            genericCheckerChangeAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV7.validation),
        v7ProposalCheckpointRequired: 'ef761e4',
        v7ReviewCheckpointRequired: '8cdff35',
        reasonLongAggregateOmitted:
            'v8-is-immutable-boundary-data-and-e560551-is-carried-forward'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v8-implementation',
        ...cloneData(proposalV7.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v7-implementation'
        ),
        'an-equation-between-PathOut_cat-and-the-total-motive-category',
        'a-generic-Sigma-fibre-shortcut'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v8-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV8 = typeof rawProposal;

export type CorePathindInternalized1dProposalV8ErrorCode =
    | 'PATHIND_INTERNALIZED_V8_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V8_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V8_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV8Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV8ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV8Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV8(
    proposal: CorePathindInternalized1dProposalV8 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8
): CorePathindInternalized1dProposalV8 {
    validateCorePathindInternalized1dProposalV7(proposalV7);
    const evidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-8' ||
        proposal.parent.supersededProposalRevision !== proposalV7.revision ||
        proposal.parent.supersededProposalCheckpoint !== 'ef761e4' ||
        proposal.parent.supersededReviewCheckpoint !== '8cdff35' ||
        proposal.parent.supersededLedgerCheckpoint !== null ||
        !evidence.allNineLocalRuntimeRulesCompiled ||
        evidence.compiledTransparentDefinitionCount !== 3 ||
        !sameData(evidence.compiledTransparentDefinitions, [
            'pathout_motive_transport_obj',
            'pathout_motive_transport_arrow',
            'PathIndSrc_catd'
        ]) ||
        evidence.failingDeclaration !== 'PathIndSrc_transport_func' ||
        evidence.requestedComparisonStepLimit !== 512 ||
        evidence.effectiveComparisonStepLimit !== 512 ||
        evidence.comparisonStepLimitExceeded ||
        evidence.comparisonStepsBeforeMismatch !== 360 ||
        evidence.mismatchCode !== 'TAG_MISMATCH' ||
        !evidence.v7ActionPresentationFusionCompiled ||
        !evidence.sourceFibreParentPresentationFusionRequired ||
        evidence.underlyingCategoryEqualityRequired ||
        evidence.genericSigmaFibreEquationRequired ||
        evidence.genericComparisonChangeRequired ||
        evidence.genericDeclarationProofIntegrationRequired ||
        evidence.additionalActiveMathematicalRuleRequired ||
        !evidence.additionalDerivedSupportRuleRequired ||
        evidence.proofRuleRequired ||
        evidence.temporaryObserverRetained
    ) {
        throw new CorePathindInternalized1dProposalV8Error(
            'PATHIND_INTERNALIZED_V8_AUTHORITY_DRIFT',
            'The reviewed-v7 source-fibre counterevidence drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const fusion = proposal.dependencyClosure
        .pathInductionSourceFibrePresentationFusion;
    if (
        implementation.trustedDeclarations.length !== 4 ||
        implementation.runtimeRules.length !== 10 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 10 ||
        implementation.exactBoundary !== '4/10/0/10' ||
        implementation.mathematicalRuntimeProjectionCount !== 5 ||
        implementation.derivedRuntimeSupportRuleCount !== 5 ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[9].id !==
            pathInductionSourceFibrePresentationFusion.id ||
        proposal.selectedPredecessor
            .localImplementationDeltaIsFourNineZeroTen ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFourTenZeroTen ||
        !proposal.selectedPredecessor
            .v7MotiveTransportActionCategoryPresentationFusionRetained ||
        !proposal.selectedPredecessor
            .v8PathInductionSourceFibrePresentationFusionSelected ||
        fusion.ruleId !== pathInductionSourceFibrePresentationFusion.id ||
        !fusion.exactCompleteParentPairSelected ||
        !fusion.sourceFibrePresentationOnly ||
        !fusion.subjectCheckRequiredBeforeImplementationCheckpoint ||
        fusion.activeMathematicalRuleDelta !== 0 ||
        fusion.derivedSupportRuleDelta !== 1 ||
        fusion.proofRuleDelta !== 0 ||
        fusion.underlyingCategoryEqualityAuthorized ||
        fusion.genericSigmaFibreRuleAuthorized ||
        fusion.genericComparisonChangeAuthorized ||
        fusion.genericDeclarationProofIntegrationAuthorized ||
        fusion.genericRuntimeMatcherChangeAuthorized ||
        fusion.genericCheckerChangeAuthorized ||
        proposal.typedLibraryConsumers.length !== 2 ||
        proposal.selectedRuntimeObservations.length !== 10 ||
        proposal.negativeConsumers.length !== 10 ||
        proposal.boundedOracle.assertions.length !== 12
    ) {
        throw new CorePathindInternalized1dProposalV8Error(
            'PATHIND_INTERNALIZED_V8_SCOPE_DRIFT',
            'The exact 4/10/0/10 source-fibre boundary drifted'
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
            'pathind-internalized-1d-v8-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV8Error(
            'PATHIND_INTERNALIZED_V8_AUTHORIZATION_DRIFT',
            'Corrected proposal v8 became self-authorizing or widened'
        );
    }
    return proposal;
}
