/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v6.
 *
 * V6 preserves v5 and adds one local two-sided classifier-presentation
 * fusion required by the first transparent internalized library definition.
 * It is the decoded functor-category analogue of the already qualified
 * fixed-source bridge; it neither collapses Catd_cat globally nor teaches
 * transparent declaration checking to run proof-unification programs.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5,
    validateCorePathindInternalized1dProposalV5
} from './pathind_internalized_proposal_v5';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-6' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-06/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-006 as proposed.';

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

const proposalV5 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5;

const motiveTransportCategoryPresentationFusion = {
    order: 7,
    id:
        'pathind.internalized.' +
        'motive-transport-functor-category-presentation-fusion',
    authority: 'derived-two-sided-classifier-presentation-fusion',
    authorityPositions: [
        'emdash2/emdash3_2.lp:3316-3317',
        'emdash2/emdash3_2.lp:5457',
        'emdash2/emdash3_2.lp:19139-19156'
    ],
    sourceOwner: 'decode',
    policy: 'runtime-rewrite-derived-support',
    mathematicalRule: false,
    variables: ['K', 'L'],
    left:
        'τ(Obj(Functor_cat(Functor_cat(K,Cat_cat),' +
        'Functor_cat(L,Cat_cat))))',
    right:
        'τ(Obj(Functor_cat(Catd_cat(K),Catd_cat(L))))'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV5.exactImplementation.runtimeRules
        .map(rule => cloneData(rule)),
    motiveTransportCategoryPresentationFusion
]);

const correctedStages = proposalV5.exactImplementation
    .implementationStages.map(stage =>
        stage.id === 'internalized-runtime-projections'
            ? {
                ...cloneData(stage),
                rules: correctedRuntimeRules.map(rule => rule.id)
            }
            : cloneData(stage)
    );

const rawProposal = {
    ...cloneData(proposalV5),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6_REVISION,
    status: 'corrected-proposal-v6-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV5.parent),
        supersededProposalRevision: proposalV5.revision,
        supersededProposalCheckpoint: 'fe0306d',
        supersededReviewCheckpoint: 'a94c2f7',
        supersededLedgerCheckpoint: null,
        priorCounterevidence:
            cloneData(proposalV5.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'reviewed-v5-cold-replay-with-comparison-v2-candidate',
            allSevenLocalRuntimeRulesCompiled: true,
            failingPhase: 'transparent-library-declaration-zero',
            failingDeclaration: 'pathout_motive_transport_obj',
            failingAuthorityPosition:
                'emdash2/emdash3_2.lp:19139-19156',
            failureReason:
                'hom-classifier-differs-from-functor-classifier',
            independentlyNormalizedBodyTypeSteps: 37,
            independentlyNormalizedExpectedTypeSteps: 21,
            independentlyNormalizedFormsExactlyEqual: false,
            exactNormalizedBodyType:
                'τ(Obj(Functor_cat(Functor_cat(PathOut_x,Cat_cat),' +
                'Functor_cat(PathOut_y,Cat_cat))))',
            exactNormalizedExpectedType:
                'τ(Obj(Functor_cat(Catd_cat(PathOut_x),' +
                'Catd_cat(PathOut_y))))',
            activeCategoryPresentationProofAuthority:
                'emdash2/emdash3_2.lp:5457',
            categoryPresentationProofAlreadyCompiledByPredecessor: true,
            genericDeclarationCheckerConsumesProofPrograms: false,
            priorGenericProofIntegrationExperimentRetained: false,
            localTwoSidedClassifierFusionRequired: true,
            genericCategoryCollapseRequired: false,
            genericDeclarationProofIntegrationRequired: false,
            additionalActiveMathematicalRuleRequired: false,
            additionalDerivedSupportRuleRequired: true,
            proofRuleRequired: false,
            temporaryObserverRetained: false
        },
        genericComparisonPrerequisite: {
            row: 'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-1',
            proposalCheckpoint: 'a42ffc9',
            reviewCheckpoint: '5277885',
            reviewSha256:
                '749c17a109856a2473faacd71148c3d8dcdc4cc175b25d5af635b0935246cd12',
            semanticCheckpointRequiredBeforePathIndCheckpoint: true,
            originalSourceRootReplayRequired: true,
            sameGlobalBudgetRequired: true,
            newReductionEquationCount: 0
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-06',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-006',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV5.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/8/0/10',
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 3
    },
    selectedPredecessor: {
        ...cloneData(proposalV5.selectedPredecessor),
        localImplementationDeltaIsFourSevenZeroTen: false,
        localImplementationDeltaIsFourEightZeroTen: true,
        v5ActivePiPullbackProjectionRetained: true,
        v6MotiveTransportCategoryPresentationFusionSelected: true
    },
    dependencyClosure: {
        ...cloneData(proposalV5.dependencyClosure),
        motiveTransportCategoryPresentationFusion: {
            ruleId: motiveTransportCategoryPresentationFusion.id,
            authorityPositions:
                motiveTransportCategoryPresentationFusion.authorityPositions,
            left: motiveTransportCategoryPresentationFusion.left,
            right: motiveTransportCategoryPresentationFusion.right,
            exactStablePostDeltaPairSelected: true,
            twoSidedCategoryPresentationOnly: true,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            activeMathematicalRuleDelta: 0,
            derivedSupportRuleDelta: 1,
            proofRuleDelta: 0,
            underlyingCategoryCollapseAuthorized: false,
            genericTwoSidedFusionAuthorized: false,
            genericDeclarationProofIntegrationAuthorized: false,
            genericRuntimeMatcherChangeAuthorized: false,
            genericCheckerChangeAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV5.validation),
        genericComparisonFocusedGateRequired: true,
        reasonLongAggregateOmitted:
            'v6-is-immutable-boundary-data-and-direct-gates-cover-it'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v6-implementation',
        ...cloneData(proposalV5.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v5-implementation'
        ),
        'an-underlying-Catd_cat-or-Functor_cat-runtime-collapse',
        'a-generic-two-sided-category-presentation-runtime-rule',
        'generic-proof-program-integration-into-declaration-checking'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v6-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV6 = typeof rawProposal;

export type CorePathindInternalized1dProposalV6ErrorCode =
    | 'PATHIND_INTERNALIZED_V6_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V6_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V6_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV6Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV6ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV6Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV6(
    proposal: CorePathindInternalized1dProposalV6 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6
): CorePathindInternalized1dProposalV6 {
    validateCorePathindInternalized1dProposalV5(proposalV5);
    const evidence = proposal.parent.counterevidence;
    const prerequisite = proposal.parent.genericComparisonPrerequisite;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-6' ||
        proposal.parent.supersededProposalRevision !== proposalV5.revision ||
        proposal.parent.supersededProposalCheckpoint !== 'fe0306d' ||
        proposal.parent.supersededReviewCheckpoint !== 'a94c2f7' ||
        proposal.parent.supersededLedgerCheckpoint !== null ||
        !evidence.allSevenLocalRuntimeRulesCompiled ||
        evidence.failingPhase !==
            'transparent-library-declaration-zero' ||
        evidence.failingDeclaration !== 'pathout_motive_transport_obj' ||
        evidence.independentlyNormalizedBodyTypeSteps !== 37 ||
        evidence.independentlyNormalizedExpectedTypeSteps !== 21 ||
        evidence.independentlyNormalizedFormsExactlyEqual ||
        !evidence.categoryPresentationProofAlreadyCompiledByPredecessor ||
        evidence.genericDeclarationCheckerConsumesProofPrograms ||
        evidence.priorGenericProofIntegrationExperimentRetained ||
        !evidence.localTwoSidedClassifierFusionRequired ||
        evidence.genericCategoryCollapseRequired ||
        evidence.genericDeclarationProofIntegrationRequired ||
        evidence.additionalActiveMathematicalRuleRequired ||
        !evidence.additionalDerivedSupportRuleRequired ||
        evidence.proofRuleRequired ||
        evidence.temporaryObserverRetained ||
        prerequisite.proposalCheckpoint !== 'a42ffc9' ||
        prerequisite.reviewCheckpoint !== '5277885' ||
        !prerequisite.semanticCheckpointRequiredBeforePathIndCheckpoint ||
        !prerequisite.originalSourceRootReplayRequired ||
        !prerequisite.sameGlobalBudgetRequired ||
        prerequisite.newReductionEquationCount !== 0
    ) {
        throw new CorePathindInternalized1dProposalV6Error(
            'PATHIND_INTERNALIZED_V6_AUTHORITY_DRIFT',
            'The v5 boundary, library mismatch, or prerequisite drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const fusion = proposal.dependencyClosure
        .motiveTransportCategoryPresentationFusion;
    if (
        implementation.trustedDeclarations.length !== 4 ||
        implementation.runtimeRules.length !== 8 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 10 ||
        implementation.exactBoundary !== '4/8/0/10' ||
        implementation.mathematicalRuntimeProjectionCount !== 5 ||
        implementation.derivedRuntimeSupportRuleCount !== 3 ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[7].id !==
            motiveTransportCategoryPresentationFusion.id ||
        proposal.selectedPredecessor
            .localImplementationDeltaIsFourSevenZeroTen ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFourEightZeroTen ||
        !proposal.selectedPredecessor
            .v5ActivePiPullbackProjectionRetained ||
        !proposal.selectedPredecessor
            .v6MotiveTransportCategoryPresentationFusionSelected ||
        fusion.ruleId !== motiveTransportCategoryPresentationFusion.id ||
        !fusion.exactStablePostDeltaPairSelected ||
        !fusion.twoSidedCategoryPresentationOnly ||
        !fusion.subjectCheckRequiredBeforeImplementationCheckpoint ||
        fusion.activeMathematicalRuleDelta !== 0 ||
        fusion.derivedSupportRuleDelta !== 1 ||
        fusion.proofRuleDelta !== 0 ||
        fusion.underlyingCategoryCollapseAuthorized ||
        fusion.genericTwoSidedFusionAuthorized ||
        fusion.genericDeclarationProofIntegrationAuthorized ||
        fusion.genericRuntimeMatcherChangeAuthorized ||
        fusion.genericCheckerChangeAuthorized ||
        proposal.typedLibraryConsumers.length !== 2 ||
        proposal.selectedRuntimeObservations.length !== 10 ||
        proposal.negativeConsumers.length !== 10 ||
        proposal.boundedOracle.assertions.length !== 12
    ) {
        throw new CorePathindInternalized1dProposalV6Error(
            'PATHIND_INTERNALIZED_V6_SCOPE_DRIFT',
            'The exact 4/8/0/10 local presentation boundary drifted'
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
            'pathind-internalized-1d-v6-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV6Error(
            'PATHIND_INTERNALIZED_V6_AUTHORIZATION_DRIFT',
            'Corrected proposal v6 became self-authorizing or widened'
        );
    }
    return proposal;
}
