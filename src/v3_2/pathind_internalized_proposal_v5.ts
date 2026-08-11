/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v5.
 *
 * V5 preserves v4 and adds the existing active Pi_pullback_funcd pointwise
 * projection required by the final PathInd_transfd component. The active
 * rule's inferred source/target family slots remain typed wildcards, exactly
 * mirroring Lambdapi's `_ _`; no new equation or proof rule is introduced.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4,
    validateCorePathindInternalized1dProposalV4
} from './pathind_internalized_proposal_v4';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-5' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-05/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-005 as proposed.';

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

const proposalV4 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4;

const piPullbackComponentProjection = {
    order: 5,
    id: 'pathind.internalized.pi-pullback-component',
    authority: 'active-emdash-v3.2-rule',
    authorityPosition: 'emdash2/emdash3_2.lp:12680',
    sourceOwner: 'tapp0_fapp0',
    policy: 'runtime-rewrite-active',
    mathematicalRule: true,
    variables: ['K', 'G', 'x'],
    inferredFamilySlots: [
        'typed-wildcard-source-family',
        'typed-wildcard-target-family'
    ],
    left:
        'tapp0_fapp0(K,Cat_cat,_,_,x,Pi_pullback_funcd(K,G))',
    right: 'Pi_func(fapp0(K,Op_cat(Cat_cat),G,x))'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV4.exactImplementation.runtimeRules
        .slice(0, 5)
        .map(rule => cloneData(rule)),
    piPullbackComponentProjection,
    ...proposalV4.exactImplementation.runtimeRules
        .slice(5)
        .map((rule, index) => ({
            ...cloneData(rule),
            order: index + 6
        }))
]);

const correctedStages = proposalV4.exactImplementation
    .implementationStages.map(stage =>
        stage.id === 'internalized-runtime-projections'
            ? {
                ...cloneData(stage),
                rules: correctedRuntimeRules.map(rule => rule.id)
            }
            : cloneData(stage)
    );

const selectedRuntimeObservations = Object.freeze([
    ...proposalV4.selectedRuntimeObservations.map(entry => cloneData(entry)),
    'Pi_pullback_funcd(G)[x]-reduces-to-Pi_func(G[x])'
]);

const boundedOracle = {
    ...cloneData(proposalV4.boundedOracle),
    assertions: Object.freeze([
        ...proposalV4.boundedOracle.assertions.map(entry => cloneData(entry)),
        'PathOutPi-component-is-pointwise-Pi'
    ])
};

const rawProposal = {
    ...cloneData(proposalV4),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5_REVISION,
    status: 'corrected-proposal-v5-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV4.parent),
        supersededProposalRevision: proposalV4.revision,
        supersededProposalCheckpoint: '001a899',
        supersededReviewCheckpoint: '7984efb',
        supersededLedgerCheckpoint: '5d1851f',
        priorCounterevidence:
            cloneData(proposalV4.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'reviewed-v4-runtime-compilation-with-in-memory-observers',
            compiledLocalRuleCountBeforeFailure: 5,
            v4PostPrefixSupportRuleSubjectChecked: true,
            v4TransfdSubjectSupportRuleSubjectChecked: true,
            failingRule:
                'pathind.internalized.path-ind-transfd-component',
            failureCode: 'INVALID_RUNTIME_RULE_TYPE',
            candidateProjectionId: piPullbackComponentProjection.id,
            candidateProjectionAuthorityPosition:
                piPullbackComponentProjection.authorityPosition,
            overSpecifiedFamilySlotCandidateReachable: false,
            typedWildcardFamilySlotCandidateSubjectChecked: true,
            typedWildcardCandidateProofRuleRequired: false,
            pairedComparisonStatusBeforeGenericCorrection: 'not-equal',
            pairedComparisonSteps: 125,
            independentlyNormalizedLeftStatus: 'normal',
            independentlyNormalizedLeftSteps: 58,
            independentlyNormalizedRightStatus: 'normal',
            independentlyNormalizedRightSteps: 68,
            independentlyNormalizedFormsExactlyEqual: true,
            exactSharedNormalFormHead:
                'tau(Obj(Transf_cat(Functor_cat(PathOut,Cat),' +
                'Cat,...)))',
            additionalActiveMathematicalRuleRequired: true,
            additionalDerivedSupportRuleRequired: false,
            proofRuleRequired: false,
            temporaryObserverRetained: false,
            genericSourceDiffEmptyAtMeasurement: true
        },
        genericComparisonPrerequisite: {
            row: 'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-1',
            proposalCheckpoint: 'cf8ed76',
            reviewCheckpoint: '778da06',
            reviewSha256:
                '465a2056fbbbcfca75af9df33fedffb0142cc53d85f004f7869c41d04f56bd98',
            semanticCheckpointRequiredBeforePathIndCheckpoint: true,
            sameGlobalBudgetRequired: true,
            newReductionEquationCount: 0
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-05',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-005',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV4.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/7/0/10',
        mathematicalRuntimeProjectionCount: 5,
        derivedRuntimeSupportRuleCount: 2
    },
    selectedPredecessor: {
        ...cloneData(proposalV4.selectedPredecessor),
        localImplementationDeltaIsFourSixZeroTen: false,
        localImplementationDeltaIsFourSevenZeroTen: true,
        v4TransfdSubjectFusionRetained: true,
        v5ActivePiPullbackProjectionSelected: true
    },
    dependencyClosure: {
        ...cloneData(proposalV4.dependencyClosure),
        piPullbackPointwiseProjection: {
            ruleId: piPullbackComponentProjection.id,
            authorityPosition:
                piPullbackComponentProjection.authorityPosition,
            left: piPullbackComponentProjection.left,
            right: piPullbackComponentProjection.right,
            inferredFamilySlotsRemainTypedWildcards: true,
            exactActiveRuleImportedOneForOne: true,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            genericComparisonClosureRequired: true,
            activeMathematicalRuleDelta: 1,
            derivedSupportRuleDelta: 0,
            proofRuleDelta: 0,
            genericRuntimeMatcherChangeAuthorized: false,
            genericCheckerChangeAuthorized: false,
            wholeStressProfileImportAuthorized: false
        }
    },
    selectedRuntimeObservations,
    boundedOracle,
    validation: {
        ...cloneData(proposalV4.validation),
        genericComparisonFocusedGateRequired: true,
        reasonLongAggregateOmitted:
            'v5-is-immutable-boundary-data-and-direct-gates-cover-it'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v5-implementation',
        ...cloneData(proposalV4.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v4-implementation'
        ),
        'over-specifying-the-active-inferred-family-slots',
        'a-PathInd-specific-outer-commuting-rule',
        'implementation-before-the-generic-comparison-prerequisite-is-green'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v5-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV5 = typeof rawProposal;

export type CorePathindInternalized1dProposalV5ErrorCode =
    | 'PATHIND_INTERNALIZED_V5_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V5_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V5_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV5Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV5ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV5Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV5(
    proposal: CorePathindInternalized1dProposalV5 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5
): CorePathindInternalized1dProposalV5 {
    validateCorePathindInternalized1dProposalV4(proposalV4);
    const counterevidence = proposal.parent.counterevidence;
    const prerequisite = proposal.parent.genericComparisonPrerequisite;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-5' ||
        proposal.parent.supersededProposalRevision !== proposalV4.revision ||
        proposal.parent.supersededProposalCheckpoint !== '001a899' ||
        proposal.parent.supersededReviewCheckpoint !== '7984efb' ||
        proposal.parent.supersededLedgerCheckpoint !== '5d1851f' ||
        counterevidence.compiledLocalRuleCountBeforeFailure !== 5 ||
        !counterevidence.v4PostPrefixSupportRuleSubjectChecked ||
        !counterevidence.v4TransfdSubjectSupportRuleSubjectChecked ||
        counterevidence.failingRule !==
            'pathind.internalized.path-ind-transfd-component' ||
        counterevidence.candidateProjectionId !==
            piPullbackComponentProjection.id ||
        counterevidence.overSpecifiedFamilySlotCandidateReachable ||
        !counterevidence.typedWildcardFamilySlotCandidateSubjectChecked ||
        counterevidence.typedWildcardCandidateProofRuleRequired ||
        counterevidence.pairedComparisonStatusBeforeGenericCorrection !==
            'not-equal' ||
        counterevidence.pairedComparisonSteps !== 125 ||
        counterevidence.independentlyNormalizedLeftSteps !== 58 ||
        counterevidence.independentlyNormalizedRightSteps !== 68 ||
        !counterevidence.independentlyNormalizedFormsExactlyEqual ||
        !counterevidence.additionalActiveMathematicalRuleRequired ||
        counterevidence.additionalDerivedSupportRuleRequired ||
        counterevidence.proofRuleRequired ||
        counterevidence.temporaryObserverRetained ||
        !counterevidence.genericSourceDiffEmptyAtMeasurement ||
        prerequisite.row !==
            'CORE-LF-COMPARISON-NORMAL-FORM-CLOSURE-1' ||
        prerequisite.proposalCheckpoint !== 'cf8ed76' ||
        prerequisite.reviewCheckpoint !== '778da06' ||
        !prerequisite.semanticCheckpointRequiredBeforePathIndCheckpoint ||
        !prerequisite.sameGlobalBudgetRequired ||
        prerequisite.newReductionEquationCount !== 0
    ) {
        throw new CorePathindInternalized1dProposalV5Error(
            'PATHIND_INTERNALIZED_V5_AUTHORITY_DRIFT',
            'The v4 boundary, Pi projection, or generic prerequisite drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const projection =
        proposal.dependencyClosure.piPullbackPointwiseProjection;
    if (
        implementation.trustedDeclarations.length !== 4 ||
        implementation.runtimeRules.length !== 7 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 10 ||
        implementation.exactBoundary !== '4/7/0/10' ||
        implementation.mathematicalRuntimeProjectionCount !== 5 ||
        implementation.derivedRuntimeSupportRuleCount !== 2 ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[5].id !==
            piPullbackComponentProjection.id ||
        proposal.selectedPredecessor
            .localImplementationDeltaIsFourSixZeroTen ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFourSevenZeroTen ||
        !proposal.selectedPredecessor.v4TransfdSubjectFusionRetained ||
        !proposal.selectedPredecessor
            .v5ActivePiPullbackProjectionSelected ||
        projection.ruleId !== piPullbackComponentProjection.id ||
        !projection.inferredFamilySlotsRemainTypedWildcards ||
        !projection.exactActiveRuleImportedOneForOne ||
        !projection.subjectCheckRequiredBeforeImplementationCheckpoint ||
        !projection.genericComparisonClosureRequired ||
        projection.activeMathematicalRuleDelta !== 1 ||
        projection.derivedSupportRuleDelta !== 0 ||
        projection.proofRuleDelta !== 0 ||
        projection.genericRuntimeMatcherChangeAuthorized ||
        projection.genericCheckerChangeAuthorized ||
        projection.wholeStressProfileImportAuthorized ||
        proposal.typedLibraryConsumers.length !== 2 ||
        proposal.selectedRuntimeObservations.length !== 10 ||
        proposal.negativeConsumers.length !== 10 ||
        proposal.boundedOracle.assertions.length !== 12
    ) {
        throw new CorePathindInternalized1dProposalV5Error(
            'PATHIND_INTERNALIZED_V5_SCOPE_DRIFT',
            'The exact 4/7/0/10 active projection boundary drifted'
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
            'pathind-internalized-1d-v5-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV5Error(
            'PATHIND_INTERNALIZED_V5_AUTHORIZATION_DRIFT',
            'Corrected proposal v5 became self-authorizing or widened'
        );
    }
    return proposal;
}
