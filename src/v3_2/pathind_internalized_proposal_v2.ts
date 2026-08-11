/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v2.
 *
 * V2 preserves every mathematical owner, projection, definition, consumer,
 * oracle assertion, and denial from v1. Measured generic-runtime admission
 * requires one narrowly scoped type-presentation fusion before the
 * PathInd_func component projection. The fusion is execution support for
 * already-active definitions and equations; it adds no mathematical rule.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL,
    validateCorePathindInternalized1dProposal
} from './pathind_internalized_proposal';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-2' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-02/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-002 as proposed.';

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

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

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const proposalV1 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL;

const componentSubjectPresentationFusion = {
    order: 2,
    id:
        'pathind.internalized.' +
        'path-ind-functor-component-subject-fusion',
    authority: 'derived-stable-presentation-fusion',
    authoritySymbols: [
        'Hom_cat-Cat_cat-to-Functor_cat',
        'Functor-definition',
        'Catd_cat-Functor_cat-proof-comparison',
        'fapp0_func-object-projection',
        'Pi_func-object-projection',
        'PathInd_src_catd-definition',
        'PathInd_tgt_catd-definition'
    ],
    sourceOwner: 'τ',
    resultOwner: 'τ',
    policy: 'runtime-rewrite',
    mathematicalRule: false,
    measuredLeft:
        'τ(Hom(Cat_cat,PathInd_src_catd(Z,x)[E],' +
        'PathInd_tgt_catd(Z,x)[E]))',
    measuredRight:
        'τ(Functor(Fibre_cat(E,pathout_refl_obj(Z,x)),Pi_cat(E)))'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV1.exactImplementation.runtimeRules
        .slice(0, 2)
        .map(rule => cloneData(rule)),
    componentSubjectPresentationFusion,
    ...proposalV1.exactImplementation.runtimeRules
        .slice(2)
        .map((rule, index) => ({
            ...cloneData(rule),
            order: index + 3
        }))
]);

const correctedStages = proposalV1.exactImplementation
    .implementationStages.map(stage =>
        stage.id === 'internalized-runtime-projections'
            ? {
                ...cloneData(stage),
                rules: correctedRuntimeRules.map(rule => rule.id)
            }
            : cloneData(stage)
    );

const rawProposal = {
    ...cloneData(proposalV1),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2_REVISION,
    status: 'corrected-proposal-v2-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV1.parent),
        supersededProposalRevision: proposalV1.revision,
        supersededProposalCheckpoint: '188b8e5',
        supersededReviewCheckpoint: 'd3a0f31',
        supersededLedgerCheckpoint: '0191db7',
        counterevidence: {
            measuredDuring:
                'first-PATHOUT-LIBRARY-INTERNALIZED-1D-runtime-compilation',
            failingRule:
                'pathind.internalized.path-ind-functor-component',
            failureCode: 'INVALID_RUNTIME_RULE_TYPE',
            normalizedMismatch:
                'stable-PathInd-component-Hom-versus-direct-Functor-' +
                'endpoint-presentation',
            stableSourcePresentation:
                'Catd_cat(PathOut_cat(Z,x))',
            genericFixedEvaluationPattern:
                'Functor_cat(PathOut_cat(Z,x),Cat_cat)',
            fixedEvaluationDependencyExperimentSolved: false,
            categoryPresentationProofExperimentStatus: 'stuck',
            temporaryExperimentsRetained: false
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-02',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-002',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV1.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/5/0/10',
        mathematicalRuntimeProjectionCount: 4,
        derivedRuntimeSupportRuleCount: 1
    },
    selectedPredecessor: {
        ...cloneData(proposalV1.selectedPredecessor),
        localImplementationDeltaIsFourFourZeroTen: false,
        localImplementationDeltaIsFourFiveZeroTen: true
    },
    dependencyClosure: {
        ...cloneData(proposalV1.dependencyClosure),
        componentSubjectPresentationCorrection: {
            ruleId: componentSubjectPresentationFusion.id,
            measuredLeft: componentSubjectPresentationFusion.measuredLeft,
            measuredRight: componentSubjectPresentationFusion.measuredRight,
            exactScope:
                'PathInd_func-component-subject-type-only',
            derivedFromActiveDefinitionsAndEquations: true,
            activeMathematicalRuleDelta: 0,
            genericRuntimeMatcherChangeAuthorized: false,
            genericCheckerChangeAuthorized: false,
            inheritedProofProgramDependencyAuthorized: false,
            genericFixedEvaluationRuntimeImportAuthorized: false,
            alternatePathIndTypeAuthorized: false,
            alternateComponentBodyAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV1.validation),
        reasonLongAggregateOmitted:
            'correction-is-immutable-data-only-and-direct-gates-cover-it'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v2-implementation',
        ...cloneData(proposalV1.doesNotAuthorize).filter(entry =>
            entry !== 'PATHOUT-LIBRARY-INTERNALIZED-1D-implementation'
        ),
        'generic-runtime-matcher-or-checker-change',
        'retaining-temporary-runtime-or-proof-experiments'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v2-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV2 = typeof rawProposal;

export type CorePathindInternalized1dProposalV2ErrorCode =
    | 'PATHIND_INTERNALIZED_V2_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V2_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V2_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV2Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV2ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV2Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV2(
    proposal: CorePathindInternalized1dProposalV2 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2
): CorePathindInternalized1dProposalV2 {
    validateCorePathindInternalized1dProposal(proposalV1);
    const counterevidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-2' ||
        proposal.parent.supersededProposalRevision !== proposalV1.revision ||
        proposal.parent.supersededProposalCheckpoint !== '188b8e5' ||
        proposal.parent.supersededReviewCheckpoint !== 'd3a0f31' ||
        proposal.parent.supersededLedgerCheckpoint !== '0191db7' ||
        counterevidence.failureCode !== 'INVALID_RUNTIME_RULE_TYPE' ||
        counterevidence.failingRule !==
            'pathind.internalized.path-ind-functor-component' ||
        counterevidence.fixedEvaluationDependencyExperimentSolved ||
        counterevidence.categoryPresentationProofExperimentStatus !==
            'stuck' ||
        counterevidence.temporaryExperimentsRetained
    ) {
        throw new CorePathindInternalized1dProposalV2Error(
            'PATHIND_INTERNALIZED_V2_AUTHORITY_DRIFT',
            'The v1 checkpoints or measured admission evidence drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const correction = proposal.dependencyClosure
        .componentSubjectPresentationCorrection;
    if (
        implementation.trustedDeclarations.length !== 4 ||
        implementation.runtimeRules.length !== 5 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 10 ||
        implementation.exactBoundary !== '4/5/0/10' ||
        implementation.mathematicalRuntimeProjectionCount !== 4 ||
        implementation.derivedRuntimeSupportRuleCount !== 1 ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[2].id !==
            componentSubjectPresentationFusion.id ||
        proposal.selectedPredecessor
            .localImplementationDeltaIsFourFourZeroTen ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFourFiveZeroTen ||
        correction.ruleId !== componentSubjectPresentationFusion.id ||
        !correction.derivedFromActiveDefinitionsAndEquations ||
        correction.activeMathematicalRuleDelta !== 0 ||
        correction.genericRuntimeMatcherChangeAuthorized ||
        correction.genericCheckerChangeAuthorized ||
        correction.inheritedProofProgramDependencyAuthorized ||
        correction.genericFixedEvaluationRuntimeImportAuthorized ||
        correction.alternatePathIndTypeAuthorized ||
        correction.alternateComponentBodyAuthorized ||
        proposal.selectedRuntimeObservations.length !== 9 ||
        proposal.negativeConsumers.length !== 10 ||
        proposal.boundedOracle.assertions.length !== 11
    ) {
        throw new CorePathindInternalized1dProposalV2Error(
            'PATHIND_INTERNALIZED_V2_SCOPE_DRIFT',
            'The corrected exact 4/5/0/10 boundary drifted'
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
            'pathind-internalized-1d-v2-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV2Error(
            'PATHIND_INTERNALIZED_V2_AUTHORIZATION_DRIFT',
            'Corrected proposal v2 became self-authorizing or widened'
        );
    }
    return proposal;
}
