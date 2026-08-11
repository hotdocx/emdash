/**
 * Corrected PATHIND-TRUSTED-PROFILE-1C non-authorizing proposal v8.
 *
 * V8 preserves the v7 boundary but replaces its unreachable pre-delta
 * Functor-classifier fusion with the exact stable decoded type reached after
 * the predecessor's Functor delta. It adds no rule and retains the global
 * runtime distinction between Functor_cat(K,Cat_cat) and Catd_cat(K).
 */

import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7,
    validateCorePathindFixedSource1cProposalV7
} from './pathind_fixed_source_proposal_v7';

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V8_REVISION =
    'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-8' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-FIXED-SOURCE-08/' +
    'D-TS-EMDASH-PATHIND-FIXED-SOURCE-008 as proposed.';

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

const proposalV7 = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7;

const fixedEvaluationPostDeltaPresentationFusionRule = {
    order: 5,
    id:
        'pathind.fixed-source.' +
        'fixed-evaluation-post-delta-presentation-fusion',
    derivedFromAuthorityLines: [
        3316,
        3317,
        5457,
        19067,
        19068,
        19069,
        19072
    ],
    sourceOwner: 'τ',
    resultOwner: 'τ',
    policy: 'runtime-rewrite-derived-post-delta-type-fusion'
} as const;

const correctedRuntimeRules = Object.freeze(
    proposalV7.exactImplementation.runtimeRules.map((rule, index) =>
        index === 5
            ? fixedEvaluationPostDeltaPresentationFusionRule
            : cloneData(rule)
    )
);

const rawProposal = {
    ...cloneData(proposalV7),
    revision: CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V8_REVISION,
    status: 'corrected-proposal-v8-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV7.parent),
        supersededProposalRevision: proposalV7.revision,
        supersededProposalCheckpoint: 'f0fd4a6',
        supersededReviewCheckpoint: '0cefb73',
        priorCounterevidence:
            cloneData(proposalV7.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'corrected-v7-runtime-and-library-compilation-with-' +
                'capped-local-trace',
            compiledRuntimeRuleCount: 12,
            allSelectedRuntimeRulesSubjectChecked: true,
            failingDeclaration: 'pathout_refl_eval_func',
            failingDeclarationOrder: 0,
            failingPhase: 'transparent-body-type-conversion',
            predecessorRuleAppliedFirst:
                'categorical.mixed-action.functor-classifier-definition',
            predecessorRuleAuthorityLines: [3316, 3317],
            v7PreDeltaFusionMatched: false,
            v7PreDeltaFusionShadowedByEarlierFragment: true,
            exactStableLeft:
                'τ(Obj(Functor_cat(Functor_cat(K,Cat_cat),Cat_cat)))',
            exactStableRight:
                'τ(Obj(Functor_cat(Catd_cat(K),Cat_cat)))',
            replacementRuleRequired: true,
            additionalRuntimeRuleRequired: false,
            diagnosticWrapperRemovedCompletely: true,
            genericCheckerDiffEmpty: true
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-FIXED-SOURCE-08',
        decisionId: 'D-TS-EMDASH-PATHIND-FIXED-SOURCE-008',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV7.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        exactBoundary: '5/12/0/6'
    },
    selectedPredecessor: {
        ...cloneData(proposalV7.selectedPredecessor),
        localImplementationDeltaIsFiveTwelveZeroSix: true,
        v7PreDeltaFusionRetained: false,
        v8PostDeltaFusionSelected: true
    },
    dependencyClosure: {
        ...cloneData(proposalV7.dependencyClosure),
        fixedEvaluationSourcePresentationFusion: {
            ruleId:
                'pathind.fixed-source.' +
                'fixed-evaluation-post-delta-presentation-fusion',
            exactLeft:
                'τ(Obj(Functor_cat(Functor_cat(K,Cat_cat),Cat_cat)))',
            exactRight:
                'τ(Obj(Functor_cat(Catd_cat(K),Cat_cat)))',
            derivedFromActiveDeltaProofAndDefinitionLines:
                cloneData(
                    fixedEvaluationPostDeltaPresentationFusionRule
                        .derivedFromAuthorityLines
                ),
            replacesUnreachableV7PreDeltaFusion: true,
            wrapsStablePostDeltaPresentationUnderDecodedObjectClassifier:
                true,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            directRuntimeFunctorCategoryCollapseAuthorized: false,
            genericDeclarationProofIntegrationAuthorized: false,
            genericCheckerChangeAuthorized: false,
            newMathematicalRule: false
        }
    },
    validation: {
        ...cloneData(proposalV7.validation),
        reasonLongAggregateOmitted:
            'post-delta-replacement-is-immutable-data-only-and-' +
            'directly-gated'
    },
    doesNotAuthorize: [
        'PATHIND-TRUSTED-PROFILE-1C-corrected-v8-implementation',
        ...cloneData(proposalV7.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHIND-TRUSTED-PROFILE-1C-corrected-v7-implementation'
        ),
        'retaining-the-unreachable-v7-pre-delta-fusion',
        'retaining-the-temporary-pathind-presentation-trace'
    ],
    nextDependencyState:
        'pathind-fixed-source-1c-v8-awaiting-separate-immutable-review'
} as const;

export type CorePathindFixedSource1cProposalV8 = typeof rawProposal;

export type CorePathindFixedSource1cProposalV8ErrorCode =
    | 'PATHIND_FIXED_SOURCE_V8_AUTHORITY_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V8_SCOPE_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V8_AUTHORIZATION_DRIFT';

export class CorePathindFixedSource1cProposalV8Error extends Error {
    constructor(
        public readonly code:
            CorePathindFixedSource1cProposalV8ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindFixedSource1cProposalV8Error';
    }
}

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V8 =
    deepFreeze(rawProposal);

export function validateCorePathindFixedSource1cProposalV8(
    proposal: CorePathindFixedSource1cProposalV8 =
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V8
): CorePathindFixedSource1cProposalV8 {
    validateCorePathindFixedSource1cProposalV7(proposalV7);
    if (
        proposal.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-8' ||
        proposal.parent.supersededProposalRevision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-7' ||
        proposal.parent.supersededProposalCheckpoint !== 'f0fd4a6' ||
        proposal.parent.supersededReviewCheckpoint !== '0cefb73' ||
        proposal.parent.counterevidence.compiledRuntimeRuleCount !== 12 ||
        !proposal.parent.counterevidence
            .allSelectedRuntimeRulesSubjectChecked ||
        proposal.parent.counterevidence.predecessorRuleAppliedFirst !==
            'categorical.mixed-action.functor-classifier-definition' ||
        proposal.parent.counterevidence.v7PreDeltaFusionMatched ||
        !proposal.parent.counterevidence
            .v7PreDeltaFusionShadowedByEarlierFragment ||
        !proposal.parent.counterevidence.replacementRuleRequired ||
        proposal.parent.counterevidence.additionalRuntimeRuleRequired ||
        !proposal.parent.counterevidence
            .diagnosticWrapperRemovedCompletely ||
        !proposal.parent.counterevidence.genericCheckerDiffEmpty
    ) {
        throw new CorePathindFixedSource1cProposalV8Error(
            'PATHIND_FIXED_SOURCE_V8_AUTHORITY_DRIFT',
            'The v7 boundary or exact post-delta trace drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const fusion = proposal.dependencyClosure
        .fixedEvaluationSourcePresentationFusion;
    if (
        implementation.trustedDeclarations.length !== 5 ||
        implementation.runtimeRules.length !== 12 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 6 ||
        implementation.exactBoundary !== '5/12/0/6' ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[5].id !==
            'pathind.fixed-source.' +
                'fixed-evaluation-post-delta-presentation-fusion' ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFiveTwelveZeroSix ||
        proposal.selectedPredecessor.v7PreDeltaFusionRetained ||
        !proposal.selectedPredecessor.v8PostDeltaFusionSelected ||
        !fusion.replacesUnreachableV7PreDeltaFusion ||
        !fusion
            .wrapsStablePostDeltaPresentationUnderDecodedObjectClassifier ||
        !fusion.subjectCheckRequiredBeforeImplementationCheckpoint ||
        fusion.directRuntimeFunctorCategoryCollapseAuthorized ||
        fusion.genericDeclarationProofIntegrationAuthorized ||
        fusion.genericCheckerChangeAuthorized ||
        fusion.newMathematicalRule ||
        proposal.selectedRuntimeObservations.length !== 5 ||
        proposal.boundedOracle.assertions.length !== 9
    ) {
        throw new CorePathindFixedSource1cProposalV8Error(
            'PATHIND_FIXED_SOURCE_V8_SCOPE_DRIFT',
            'The corrected exact replacement boundary drifted'
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
            'pathind-fixed-source-1c-v8-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindFixedSource1cProposalV8Error(
            'PATHIND_FIXED_SOURCE_V8_AUTHORIZATION_DRIFT',
            'Corrected proposal v8 became self-authorizing or widened'
        );
    }
    return proposal;
}
