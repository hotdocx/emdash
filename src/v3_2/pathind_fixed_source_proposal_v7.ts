/**
 * Corrected PATHIND-TRUSTED-PROFILE-1C non-authorizing proposal v7.
 *
 * V7 preserves v6 and adds one classifier-wrapped type-presentation fusion
 * for the first transparent fixed-evaluation definition. The fusion derives
 * from the active proof-time Functor_cat/Catd_cat comparison without turning
 * that comparison into a global runtime category collapse or widening the
 * generic declaration checker.
 */

import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6,
    validateCorePathindFixedSource1cProposalV6
} from './pathind_fixed_source_proposal_v6';

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7_REVISION =
    'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-7' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-FIXED-SOURCE-07/' +
    'D-TS-EMDASH-PATHIND-FIXED-SOURCE-007 as proposed.';

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

const proposalV6 = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6;

const fixedEvaluationSourcePresentationFusionRule = {
    order: 5,
    id: 'pathind.fixed-source.fixed-evaluation-source-presentation-fusion',
    derivedFromAuthorityLines: [5457, 19067, 19068, 19069, 19072],
    sourceOwner: 'Functor',
    resultOwner: 'Functor',
    policy: 'runtime-rewrite-derived-type-presentation-fusion'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV6.exactImplementation.runtimeRules
        .slice(0, 5)
        .map(rule => cloneData(rule)),
    fixedEvaluationSourcePresentationFusionRule,
    ...proposalV6.exactImplementation.runtimeRules
        .slice(5)
        .map((rule, index) => ({
            ...cloneData(rule),
            order: index + 6
        }))
]);

const rawProposal = {
    ...cloneData(proposalV6),
    revision: CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7_REVISION,
    status: 'corrected-proposal-v7-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV6.parent),
        supersededProposalRevision: proposalV6.revision,
        supersededProposalCheckpoint: 'b41c3b0',
        supersededReviewCheckpoint: '9b22034',
        priorCounterevidence:
            cloneData(proposalV6.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'corrected-v6-runtime-and-library-compilation',
            compiledRuntimeRuleCount: 11,
            allSelectedRuntimeRulesSubjectChecked: true,
            failingDeclaration: 'pathout_refl_eval_func',
            failingDeclarationOrder: 0,
            failingPhase: 'transparent-body-type-conversion',
            exactBodySourcePresentation:
                'τ(Functor(Functor_cat(PathOut_cat(Z,x),' +
                'Cat_cat),Cat_cat))',
            exactDeclaredSourcePresentation:
                'τ(Functor(Catd_cat(PathOut_cat(Z,x)),Cat_cat))',
            activeProofRule:
                'categorical.dependent-target.category-presentation',
            activeProofRuleAuthorityLine: 5457,
            declarationCompilerConsumesRuntimeButNotProofProgram: true,
            directRuntimeCategoryCollapseRequired: false,
            classifierWrappedForwardFusionRequired: true,
            genericCheckerChangeRequired: false
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-FIXED-SOURCE-07',
        decisionId: 'D-TS-EMDASH-PATHIND-FIXED-SOURCE-007',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV6.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        exactBoundary: '5/12/0/6'
    },
    selectedPredecessor: {
        ...cloneData(proposalV6.selectedPredecessor),
        localImplementationDeltaIsFiveElevenZeroSix: false,
        localImplementationDeltaIsFiveTwelveZeroSix: true
    },
    dependencyClosure: {
        ...cloneData(proposalV6.dependencyClosure),
        fixedEvaluationSourcePresentationFusion: {
            ruleId:
                'pathind.fixed-source.' +
                'fixed-evaluation-source-presentation-fusion',
            exactLeft:
                'Functor(Functor_cat(K,Cat_cat),Cat_cat)',
            exactRight:
                'Functor(Catd_cat(K),Cat_cat)',
            derivedFromActiveProofAndDefinitionLines:
                cloneData(
                    fixedEvaluationSourcePresentationFusionRule
                        .derivedFromAuthorityLines
                ),
            wrapsProofTimeCategoryPresentationUnderFunctorClassifier: true,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            directRuntimeFunctorCategoryCollapseAuthorized: false,
            genericDeclarationProofIntegrationAuthorized: false,
            genericCheckerChangeAuthorized: false,
            newMathematicalRule: false
        }
    },
    validation: {
        ...cloneData(proposalV6.validation),
        reasonLongAggregateOmitted:
            'type-presentation-fusion-is-immutable-data-only-and-' +
            'directly-gated'
    },
    doesNotAuthorize: [
        'PATHIND-TRUSTED-PROFILE-1C-corrected-v7-implementation',
        ...cloneData(proposalV6.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHIND-TRUSTED-PROFILE-1C-corrected-v6-implementation'
        ),
        'runtime-Functor_cat-to-Catd_cat-category-collapse',
        'proof-program-integration-into-generic-declaration-checking'
    ],
    nextDependencyState:
        'pathind-fixed-source-1c-v7-awaiting-separate-immutable-review'
} as const;

export type CorePathindFixedSource1cProposalV7 = typeof rawProposal;

export type CorePathindFixedSource1cProposalV7ErrorCode =
    | 'PATHIND_FIXED_SOURCE_V7_AUTHORITY_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V7_SCOPE_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V7_AUTHORIZATION_DRIFT';

export class CorePathindFixedSource1cProposalV7Error extends Error {
    constructor(
        public readonly code:
            CorePathindFixedSource1cProposalV7ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindFixedSource1cProposalV7Error';
    }
}

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7 =
    deepFreeze(rawProposal);

export function validateCorePathindFixedSource1cProposalV7(
    proposal: CorePathindFixedSource1cProposalV7 =
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7
): CorePathindFixedSource1cProposalV7 {
    validateCorePathindFixedSource1cProposalV6(proposalV6);
    if (
        proposal.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-7' ||
        proposal.parent.supersededProposalRevision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-6' ||
        proposal.parent.supersededProposalCheckpoint !== 'b41c3b0' ||
        proposal.parent.supersededReviewCheckpoint !== '9b22034' ||
        proposal.parent.counterevidence.compiledRuntimeRuleCount !== 11 ||
        !proposal.parent.counterevidence
            .allSelectedRuntimeRulesSubjectChecked ||
        proposal.parent.counterevidence.failingDeclaration !==
            'pathout_refl_eval_func' ||
        proposal.parent.counterevidence.activeProofRuleAuthorityLine !==
            5457 ||
        !proposal.parent.counterevidence
            .declarationCompilerConsumesRuntimeButNotProofProgram ||
        proposal.parent.counterevidence
            .directRuntimeCategoryCollapseRequired ||
        !proposal.parent.counterevidence
            .classifierWrappedForwardFusionRequired
    ) {
        throw new CorePathindFixedSource1cProposalV7Error(
            'PATHIND_FIXED_SOURCE_V7_AUTHORITY_DRIFT',
            'The v6 boundary or measured declaration residual drifted'
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
                'fixed-evaluation-source-presentation-fusion' ||
        proposal.selectedPredecessor
            .localImplementationDeltaIsFiveElevenZeroSix ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFiveTwelveZeroSix ||
        !fusion.wrapsProofTimeCategoryPresentationUnderFunctorClassifier ||
        !fusion.subjectCheckRequiredBeforeImplementationCheckpoint ||
        fusion.directRuntimeFunctorCategoryCollapseAuthorized ||
        fusion.genericDeclarationProofIntegrationAuthorized ||
        fusion.genericCheckerChangeAuthorized ||
        fusion.newMathematicalRule ||
        proposal.selectedRuntimeObservations.length !== 5 ||
        proposal.boundedOracle.assertions.length !== 9
    ) {
        throw new CorePathindFixedSource1cProposalV7Error(
            'PATHIND_FIXED_SOURCE_V7_SCOPE_DRIFT',
            'The corrected exact 5/12/0/6 boundary drifted'
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
            'pathind-fixed-source-1c-v7-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindFixedSource1cProposalV7Error(
            'PATHIND_FIXED_SOURCE_V7_AUTHORIZATION_DRIFT',
            'Corrected proposal v7 became self-authorizing or widened'
        );
    }
    return proposal;
}
