/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v3.
 *
 * V3 preserves the v2 boundary but replaces its unreachable pre-prefix
 * Hom-classifier fusion with the exact decoded Functor-category object type
 * reached after the dependency runtime. It adds no rule or mathematics.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2,
    validateCorePathindInternalized1dProposalV2
} from './pathind_internalized_proposal_v2';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-3' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-03/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-003 as proposed.';

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

const proposalV2 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2;

const prePrefixRuleId =
    'pathind.internalized.' +
    'path-ind-functor-component-subject-fusion';

const postPrefixRuleId =
    'pathind.internalized.' +
    'path-ind-functor-component-post-prefix-subject-fusion';

const componentPostPrefixSubjectFusion = {
    order: 2,
    id: postPrefixRuleId,
    authority: 'derived-stable-post-prefix-presentation-fusion',
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
    policy: 'runtime-rewrite-derived-post-prefix-type-fusion',
    mathematicalRule: false,
    measuredLeft:
        'τ(Obj(Functor_cat(PathInd_src_catd(Z,x)[E],' +
        'PathInd_tgt_catd(Z,x)[E])))',
    measuredRight:
        'τ(Obj(Functor_cat(Fibre_cat(E,pathout_refl_obj(Z,x)),' +
        'Pi_cat(E))))'
} as const;

const correctedRuntimeRules = Object.freeze(
    proposalV2.exactImplementation.runtimeRules.map((rule, index) =>
        index === 2
            ? componentPostPrefixSubjectFusion
            : cloneData(rule)
    )
);

const correctedStages = proposalV2.exactImplementation
    .implementationStages.map(stage =>
        stage.id === 'internalized-runtime-projections'
            ? {
                ...cloneData(stage),
                rules: correctedRuntimeRules.map(rule => rule.id)
            }
            : cloneData(stage)
    );

const rawProposal = {
    ...cloneData(proposalV2),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3_REVISION,
    status: 'corrected-proposal-v3-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV2.parent),
        supersededProposalRevision: proposalV2.revision,
        supersededProposalCheckpoint: 'fbfc4dd',
        supersededReviewCheckpoint: '2a250fb',
        supersededLedgerCheckpoint: '2ede000',
        priorCounterevidence:
            cloneData(proposalV2.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'corrected-v2-runtime-compilation-with-in-memory-observer',
            correctedEvaluationBase:
                'Catd_cat(PathOut_cat(Z,x))',
            v2SupportRuleSubjectChecked: true,
            compiledLocalRuleCountBeforeFailure: 3,
            failingRule:
                'pathind.internalized.path-ind-functor-component',
            failureCode: 'INVALID_RUNTIME_RULE_TYPE',
            dependencyRulesAppliedBeforeLocalSupport: [
                'directed.category-hom.decode',
                'categorical.mixed-action.functor-classifier-definition'
            ],
            v2PrePrefixFusionMatched: false,
            v2PrePrefixFusionShadowedByDependencyPrefix: true,
            exactStableLeft:
                componentPostPrefixSubjectFusion.measuredLeft,
            exactStableRight:
                componentPostPrefixSubjectFusion.measuredRight,
            replacementRuleRequired: true,
            additionalRuntimeRuleRequired: false,
            temporaryObserversRetained: false,
            genericCheckerDiffEmpty: true
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-03',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-003',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV2.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/5/0/10',
        mathematicalRuntimeProjectionCount: 4,
        derivedRuntimeSupportRuleCount: 1
    },
    selectedPredecessor: {
        ...cloneData(proposalV2.selectedPredecessor),
        localImplementationDeltaIsFourFiveZeroTen: true,
        v2PrePrefixFusionRetained: false,
        v3PostPrefixFusionSelected: true
    },
    dependencyClosure: {
        ...cloneData(proposalV2.dependencyClosure),
        componentSubjectPresentationCorrection: {
            ruleId: postPrefixRuleId,
            measuredLeft:
                componentPostPrefixSubjectFusion.measuredLeft,
            measuredRight:
                componentPostPrefixSubjectFusion.measuredRight,
            exactScope:
                'PathInd_func-component-post-prefix-subject-type-only',
            replacesUnreachableV2PrePrefixFusion: true,
            wrapsStablePostPrefixPresentationUnderDecodedObjectClassifier:
                true,
            derivedFromActiveDefinitionsAndEquations: true,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            activeMathematicalRuleDelta: 0,
            additionalRuntimeRuleAuthorized: false,
            genericRuntimeMatcherChangeAuthorized: false,
            genericCheckerChangeAuthorized: false,
            inheritedProofProgramDependencyAuthorized: false,
            genericFixedEvaluationRuntimeImportAuthorized: false,
            alternatePathIndTypeAuthorized: false,
            alternateComponentBodyAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV2.validation),
        reasonLongAggregateOmitted:
            'post-prefix-replacement-is-immutable-data-only-and-' +
            'directly-gated'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v3-implementation',
        ...cloneData(proposalV2.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v2-implementation'
        ),
        'retaining-the-unreachable-v2-pre-prefix-fusion',
        'retaining-temporary-in-memory-diagnostic-observers'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v3-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV3 = typeof rawProposal;

export type CorePathindInternalized1dProposalV3ErrorCode =
    | 'PATHIND_INTERNALIZED_V3_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V3_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V3_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV3Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV3ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV3Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV3(
    proposal: CorePathindInternalized1dProposalV3 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3
): CorePathindInternalized1dProposalV3 {
    validateCorePathindInternalized1dProposalV2(proposalV2);
    const counterevidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-3' ||
        proposal.parent.supersededProposalRevision !== proposalV2.revision ||
        proposal.parent.supersededProposalCheckpoint !== 'fbfc4dd' ||
        proposal.parent.supersededReviewCheckpoint !== '2a250fb' ||
        proposal.parent.supersededLedgerCheckpoint !== '2ede000' ||
        counterevidence.correctedEvaluationBase !==
            'Catd_cat(PathOut_cat(Z,x))' ||
        !counterevidence.v2SupportRuleSubjectChecked ||
        counterevidence.compiledLocalRuleCountBeforeFailure !== 3 ||
        counterevidence.failureCode !== 'INVALID_RUNTIME_RULE_TYPE' ||
        counterevidence.failingRule !==
            'pathind.internalized.path-ind-functor-component' ||
        !sameData(
            counterevidence.dependencyRulesAppliedBeforeLocalSupport,
            [
                'directed.category-hom.decode',
                'categorical.mixed-action.functor-classifier-definition'
            ]
        ) ||
        counterevidence.v2PrePrefixFusionMatched ||
        !counterevidence.v2PrePrefixFusionShadowedByDependencyPrefix ||
        !counterevidence.replacementRuleRequired ||
        counterevidence.additionalRuntimeRuleRequired ||
        counterevidence.temporaryObserversRetained ||
        !counterevidence.genericCheckerDiffEmpty
    ) {
        throw new CorePathindInternalized1dProposalV3Error(
            'PATHIND_INTERNALIZED_V3_AUTHORITY_DRIFT',
            'The v2 checkpoint or exact post-prefix trace drifted'
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
        implementation.runtimeRules[2].id !== postPrefixRuleId ||
        implementation.runtimeRules.some(rule =>
            rule.id === prePrefixRuleId
        ) ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFourFiveZeroTen ||
        proposal.selectedPredecessor.v2PrePrefixFusionRetained ||
        !proposal.selectedPredecessor.v3PostPrefixFusionSelected ||
        correction.ruleId !== postPrefixRuleId ||
        !correction.replacesUnreachableV2PrePrefixFusion ||
        !correction
            .wrapsStablePostPrefixPresentationUnderDecodedObjectClassifier ||
        !correction.derivedFromActiveDefinitionsAndEquations ||
        !correction.subjectCheckRequiredBeforeImplementationCheckpoint ||
        correction.activeMathematicalRuleDelta !== 0 ||
        correction.additionalRuntimeRuleAuthorized ||
        correction.genericRuntimeMatcherChangeAuthorized ||
        correction.genericCheckerChangeAuthorized ||
        correction.inheritedProofProgramDependencyAuthorized ||
        correction.genericFixedEvaluationRuntimeImportAuthorized ||
        correction.alternatePathIndTypeAuthorized ||
        correction.alternateComponentBodyAuthorized ||
        proposal.typedLibraryConsumers.length !== 2 ||
        proposal.selectedRuntimeObservations.length !== 9 ||
        proposal.negativeConsumers.length !== 10 ||
        proposal.boundedOracle.assertions.length !== 11
    ) {
        throw new CorePathindInternalized1dProposalV3Error(
            'PATHIND_INTERNALIZED_V3_SCOPE_DRIFT',
            'The corrected exact post-prefix replacement boundary drifted'
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
            'pathind-internalized-1d-v3-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV3Error(
            'PATHIND_INTERNALIZED_V3_AUTHORIZATION_DRIFT',
            'Corrected proposal v3 became self-authorizing or widened'
        );
    }
    return proposal;
}
