/**
 * Corrected PATHOUT-LIBRARY-INTERNALIZED-1D non-authorizing proposal v4.
 *
 * V4 preserves v3 and adds one local subject-presentation fusion for the
 * final PathInd_transfd component projection. The fusion wraps the active
 * Catd/Functor comparison under Transf_cat; it adds no mathematics.
 */

import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3,
    validateCorePathindInternalized1dProposalV3
} from './pathind_internalized_proposal_v3';

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4_REVISION =
    'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-4' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-INTERNALIZED-04/' +
    'D-TS-EMDASH-PATHIND-INTERNALIZED-004 as proposed.';

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

const proposalV3 = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3;

const transfdSubjectFusion = {
    order: 4,
    id:
        'pathind.internalized.' +
        'path-ind-transfd-component-subject-fusion',
    authority: 'derived-transfor-category-presentation-fusion',
    authoritySymbols: [
        'Functord-definition',
        'Transf-definition',
        'Catd_cat-Functor_cat-proof-comparison',
        'PathInd_src_catd-definition',
        'PathInd_tgt_catd-definition'
    ],
    sourceOwner: 'τ',
    resultOwner: 'τ',
    policy: 'runtime-rewrite-derived-type-presentation-fusion',
    mathematicalRule: false,
    measuredLeft:
        'τ(Obj(Transf_cat(Catd_cat(PathOut_cat(Z,x)),Cat_cat,' +
        'PathInd_src_catd(Z,x),PathInd_tgt_catd(Z,x))))',
    measuredRight:
        'τ(Obj(Transf_cat(Functor_cat(PathOut_cat(Z,x),Cat_cat),' +
        'Cat_cat,PathInd_src_catd(Z,x),PathInd_tgt_catd(Z,x))))'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV3.exactImplementation.runtimeRules
        .slice(0, 4)
        .map(rule => cloneData(rule)),
    transfdSubjectFusion,
    ...proposalV3.exactImplementation.runtimeRules
        .slice(4)
        .map((rule, index) => ({
            ...cloneData(rule),
            order: index + 5
        }))
]);

const correctedStages = proposalV3.exactImplementation
    .implementationStages.map(stage =>
        stage.id === 'internalized-runtime-projections'
            ? {
                ...cloneData(stage),
                rules: correctedRuntimeRules.map(rule => rule.id)
            }
            : cloneData(stage)
    );

const rawProposal = {
    ...cloneData(proposalV3),
    revision: CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4_REVISION,
    status: 'corrected-proposal-v4-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV3.parent),
        supersededProposalRevision: proposalV3.revision,
        supersededProposalCheckpoint: '5a1d635',
        supersededReviewCheckpoint: '6694c87',
        supersededLedgerCheckpoint: 'e26091d',
        priorCounterevidence:
            cloneData(proposalV3.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'corrected-v3-runtime-compilation-with-in-memory-observer',
            compiledLocalRuleCountBeforeFailure: 4,
            v3PostPrefixSupportRuleSubjectChecked: true,
            pathIndFunctorComponentRuleSubjectChecked: true,
            failingRule:
                'pathind.internalized.path-ind-transfd-component',
            failureCode: 'INVALID_RUNTIME_RULE_TYPE',
            exactNormalizedActual: transfdSubjectFusion.measuredLeft,
            exactNormalizedExpected: transfdSubjectFusion.measuredRight,
            mismatchPath:
                'τ/Obj/Transf_cat/source-category',
            mismatchLeft:
                'Catd_cat(PathOut_cat(Z,x))',
            mismatchRight:
                'Functor_cat(PathOut_cat(Z,x),Cat_cat)',
            additionalSupportRuleRequired: true,
            additionalMathematicalRuleRequired: false,
            proofRuleRequired: false,
            temporaryObserverRetained: false,
            genericCheckerDiffEmpty: true
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-INTERNALIZED-04',
        decisionId: 'D-TS-EMDASH-PATHIND-INTERNALIZED-004',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV3.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        implementationStages: correctedStages,
        exactBoundary: '4/6/0/10',
        mathematicalRuntimeProjectionCount: 4,
        derivedRuntimeSupportRuleCount: 2
    },
    selectedPredecessor: {
        ...cloneData(proposalV3.selectedPredecessor),
        localImplementationDeltaIsFourFiveZeroTen: false,
        localImplementationDeltaIsFourSixZeroTen: true,
        v3PostPrefixFusionRetained: true,
        v4TransfdSubjectFusionSelected: true
    },
    dependencyClosure: {
        ...cloneData(proposalV3.dependencyClosure),
        transformationComponentSubjectPresentationCorrection: {
            ruleId: transfdSubjectFusion.id,
            measuredLeft: transfdSubjectFusion.measuredLeft,
            measuredRight: transfdSubjectFusion.measuredRight,
            exactScope:
                'PathInd_transfd-base-component-subject-type-only',
            wrapsCatdFunctorComparisonUnderTransforCategory: true,
            derivedFromActiveDefinitionsAndEquations: true,
            subjectCheckRequiredBeforeImplementationCheckpoint: true,
            activeMathematicalRuleDelta: 0,
            proofRuleDelta: 0,
            genericCategoryCollapseAuthorized: false,
            genericRuntimeMatcherChangeAuthorized: false,
            genericCheckerChangeAuthorized: false,
            inheritedProofProgramDependencyAuthorized: false,
            alternatePathIndTransfdTypeAuthorized: false,
            alternatePathIndTransfdComponentBodyAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV3.validation),
        reasonLongAggregateOmitted:
            'transfd-subject-fusion-is-immutable-data-only-and-' +
            'directly-gated'
    },
    doesNotAuthorize: [
        'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v4-implementation',
        ...cloneData(proposalV3.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHOUT-LIBRARY-INTERNALIZED-1D-corrected-v3-implementation'
        ),
        'a-generic-Catd_cat-to-Functor_cat-runtime-collapse',
        'retaining-temporary-transfd-diagnostic-observers'
    ],
    nextDependencyState:
        'pathind-internalized-1d-v4-awaiting-separate-immutable-review'
} as const;

export type CorePathindInternalized1dProposalV4 = typeof rawProposal;

export type CorePathindInternalized1dProposalV4ErrorCode =
    | 'PATHIND_INTERNALIZED_V4_AUTHORITY_DRIFT'
    | 'PATHIND_INTERNALIZED_V4_SCOPE_DRIFT'
    | 'PATHIND_INTERNALIZED_V4_AUTHORIZATION_DRIFT';

export class CorePathindInternalized1dProposalV4Error extends Error {
    constructor(
        public readonly code:
            CorePathindInternalized1dProposalV4ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindInternalized1dProposalV4Error';
    }
}

export const CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4 =
    deepFreeze(rawProposal);

export function validateCorePathindInternalized1dProposalV4(
    proposal: CorePathindInternalized1dProposalV4 =
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4
): CorePathindInternalized1dProposalV4 {
    validateCorePathindInternalized1dProposalV3(proposalV3);
    const counterevidence = proposal.parent.counterevidence;
    if (
        proposal.revision !==
            'PATHOUT-LIBRARY-INTERNALIZED-1D-PROPOSAL-4' ||
        proposal.parent.supersededProposalRevision !== proposalV3.revision ||
        proposal.parent.supersededProposalCheckpoint !== '5a1d635' ||
        proposal.parent.supersededReviewCheckpoint !== '6694c87' ||
        proposal.parent.supersededLedgerCheckpoint !== 'e26091d' ||
        counterevidence.compiledLocalRuleCountBeforeFailure !== 4 ||
        !counterevidence.v3PostPrefixSupportRuleSubjectChecked ||
        !counterevidence.pathIndFunctorComponentRuleSubjectChecked ||
        counterevidence.failureCode !== 'INVALID_RUNTIME_RULE_TYPE' ||
        counterevidence.failingRule !==
            'pathind.internalized.path-ind-transfd-component' ||
        counterevidence.mismatchLeft !==
            'Catd_cat(PathOut_cat(Z,x))' ||
        counterevidence.mismatchRight !==
            'Functor_cat(PathOut_cat(Z,x),Cat_cat)' ||
        !counterevidence.additionalSupportRuleRequired ||
        counterevidence.additionalMathematicalRuleRequired ||
        counterevidence.proofRuleRequired ||
        counterevidence.temporaryObserverRetained ||
        !counterevidence.genericCheckerDiffEmpty
    ) {
        throw new CorePathindInternalized1dProposalV4Error(
            'PATHIND_INTERNALIZED_V4_AUTHORITY_DRIFT',
            'The v3 checkpoint or exact transfd subject trace drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const correction = proposal.dependencyClosure
        .transformationComponentSubjectPresentationCorrection;
    if (
        implementation.trustedDeclarations.length !== 4 ||
        implementation.runtimeRules.length !== 6 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 10 ||
        implementation.exactBoundary !== '4/6/0/10' ||
        implementation.mathematicalRuntimeProjectionCount !== 4 ||
        implementation.derivedRuntimeSupportRuleCount !== 2 ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[4].id !== transfdSubjectFusion.id ||
        proposal.selectedPredecessor
            .localImplementationDeltaIsFourFiveZeroTen ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFourSixZeroTen ||
        !proposal.selectedPredecessor.v3PostPrefixFusionRetained ||
        !proposal.selectedPredecessor.v4TransfdSubjectFusionSelected ||
        correction.ruleId !== transfdSubjectFusion.id ||
        !correction.wrapsCatdFunctorComparisonUnderTransforCategory ||
        !correction.derivedFromActiveDefinitionsAndEquations ||
        !correction.subjectCheckRequiredBeforeImplementationCheckpoint ||
        correction.activeMathematicalRuleDelta !== 0 ||
        correction.proofRuleDelta !== 0 ||
        correction.genericCategoryCollapseAuthorized ||
        correction.genericRuntimeMatcherChangeAuthorized ||
        correction.genericCheckerChangeAuthorized ||
        correction.inheritedProofProgramDependencyAuthorized ||
        correction.alternatePathIndTransfdTypeAuthorized ||
        correction.alternatePathIndTransfdComponentBodyAuthorized ||
        proposal.typedLibraryConsumers.length !== 2 ||
        proposal.selectedRuntimeObservations.length !== 9 ||
        proposal.negativeConsumers.length !== 10 ||
        proposal.boundedOracle.assertions.length !== 11
    ) {
        throw new CorePathindInternalized1dProposalV4Error(
            'PATHIND_INTERNALIZED_V4_SCOPE_DRIFT',
            'The exact 4/6/0/10 transfd correction boundary drifted'
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
            'pathind-internalized-1d-v4-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindInternalized1dProposalV4Error(
            'PATHIND_INTERNALIZED_V4_AUTHORIZATION_DRIFT',
            'Corrected proposal v4 became self-authorizing or widened'
        );
    }
    return proposal;
}
