/**
 * Corrected PATHIND-TRUSTED-PROFILE-1C non-authorizing proposal v6.
 *
 * V6 preserves v5 and adds one subject-checked fusion of the exact residual
 * measured at the third FibCov projection. The fusion follows the complete
 * active reduction path without reversing Transf or adding declaration
 * unfolding to the generic conversion engine.
 */

import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5,
    validateCorePathindFixedSource1cProposalV5
} from './pathind_fixed_source_proposal_v5';

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6_REVISION =
    'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-6' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-FIXED-SOURCE-06/' +
    'D-TS-EMDASH-PATHIND-FIXED-SOURCE-006 as proposed.';

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

const proposalV5 = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5;

const fibreCovariantTargetSectionFusionRule = {
    order: 4,
    id: 'pathind.fixed-source.fib-cov-target-section-fusion',
    derivedFromAuthorityLines: [
        5481,
        7865,
        8419,
        9177,
        13765,
        13767,
        13773,
        13775,
        13923,
        13928
    ],
    sourceOwner: 'Obj',
    resultOwner: 'Obj',
    policy: 'runtime-rewrite-derived-head-fusion'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV5.exactImplementation.runtimeRules
        .slice(0, 4)
        .map(rule => cloneData(rule)),
    fibreCovariantTargetSectionFusionRule,
    ...proposalV5.exactImplementation.runtimeRules
        .slice(4)
        .map((rule, index) => ({
            ...cloneData(rule),
            order: index + 5
        }))
]);

const rawProposal = {
    ...cloneData(proposalV5),
    revision: CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6_REVISION,
    status: 'corrected-proposal-v6-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV5.parent),
        supersededProposalRevision: proposalV5.revision,
        supersededProposalCheckpoint: '7219828',
        supersededReviewCheckpoint: '3f95e7c',
        priorCounterevidence:
            cloneData(proposalV5.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'corrected-v5-runtime-compilation-with-exact-owner-trace',
            failingRule:
                'pathind.fixed-source.fib-cov-section-point',
            failingPhase: 'left-side-inference',
            failureCode: 'INVALID_RUNTIME_RULE_TYPE',
            exactResidualLeft:
                'Obj(fapp0(K,Cat_cat,FibCov_target_catd(K,E),x))',
            exactResidualRight:
                'Transf(K,Cat_cat,Rep_catd(K,x),E)',
            v4DisplayedHomFusionSubjectCheckedButNotReached: true,
            v5TransforDeltaSubjectCheckedButLeftStillBlocked: true,
            genericConversionDoesNotUnfoldNamedDeclarationBodies: true,
            directForwardFusionRequired: true,
            diagnosticCheckerHookRemovedCompletely: true
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-FIXED-SOURCE-06',
        decisionId: 'D-TS-EMDASH-PATHIND-FIXED-SOURCE-006',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV5.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        exactBoundary: '5/11/0/6'
    },
    selectedPredecessor: {
        ...cloneData(proposalV5.selectedPredecessor),
        localImplementationDeltaIsFiveTenZeroSix: false,
        localImplementationDeltaIsFiveElevenZeroSix: true
    },
    dependencyClosure: {
        ...cloneData(proposalV5.dependencyClosure),
        fibreCovariantTargetSectionWeakHeadFusion: {
            ruleId:
                'pathind.fixed-source.fib-cov-target-section-fusion',
            exactLeft:
                'Obj(fapp0(K,Cat_cat,FibCov_target_catd(K,E),x))',
            exactRight:
                'Obj(Transf_cat(K,Cat_cat,Rep_catd(K,x),E))',
            derivedFromActiveRuntimeAndTransparentLines:
                cloneData(
                    fibreCovariantTargetSectionFusionRule
                        .derivedFromAuthorityLines
                ),
            subjectCheckedByGenericRuntimeCompiler: true,
            rightSidePreservesForwardTransfDeltaOrientation: true,
            newMathematicalRule: false,
            declarationUnfoldingEngineAuthorized: false,
            genericCheckerChangeAuthorized: false,
            alternateFibCovSignatureOrBodyAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV5.validation),
        reasonLongAggregateOmitted:
            'exact-residual-fusion-is-immutable-data-only-and-directly-gated'
    },
    doesNotAuthorize: [
        'PATHIND-TRUSTED-PROFILE-1C-corrected-v6-implementation',
        ...cloneData(proposalV5.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHIND-TRUSTED-PROFILE-1C-corrected-v5-implementation'
        ),
        'generic-declaration-unfolding-during-conversion',
        'retaining-the-temporary-checker-diagnostic-hook'
    ],
    nextDependencyState:
        'pathind-fixed-source-1c-v6-awaiting-separate-immutable-review'
} as const;

export type CorePathindFixedSource1cProposalV6 = typeof rawProposal;

export type CorePathindFixedSource1cProposalV6ErrorCode =
    | 'PATHIND_FIXED_SOURCE_V6_AUTHORITY_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V6_SCOPE_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V6_AUTHORIZATION_DRIFT';

export class CorePathindFixedSource1cProposalV6Error extends Error {
    constructor(
        public readonly code:
            CorePathindFixedSource1cProposalV6ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindFixedSource1cProposalV6Error';
    }
}

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6 =
    deepFreeze(rawProposal);

export function validateCorePathindFixedSource1cProposalV6(
    proposal: CorePathindFixedSource1cProposalV6 =
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6
): CorePathindFixedSource1cProposalV6 {
    validateCorePathindFixedSource1cProposalV5(proposalV5);
    if (
        proposal.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-6' ||
        proposal.parent.supersededProposalRevision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-5' ||
        proposal.parent.supersededProposalCheckpoint !== '7219828' ||
        proposal.parent.supersededReviewCheckpoint !== '3f95e7c' ||
        proposal.parent.counterevidence.exactResidualLeft !==
            'Obj(fapp0(K,Cat_cat,FibCov_target_catd(K,E),x))' ||
        proposal.parent.counterevidence.exactResidualRight !==
            'Transf(K,Cat_cat,Rep_catd(K,x),E)' ||
        !proposal.parent.counterevidence
            .genericConversionDoesNotUnfoldNamedDeclarationBodies ||
        !proposal.parent.counterevidence
            .diagnosticCheckerHookRemovedCompletely
    ) {
        throw new CorePathindFixedSource1cProposalV6Error(
            'PATHIND_FIXED_SOURCE_V6_AUTHORITY_DRIFT',
            'The v5 boundary or exact measured residual drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const fusion = proposal.dependencyClosure
        .fibreCovariantTargetSectionWeakHeadFusion;
    if (
        implementation.trustedDeclarations.length !== 5 ||
        implementation.runtimeRules.length !== 11 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 6 ||
        implementation.exactBoundary !== '5/11/0/6' ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[4].id !==
            'pathind.fixed-source.fib-cov-target-section-fusion' ||
        proposal.selectedPredecessor
            .localImplementationDeltaIsFiveTenZeroSix ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFiveElevenZeroSix ||
        !fusion.subjectCheckedByGenericRuntimeCompiler ||
        !fusion.rightSidePreservesForwardTransfDeltaOrientation ||
        fusion.newMathematicalRule ||
        fusion.declarationUnfoldingEngineAuthorized ||
        fusion.genericCheckerChangeAuthorized ||
        fusion.alternateFibCovSignatureOrBodyAuthorized ||
        proposal.selectedRuntimeObservations.length !== 5 ||
        proposal.boundedOracle.assertions.length !== 9
    ) {
        throw new CorePathindFixedSource1cProposalV6Error(
            'PATHIND_FIXED_SOURCE_V6_SCOPE_DRIFT',
            'The corrected exact 5/11/0/6 boundary drifted'
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
            'pathind-fixed-source-1c-v6-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindFixedSource1cProposalV6Error(
            'PATHIND_FIXED_SOURCE_V6_AUTHORIZATION_DRIFT',
            'Corrected proposal v6 became self-authorizing or widened'
        );
    }
    return proposal;
}
