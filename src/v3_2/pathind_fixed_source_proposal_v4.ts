/**
 * Corrected PATHIND-TRUSTED-PROFILE-1C non-authorizing proposal v4.
 *
 * V4 preserves v3 and adds one subject-checked weak-head fusion derived only
 * from active lines 5481 and 9177. The generic runtime intentionally does not
 * normalize a nested Hom_cat before matching the surrounding Obj head.
 */

import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3,
    validateCorePathindFixedSource1cProposalV3
} from './pathind_fixed_source_proposal_v3';

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4_REVISION =
    'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-4' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-FIXED-SOURCE-04/' +
    'D-TS-EMDASH-PATHIND-FIXED-SOURCE-004 as proposed.';

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

const proposalV3 = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3;

const displayedHomObjectFusionRule = {
    order: 2,
    id: 'pathind.fixed-source.displayed-hom-object-fusion',
    authorityLine: 9177,
    derivedFromAuthorityLines: [5481, 9177],
    sourceOwner: 'Obj',
    resultOwner: 'Obj',
    policy: 'runtime-rewrite-derived-head-fusion'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV3.exactImplementation.runtimeRules
        .slice(0, 2)
        .map(rule => cloneData(rule)),
    displayedHomObjectFusionRule,
    ...proposalV3.exactImplementation.runtimeRules
        .slice(2)
        .map((rule, index) => ({
            ...cloneData(rule),
            order: index + 3
        }))
]);

const rawProposal = {
    ...cloneData(proposalV3),
    revision: CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4_REVISION,
    status: 'corrected-proposal-v4-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV3.parent),
        supersededProposalRevision: proposalV3.revision,
        supersededProposalCheckpoint: 'bfe09e3',
        supersededReviewCheckpoint: '880593e',
        priorCounterevidence:
            cloneData(proposalV3.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'corrected-v3-runtime-compilation-with-lines-7865-9177',
            failingRule:
                'pathind.fixed-source.fib-cov-section-point',
            failingPhase: 'left-side-inference',
            failureCode: 'INVALID_RUNTIME_RULE_TYPE',
            normalizedMismatch:
                'object-classifier-versus-transfor-classifier',
            line9177RegisteredButNestedHomCatNotNormalized: true,
            executionStrategy: 'head-only-no-nested-pattern-normalization',
            measuredOuterHead: 'Obj',
            measuredNestedHead: 'Hom_cat(Catd_cat(K),E,D)',
            requiredDerivedFromAuthorityLines: [5481, 9177]
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-FIXED-SOURCE-04',
        decisionId: 'D-TS-EMDASH-PATHIND-FIXED-SOURCE-004',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV3.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        exactBoundary: '5/9/0/6'
    },
    selectedPredecessor: {
        ...cloneData(proposalV3.selectedPredecessor),
        localImplementationDeltaIsFiveEightZeroSix: false,
        localImplementationDeltaIsFiveNineZeroSix: true
    },
    dependencyClosure: {
        ...cloneData(proposalV3.dependencyClosure),
        displayedHomObjectWeakHeadFusion: {
            executionStrategy: 'head-only-no-nested-pattern-normalization',
            measuredOuterHead: 'Obj',
            nestedActiveFirstStep:
                'Hom_cat(Catd_cat(K),E,D)-to-Functord_cat(K,E,D)',
            outerActiveSecondStep:
                'Obj(Functord_cat(K,E,D))-to-' +
                'Obj(Transf_cat(K,Cat_cat,E,D))',
            ruleId:
                'pathind.fixed-source.displayed-hom-object-fusion',
            derivedFromActiveRuntimeLines: [5481, 9177],
            fusedLeft: 'Obj(Hom_cat(Catd_cat(K),E,D))',
            fusedRight: 'Obj(Transf_cat(K,Cat_cat,E,D))',
            subjectCheckedByGenericRuntimeCompiler: true,
            newMathematicalRule: false,
            nestedNormalizationEngineAuthorized: false,
            genericCheckerChangeAuthorized: false,
            canonicalSignatureSubstitutionAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV3.validation),
        reasonLongAggregateOmitted:
            'weak-head-correction-is-immutable-data-only-and-directly-gated'
    },
    doesNotAuthorize: [
        'PATHIND-TRUSTED-PROFILE-1C-corrected-v4-implementation',
        ...cloneData(proposalV3.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHIND-TRUSTED-PROFILE-1C-corrected-v3-implementation'
        ),
        'generic-nested-runtime-normalization'
    ],
    nextDependencyState:
        'pathind-fixed-source-1c-v4-awaiting-separate-immutable-review'
} as const;

export type CorePathindFixedSource1cProposalV4 = typeof rawProposal;

export type CorePathindFixedSource1cProposalV4ErrorCode =
    | 'PATHIND_FIXED_SOURCE_V4_AUTHORITY_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V4_SCOPE_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V4_AUTHORIZATION_DRIFT';

export class CorePathindFixedSource1cProposalV4Error extends Error {
    constructor(
        public readonly code:
            CorePathindFixedSource1cProposalV4ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindFixedSource1cProposalV4Error';
    }
}

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4 =
    deepFreeze(rawProposal);

export function validateCorePathindFixedSource1cProposalV4(
    proposal: CorePathindFixedSource1cProposalV4 =
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4
): CorePathindFixedSource1cProposalV4 {
    validateCorePathindFixedSource1cProposalV3(proposalV3);
    if (
        proposal.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-4' ||
        proposal.parent.supersededProposalRevision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-3' ||
        proposal.parent.supersededProposalCheckpoint !== 'bfe09e3' ||
        proposal.parent.supersededReviewCheckpoint !== '880593e' ||
        !proposal.parent.counterevidence
            .line9177RegisteredButNestedHomCatNotNormalized ||
        proposal.parent.counterevidence.executionStrategy !==
            'head-only-no-nested-pattern-normalization' ||
        !sameData(
            proposal.parent.counterevidence
                .requiredDerivedFromAuthorityLines,
            [5481, 9177]
        )
    ) {
        throw new CorePathindFixedSource1cProposalV4Error(
            'PATHIND_FIXED_SOURCE_V4_AUTHORITY_DRIFT',
            'The v3 boundary or measured weak-head counterevidence drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const fusion =
        proposal.dependencyClosure.displayedHomObjectWeakHeadFusion;
    if (
        implementation.trustedDeclarations.length !== 5 ||
        implementation.runtimeRules.length !== 9 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 6 ||
        implementation.exactBoundary !== '5/9/0/6' ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[2].id !==
            'pathind.fixed-source.displayed-hom-object-fusion' ||
        !sameData(
            implementation.runtimeRules[2].derivedFromAuthorityLines,
            [5481, 9177]
        ) ||
        proposal.selectedPredecessor
            .localImplementationDeltaIsFiveEightZeroSix ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFiveNineZeroSix ||
        !fusion.subjectCheckedByGenericRuntimeCompiler ||
        fusion.newMathematicalRule ||
        fusion.nestedNormalizationEngineAuthorized ||
        fusion.genericCheckerChangeAuthorized ||
        fusion.canonicalSignatureSubstitutionAuthorized ||
        proposal.selectedRuntimeObservations.length !== 5 ||
        proposal.boundedOracle.assertions.length !== 9
    ) {
        throw new CorePathindFixedSource1cProposalV4Error(
            'PATHIND_FIXED_SOURCE_V4_SCOPE_DRIFT',
            'The corrected exact 5/9/0/6 boundary drifted'
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
            'pathind-fixed-source-1c-v4-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindFixedSource1cProposalV4Error(
            'PATHIND_FIXED_SOURCE_V4_AUTHORIZATION_DRIFT',
            'Corrected proposal v4 became self-authorizing or widened'
        );
    }
    return proposal;
}
