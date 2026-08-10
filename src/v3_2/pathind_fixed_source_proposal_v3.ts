/**
 * Corrected PATHIND-TRUSTED-PROFILE-1C non-authorizing proposal v3.
 *
 * V3 preserves v2 and adds only the active displayed-functor object bridge at
 * authority line 9177.  Measured TypeScript rule admission reached the third
 * FibCov projection only after restoring the exact active Fibre signatures.
 */

import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2,
    validateCorePathindFixedSource1cProposalV2
} from './pathind_fixed_source_proposal_v2';

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3_REVISION =
    'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-3' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-FIXED-SOURCE-03/' +
    'D-TS-EMDASH-PATHIND-FIXED-SOURCE-003 as proposed.';

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

const proposalV2 = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2;

const displayedFunctorObjectRule = {
    order: 1,
    id: 'pathind.fixed-source.displayed-functor-object',
    authorityLine: 9177,
    sourceOwner: 'Obj',
    resultOwner: 'Obj',
    policy: 'runtime-rewrite'
} as const;

const correctedRuntimeRules = Object.freeze([
    cloneData(proposalV2.exactImplementation.runtimeRules[0]),
    displayedFunctorObjectRule,
    ...proposalV2.exactImplementation.runtimeRules
        .slice(1)
        .map((rule, index) => ({
            ...cloneData(rule),
            order: index + 2
        }))
]);

const rawProposal = {
    ...cloneData(proposalV2),
    revision: CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3_REVISION,
    status: 'corrected-proposal-v3-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV2.parent),
        supersededProposalRevision: proposalV2.revision,
        supersededProposalCheckpoint: '7413dd6',
        supersededReviewCheckpoint: '3421647',
        priorCounterevidence:
            cloneData(proposalV2.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'corrected-v2-runtime-compilation-with-active-signatures',
            exactActiveFibreSignaturesRestored: true,
            line7865AdmitsFirstTwoFibCovProjections: true,
            failingRule:
                'pathind.fixed-source.fib-cov-section-point',
            failingPhase: 'left-side-inference',
            failureCode: 'INVALID_RUNTIME_RULE_TYPE',
            normalizedMismatch:
                'object-classifier-versus-transfor-classifier',
            missingActiveAuthorityLine: 9177,
            predecessorDeclaresFunctordAndTransf: true,
            predecessorTransfersFunctordObjectProjection: false
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-FIXED-SOURCE-03',
        decisionId: 'D-TS-EMDASH-PATHIND-FIXED-SOURCE-003',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV2.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        exactBoundary: '5/8/0/6'
    },
    selectedPredecessor: {
        ...cloneData(proposalV2.selectedPredecessor),
        localImplementationDeltaIsFiveSevenZeroSix: false,
        localImplementationDeltaIsFiveEightZeroSix: true
    },
    dependencyClosure: {
        ...cloneData(proposalV2.dependencyClosure),
        displayedFunctorObjectCorrection: {
            sourceOwner: 'Functord_cat',
            resultOwner: 'Transf_cat',
            ownersAlreadyTransferred: true,
            activeAuthorityLine: 9177,
            ruleId:
                'pathind.fixed-source.displayed-functor-object',
            activeLeft: 'Obj(Functord_cat(K,E,D))',
            activeRight: 'Obj(Transf_cat(K,Cat_cat,E,D))',
            neededFor:
                'fib_cov_transf-as-displayed-functor-at-third-projection',
            genericCheckerChangeAuthorized: false,
            canonicalSignatureSubstitutionAuthorized: false,
            duplicateClassifierDeclarationAuthorized: false
        }
    },
    selectedRuntimeObservations: [
        'Obj(Functord_cat(K,E,D))-reduces-to-' +
            'Obj(Transf_cat(K,Cat_cat,E,D))',
        ...cloneData(proposalV2.selectedRuntimeObservations)
    ],
    boundedOracle: {
        ...cloneData(proposalV2.boundedOracle),
        assertions: [
            'displayed-functor-object-is-transfor-object',
            ...cloneData(proposalV2.boundedOracle.assertions)
        ]
    },
    validation: {
        ...cloneData(proposalV2.validation),
        reasonLongAggregateOmitted:
            'second-correction-is-immutable-data-only-and-directly-gated'
    },
    doesNotAuthorize: [
        'PATHIND-TRUSTED-PROFILE-1C-corrected-v3-implementation',
        ...cloneData(proposalV2.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHIND-TRUSTED-PROFILE-1C-corrected-v2-implementation'
        )
    ],
    nextDependencyState:
        'pathind-fixed-source-1c-v3-awaiting-separate-immutable-review'
} as const;

export type CorePathindFixedSource1cProposalV3 = typeof rawProposal;

export type CorePathindFixedSource1cProposalV3ErrorCode =
    | 'PATHIND_FIXED_SOURCE_V3_AUTHORITY_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V3_SCOPE_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V3_AUTHORIZATION_DRIFT';

export class CorePathindFixedSource1cProposalV3Error extends Error {
    constructor(
        public readonly code:
            CorePathindFixedSource1cProposalV3ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindFixedSource1cProposalV3Error';
    }
}

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3 =
    deepFreeze(rawProposal);

export function validateCorePathindFixedSource1cProposalV3(
    proposal: CorePathindFixedSource1cProposalV3 =
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3
): CorePathindFixedSource1cProposalV3 {
    validateCorePathindFixedSource1cProposalV2(proposalV2);
    if (
        proposal.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-3' ||
        proposal.parent.supersededProposalRevision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-2' ||
        proposal.parent.supersededProposalCheckpoint !== '7413dd6' ||
        proposal.parent.supersededReviewCheckpoint !== '3421647' ||
        proposal.parent.counterevidence.missingActiveAuthorityLine !== 9177 ||
        !proposal.parent.counterevidence.exactActiveFibreSignaturesRestored ||
        !proposal.parent.counterevidence
            .line7865AdmitsFirstTwoFibCovProjections ||
        !proposal.parent.counterevidence
            .predecessorDeclaresFunctordAndTransf ||
        proposal.parent.counterevidence
            .predecessorTransfersFunctordObjectProjection
    ) {
        throw new CorePathindFixedSource1cProposalV3Error(
            'PATHIND_FIXED_SOURCE_V3_AUTHORITY_DRIFT',
            'The v2 boundary or measured line-9177 counterevidence drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const correction =
        proposal.dependencyClosure.displayedFunctorObjectCorrection;
    if (
        implementation.trustedDeclarations.length !== 5 ||
        implementation.runtimeRules.length !== 8 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 6 ||
        implementation.exactBoundary !== '5/8/0/6' ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[1].authorityLine !== 9177 ||
        implementation.runtimeRules[1].id !==
            'pathind.fixed-source.displayed-functor-object' ||
        proposal.selectedPredecessor
            .localImplementationDeltaIsFiveSevenZeroSix ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFiveEightZeroSix ||
        correction.activeAuthorityLine !== 9177 ||
        !correction.ownersAlreadyTransferred ||
        correction.genericCheckerChangeAuthorized ||
        correction.canonicalSignatureSubstitutionAuthorized ||
        correction.duplicateClassifierDeclarationAuthorized ||
        proposal.selectedRuntimeObservations.length !== 5 ||
        proposal.boundedOracle.assertions.length !== 9
    ) {
        throw new CorePathindFixedSource1cProposalV3Error(
            'PATHIND_FIXED_SOURCE_V3_SCOPE_DRIFT',
            'The corrected exact 5/8/0/6 boundary drifted'
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
            'pathind-fixed-source-1c-v3-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindFixedSource1cProposalV3Error(
            'PATHIND_FIXED_SOURCE_V3_AUTHORIZATION_DRIFT',
            'Corrected proposal v3 became self-authorizing or widened'
        );
    }
    return proposal;
}
