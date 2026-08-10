/**
 * Corrected PATHIND-TRUSTED-PROFILE-1C non-authorizing proposal v2.
 *
 * V2 preserves proposal v1 and adds only the active hom_con object projection
 * at authority line 7865.  Measured TypeScript rule admission showed that the
 * selected predecessor declares hom_con but does not transfer this rule.
 */

import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL,
    validateCorePathindFixedSource1cProposal
} from './pathind_fixed_source_proposal';
import {
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT
} from './pathout_trust_boundary_audit';

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2_REVISION =
    'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-2' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-FIXED-SOURCE-02/' +
    'D-TS-EMDASH-PATHIND-FIXED-SOURCE-002 as proposed.';

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

const proposalV1 = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL;

const homConObjectRule = {
    order: 0,
    id: 'pathind.fixed-source.contravariant-representable-object',
    authorityLine: 7865,
    sourceOwner: 'fapp0',
    resultOwner: 'Hom_cat',
    policy: 'runtime-rewrite'
} as const;

const correctedRuntimeRules = Object.freeze([
    homConObjectRule,
    ...proposalV1.exactImplementation.runtimeRules.map((rule, index) => ({
        ...cloneData(rule),
        order: index + 1
    }))
]);

const rawProposal = {
    ...cloneData(proposalV1),
    revision: CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2_REVISION,
    status: 'corrected-proposal-v2-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV1.parent),
        supersededProposalRevision: proposalV1.revision,
        supersededProposalCheckpoint: 'cc639fc',
        supersededReviewCheckpoint: '2deae91',
        counterevidence: {
            measuredDuring:
                'first-PATHIND-TRUSTED-PROFILE-1C-runtime-compilation',
            failingRule:
                'pathind.fixed-source.fib-cov-package-component',
            failureCode: 'INVALID_RUNTIME_RULE_TYPE',
            normalizedMismatch:
                'functor-classifier-versus-hom-classifier',
            missingActiveAuthorityLine: 7865,
            predecessorDeclaresHomCon: true,
            predecessorTransfersHomConObjectProjection: false
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-FIXED-SOURCE-02',
        decisionId: 'D-TS-EMDASH-PATHIND-FIXED-SOURCE-002',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV1.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        exactBoundary: '5/7/0/6'
    },
    selectedPredecessor: {
        ...cloneData(proposalV1.selectedPredecessor),
        localImplementationDeltaIsFiveSixZeroSix: false,
        localImplementationDeltaIsFiveSevenZeroSix: true
    },
    dependencyClosure: {
        ...cloneData(proposalV1.dependencyClosure),
        contravariantRepresentableObjectCorrection: {
            owner: 'hom_con',
            ownerAlreadyTransferred: true,
            activeAuthorityLine: 7865,
            ruleId:
                'pathind.fixed-source.' +
                'contravariant-representable-object',
            activeLeft: 'fapp0(hom_con(A,W,B,F),x)',
            activeRight: 'Hom_cat(A,fapp0(F,x),W)',
            neededFor:
                'FibCov_target(E)[x]-to-Hom(Catd(K),Rep(x),E)',
            genericCheckerChangeAuthorized: false,
            alternativeFibCovBodyAuthorized: false,
            duplicateHomConDeclarationAuthorized: false
        }
    },
    selectedRuntimeObservations: [
        'FibCov_target(E)[x]-reduces-to-Hom(Catd(K),Rep(x),E)',
        ...cloneData(proposalV1.selectedRuntimeObservations)
    ],
    boundedOracle: {
        ...cloneData(proposalV1.boundedOracle),
        assertions: [
            'hom-con-object-is-Hom-Catd-Rep-E',
            ...cloneData(proposalV1.boundedOracle.assertions)
        ]
    },
    validation: {
        ...cloneData(proposalV1.validation),
        reasonLongAggregateOmitted:
            'correction-is-immutable-data-only-and-direct-gates-cover-it'
    },
    doesNotAuthorize: [
        'PATHIND-TRUSTED-PROFILE-1C-corrected-v2-implementation',
        ...cloneData(proposalV1.doesNotAuthorize).filter(entry =>
            entry !== 'PATHIND-TRUSTED-PROFILE-1C-implementation'
        )
    ],
    nextDependencyState:
        'pathind-fixed-source-1c-v2-awaiting-separate-immutable-review'
} as const;

export type CorePathindFixedSource1cProposalV2 = typeof rawProposal;

export type CorePathindFixedSource1cProposalV2ErrorCode =
    | 'PATHIND_FIXED_SOURCE_V2_AUTHORITY_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V2_SCOPE_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V2_AUTHORIZATION_DRIFT';

export class CorePathindFixedSource1cProposalV2Error extends Error {
    constructor(
        public readonly code:
            CorePathindFixedSource1cProposalV2ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindFixedSource1cProposalV2Error';
    }
}

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2 =
    deepFreeze(rawProposal);

export function validateCorePathindFixedSource1cProposalV2(
    proposal: CorePathindFixedSource1cProposalV2 =
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2
): CorePathindFixedSource1cProposalV2 {
    validateCorePathindFixedSource1cProposal(proposalV1);
    if (
        proposal.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-2' ||
        proposal.parent.auditRevision !==
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT.revision ||
        proposal.parent.supersededProposalRevision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-1' ||
        proposal.parent.supersededProposalCheckpoint !== 'cc639fc' ||
        proposal.parent.supersededReviewCheckpoint !== '2deae91' ||
        proposal.parent.counterevidence.missingActiveAuthorityLine !== 7865 ||
        !proposal.parent.counterevidence.predecessorDeclaresHomCon ||
        proposal.parent.counterevidence
            .predecessorTransfersHomConObjectProjection
    ) {
        throw new CorePathindFixedSource1cProposalV2Error(
            'PATHIND_FIXED_SOURCE_V2_AUTHORITY_DRIFT',
            'The v1 boundary or measured line-7865 counterevidence drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const correction =
        proposal.dependencyClosure
            .contravariantRepresentableObjectCorrection;
    if (
        implementation.trustedDeclarations.length !== 5 ||
        implementation.runtimeRules.length !== 7 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 6 ||
        implementation.exactBoundary !== '5/7/0/6' ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[0].authorityLine !== 7865 ||
        implementation.runtimeRules[0].id !==
            'pathind.fixed-source.contravariant-representable-object' ||
        proposal.selectedPredecessor
            .localImplementationDeltaIsFiveSixZeroSix ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFiveSevenZeroSix ||
        correction.activeAuthorityLine !== 7865 ||
        correction.owner !== 'hom_con' ||
        !correction.ownerAlreadyTransferred ||
        correction.genericCheckerChangeAuthorized ||
        correction.alternativeFibCovBodyAuthorized ||
        correction.duplicateHomConDeclarationAuthorized ||
        proposal.selectedRuntimeObservations.length !== 4 ||
        proposal.boundedOracle.assertions.length !== 8
    ) {
        throw new CorePathindFixedSource1cProposalV2Error(
            'PATHIND_FIXED_SOURCE_V2_SCOPE_DRIFT',
            'The corrected exact 5/7/0/6 boundary drifted'
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
            'pathind-fixed-source-1c-v2-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindFixedSource1cProposalV2Error(
            'PATHIND_FIXED_SOURCE_V2_AUTHORIZATION_DRIFT',
            'Corrected proposal v2 became self-authorizing or widened'
        );
    }
    return proposal;
}
