/**
 * Corrected PATHIND-TRUSTED-PROFILE-1C non-authorizing proposal v5.
 *
 * V5 preserves v4 and imports the active transparent Transf-classifier delta
 * omitted by this predecessor's runtime chain. The v4 fusion subject-checks,
 * but its Obj(Transf_cat) result cannot meet the generic Core signature's
 * Transf alias until active source lines 9150-9151 are executable.
 */

import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4,
    validateCorePathindFixedSource1cProposalV4
} from './pathind_fixed_source_proposal_v4';

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5_REVISION =
    'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-5' as const;

const DECISION_QUESTION =
    'Approve H-TS-EMDASH-PATHIND-FIXED-SOURCE-05/' +
    'D-TS-EMDASH-PATHIND-FIXED-SOURCE-005 as proposed.';

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

const proposalV4 = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4;

const transforClassifierDeltaRule = {
    order: 3,
    id: 'pathind.fixed-source.transfor-classifier-delta',
    authorityLine: 9151,
    authorityLines: [9150, 9151],
    sourceOwner: 'Transf',
    resultOwner: 'Obj',
    policy: 'runtime-rewrite-active-transparent-definition'
} as const;

const correctedRuntimeRules = Object.freeze([
    ...proposalV4.exactImplementation.runtimeRules
        .slice(0, 3)
        .map(rule => cloneData(rule)),
    transforClassifierDeltaRule,
    ...proposalV4.exactImplementation.runtimeRules
        .slice(3)
        .map((rule, index) => ({
            ...cloneData(rule),
            order: index + 4
        }))
]);

const rawProposal = {
    ...cloneData(proposalV4),
    revision: CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5_REVISION,
    status: 'corrected-proposal-v5-awaiting-separate-review',
    parent: {
        ...cloneData(proposalV4.parent),
        supersededProposalRevision: proposalV4.revision,
        supersededProposalCheckpoint: 'f4101e2',
        supersededReviewCheckpoint: '397472f',
        priorCounterevidence:
            cloneData(proposalV4.parent.counterevidence),
        counterevidence: {
            measuredDuring:
                'corrected-v4-runtime-compilation-with-displayed-hom-fusion',
            failingRule:
                'pathind.fixed-source.fib-cov-section-point',
            failingPhase: 'left-side-inference',
            failureCode: 'INVALID_RUNTIME_RULE_TYPE',
            normalizedMismatch:
                'object-classifier-versus-transfor-classifier',
            displayedHomObjectFusionSubjectChecked: true,
            displayedHomObjectFusionInsufficient: true,
            actualStableClassifier: 'Obj(Transf_cat(K,Cat_cat,E,D))',
            expectedGenericCoreClassifier: 'Transf(K,Cat_cat,E,D)',
            activeTransparentDeltaAuthorityLines: [9150, 9151],
            predecessorImportsDeclarationLinkageButOmitsRuntimeDelta: true,
            measuredCompileExitedBeforeLibraryCompilation: true
        }
    },
    decision: {
        gate: 'H-TS-EMDASH-PATHIND-FIXED-SOURCE-05',
        decisionId: 'D-TS-EMDASH-PATHIND-FIXED-SOURCE-005',
        question: DECISION_QUESTION,
        status: 'proposal-only',
        implementationAuthorized: false,
        separateImmutableReviewRequired: true,
        humanDecisionSupersedes: true
    },
    exactImplementation: {
        ...cloneData(proposalV4.exactImplementation),
        runtimeRules: correctedRuntimeRules,
        exactBoundary: '5/10/0/6'
    },
    selectedPredecessor: {
        ...cloneData(proposalV4.selectedPredecessor),
        localImplementationDeltaIsFiveNineZeroSix: false,
        localImplementationDeltaIsFiveTenZeroSix: true
    },
    dependencyClosure: {
        ...cloneData(proposalV4.dependencyClosure),
        transforClassifierTransparentDelta: {
            ruleId:
                'pathind.fixed-source.transfor-classifier-delta',
            activeAuthorityLines: [9150, 9151],
            activeDefinition:
                'Transf(A,B,F,G)-is-Obj(Transf_cat(A,B,F,G))',
            sourceOwner: 'Transf',
            resultOwner: 'Obj',
            alreadyTransferredInSiblingProfile:
                'categorical.transfor-classifier.delta',
            absentFromSelectedPredecessorRuntimeChain: true,
            declarationOwnerAlreadyPresent: true,
            duplicateDeclarationAuthorized: false,
            newMathematicalRule: false,
            genericCheckerChangeAuthorized: false,
            reversedActiveReductionAuthorized: false
        }
    },
    validation: {
        ...cloneData(proposalV4.validation),
        reasonLongAggregateOmitted:
            'transparent-delta-correction-is-immutable-data-only-and-' +
            'directly-gated'
    },
    doesNotAuthorize: [
        'PATHIND-TRUSTED-PROFILE-1C-corrected-v5-implementation',
        ...cloneData(proposalV4.doesNotAuthorize).filter(entry =>
            entry !==
                'PATHIND-TRUSTED-PROFILE-1C-corrected-v4-implementation'
        ),
        'reversing-the-active-Transf-delta',
        'importing-the-whole-fibred-product-runtime-profile'
    ],
    nextDependencyState:
        'pathind-fixed-source-1c-v5-awaiting-separate-immutable-review'
} as const;

export type CorePathindFixedSource1cProposalV5 = typeof rawProposal;

export type CorePathindFixedSource1cProposalV5ErrorCode =
    | 'PATHIND_FIXED_SOURCE_V5_AUTHORITY_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V5_SCOPE_DRIFT'
    | 'PATHIND_FIXED_SOURCE_V5_AUTHORIZATION_DRIFT';

export class CorePathindFixedSource1cProposalV5Error extends Error {
    constructor(
        public readonly code:
            CorePathindFixedSource1cProposalV5ErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CorePathindFixedSource1cProposalV5Error';
    }
}

export const CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5 =
    deepFreeze(rawProposal);

export function validateCorePathindFixedSource1cProposalV5(
    proposal: CorePathindFixedSource1cProposalV5 =
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5
): CorePathindFixedSource1cProposalV5 {
    validateCorePathindFixedSource1cProposalV4(proposalV4);
    if (
        proposal.revision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-5' ||
        proposal.parent.supersededProposalRevision !==
            'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-4' ||
        proposal.parent.supersededProposalCheckpoint !== 'f4101e2' ||
        proposal.parent.supersededReviewCheckpoint !== '397472f' ||
        !proposal.parent.counterevidence
            .displayedHomObjectFusionSubjectChecked ||
        !proposal.parent.counterevidence
            .displayedHomObjectFusionInsufficient ||
        !proposal.parent.counterevidence
            .predecessorImportsDeclarationLinkageButOmitsRuntimeDelta ||
        !sameData(
            proposal.parent.counterevidence
                .activeTransparentDeltaAuthorityLines,
            [9150, 9151]
        )
    ) {
        throw new CorePathindFixedSource1cProposalV5Error(
            'PATHIND_FIXED_SOURCE_V5_AUTHORITY_DRIFT',
            'The v4 boundary or measured Transf-delta evidence drifted'
        );
    }

    const implementation = proposal.exactImplementation;
    const delta =
        proposal.dependencyClosure.transforClassifierTransparentDelta;
    if (
        implementation.trustedDeclarations.length !== 5 ||
        implementation.runtimeRules.length !== 10 ||
        implementation.proofRules.length !== 0 ||
        implementation.transparentDefinitions.length !== 6 ||
        implementation.exactBoundary !== '5/10/0/6' ||
        !sameData(implementation.runtimeRules, correctedRuntimeRules) ||
        implementation.runtimeRules[3].id !==
            'pathind.fixed-source.transfor-classifier-delta' ||
        !sameData(
            implementation.runtimeRules[3].authorityLines,
            [9150, 9151]
        ) ||
        proposal.selectedPredecessor
            .localImplementationDeltaIsFiveNineZeroSix ||
        !proposal.selectedPredecessor
            .localImplementationDeltaIsFiveTenZeroSix ||
        !delta.absentFromSelectedPredecessorRuntimeChain ||
        !delta.declarationOwnerAlreadyPresent ||
        delta.duplicateDeclarationAuthorized ||
        delta.newMathematicalRule ||
        delta.genericCheckerChangeAuthorized ||
        delta.reversedActiveReductionAuthorized ||
        proposal.selectedRuntimeObservations.length !== 5 ||
        proposal.boundedOracle.assertions.length !== 9
    ) {
        throw new CorePathindFixedSource1cProposalV5Error(
            'PATHIND_FIXED_SOURCE_V5_SCOPE_DRIFT',
            'The corrected exact 5/10/0/6 boundary drifted'
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
            'pathind-fixed-source-1c-v5-awaiting-separate-immutable-review'
    ) {
        throw new CorePathindFixedSource1cProposalV5Error(
            'PATHIND_FIXED_SOURCE_V5_AUTHORIZATION_DRIFT',
            'Corrected proposal v5 became self-authorizing or widened'
        );
    }
    return proposal;
}
