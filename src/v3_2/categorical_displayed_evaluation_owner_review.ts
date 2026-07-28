/**
 * Separate immutable delegated-approval record for
 * H-DTTLF-USABILITY-DISPLAYED-EVAL-OWNER-01/D-DTTLF-USABILITY-011.
 *
 * The pre-review DISPLAYED-EVAL-OWNER-0C proposal remains unchanged and
 * non-self-authorizing. This artifact records the user's plan-specific
 * unattended delegation after no immediate human response to the exact
 * presented proposal. It authorizes only the bounded DISPLAYED-EVAL-1A
 * semantic slice.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL,
    CoreCategoricalDisplayedEvaluationOwnerProposalInput,
    validateCoreCategoricalDisplayedEvaluationOwnerProposal
} from './categorical_displayed_evaluation_owner_proposal';

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

const proposal =
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL;

const rawReview = {
    revision: 'DISPLAYED-EVAL-OWNER-0C-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-DTTLF-USABILITY-DISPLAYED-EVAL-OWNER-01',
        decisionId: 'D-DTTLF-USABILITY-011',
        decision: 'approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-response-after-presented-frozen-proposal',
        recordedOn: '2026-07-28',
        humanDecisionSupersedes: true,
        decisionEvidence:
            'The user authorized the coding agent to approve a frozen ' +
            'proposal during unattended continuation when no immediate ' +
            'human response follows, provided the Git checkpoint SOP is ' +
            'followed'
    },
    /**
     * Immutable snapshot of the exact pre-review proposal. Its pending
     * status remains historical evidence and is not mutated by approval.
     */
    recommendation:
        cloneData(proposal) as
            CoreCategoricalDisplayedEvaluationOwnerProposalInput,
    authorization: {
        implementationRow: 'DISPLAYED-EVAL-1A',
        implementationRowAuthorized: true,
        exactKernelOwners: [
            'Eval_funcd',
            'Terminal_funcd'
        ],
        exactKernelOwnerCount: 2,
        exactRuntimeRuleIds: [
            'categorical.displayed-evaluation.component',
            'categorical.displayed-terminal.component'
        ],
        exactRuntimeRuleCount: 2,
        activeLambdapiOwnerAndRuleEditAuthorized: true,
        genericDeclarationAndRuntimeTransferAuthorized: true,
        intrinsicCoreOwnerAuthorized: false,
        dependentTargetFinalRuntimeRecheckAuthorized: true,
        recursiveTypedApplicationJudgments: [
            'varying-subject-varying-coherent-argument',
            'varying-subject-fixed-argument'
        ],
        recursiveTypedApplicationJudgmentCount: 2,
        existingApplicationNodeReuseRequired: true,
        deriveFixedArgumentThroughTerminalFuncdRequired: true,
        thirdFixedEvaluatorOwnerAuthorized: false,
        genericFappTappRemainsSoleCoherenceOwner: true,
        constructorSpecificCoherenceRulesAuthorized: false,
        warningDeltaIsDiagnosticNotVeto: true,
        arbitraryMixedDomainEvaluationAuthorized: false,
        genuineDependentChainAuthorized: false,
        nestedDisplayedAbstractionBeyondSliceAuthorized: false,
        generalNdCoherenceAuthorized: false,
        sigmaArrowActionAuthorized: false,
        totalCategoryEquivalenceAuthorized: false,
        groupoidalClosureAuthorized: false,
        rawExprOrSecondCheckerAuthorized: false,
        parserOrBulkTransferAuthorized: false,
        browserOrDeployedPromotionAuthorized: false
    },
    retainedBoundaries: {
        selectedDomain:
            cloneData(proposal.selectedDomain),
        proposedKernelOwners:
            cloneData(proposal.proposedKernelOwners),
        proposedRuntimeRules:
            cloneData(proposal.proposedRuntimeRules),
        derivedConstructions:
            cloneData(proposal.derivedConstructions),
        coherenceContract:
            cloneData(proposal.coherenceContract),
        profileRepair:
            cloneData(proposal.profileRepair),
        typedFrontendSlice:
            cloneData(proposal.typedFrontendSlice),
        validationPlan:
            cloneData(proposal.validationPlan),
        alternativesRetained:
            cloneData(proposal.alternativesRetained),
        proposedSemanticDelta:
            cloneData(proposal.proposedSemanticDelta),
        withheld:
            cloneData(proposal.withheld),
        preReviewDecisionEffects:
            cloneData(proposal.decisionEffects)
    },
    validation: {
        proposalRevision: 'DISPLAYED-EVAL-OWNER-0C-PROPOSAL-1',
        proposalCheckpoint:
            '7df9993f06fc55e2f34b09094b87987ef19cecba',
        proposalLedgerCheckpoint:
            '9c06e36ce715b1c6410c4974c25efbfbdb0818bc',
        focusedProposalGate: '22-tests-pass',
        rootProposalGate:
            '882-tests-836-pass-46-intentional-skip-zero-fail',
        liveConformanceGate:
            '19-judgments-global-60-second-pass',
        activeKernelGate: 'bounded-make-check-pass',
        focusedReviewGate: '10-tests-required',
        rootReviewGate:
            '892-tests-846-pass-46-intentional-skip-zero-fail-required'
    },
    gitBoundary: {
        rollbackEvidence:
            'proposal-and-ledger-checkpoints-recorded-before-delegation',
        localCheckpointRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false,
        preservedTimeoutArtifactsUntouched: true
    },
    nonEffects: [
        'does-not-mutate-the-pre-review-proposal',
        'does-not-itself-install-the-two-kernel-owners-or-rules',
        'does-not-add-an-intrinsic-core-owner-or-checker-layer',
        'does-not-authorize-a-third-fixed-evaluator-owner',
        'does-not-duplicate-generic-fapp-tapp-coherence-rules',
        'does-not-authorize-arbitrary-mixed-domain-evaluation',
        'does-not-authorize-dependent-chain-or-general-nd-work',
        'does-not-authorize-parser-acquisition-or-bulk-transfer',
        'does-not-authorize-browser-or-deployed-profile-promotion',
        'does-not-broaden-local-checkpoint-git-authority'
    ],
    nextDependencyState:
        'displayed-eval-1a-exact-implementation-ready'
} as const;

export type CoreCategoricalDisplayedEvaluationOwnerReviewInput =
    typeof rawReview;

export type CoreCategoricalDisplayedEvaluationOwnerReviewErrorCode =
    | 'DISPLAYED_EVALUATION_OWNER_REVIEW_DECISION_DRIFT'
    | 'DISPLAYED_EVALUATION_OWNER_REVIEW_PREREQUISITE_DRIFT'
    | 'DISPLAYED_EVALUATION_OWNER_REVIEW_PROPOSAL_DRIFT'
    | 'DISPLAYED_EVALUATION_OWNER_REVIEW_AUTHORIZATION_DRIFT';

export class CoreCategoricalDisplayedEvaluationOwnerReviewError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedEvaluationOwnerReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreCategoricalDisplayedEvaluationOwnerReviewError';
    }
}

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW =
    deepFreeze(rawReview);

export function
validateCoreCategoricalDisplayedEvaluationOwnerReview(
    review: CoreCategoricalDisplayedEvaluationOwnerReviewInput =
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW
): void {
    if (
        review.revision !==
            'DISPLAYED-EVAL-OWNER-0C-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-DISPLAYED-EVAL-OWNER-01' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-011' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-response-after-presented-frozen-proposal' ||
        review.approval.recordedOn !== '2026-07-28' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new CoreCategoricalDisplayedEvaluationOwnerReviewError(
            'DISPLAYED_EVALUATION_OWNER_REVIEW_DECISION_DRIFT',
            'The delegated review must preserve the exact D-011 ' +
                'decision, authority, and human-supersession boundary'
        );
    }

    try {
        validateCoreCategoricalDisplayedEvaluationOwnerProposal(proposal);
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedEvaluationOwnerReviewError(
            'DISPLAYED_EVALUATION_OWNER_REVIEW_PREREQUISITE_DRIFT',
            'The approved DISPLAYED-EVAL-OWNER-0C proposal drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-eval-owner-01' ||
        review.recommendation.decisionId !== 'D-DTTLF-USABILITY-011'
    ) {
        throw new CoreCategoricalDisplayedEvaluationOwnerReviewError(
            'DISPLAYED_EVALUATION_OWNER_REVIEW_PROPOSAL_DRIFT',
            'The reviewed recommendation is not the exact immutable ' +
                'pre-review proposal'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !== 'DISPLAYED-EVAL-1A' ||
        !authorization.implementationRowAuthorized ||
        authorization.exactKernelOwners.join(',') !==
            'Eval_funcd,Terminal_funcd' ||
        authorization.exactKernelOwnerCount !== 2 ||
        authorization.exactRuntimeRuleIds.join(',') !==
            'categorical.displayed-evaluation.component,' +
            'categorical.displayed-terminal.component' ||
        authorization.exactRuntimeRuleCount !== 2 ||
        !authorization.activeLambdapiOwnerAndRuleEditAuthorized ||
        !authorization.genericDeclarationAndRuntimeTransferAuthorized ||
        authorization.intrinsicCoreOwnerAuthorized ||
        !authorization.dependentTargetFinalRuntimeRecheckAuthorized ||
        authorization.recursiveTypedApplicationJudgments.join(',') !==
            'varying-subject-varying-coherent-argument,' +
            'varying-subject-fixed-argument' ||
        authorization.recursiveTypedApplicationJudgmentCount !== 2 ||
        !authorization.existingApplicationNodeReuseRequired ||
        !authorization.deriveFixedArgumentThroughTerminalFuncdRequired ||
        authorization.thirdFixedEvaluatorOwnerAuthorized ||
        !authorization.genericFappTappRemainsSoleCoherenceOwner ||
        authorization.constructorSpecificCoherenceRulesAuthorized ||
        !authorization.warningDeltaIsDiagnosticNotVeto ||
        authorization.arbitraryMixedDomainEvaluationAuthorized ||
        authorization.genuineDependentChainAuthorized ||
        authorization.nestedDisplayedAbstractionBeyondSliceAuthorized ||
        authorization.generalNdCoherenceAuthorized ||
        authorization.sigmaArrowActionAuthorized ||
        authorization.totalCategoryEquivalenceAuthorized ||
        authorization.groupoidalClosureAuthorized ||
        authorization.rawExprOrSecondCheckerAuthorized ||
        authorization.parserOrBulkTransferAuthorized ||
        authorization.browserOrDeployedPromotionAuthorized ||
        !review.gitBoundary.localCheckpointRequired ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        !review.gitBoundary.preservedTimeoutArtifactsUntouched ||
        review.nextDependencyState !==
            'displayed-eval-1a-exact-implementation-ready'
    ) {
        throw new CoreCategoricalDisplayedEvaluationOwnerReviewError(
            'DISPLAYED_EVALUATION_OWNER_REVIEW_AUTHORIZATION_DRIFT',
            'The delegated approval exceeds the frozen semantic slice ' +
                'or its Git boundary'
        );
    }

    if (
        !sameData(review.retainedBoundaries, rawReview.retainedBoundaries) ||
        !sameData(review, rawReview)
    ) {
        throw new CoreCategoricalDisplayedEvaluationOwnerReviewError(
            'DISPLAYED_EVALUATION_OWNER_REVIEW_AUTHORIZATION_DRIFT',
            'The retained scope, alternatives, warnings, or non-effects ' +
                'drifted'
        );
    }
}

validateCoreCategoricalDisplayedEvaluationOwnerReview();
