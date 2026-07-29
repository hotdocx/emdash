/**
 * Separate immutable unattended review for
 * H-DTTLF-USABILITY-DISPLAYED-CHAIN-04/D-DTTLF-USABILITY-015.
 *
 * The proposal remains unchanged and non-self-authorizing. This review uses
 * the user's standing unattended delegation, remains supersedable by a human
 * decision, and authorizes only the frozen computation-closure correction.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_PROPOSAL,
    CoreCategoricalDisplayedChainComputationClosureCorrectionProposalInput,
    validateCoreCategoricalDisplayedChainComputationClosureCorrectionProposal
} from './categorical_displayed_chain_computation_closure_correction_proposal';

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
    CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_PROPOSAL;

const rawReview = {
    revision:
        'DISPLAYED-CHAIN-COMPUTATION-CLOSURE-CORRECTION-0A-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-DTTLF-USABILITY-DISPLAYED-CHAIN-04',
        decisionId: 'D-DTTLF-USABILITY-015',
        decision: 'approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-response-after-presented-frozen-proposal',
        recordedOn: '2026-07-29',
        humanDecisionSupersedes: true
    },
    recommendation:
        cloneData(proposal) as
            CoreCategoricalDisplayedChainComputationClosureCorrectionProposalInput,
    authorization: {
        implementationRow: 'DISPLAYED-CHAIN-1A',
        implementationAuthorized: true,
        restoredTransparentDefinitions: [
            'functord_transport_lhs_func',
            'functord_transport_rhs_func'
        ],
        restoredTransparentDefinitionCount: 2,
        checkedTransparentMirrorDeclarations: [
            'Obj_func__displayed_chain_mirror'
        ],
        checkedTransparentMirrorCount: 1,
        approvedExistingDeclarationPrerequisiteCount: 5,
        totalGenericTransferDeclarationCount: 6,
        exactExistingRuntimeEquationCount: 5,
        typedNormalFormSpecializationOwners: ['piapp0'],
        typedNormalFormSpecializationCount: 1,
        typedIgnoredTermCaptureCount: 1,
        mathematicalOwnerCountRemains: 1,
        mathematicalRuntimeRuleCountRemains: 6,
        mathematicalProofRuleCountRemains: 0,
        activeLambdapiEditAuthorized: false,
        completedWeakeningTransferMutationAuthorized: false,
        directed1cGlobalTransparencyAuthorized: false,
        intrinsicCoreOwnerAuthorized: false,
        externalSubjectOracleAuthorized: false,
        semanticRuleRewriteOrBroadeningAuthorized: false,
        parserRawExprOrSecondCheckerAuthorized: false,
        browserOrBulkTransferAuthorized: false
    },
    retainedBoundaries: {
        prerequisite: cloneData(proposal.prerequisite),
        compilationAudit: cloneData(proposal.compilationAudit),
        authorityCorrections: cloneData(proposal.authorityCorrections),
        alternatives: cloneData(proposal.alternatives),
        proposedCorrection: cloneData(proposal.proposedCorrection),
        validationPlan: cloneData(proposal.validationPlan),
        nonEffects: cloneData(proposal.nonEffects),
        preReviewDecisionEffects: cloneData(proposal.decisionEffects)
    },
    validation: {
        proposalRevision:
            'DISPLAYED-CHAIN-COMPUTATION-CLOSURE-CORRECTION-0A-PROPOSAL-1',
        proposalCheckpoint:
            'adc7bcc5677ec64efcb400b43e3182c40bf6ff10',
        proposalLedgerCheckpoint:
            'babce5302f964e20c928d88323ee951a5997ef04',
        focusedProposalGate: '6-tests-pass',
        rootProposalGate:
            '952-tests-905-pass-47-intentional-skip-zero-fail',
        boundedKernelProposalGate: 'active-kernel-check-pass',
        focusedReviewGate: '7-tests-required',
        rootReviewGate:
            '959-tests-912-pass-47-intentional-skip-zero-fail-required'
    },
    gitBoundary: {
        localCheckpointRequired: true,
        exactStagedDiffReviewRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false,
        preservedTimeoutArtifactsUntouched: true
    },
    nextDependencyState:
        'displayed-chain-1a-computation-closed-generic-transfer-ready'
} as const;

export type CoreCategoricalDisplayedChainComputationClosureCorrectionReviewInput =
    typeof rawReview;

export type CoreCategoricalDisplayedChainComputationClosureCorrectionReviewErrorCode =
    | 'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_REVIEW_DECISION_DRIFT'
    | 'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_REVIEW_PROPOSAL_DRIFT'
    | 'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_REVIEW_SCOPE_DRIFT';

export class
CoreCategoricalDisplayedChainComputationClosureCorrectionReviewError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedChainComputationClosureCorrectionReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreCategoricalDisplayedChainComputationClosureCorrectionReviewError';
    }
}

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_REVIEW =
    deepFreeze(rawReview);

export function
validateCoreCategoricalDisplayedChainComputationClosureCorrectionReview(
    review:
        CoreCategoricalDisplayedChainComputationClosureCorrectionReviewInput =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_REVIEW
): void {
    try {
        validateCoreCategoricalDisplayedChainComputationClosureCorrectionProposal();
    } catch (error: unknown) {
        throw new
        CoreCategoricalDisplayedChainComputationClosureCorrectionReviewError(
            'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_REVIEW_PROPOSAL_DRIFT',
            'The D-015 proposal drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        review.revision !==
            'DISPLAYED-CHAIN-COMPUTATION-CLOSURE-CORRECTION-0A-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-DISPLAYED-CHAIN-04' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-015' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-response-after-presented-frozen-proposal' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new
        CoreCategoricalDisplayedChainComputationClosureCorrectionReviewError(
            'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_REVIEW_DECISION_DRIFT',
            'The exact delegated D-015 decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-chain-04'
    ) {
        throw new
        CoreCategoricalDisplayedChainComputationClosureCorrectionReviewError(
            'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_REVIEW_PROPOSAL_DRIFT',
            'The review must snapshot the unchanged pending proposal'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        authorization.restoredTransparentDefinitions.join(',') !==
            'functord_transport_lhs_func,functord_transport_rhs_func' ||
        authorization.restoredTransparentDefinitionCount !== 2 ||
        authorization.checkedTransparentMirrorDeclarations.join(',') !==
            'Obj_func__displayed_chain_mirror' ||
        authorization.checkedTransparentMirrorCount !== 1 ||
        authorization.approvedExistingDeclarationPrerequisiteCount !== 5 ||
        authorization.totalGenericTransferDeclarationCount !== 6 ||
        authorization.exactExistingRuntimeEquationCount !== 5 ||
        authorization.typedNormalFormSpecializationOwners.join(',') !==
            'piapp0' ||
        authorization.typedNormalFormSpecializationCount !== 1 ||
        authorization.typedIgnoredTermCaptureCount !== 1 ||
        authorization.mathematicalOwnerCountRemains !== 1 ||
        authorization.mathematicalRuntimeRuleCountRemains !== 6 ||
        authorization.mathematicalProofRuleCountRemains !== 0 ||
        authorization.activeLambdapiEditAuthorized ||
        authorization.completedWeakeningTransferMutationAuthorized ||
        authorization.directed1cGlobalTransparencyAuthorized ||
        authorization.intrinsicCoreOwnerAuthorized ||
        authorization.externalSubjectOracleAuthorized ||
        authorization.semanticRuleRewriteOrBroadeningAuthorized ||
        authorization.parserRawExprOrSecondCheckerAuthorized ||
        authorization.browserOrBulkTransferAuthorized ||
        review.validation.proposalCheckpoint !==
            'adc7bcc5677ec64efcb400b43e3182c40bf6ff10' ||
        review.validation.proposalLedgerCheckpoint !==
            'babce5302f964e20c928d88323ee951a5997ef04' ||
        review.validation.focusedProposalGate !== '6-tests-pass' ||
        review.validation.rootProposalGate !==
            '952-tests-905-pass-47-intentional-skip-zero-fail' ||
        review.validation.boundedKernelProposalGate !==
            'active-kernel-check-pass' ||
        !review.gitBoundary.localCheckpointRequired ||
        !review.gitBoundary.exactStagedDiffReviewRequired ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        !review.gitBoundary.preservedTimeoutArtifactsUntouched ||
        review.nextDependencyState !==
            'displayed-chain-1a-computation-closed-generic-transfer-ready'
    ) {
        throw new
        CoreCategoricalDisplayedChainComputationClosureCorrectionReviewError(
            'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_REVIEW_SCOPE_DRIFT',
            'The review exceeds the frozen computation-closure correction'
        );
    }

    if (
        !sameData(
            review.retainedBoundaries,
            rawReview.retainedBoundaries
        ) ||
        !sameData(review, rawReview)
    ) {
        throw new
        CoreCategoricalDisplayedChainComputationClosureCorrectionReviewError(
            'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_REVIEW_SCOPE_DRIFT',
            'The retained evidence or non-effects drifted'
        );
    }
}

validateCoreCategoricalDisplayedChainComputationClosureCorrectionReview();
