/**
 * Separate immutable unattended review for
 * H-DTTLF-USABILITY-DISPLAYED-CHAIN-02/D-DTTLF-USABILITY-013.
 *
 * The proposal remains unchanged and non-self-authorizing. This review uses
 * the user's standing unattended delegation, remains supersedable by a
 * human decision, and authorizes only the exact ambient `Terminal_obj`
 * signature correction.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL,
    CoreCategoricalDisplayedChainTransferCorrectionProposalInput,
    validateCoreCategoricalDisplayedChainTransferCorrectionProposal
} from './categorical_displayed_chain_transfer_correction_proposal';

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
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL;

const rawReview = {
    revision:
        'DISPLAYED-CHAIN-TRANSFER-CORRECTION-0A-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-DTTLF-USABILITY-DISPLAYED-CHAIN-02',
        decisionId: 'D-DTTLF-USABILITY-013',
        decision: 'approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-response-after-presented-frozen-proposal',
        recordedOn: '2026-07-28',
        humanDecisionSupersedes: true
    },
    recommendation:
        cloneData(proposal) as
            CoreCategoricalDisplayedChainTransferCorrectionProposalInput,
    authorization: {
        implementationRow: 'DISPLAYED-CHAIN-1A',
        implementationAuthorized: true,
        ambientDeclarationPrerequisites: ['Terminal_obj'],
        ambientDeclarationPrerequisiteCount: 1,
        chainSpecificDeclarationPrerequisiteCountRemains: 3,
        totalExistingDeclarationsCompiledForSlice: 4,
        existingRuntimeRulePrerequisiteCountRemains: 2,
        mathematicalOwnerCountRemains: 1,
        mathematicalRuntimeRuleCountRemains: 6,
        activeLambdapiEditAuthorized: false,
        genericDeclarationTransferRequired: true,
        intrinsicCoreOwnerAuthorized: false,
        wildcardOrRuleBroadeningAuthorized: false,
        parserRawExprOrSecondCheckerAuthorized: false,
        browserOrBulkTransferAuthorized: false
    },
    retainedBoundaries: {
        prerequisite: cloneData(proposal.prerequisite),
        discoveredGap: cloneData(proposal.discoveredGap),
        alternatives: cloneData(proposal.alternatives),
        proposedCorrection: cloneData(proposal.proposedCorrection),
        validationPlan: cloneData(proposal.validationPlan),
        nonEffects: cloneData(proposal.nonEffects),
        preReviewDecisionEffects: cloneData(proposal.decisionEffects)
    },
    validation: {
        proposalRevision:
            'DISPLAYED-CHAIN-TRANSFER-CORRECTION-0A-PROPOSAL-1',
        proposalCheckpoint:
            '6a46dea169ec358a3882f9ec86a04be9af713963',
        proposalLedgerCheckpoint:
            'cdb064622e82a7a5d39f92dfecc61f1ab186e0bd',
        focusedProposalGate: '6-tests-pass',
        rootProposalGate:
            '929-tests-882-pass-47-intentional-skip-zero-fail',
        liveCanonicalExportGate: '14-tests-pass',
        focusedReviewGate: '6-tests-required',
        rootReviewGate:
            '935-tests-888-pass-47-intentional-skip-zero-fail-required'
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
        'displayed-chain-1a-corrected-generic-transfer-ready'
} as const;

export type CoreCategoricalDisplayedChainTransferCorrectionReviewInput =
    typeof rawReview;

export type CoreCategoricalDisplayedChainTransferCorrectionReviewErrorCode =
    | 'DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW_DECISION_DRIFT'
    | 'DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW_PROPOSAL_DRIFT'
    | 'DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW_SCOPE_DRIFT';

export class
CoreCategoricalDisplayedChainTransferCorrectionReviewError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedChainTransferCorrectionReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreCategoricalDisplayedChainTransferCorrectionReviewError';
    }
}

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW =
    deepFreeze(rawReview);

export function
validateCoreCategoricalDisplayedChainTransferCorrectionReview(
    review:
        CoreCategoricalDisplayedChainTransferCorrectionReviewInput =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW
): void {
    try {
        validateCoreCategoricalDisplayedChainTransferCorrectionProposal();
    } catch (error: unknown) {
        throw new
        CoreCategoricalDisplayedChainTransferCorrectionReviewError(
            'DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW_PROPOSAL_DRIFT',
            'The correction proposal drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        review.revision !==
            'DISPLAYED-CHAIN-TRANSFER-CORRECTION-0A-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-DISPLAYED-CHAIN-02' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-013' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-response-after-presented-frozen-proposal' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new
        CoreCategoricalDisplayedChainTransferCorrectionReviewError(
            'DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW_DECISION_DRIFT',
            'The exact delegated D-013 decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-chain-02'
    ) {
        throw new
        CoreCategoricalDisplayedChainTransferCorrectionReviewError(
            'DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW_PROPOSAL_DRIFT',
            'The review must snapshot the unchanged pending proposal'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        authorization.ambientDeclarationPrerequisites.join(',') !==
            'Terminal_obj' ||
        authorization.ambientDeclarationPrerequisiteCount !== 1 ||
        authorization.chainSpecificDeclarationPrerequisiteCountRemains !==
            3 ||
        authorization.totalExistingDeclarationsCompiledForSlice !== 4 ||
        authorization.existingRuntimeRulePrerequisiteCountRemains !== 2 ||
        authorization.mathematicalOwnerCountRemains !== 1 ||
        authorization.mathematicalRuntimeRuleCountRemains !== 6 ||
        authorization.activeLambdapiEditAuthorized ||
        !authorization.genericDeclarationTransferRequired ||
        authorization.intrinsicCoreOwnerAuthorized ||
        authorization.wildcardOrRuleBroadeningAuthorized ||
        authorization.parserRawExprOrSecondCheckerAuthorized ||
        authorization.browserOrBulkTransferAuthorized ||
        review.validation.proposalCheckpoint !==
            '6a46dea169ec358a3882f9ec86a04be9af713963' ||
        review.validation.proposalLedgerCheckpoint !==
            'cdb064622e82a7a5d39f92dfecc61f1ab186e0bd' ||
        review.validation.focusedProposalGate !== '6-tests-pass' ||
        review.validation.rootProposalGate !==
            '929-tests-882-pass-47-intentional-skip-zero-fail' ||
        review.validation.liveCanonicalExportGate !== '14-tests-pass' ||
        !review.gitBoundary.localCheckpointRequired ||
        !review.gitBoundary.exactStagedDiffReviewRequired ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        !review.gitBoundary.preservedTimeoutArtifactsUntouched ||
        review.nextDependencyState !==
            'displayed-chain-1a-corrected-generic-transfer-ready'
    ) {
        throw new
        CoreCategoricalDisplayedChainTransferCorrectionReviewError(
            'DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW_SCOPE_DRIFT',
            'The review exceeds the one-signature correction'
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
        CoreCategoricalDisplayedChainTransferCorrectionReviewError(
            'DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW_SCOPE_DRIFT',
            'The retained evidence or non-effects drifted'
        );
    }
}

validateCoreCategoricalDisplayedChainTransferCorrectionReview();
