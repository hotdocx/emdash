/**
 * Separate immutable unattended review for
 * H-DTTLF-USABILITY-DISPLAYED-CHAIN-03/D-DTTLF-USABILITY-014.
 *
 * The proposal remains unchanged and non-self-authorizing. This review uses
 * the user's standing unattended delegation, remains supersedable by a human
 * decision, and authorizes only the exact ambient `Const_func` signature
 * correction.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL,
    CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalInput,
    validateCoreCategoricalDisplayedChainConstantFunctorCorrectionProposal
} from './categorical_displayed_chain_constant_functor_correction_proposal';

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
    CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL;

const rawReview = {
    revision:
        'DISPLAYED-CHAIN-CONST-FUNCTOR-CORRECTION-0A-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-DTTLF-USABILITY-DISPLAYED-CHAIN-03',
        decisionId: 'D-DTTLF-USABILITY-014',
        decision: 'approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-response-after-presented-frozen-proposal',
        recordedOn: '2026-07-28',
        humanDecisionSupersedes: true
    },
    recommendation:
        cloneData(proposal) as
            CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalInput,
    authorization: {
        implementationRow: 'DISPLAYED-CHAIN-1A',
        implementationAuthorized: true,
        additionalAmbientDeclarationPrerequisites: ['Const_func'],
        additionalAmbientDeclarationPrerequisiteCount: 1,
        totalAmbientDeclarationPrerequisites: [
            'Terminal_obj',
            'Const_func'
        ],
        totalAmbientDeclarationPrerequisiteCount: 2,
        chainSpecificDeclarationPrerequisiteCountRemains: 3,
        totalExistingDeclarationsCompiledForSlice: 5,
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
        exhaustiveLinkageAudit:
            cloneData(proposal.exhaustiveLinkageAudit),
        discoveredGap: cloneData(proposal.discoveredGap),
        alternatives: cloneData(proposal.alternatives),
        proposedCorrection: cloneData(proposal.proposedCorrection),
        validationPlan: cloneData(proposal.validationPlan),
        nonEffects: cloneData(proposal.nonEffects),
        preReviewDecisionEffects: cloneData(proposal.decisionEffects)
    },
    validation: {
        proposalRevision:
            'DISPLAYED-CHAIN-CONST-FUNCTOR-CORRECTION-0A-PROPOSAL-1',
        proposalCheckpoint:
            'fe20a7af2b5ad8835a98f0acce987953c29d33de',
        proposalLedgerCheckpoint:
            '774f5647ef397e62d254e942b7eefc97cf8ce8a0',
        focusedProposalGate: '5-tests-pass',
        rootProposalGate:
            '940-tests-893-pass-47-intentional-skip-zero-fail',
        liveCanonicalExportGate: '14-tests-pass',
        focusedReviewGate: '6-tests-required',
        rootReviewGate:
            '946-tests-899-pass-47-intentional-skip-zero-fail-required'
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
        'displayed-chain-1a-final-dependency-closed-generic-transfer-ready'
} as const;

export type CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewInput =
    typeof rawReview;

export type CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewErrorCode =
    | 'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_REVIEW_DECISION_DRIFT'
    | 'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_REVIEW_PROPOSAL_DRIFT'
    | 'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_REVIEW_SCOPE_DRIFT';

export class
CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewError';
    }
}

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_REVIEW =
    deepFreeze(rawReview);

export function
validateCoreCategoricalDisplayedChainConstantFunctorCorrectionReview(
    review:
        CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewInput =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_REVIEW
): void {
    try {
        validateCoreCategoricalDisplayedChainConstantFunctorCorrectionProposal();
    } catch (error: unknown) {
        throw new
        CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewError(
            'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_REVIEW_PROPOSAL_DRIFT',
            'The final correction proposal drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        review.revision !==
            'DISPLAYED-CHAIN-CONST-FUNCTOR-CORRECTION-0A-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-DISPLAYED-CHAIN-03' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-014' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-response-after-presented-frozen-proposal' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new
        CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewError(
            'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_REVIEW_DECISION_DRIFT',
            'The exact delegated D-014 decision drifted'
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-chain-03'
    ) {
        throw new
        CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewError(
            'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_REVIEW_PROPOSAL_DRIFT',
            'The review must snapshot the unchanged pending proposal'
        );
    }

    const authorization = review.authorization;
    if (
        !authorization.implementationAuthorized ||
        authorization.additionalAmbientDeclarationPrerequisites.join(',') !==
            'Const_func' ||
        authorization.additionalAmbientDeclarationPrerequisiteCount !== 1 ||
        authorization.totalAmbientDeclarationPrerequisites.join(',') !==
            'Terminal_obj,Const_func' ||
        authorization.totalAmbientDeclarationPrerequisiteCount !== 2 ||
        authorization.chainSpecificDeclarationPrerequisiteCountRemains !==
            3 ||
        authorization.totalExistingDeclarationsCompiledForSlice !== 5 ||
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
            'fe20a7af2b5ad8835a98f0acce987953c29d33de' ||
        review.validation.proposalLedgerCheckpoint !==
            '774f5647ef397e62d254e942b7eefc97cf8ce8a0' ||
        review.validation.focusedProposalGate !== '5-tests-pass' ||
        review.validation.rootProposalGate !==
            '940-tests-893-pass-47-intentional-skip-zero-fail' ||
        review.validation.liveCanonicalExportGate !== '14-tests-pass' ||
        !review.gitBoundary.localCheckpointRequired ||
        !review.gitBoundary.exactStagedDiffReviewRequired ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized ||
        !review.gitBoundary.preservedTimeoutArtifactsUntouched ||
        review.nextDependencyState !==
            'displayed-chain-1a-final-dependency-closed-generic-transfer-ready'
    ) {
        throw new
        CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewError(
            'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_REVIEW_SCOPE_DRIFT',
            'The review exceeds the final one-signature correction'
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
        CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewError(
            'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_REVIEW_SCOPE_DRIFT',
            'The retained evidence or non-effects drifted'
        );
    }
}

validateCoreCategoricalDisplayedChainConstantFunctorCorrectionReview();
