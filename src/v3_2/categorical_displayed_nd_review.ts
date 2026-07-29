/**
 * Separate immutable delegated-approval record for
 * H-DTTLF-USABILITY-DISPLAYED-ND-01/D-DTTLF-USABILITY-018.
 *
 * The checkpointed DISPLAYED-ND-0A audit/proposal remains unchanged and
 * non-self-authorizing. This review records the user's standing unattended
 * delegation after the exact green gate was presented, retains human
 * supersession, and authorizes only the bounded recursive vertical-
 * composition case frozen there.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_ND_AUDIT,
    CoreCategoricalDisplayedNdAuditInput,
    validateCoreCategoricalDisplayedNdAudit
} from './categorical_displayed_nd_audit';

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

const proposal = CORE_CATEGORICAL_DISPLAYED_ND_AUDIT;
const continuation = proposal.recommendedContinuation;

const rawReview = {
    revision: 'DISPLAYED-ND-0A-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-DTTLF-USABILITY-DISPLAYED-ND-01',
        decisionId: 'D-DTTLF-USABILITY-018',
        decision: 'approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-response-after-presented-frozen-proposal',
        recordedOn: '2026-07-29',
        humanDecisionSupersedes: true,
        decisionEvidence:
            'The user authorized the coding agent to approve a frozen ' +
            'dependency-ready proposal during unattended continuation ' +
            'when no immediate human response follows, provided the Git ' +
            'checkpoint SOP is followed'
    },
    /**
     * Immutable snapshot of the exact checkpointed audit/proposal. Its
     * false implementation-authority field and non-effects remain
     * historical evidence and are not rewritten by approval.
     */
    recommendation:
        cloneData(proposal) as CoreCategoricalDisplayedNdAuditInput,
    authorization: {
        implementationRow: continuation.row,
        implementationAuthorized: true,
        exactFirstCase: continuation.exactFirstCase,
        surfaceMethod: continuation.surfaceMethod,
        irTag: continuation.selectedIr.tag,
        irRole: continuation.selectedIr.role,
        firstAcceptedClassifier:
            continuation.selectedIr.firstAcceptedClassifier,
        typeContract: continuation.selectedIr.typeContract,
        recursion: continuation.selectedIr.recursion,
        lowering: continuation.selectedLowering,
        requiredEvidence:
            cloneData(continuation.requiredEvidence),
        activeLambdapiOwnerDelta:
            continuation.activeLambdapiOwnerDelta,
        activeLambdapiRuleDelta:
            continuation.activeLambdapiRuleDelta,
        typescriptTransferEntryDelta:
            continuation.typescriptTransferEntryDelta,
        intrinsicCoreOwnerDelta:
            continuation.intrinsicCoreOwnerDelta,
        ownerSpecificCheckerBranchDelta:
            continuation.ownerSpecificCheckerBranchDelta,
        nextHomTransferIncluded:
            continuation.nextHomTransferIncluded,
        identitySyntaxAuthorized: false,
        arbitraryPointwiseCoherenceAuthorized: false,
        mixedVarianceBridgeAuthorized: false,
        compositeBaseArrowCellBetaAuthorized: false,
        newLfOrCoreBinderModeAuthorized: false,
        parserOrSecondCheckerAuthorized: false,
        browserOrDeployedPromotionAuthorized: false,
        wholeLibraryScaleTransferAuthorized: false,
        externalOrDestructiveGitActionAuthorized: false
    },
    retainedBoundary: {
        prerequisite: cloneData(proposal.prerequisite),
        architecture: cloneData(proposal.retainedArchitecture),
        binderMeaning: cloneData(proposal.binderMeaning),
        observationMatrix: cloneData(proposal.observationMatrix),
        introductionMatrix: cloneData(proposal.introductionMatrix),
        higherActionAuthority:
            cloneData(proposal.higherActionAuthority),
        computationBoundary:
            cloneData(proposal.computationBoundary),
        alternatives: cloneData(proposal.alternatives),
        semanticDelta: cloneData(proposal.semanticDelta),
        nonEffects: cloneData(proposal.nonEffects)
    },
    validation: {
        proposalRevision: 'DISPLAYED-ND-0A-AUDIT-1',
        proposalCheckpoint:
            'bc29f0d98de32fe0fdbad992859e97711e493e5c',
        proposalLedgerCheckpoint:
            '0047ee1761d48d80fd71ab9ec5ac157ad08779f4',
        focusedProposalGate: '7-tests-pass',
        rootProposalGate:
            '1029-tests-982-pass-47-intentional-skip-zero-fail',
        liveConformanceProposalGate:
            '19-judgments-global-60-second-pass',
        activeKernelProposalGate: 'bounded-make-check-pass',
        focusedReviewGate: '7-tests-required',
        rootReviewGate:
            '1036-tests-989-pass-47-intentional-skip-zero-fail-required',
        liveConformanceReviewGate:
            '19-judgments-global-60-second-pass-required',
        activeKernelReviewGate: 'bounded-make-check-pass-required'
    },
    gitBoundary: {
        rollbackEvidence:
            'proposal-and-ledger-checkpoints-recorded-before-delegation',
        localCheckpointRequired: true,
        exactStagedDiffReviewRequired: true,
        pushMergePublishAuthorized: false,
        historyRewriteAuthorized: false,
        cleanupAuthorized: false
    },
    nonEffects: [
        'does-not-mutate-the-pre-review-audit-or-proposal',
        'does-not-rewrite-or-falsify-d017-history',
        'does-not-itself-implement-displayed-nd-1a',
        'does-not-authorize-a-lambdapi-owner-or-rule',
        'does-not-authorize-a-typescript-transfer-entry',
        'does-not-authorize-an-intrinsic-core-owner',
        'does-not-authorize-an-owner-specific-checker-or-evaluator-branch',
        'does-not-authorize-arbitrary-pointwise-coherence',
        'does-not-authorize-identity-or-next-hom-syntax',
        'does-not-authorize-mixed-variance-or-composite-cell-normalization',
        'does-not-authorize-a-parser-or-second-checker',
        'does-not-authorize-browser-or-deployed-profile-promotion',
        'does-not-resume-bulk-or-whole-development-transfer',
        'does-not-broaden-local-checkpoint-git-authority'
    ],
    nextDependencyState:
        'displayed-nd-1a-recursive-vertical-composition-ready'
} as const;

export type CoreCategoricalDisplayedNdReviewInput =
    typeof rawReview;

export type CoreCategoricalDisplayedNdReviewErrorCode =
    | 'DISPLAYED_ND_REVIEW_DECISION_DRIFT'
    | 'DISPLAYED_ND_REVIEW_PREREQUISITE_DRIFT'
    | 'DISPLAYED_ND_REVIEW_PROPOSAL_DRIFT'
    | 'DISPLAYED_ND_REVIEW_AUTHORIZATION_DRIFT';

export class CoreCategoricalDisplayedNdReviewError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedNdReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDisplayedNdReviewError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_ND_REVIEW =
    deepFreeze(rawReview);

export function validateCoreCategoricalDisplayedNdReview(
    review: CoreCategoricalDisplayedNdReviewInput =
        CORE_CATEGORICAL_DISPLAYED_ND_REVIEW
): void {
    if (
        review.revision !== 'DISPLAYED-ND-0A-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-DISPLAYED-ND-01' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-018' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-response-after-presented-frozen-proposal' ||
        review.approval.recordedOn !== '2026-07-29' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new CoreCategoricalDisplayedNdReviewError(
            'DISPLAYED_ND_REVIEW_DECISION_DRIFT',
            'The delegated review must preserve the exact D-018 decision, ' +
                'condition, and human-supersession boundary'
        );
    }

    try {
        validateCoreCategoricalDisplayedNdAudit(proposal);
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedNdReviewError(
            'DISPLAYED_ND_REVIEW_PREREQUISITE_DRIFT',
            'The checkpointed DISPLAYED-ND-0A audit drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.status !==
            'completed-read-only-audit-with-non-self-authorizing-' +
            'continuation-proposal' ||
        review.recommendation.prerequisite
            .semanticImplementationAuthorized ||
        !review.recommendation.nonEffects.includes(
            'does-not-authorize-DISPLAYED-ND-1A'
        )
    ) {
        throw new CoreCategoricalDisplayedNdReviewError(
            'DISPLAYED_ND_REVIEW_PROPOSAL_DRIFT',
            'The recommendation is not the exact immutable, ' +
                'non-self-authorizing D-018 proposal'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !== 'DISPLAYED-ND-1A' ||
        !authorization.implementationAuthorized ||
        authorization.exactFirstCase !==
            'lambda-k-nd-pointwise-vertical-composition' ||
        authorization.surfaceMethod !== 'composeCells' ||
        authorization.irTag !== 'typed-cell-composition' ||
        authorization.firstAcceptedClassifier !==
            'indexed-transfor' ||
        authorization.lowering !==
            'recursive-factorization-to-comp_fapp0-at-Functord_cat' ||
        authorization.requiredEvidence.join(',') !==
            continuation.requiredEvidence.join(',') ||
        authorization.activeLambdapiOwnerDelta !== 0 ||
        authorization.activeLambdapiRuleDelta !== 0 ||
        authorization.typescriptTransferEntryDelta !== 0 ||
        authorization.intrinsicCoreOwnerDelta !== 0 ||
        authorization.ownerSpecificCheckerBranchDelta !== 0 ||
        authorization.nextHomTransferIncluded ||
        authorization.identitySyntaxAuthorized ||
        authorization.arbitraryPointwiseCoherenceAuthorized ||
        authorization.mixedVarianceBridgeAuthorized ||
        authorization.compositeBaseArrowCellBetaAuthorized ||
        authorization.newLfOrCoreBinderModeAuthorized ||
        authorization.parserOrSecondCheckerAuthorized ||
        authorization.browserOrDeployedPromotionAuthorized ||
        authorization.wholeLibraryScaleTransferAuthorized ||
        authorization.externalOrDestructiveGitActionAuthorized
    ) {
        throw new CoreCategoricalDisplayedNdReviewError(
            'DISPLAYED_ND_REVIEW_AUTHORIZATION_DRIFT',
            'The D-018 review authorization exceeded or drifted from the ' +
                'frozen recursive vertical-composition case'
        );
    }

    if (
        review.validation.proposalCheckpoint !==
            'bc29f0d98de32fe0fdbad992859e97711e493e5c' ||
        review.validation.proposalLedgerCheckpoint !==
            '0047ee1761d48d80fd71ab9ec5ac157ad08779f4' ||
        !sameData(review.validation, rawReview.validation) ||
        !sameData(
            review.retainedBoundary,
            rawReview.retainedBoundary
        ) ||
        !sameData(review.nonEffects, rawReview.nonEffects) ||
        review.nextDependencyState !==
            'displayed-nd-1a-recursive-vertical-composition-ready' ||
        review.gitBoundary.rollbackEvidence !==
            'proposal-and-ledger-checkpoints-recorded-before-delegation' ||
        !review.gitBoundary.localCheckpointRequired ||
        !review.gitBoundary.exactStagedDiffReviewRequired ||
        review.gitBoundary.pushMergePublishAuthorized ||
        review.gitBoundary.historyRewriteAuthorized ||
        review.gitBoundary.cleanupAuthorized
    ) {
        throw new CoreCategoricalDisplayedNdReviewError(
            'DISPLAYED_ND_REVIEW_AUTHORIZATION_DRIFT',
            'The D-018 validation or Git rollback boundary drifted'
        );
    }
}
