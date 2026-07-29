/**
 * Separate immutable delegated review for
 * H-DTTLF-SCALE-INDUCTIVE-01/D-DTTLF-SCALE-INDUCTIVE-001.
 *
 * The checkpointed proposal remains non-self-authorizing. This record
 * approves only its required nonrecursive indexed generated-owner contract
 * under the user's standing unattended delegation, with human supersession.
 */

import {
    CORE_LF_SCALE_INDUCTIVE_1B1_PROPOSAL,
    CoreLfScaleInductive1b1Proposal,
    validateCoreLfScaleInductive1b1Proposal
} from './scale_inductive_1b_proposal';

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

const proposal = CORE_LF_SCALE_INDUCTIVE_1B1_PROPOSAL;

const rawReview = {
    revision: 'SCALE-INDUCTIVE-1B1-REVIEWED-1',
    status: 'reviewed-approved-under-delegated-unattended-authority',
    approval: {
        gate: 'H-DTTLF-SCALE-INDUCTIVE-01',
        decisionId: 'D-DTTLF-SCALE-INDUCTIVE-001',
        decision: 'approved-as-proposed',
        authority: 'user-delegated-unattended-approval',
        condition:
            'no-immediate-human-objection-after-presented-' +
            'checkpointed-proposal',
        recordedOn: '2026-07-29',
        humanDecisionSupersedes: true
    },
    recommendation:
        cloneData(proposal) as CoreLfScaleInductive1b1Proposal,
    authorization: {
        implementationRow: 'SCALE-INDUCTIVE-1B1',
        implementationAuthorized: true,
        exactImplementation:
            cloneData(proposal.proposedImplementation),
        correctedIndices:
            cloneData(
                proposal.representationCorrection.correctedIndices
            ),
        erasedSignatureDelta:
            proposal.representationCorrection.erasedSignatureDelta,
        generatedOwner: 'ind_τΣ_',
        generatedRuntimeRuleCount: 1,
        generatedConsumer:
            proposal.measuredAuthority.generatedConsumer,
        nonrecursiveIndexedOnly: true,
        directRecursionAuthorized: false,
        recursiveInductionHypothesisAuthorized: false,
        generalStrictPositivityAuthorized: false,
        automaticEliminatorSynthesisAuthorized: false,
        endUserInductiveDeclarationFacadeAuthorized: false,
        parserOrSurfaceSyntaxAuthorized: false,
        activeProfileOrBrowserPromotionAuthorized: false,
        LambdapiSourceChangeAuthorized: false,
        bulkOrWholeTransferGraduationAuthorized: false,
        externalOrDestructiveGitActionAuthorized: false
    },
    validation: {
        proposalCheckpoint:
            '830fb975756d1d13d8ddcb516690ea88b19d51d6',
        proposalLedgerCheckpoint:
            'ecc0cf32b3b5a96662cca2b9e1fff283e65f9d59',
        focusedProposalGate:
            '7-tests-6-pass-1-intentional-live-skip-zero-fail',
        liveLambdapiProposalGate: '7-tests-all-pass',
        rootProposalGate:
            '1085-tests-1035-pass-50-intentional-skip-zero-fail',
        activeKernelProposalGate: 'bounded-make-check-pass'
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
        'does-not-mutate-the-pre-review-proposal',
        'does-not-itself-implement-SCALE-INDUCTIVE-1B1',
        'does-not-authorize-SCALE-INDUCTIVE-1B2',
        'does-not-authorize-automatic-eliminator-synthesis',
        'does-not-authorize-an-end-user-inductive-declaration-facade',
        'does-not-authorize-parser-or-surface-syntax',
        'does-not-authorize-active-profile-or-browser-promotion',
        'does-not-authorize-a-Lambdapi-source-change',
        'does-not-graduate-bulk-or-whole-development-transfer',
        'does-not-broaden-local-checkpoint-Git-authority'
    ],
    nextDependencyState: 'scale-inductive-1b1-implementation-ready'
} as const;

export type CoreLfScaleInductive1b1ReviewInput = typeof rawReview;

export type CoreLfScaleInductive1b1ReviewErrorCode =
    | 'INDUCTIVE_REVIEW_DECISION_DRIFT'
    | 'INDUCTIVE_REVIEW_PROPOSAL_DRIFT'
    | 'INDUCTIVE_REVIEW_AUTHORIZATION_DRIFT';

export class CoreLfScaleInductive1b1ReviewError extends Error {
    constructor(
        public readonly code:
            CoreLfScaleInductive1b1ReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfScaleInductive1b1ReviewError';
    }
}

export const CORE_LF_SCALE_INDUCTIVE_1B1_REVIEW =
    deepFreeze(rawReview);

export function validateCoreLfScaleInductive1b1Review(
    review: CoreLfScaleInductive1b1ReviewInput =
        CORE_LF_SCALE_INDUCTIVE_1B1_REVIEW
): void {
    if (
        review.revision !== 'SCALE-INDUCTIVE-1B1-REVIEWED-1' ||
        review.status !==
            'reviewed-approved-under-delegated-unattended-authority' ||
        review.approval.gate !==
            'H-DTTLF-SCALE-INDUCTIVE-01' ||
        review.approval.decisionId !==
            'D-DTTLF-SCALE-INDUCTIVE-001' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.authority !==
            'user-delegated-unattended-approval' ||
        review.approval.condition !==
            'no-immediate-human-objection-after-presented-' +
            'checkpointed-proposal' ||
        review.approval.recordedOn !== '2026-07-29' ||
        !review.approval.humanDecisionSupersedes
    ) {
        throw new CoreLfScaleInductive1b1ReviewError(
            'INDUCTIVE_REVIEW_DECISION_DRIFT',
            'The D-DTTLF-SCALE-INDUCTIVE-001 decision boundary drifted'
        );
    }

    validateCoreLfScaleInductive1b1Proposal(proposal);
    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.decision.status !== 'proposal-only' ||
        review.recommendation.status !==
            'proposal-awaiting-separate-review'
    ) {
        throw new CoreLfScaleInductive1b1ReviewError(
            'INDUCTIVE_REVIEW_PROPOSAL_DRIFT',
            'The review must retain the exact non-authorizing proposal'
        );
    }

    const authorization = review.authorization;
    if (
        authorization.implementationRow !==
            'SCALE-INDUCTIVE-1B1' ||
        !authorization.implementationAuthorized ||
        !sameData(
            authorization.exactImplementation,
            proposal.proposedImplementation
        ) ||
        !sameData(
            authorization.correctedIndices,
            proposal.representationCorrection.correctedIndices
        ) ||
        authorization.erasedSignatureDelta !== 'none' ||
        authorization.generatedOwner !== 'ind_τΣ_' ||
        authorization.generatedRuntimeRuleCount !== 1 ||
        authorization.generatedConsumer !==
            proposal.measuredAuthority.generatedConsumer ||
        !authorization.nonrecursiveIndexedOnly ||
        authorization.directRecursionAuthorized ||
        authorization.recursiveInductionHypothesisAuthorized ||
        authorization.generalStrictPositivityAuthorized ||
        authorization.automaticEliminatorSynthesisAuthorized ||
        authorization.endUserInductiveDeclarationFacadeAuthorized ||
        authorization.parserOrSurfaceSyntaxAuthorized ||
        authorization.activeProfileOrBrowserPromotionAuthorized ||
        authorization.LambdapiSourceChangeAuthorized ||
        authorization.bulkOrWholeTransferGraduationAuthorized ||
        authorization.externalOrDestructiveGitActionAuthorized ||
        !sameData(review.validation, rawReview.validation) ||
        !sameData(review.gitBoundary, rawReview.gitBoundary) ||
        !sameData(review.nonEffects, rawReview.nonEffects) ||
        review.nextDependencyState !==
            'scale-inductive-1b1-implementation-ready'
    ) {
        throw new CoreLfScaleInductive1b1ReviewError(
            'INDUCTIVE_REVIEW_AUTHORIZATION_DRIFT',
            'The review exceeded the exact nonrecursive 1B1 boundary'
        );
    }
}
