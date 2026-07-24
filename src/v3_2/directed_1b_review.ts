/**
 * Separate immutable record for the DIRECTED-1B H-DTTLF-02 approval.
 *
 * The pre-review proposal remains unchanged. This artifact authorizes only
 * its exact five-owner, one-definition, three-runtime-rule candidate slice.
 */

import {
    CORE_DIRECTED_1A_REVIEW,
    CORE_LF_CONTINUATION_PROFILE_REVIEW,
    validateCoreDirected1aReview,
    validateCoreLfContinuationProfileReview
} from './continuation_review';
import {
    CORE_DIRECTED_1B_PROPOSAL,
    CoreDirected1bCandidateOwnerId,
    CoreDirected1bProposalInput,
    CoreDirected1bRuntimeRuleId,
    validateCoreDirected1bProposal
} from './directed_1b_proposal';

export interface CoreDirected1bReviewInput {
    readonly revision: 'DIRECTED-1B-REVIEWED';
    readonly gate: 'H-DTTLF-02/DIRECTED-1B';
    readonly decision: 'approved-as-proposed';
    readonly reviewedOn: '2026-07-24';
    readonly decisionEvidence:
        'Approve H-DTTLF-02/DIRECTED-1B as proposed.';
    readonly proposal: CoreDirected1bProposalInput;
    readonly authorization: {
        readonly isolatedCandidateIntegration: true;
        readonly ownerIds: readonly CoreDirected1bCandidateOwnerId[];
        readonly checkedTransparentDefinitionIds:
            readonly ['sigma-telescope-transport'];
        readonly runtimeRuleIds:
            readonly CoreDirected1bRuntimeRuleId[];
        readonly proofTimeRuleIds: readonly [];
        readonly runtimeScope: 'directed-catalog-local';
        readonly sharedOuterLfBudget: true;
        readonly defaultLfProfileChange: false;
        readonly browserEntryPoint: false;
        readonly deployedManifestChange: false;
        readonly generalSigmaHomPreapproved: false;
        readonly directed1cPreapproved: false;
        readonly newMetatheoryClaim: false;
    };
}

export type CoreDirected1bReviewErrorCode =
    | 'INVALID_REVIEW_DECISION'
    | 'REVIEW_PREREQUISITE_DRIFT'
    | 'REVIEW_PROPOSAL_DRIFT'
    | 'REVIEW_AUTHORIZATION_DRIFT';

export class CoreDirected1bReviewError extends Error {
    constructor(
        public readonly code: CoreDirected1bReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirected1bReviewError';
    }
}

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(item =>
            deepFreeze(item)
        );
        Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const rawReview: CoreDirected1bReviewInput = {
    revision: 'DIRECTED-1B-REVIEWED',
    gate: 'H-DTTLF-02/DIRECTED-1B',
    decision: 'approved-as-proposed',
    reviewedOn: '2026-07-24',
    decisionEvidence:
        'Approve H-DTTLF-02/DIRECTED-1B as proposed.',
    proposal: cloneData(CORE_DIRECTED_1B_PROPOSAL),
    authorization: {
        isolatedCandidateIntegration: true,
        ownerIds: [
            'decoded-dependent-pair',
            'dependent-pair',
            'sigma-first-projection',
            'sigma-transport-arrow',
            'sigma-telescope-transport'
        ],
        checkedTransparentDefinitionIds: [
            'sigma-telescope-transport'
        ],
        runtimeRuleIds: [
            'directed.sigma-object.decode',
            'directed.sigma-first-projection.evaluate',
            'directed.sigma-telescope-fibre.evaluate'
        ],
        proofTimeRuleIds: [],
        runtimeScope: 'directed-catalog-local',
        sharedOuterLfBudget: true,
        defaultLfProfileChange: false,
        browserEntryPoint: false,
        deployedManifestChange: false,
        generalSigmaHomPreapproved: false,
        directed1cPreapproved: false,
        newMetatheoryClaim: false
    }
};

export const CORE_DIRECTED_1B_REVIEW = deepFreeze(rawReview);

export function validateCoreDirected1bReview(
    review: CoreDirected1bReviewInput = CORE_DIRECTED_1B_REVIEW
): void {
    if (
        review.revision !== 'DIRECTED-1B-REVIEWED' ||
        review.gate !== 'H-DTTLF-02/DIRECTED-1B' ||
        review.decision !== 'approved-as-proposed' ||
        review.reviewedOn !== '2026-07-24' ||
        review.decisionEvidence !==
            'Approve H-DTTLF-02/DIRECTED-1B as proposed.'
    ) {
        throw new CoreDirected1bReviewError(
            'INVALID_REVIEW_DECISION',
            'The DIRECTED-1B review must preserve the exact ' +
            'H-DTTLF-02 approval'
        );
    }

    try {
        validateCoreLfContinuationProfileReview(
            CORE_LF_CONTINUATION_PROFILE_REVIEW
        );
        validateCoreDirected1aReview(CORE_DIRECTED_1A_REVIEW);
    } catch (error: unknown) {
        throw new CoreDirected1bReviewError(
            'REVIEW_PREREQUISITE_DRIFT',
            'The DIRECTED-1B reviewed prerequisites drifted: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }

    try {
        validateCoreDirected1bProposal(review.proposal);
    } catch (error: unknown) {
        throw new CoreDirected1bReviewError(
            'REVIEW_PROPOSAL_DRIFT',
            'The reviewed proposal differs from DIRECTED-1B: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
    if (!sameData(review.proposal, CORE_DIRECTED_1B_PROPOSAL)) {
        throw new CoreDirected1bReviewError(
            'REVIEW_PROPOSAL_DRIFT',
            'The reviewed DIRECTED-1B proposal snapshot is not exact'
        );
    }

    if (
        !sameData(review.authorization, rawReview.authorization) ||
        !sameData(review, rawReview)
    ) {
        throw new CoreDirected1bReviewError(
            'REVIEW_AUTHORIZATION_DRIFT',
            'The DIRECTED-1B H-DTTLF-02 authorization boundary drifted'
        );
    }
}

validateCoreDirected1bReview();
