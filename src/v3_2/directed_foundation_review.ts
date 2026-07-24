/**
 * Separate immutable record for the DIRECTED-FOUNDATION-1 H-DTTLF-02
 * approval.
 *
 * The pre-review proposal and the already-approved DIRECTED-1B artifacts
 * remain unchanged.
 */

import {
    CORE_DIRECTED_1B_REVIEW,
    validateCoreDirected1bReview
} from './directed_1b_review';
import {
    CORE_DIRECTED_FOUNDATION_PROPOSAL,
    CoreDirectedFoundationProposalInput,
    CoreDirectedFoundationRuleId,
    validateCoreDirectedFoundationProposal
} from './directed_foundation_proposal';

export interface CoreDirectedFoundationReviewInput {
    readonly revision: 'DIRECTED-FOUNDATION-1-REVIEWED';
    readonly gate: 'H-DTTLF-02/DIRECTED-FOUNDATION-1';
    readonly decision: 'approved-as-proposed';
    readonly reviewedOn: '2026-07-24';
    readonly decisionEvidence:
        'Approve H-DTTLF-02/DIRECTED-FOUNDATION-1 as proposed.';
    readonly proposal: CoreDirectedFoundationProposalInput;
    readonly authorization: {
        readonly isolatedCandidateIntegration: true;
        readonly runtimeRuleIds:
            readonly CoreDirectedFoundationRuleId[];
        readonly ownerIds: readonly [];
        readonly proofTimeRuleIds: readonly [];
        readonly runtimeScope: 'directed-catalog-local';
        readonly runtimeOrder:
            'foundation-before-directed-1b-before-frozen-mvp';
        readonly sharedOuterLfBudget: true;
        readonly stableCategoryHeadRewrites: false;
        readonly defaultLfProfileChange: false;
        readonly browserEntryPoint: false;
        readonly deployedManifestChange: false;
        readonly arbitraryUserRules: false;
        readonly approvedDirected1bArtifactChange: false;
        readonly newMetatheoryClaim: false;
    };
}

export type CoreDirectedFoundationReviewErrorCode =
    | 'INVALID_REVIEW_DECISION'
    | 'REVIEW_PREREQUISITE_DRIFT'
    | 'REVIEW_PROPOSAL_DRIFT'
    | 'REVIEW_AUTHORIZATION_DRIFT';

export class CoreDirectedFoundationReviewError extends Error {
    constructor(
        public readonly code: CoreDirectedFoundationReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirectedFoundationReviewError';
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

const rawReview: CoreDirectedFoundationReviewInput = {
    revision: 'DIRECTED-FOUNDATION-1-REVIEWED',
    gate: 'H-DTTLF-02/DIRECTED-FOUNDATION-1',
    decision: 'approved-as-proposed',
    reviewedOn: '2026-07-24',
    decisionEvidence:
        'Approve H-DTTLF-02/DIRECTED-FOUNDATION-1 as proposed.',
    proposal: cloneData(CORE_DIRECTED_FOUNDATION_PROPOSAL),
    authorization: {
        isolatedCandidateIntegration: true,
        runtimeRuleIds: [
            'directed.category-object.decode',
            'directed.displayed-family.decode',
            'directed.displayed-functor.decode'
        ],
        ownerIds: [],
        proofTimeRuleIds: [],
        runtimeScope: 'directed-catalog-local',
        runtimeOrder:
            'foundation-before-directed-1b-before-frozen-mvp',
        sharedOuterLfBudget: true,
        stableCategoryHeadRewrites: false,
        defaultLfProfileChange: false,
        browserEntryPoint: false,
        deployedManifestChange: false,
        arbitraryUserRules: false,
        approvedDirected1bArtifactChange: false,
        newMetatheoryClaim: false
    }
};

export const CORE_DIRECTED_FOUNDATION_REVIEW =
    deepFreeze(rawReview);

export function validateCoreDirectedFoundationReview(
    review: CoreDirectedFoundationReviewInput =
        CORE_DIRECTED_FOUNDATION_REVIEW
): void {
    if (
        review.revision !== 'DIRECTED-FOUNDATION-1-REVIEWED' ||
        review.gate !==
            'H-DTTLF-02/DIRECTED-FOUNDATION-1' ||
        review.decision !== 'approved-as-proposed' ||
        review.reviewedOn !== '2026-07-24' ||
        review.decisionEvidence !==
            'Approve H-DTTLF-02/DIRECTED-FOUNDATION-1 as proposed.'
    ) {
        throw new CoreDirectedFoundationReviewError(
            'INVALID_REVIEW_DECISION',
            'The DIRECTED-FOUNDATION-1 review must preserve the exact ' +
            'H-DTTLF-02 approval'
        );
    }

    try {
        validateCoreDirected1bReview(CORE_DIRECTED_1B_REVIEW);
    } catch (error: unknown) {
        throw new CoreDirectedFoundationReviewError(
            'REVIEW_PREREQUISITE_DRIFT',
            'The approved DIRECTED-1B prerequisite drifted: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }

    try {
        validateCoreDirectedFoundationProposal(review.proposal);
    } catch (error: unknown) {
        throw new CoreDirectedFoundationReviewError(
            'REVIEW_PROPOSAL_DRIFT',
            'The reviewed proposal differs from ' +
            'DIRECTED-FOUNDATION-1: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
    if (
        !sameData(
            review.proposal,
            CORE_DIRECTED_FOUNDATION_PROPOSAL
        )
    ) {
        throw new CoreDirectedFoundationReviewError(
            'REVIEW_PROPOSAL_DRIFT',
            'The reviewed DIRECTED-FOUNDATION-1 proposal snapshot is not exact'
        );
    }

    if (
        !sameData(review.authorization, rawReview.authorization) ||
        !sameData(review, rawReview)
    ) {
        throw new CoreDirectedFoundationReviewError(
            'REVIEW_AUTHORIZATION_DRIFT',
            'The DIRECTED-FOUNDATION-1 H-DTTLF-02 authorization drifted'
        );
    }
}

validateCoreDirectedFoundationReview();
