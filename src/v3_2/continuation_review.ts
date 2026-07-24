/**
 * Separate immutable records for the user's H-DTTLF-01 and H-DTTLF-02
 * approvals. The pre-review proposals remain unchanged.
 */

import {
    CORE_DIRECTED_1A_PROPOSAL,
    CoreDirected1aCandidateOwnerId,
    CoreDirected1aProposalInput,
    validateCoreDirected1aProposal
} from './directed_1a_proposal';
import {
    CORE_LF_CONTINUATION_PROFILE_PROPOSAL,
    CoreLfProfileProposalInput,
    validateCoreLfProfileProposal
} from './lf_profile_proposal';

export interface CoreLfContinuationProfileReviewInput {
    readonly revision: 'LF-PROFILE-1-REVIEWED';
    readonly gate: 'H-DTTLF-01';
    readonly decision: 'approved-as-proposed';
    readonly reviewedOn: '2026-07-24';
    readonly decisionEvidence:
        'Approve H-DTTLF-01 and H-DTTLF-02 as proposed.';
    readonly proposal: CoreLfProfileProposalInput;
    readonly authorization: {
        readonly activeContinuationCheckerApi: true;
        readonly directedCandidateUse: true;
        readonly browserEntryPoint: false;
        readonly deployedManifestChange: false;
        readonly arbitraryUserRules: false;
        readonly newMetatheoryClaim: false;
    };
}

export interface CoreDirected1aReviewInput {
    readonly revision: 'DIRECTED-1A-REVIEWED';
    readonly gate: 'H-DTTLF-02';
    readonly decision: 'approved-as-proposed';
    readonly reviewedOn: '2026-07-24';
    readonly decisionEvidence:
        'Approve H-DTTLF-01 and H-DTTLF-02 as proposed.';
    readonly proposal: CoreDirected1aProposalInput;
    readonly authorization: {
        readonly isolatedCandidateCatalogIntegration: true;
        readonly ownerIds:
            readonly CoreDirected1aCandidateOwnerId[];
        readonly runtimeRuleIds: readonly [];
        readonly proofTimeRuleIds: readonly [];
        readonly browserEntryPoint: false;
        readonly deployedManifestChange: false;
        readonly directed1bRulesPreapproved: false;
    };
}

export type CoreContinuationReviewErrorCode =
    | 'INVALID_REVIEW_DECISION'
    | 'REVIEW_PROPOSAL_DRIFT'
    | 'REVIEW_AUTHORIZATION_DRIFT';

export class CoreContinuationReviewError extends Error {
    constructor(
        public readonly code: CoreContinuationReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreContinuationReviewError';
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

const rawLfReview: CoreLfContinuationProfileReviewInput = {
    revision: 'LF-PROFILE-1-REVIEWED',
    gate: 'H-DTTLF-01',
    decision: 'approved-as-proposed',
    reviewedOn: '2026-07-24',
    decisionEvidence:
        'Approve H-DTTLF-01 and H-DTTLF-02 as proposed.',
    proposal: cloneData(CORE_LF_CONTINUATION_PROFILE_PROPOSAL),
    authorization: {
        activeContinuationCheckerApi: true,
        directedCandidateUse: true,
        browserEntryPoint: false,
        deployedManifestChange: false,
        arbitraryUserRules: false,
        newMetatheoryClaim: false
    }
};

const rawDirectedReview: CoreDirected1aReviewInput = {
    revision: 'DIRECTED-1A-REVIEWED',
    gate: 'H-DTTLF-02',
    decision: 'approved-as-proposed',
    reviewedOn: '2026-07-24',
    decisionEvidence:
        'Approve H-DTTLF-01 and H-DTTLF-02 as proposed.',
    proposal: cloneData(CORE_DIRECTED_1A_PROPOSAL),
    authorization: {
        isolatedCandidateCatalogIntegration: true,
        ownerIds: [
            'displayed-functor-category',
            'sigma-category',
            'sigma-telescope-family'
        ],
        runtimeRuleIds: [],
        proofTimeRuleIds: [],
        browserEntryPoint: false,
        deployedManifestChange: false,
        directed1bRulesPreapproved: false
    }
};

export const CORE_LF_CONTINUATION_PROFILE_REVIEW =
    deepFreeze(rawLfReview);

export const CORE_DIRECTED_1A_REVIEW =
    deepFreeze(rawDirectedReview);

export function validateCoreLfContinuationProfileReview(
    review: CoreLfContinuationProfileReviewInput =
        CORE_LF_CONTINUATION_PROFILE_REVIEW
): void {
    if (
        review.revision !== 'LF-PROFILE-1-REVIEWED' ||
        review.gate !== 'H-DTTLF-01' ||
        review.decision !== 'approved-as-proposed' ||
        review.reviewedOn !== '2026-07-24' ||
        review.decisionEvidence !==
            'Approve H-DTTLF-01 and H-DTTLF-02 as proposed.'
    ) {
        throw new CoreContinuationReviewError(
            'INVALID_REVIEW_DECISION',
            'The LF continuation review must preserve the exact ' +
            'H-DTTLF-01 approval'
        );
    }
    try {
        validateCoreLfProfileProposal(review.proposal);
    } catch (error: unknown) {
        throw new CoreContinuationReviewError(
            'REVIEW_PROPOSAL_DRIFT',
            'The reviewed LF profile differs from LF-PROFILE-1: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
    if (
        !sameData(review.proposal, CORE_LF_CONTINUATION_PROFILE_PROPOSAL)
    ) {
        throw new CoreContinuationReviewError(
            'REVIEW_PROPOSAL_DRIFT',
            'The reviewed LF profile snapshot is not exact'
        );
    }
    if (
        !sameData(review.authorization, rawLfReview.authorization) ||
        !sameData(review, rawLfReview)
    ) {
        throw new CoreContinuationReviewError(
            'REVIEW_AUTHORIZATION_DRIFT',
            'The H-DTTLF-01 authorization boundary drifted'
        );
    }
}

export function validateCoreDirected1aReview(
    review: CoreDirected1aReviewInput = CORE_DIRECTED_1A_REVIEW
): void {
    if (
        review.revision !== 'DIRECTED-1A-REVIEWED' ||
        review.gate !== 'H-DTTLF-02' ||
        review.decision !== 'approved-as-proposed' ||
        review.reviewedOn !== '2026-07-24' ||
        review.decisionEvidence !==
            'Approve H-DTTLF-01 and H-DTTLF-02 as proposed.'
    ) {
        throw new CoreContinuationReviewError(
            'INVALID_REVIEW_DECISION',
            'The directed review must preserve the exact H-DTTLF-02 approval'
        );
    }
    try {
        validateCoreDirected1aProposal(review.proposal);
    } catch (error: unknown) {
        throw new CoreContinuationReviewError(
            'REVIEW_PROPOSAL_DRIFT',
            'The reviewed directed proposal differs from DIRECTED-1A: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
    if (!sameData(review.proposal, CORE_DIRECTED_1A_PROPOSAL)) {
        throw new CoreContinuationReviewError(
            'REVIEW_PROPOSAL_DRIFT',
            'The reviewed directed proposal snapshot is not exact'
        );
    }
    if (
        !sameData(
            review.authorization,
            rawDirectedReview.authorization
        ) ||
        !sameData(review, rawDirectedReview)
    ) {
        throw new CoreContinuationReviewError(
            'REVIEW_AUTHORIZATION_DRIFT',
            'The H-DTTLF-02 authorization boundary drifted'
        );
    }
}

validateCoreLfContinuationProfileReview();
validateCoreDirected1aReview();
