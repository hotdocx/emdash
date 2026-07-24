/**
 * Separate immutable record for the DIRECTED-FOUNDATION-2 H-DTTLF-02
 * approval.
 *
 * The pre-review proposal and every earlier approved artifact remain
 * unchanged.
 */

import {
    CORE_DIRECTED_1B_REVIEW,
    validateCoreDirected1bReview
} from './directed_1b_review';
import {
    CORE_DIRECTED_FOUNDATION_2_PROPOSAL,
    CoreDirectedFoundation2ProposalInput,
    CoreDirectedFoundation2RuleId,
    validateCoreDirectedFoundation2Proposal
} from './directed_foundation_2_proposal';
import {
    CORE_DIRECTED_FOUNDATION_REVIEW,
    validateCoreDirectedFoundationReview
} from './directed_foundation_review';

export interface CoreDirectedFoundation2ReviewInput {
    readonly revision: 'DIRECTED-FOUNDATION-2-REVIEWED';
    readonly gate: 'H-DTTLF-02/DIRECTED-FOUNDATION-2';
    readonly decision: 'approved-as-proposed';
    readonly reviewedOn: '2026-07-24';
    readonly decisionEvidence:
        'Approve H-DTTLF-02/DIRECTED-FOUNDATION-2 as proposed.';
    readonly proposal: CoreDirectedFoundation2ProposalInput;
    readonly authorization: {
        readonly isolatedCandidateIntegration: true;
        readonly runtimeRuleIds:
            readonly CoreDirectedFoundation2RuleId[];
        readonly ownerIds: readonly [];
        readonly proofTimeRuleIds: readonly [];
        readonly runtimeScope: 'directed-catalog-local';
        readonly runtimeOrder:
            'foundation-1-before-foundation-2-before-directed-1b-before-frozen-mvp';
        readonly sharedOuterLfBudget: true;
        readonly redexScope: 'decoded-category-hom-only';
        readonly rawClassifierRewrite: false;
        readonly categoryHeadRewrite: false;
        readonly defaultLfProfileChange: false;
        readonly browserEntryPoint: false;
        readonly deployedManifestChange: false;
        readonly arbitraryUserRules: false;
        readonly approvedArtifactChange: false;
        readonly newMetatheoryClaim: false;
    };
}

export type CoreDirectedFoundation2ReviewErrorCode =
    | 'INVALID_REVIEW_DECISION'
    | 'REVIEW_PREREQUISITE_DRIFT'
    | 'REVIEW_PROPOSAL_DRIFT'
    | 'REVIEW_AUTHORIZATION_DRIFT';

export class CoreDirectedFoundation2ReviewError extends Error {
    constructor(
        public readonly code:
            CoreDirectedFoundation2ReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirectedFoundation2ReviewError';
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

const rawReview: CoreDirectedFoundation2ReviewInput = {
    revision: 'DIRECTED-FOUNDATION-2-REVIEWED',
    gate: 'H-DTTLF-02/DIRECTED-FOUNDATION-2',
    decision: 'approved-as-proposed',
    reviewedOn: '2026-07-24',
    decisionEvidence:
        'Approve H-DTTLF-02/DIRECTED-FOUNDATION-2 as proposed.',
    proposal: cloneData(CORE_DIRECTED_FOUNDATION_2_PROPOSAL),
    authorization: {
        isolatedCandidateIntegration: true,
        runtimeRuleIds: ['directed.category-hom.decode'],
        ownerIds: [],
        proofTimeRuleIds: [],
        runtimeScope: 'directed-catalog-local',
        runtimeOrder:
            'foundation-1-before-foundation-2-before-directed-1b-before-frozen-mvp',
        sharedOuterLfBudget: true,
        redexScope: 'decoded-category-hom-only',
        rawClassifierRewrite: false,
        categoryHeadRewrite: false,
        defaultLfProfileChange: false,
        browserEntryPoint: false,
        deployedManifestChange: false,
        arbitraryUserRules: false,
        approvedArtifactChange: false,
        newMetatheoryClaim: false
    }
};

export const CORE_DIRECTED_FOUNDATION_2_REVIEW =
    deepFreeze(rawReview);

export function validateCoreDirectedFoundation2Review(
    review: CoreDirectedFoundation2ReviewInput =
        CORE_DIRECTED_FOUNDATION_2_REVIEW
): void {
    if (
        review.revision !== 'DIRECTED-FOUNDATION-2-REVIEWED' ||
        review.gate !==
            'H-DTTLF-02/DIRECTED-FOUNDATION-2' ||
        review.decision !== 'approved-as-proposed' ||
        review.reviewedOn !== '2026-07-24' ||
        review.decisionEvidence !==
            'Approve H-DTTLF-02/DIRECTED-FOUNDATION-2 as proposed.'
    ) {
        throw new CoreDirectedFoundation2ReviewError(
            'INVALID_REVIEW_DECISION',
            'The DIRECTED-FOUNDATION-2 review must preserve the exact ' +
            'H-DTTLF-02 approval'
        );
    }

    try {
        validateCoreDirectedFoundationReview(
            CORE_DIRECTED_FOUNDATION_REVIEW
        );
        validateCoreDirected1bReview(CORE_DIRECTED_1B_REVIEW);
    } catch (error: unknown) {
        throw new CoreDirectedFoundation2ReviewError(
            'REVIEW_PREREQUISITE_DRIFT',
            'An approved DIRECTED-FOUNDATION-2 prerequisite drifted: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }

    try {
        validateCoreDirectedFoundation2Proposal(review.proposal);
    } catch (error: unknown) {
        throw new CoreDirectedFoundation2ReviewError(
            'REVIEW_PROPOSAL_DRIFT',
            'The reviewed proposal differs from ' +
            'DIRECTED-FOUNDATION-2: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
    if (!sameData(
        review.proposal,
        CORE_DIRECTED_FOUNDATION_2_PROPOSAL
    )) {
        throw new CoreDirectedFoundation2ReviewError(
            'REVIEW_PROPOSAL_DRIFT',
            'The reviewed DIRECTED-FOUNDATION-2 proposal snapshot is not exact'
        );
    }

    if (
        !sameData(review.authorization, rawReview.authorization) ||
        !sameData(review, rawReview)
    ) {
        throw new CoreDirectedFoundation2ReviewError(
            'REVIEW_AUTHORIZATION_DRIFT',
            'The DIRECTED-FOUNDATION-2 H-DTTLF-02 authorization drifted'
        );
    }
}

validateCoreDirectedFoundation2Review();
