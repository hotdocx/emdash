/**
 * Separate immutable approval record for
 * H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-006.
 *
 * The frozen FIBRED-STRUCTURE-0A proposal remains non-self-authorizing.
 * This record binds the user's approval to that exact proposal without
 * broadening its kernel or profile boundary.
 */

import {
    CORE_CATEGORICAL_FIBRED_STRUCTURE_PROPOSAL,
    CoreCategoricalFibredStructureProposalInput,
    validateCoreCategoricalFibredStructureProposal
} from './categorical_fibred_structure_proposal';

export interface CoreCategoricalFibredStructureReviewInput {
    readonly revision: 'FIBRED-STRUCTURE-0A-REVIEWED';
    readonly status: 'reviewed-approved';
    readonly approval: {
        readonly gate: 'H-DTTLF-USABILITY-02';
        readonly decisionId: 'D-DTTLF-USABILITY-006';
        readonly decision: 'approved-as-proposed';
        readonly reviewedOn: '2026-07-27';
        readonly decisionEvidence:
            'Approve H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-006 as proposed';
    };
    readonly proposal: CoreCategoricalFibredStructureProposalInput;
    readonly authorization: {
        readonly authorizedSlice: 'FIBRED-STRUCTURE-1A';
        readonly newInjectiveOwners: readonly [
            'Product_projL_funcd',
            'Product_projR_funcd',
            'Product_pair_funcd'
        ];
        readonly newRuntimeRuleCount: 11;
        readonly productFamilyRemainsTransparent: true;
        readonly swapAndDiagonalRemainDerived: true;
        readonly groupedReindexingIsFrontendCanonicalization: true;
        readonly productCatdOwnerAuthorized: false;
        readonly kernelReindexingRuleAuthorized: false;
        readonly browserProfilePromotionAuthorized: false;
        readonly parserOrBulkTransferAuthorized: false;
    };
    readonly nextDependencyState:
        'implement-and-validate-fibred-structure-1a-only';
}

export type CoreCategoricalFibredStructureReviewErrorCode =
    | 'FIBRED_STRUCTURE_REVIEW_DECISION_DRIFT'
    | 'FIBRED_STRUCTURE_REVIEW_PROPOSAL_DRIFT'
    | 'FIBRED_STRUCTURE_REVIEW_AUTHORIZATION_DRIFT';

export class CoreCategoricalFibredStructureReviewError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalFibredStructureReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalFibredStructureReviewError';
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
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const proposalSnapshot = cloneData(
    CORE_CATEGORICAL_FIBRED_STRUCTURE_PROPOSAL
);

const rawReview: CoreCategoricalFibredStructureReviewInput = {
    revision: 'FIBRED-STRUCTURE-0A-REVIEWED',
    status: 'reviewed-approved',
    approval: {
        gate: 'H-DTTLF-USABILITY-02',
        decisionId: 'D-DTTLF-USABILITY-006',
        decision: 'approved-as-proposed',
        reviewedOn: '2026-07-27',
        decisionEvidence:
            'Approve H-DTTLF-USABILITY-02/D-DTTLF-USABILITY-006 as proposed'
    },
    proposal: proposalSnapshot,
    authorization: {
        authorizedSlice: 'FIBRED-STRUCTURE-1A',
        newInjectiveOwners: [
            'Product_projL_funcd',
            'Product_projR_funcd',
            'Product_pair_funcd'
        ],
        newRuntimeRuleCount: 11,
        productFamilyRemainsTransparent: true,
        swapAndDiagonalRemainDerived: true,
        groupedReindexingIsFrontendCanonicalization: true,
        productCatdOwnerAuthorized: false,
        kernelReindexingRuleAuthorized: false,
        browserProfilePromotionAuthorized: false,
        parserOrBulkTransferAuthorized: false
    },
    nextDependencyState:
        'implement-and-validate-fibred-structure-1a-only'
};

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_REVIEW =
    deepFreeze(rawReview);

export function validateCoreCategoricalFibredStructureReview(
    review: CoreCategoricalFibredStructureReviewInput =
        CORE_CATEGORICAL_FIBRED_STRUCTURE_REVIEW
): void {
    try {
        validateCoreCategoricalFibredStructureProposal();
    } catch (error: unknown) {
        throw new CoreCategoricalFibredStructureReviewError(
            'FIBRED_STRUCTURE_REVIEW_PROPOSAL_DRIFT',
            'FIBRED-STRUCTURE-0A proposal prerequisite drifted: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
    if (
        review.approval.gate !== 'H-DTTLF-USABILITY-02' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-006' ||
        review.approval.decisionEvidence !==
            'Approve H-DTTLF-USABILITY-02/' +
            'D-DTTLF-USABILITY-006 as proposed'
    ) {
        throw new CoreCategoricalFibredStructureReviewError(
            'FIBRED_STRUCTURE_REVIEW_DECISION_DRIFT',
            'D-DTTLF-USABILITY-006 exact approval evidence drifted'
        );
    }
    if (
        !sameData(review.proposal, proposalSnapshot) ||
        review.proposal.recommendation.authorityAuthorized
    ) {
        throw new CoreCategoricalFibredStructureReviewError(
            'FIBRED_STRUCTURE_REVIEW_PROPOSAL_DRIFT',
            'The immutable non-authorizing proposal snapshot drifted'
        );
    }
    if (
        review.authorization.newRuntimeRuleCount !== 11 ||
        review.authorization.productCatdOwnerAuthorized ||
        review.authorization.kernelReindexingRuleAuthorized ||
        review.authorization.browserProfilePromotionAuthorized ||
        review.authorization.parserOrBulkTransferAuthorized
    ) {
        throw new CoreCategoricalFibredStructureReviewError(
            'FIBRED_STRUCTURE_REVIEW_AUTHORIZATION_DRIFT',
            'D-006 authorization broadened or lost its exact boundary'
        );
    }
    if (!sameData(review, rawReview)) {
        throw new CoreCategoricalFibredStructureReviewError(
            'FIBRED_STRUCTURE_REVIEW_AUTHORIZATION_DRIFT',
            'D-006 review record drifted'
        );
    }
}

validateCoreCategoricalFibredStructureReview();
