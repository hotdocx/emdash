/**
 * Separate immutable record for the DIRECTED-1C H-DTTLF-02 approval.
 *
 * The pre-review proposal remains unchanged. This artifact authorizes only
 * its exact one-owner, body-free, rule-free candidate integration.
 */

import {
    CORE_DIRECTED_1C_PROPOSAL,
    CoreDirected1cCandidateOwnerId,
    CoreDirected1cProposalInput,
    validateCoreDirected1cProposal
} from './directed_1c_proposal';

export interface CoreDirected1cReviewInput {
    readonly revision: 'DIRECTED-1C-REVIEWED';
    readonly gate: 'H-DTTLF-02/DIRECTED-1C';
    readonly decision: 'approved-as-proposed';
    readonly reviewedOn: '2026-07-24';
    readonly decisionEvidence:
        'Approve H-DTTLF-02/DIRECTED-1C as proposed.';
    readonly proposal: CoreDirected1cProposalInput;
    readonly authorization: {
        readonly isolatedCandidateIntegration: true;
        readonly ownerIds: readonly CoreDirected1cCandidateOwnerId[];
        readonly opaqueImportOwnerIds:
            readonly ['section-object-evaluation'];
        readonly activeTransparentDefinitionIds:
            readonly ['section-object-evaluation'];
        readonly transferredDefinitionBodyIds: readonly [];
        readonly runtimeRuleIds: readonly [];
        readonly proofTimeRuleIds: readonly [];
        readonly reuseExistingSectionCategory: true;
        readonly reuseGenericOuterLfBeta: true;
        readonly reuseDirected1bTelescopeFibreRule: true;
        readonly emittedShadowDeclarations: false;
        readonly defaultLfProfileChange: false;
        readonly browserEntryPoint: false;
        readonly deployedManifestChange: false;
        readonly directedGraduate1Preapproved: false;
        readonly newMetatheoryClaim: false;
    };
}

export type CoreDirected1cReviewErrorCode =
    | 'INVALID_REVIEW_DECISION'
    | 'REVIEW_PREREQUISITE_DRIFT'
    | 'REVIEW_PROPOSAL_DRIFT'
    | 'REVIEW_AUTHORIZATION_DRIFT';

export class CoreDirected1cReviewError extends Error {
    constructor(
        public readonly code: CoreDirected1cReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirected1cReviewError';
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

const rawReview: CoreDirected1cReviewInput = {
    revision: 'DIRECTED-1C-REVIEWED',
    gate: 'H-DTTLF-02/DIRECTED-1C',
    decision: 'approved-as-proposed',
    reviewedOn: '2026-07-24',
    decisionEvidence:
        'Approve H-DTTLF-02/DIRECTED-1C as proposed.',
    proposal: cloneData(CORE_DIRECTED_1C_PROPOSAL),
    authorization: {
        isolatedCandidateIntegration: true,
        ownerIds: ['section-object-evaluation'],
        opaqueImportOwnerIds: ['section-object-evaluation'],
        activeTransparentDefinitionIds: [
            'section-object-evaluation'
        ],
        transferredDefinitionBodyIds: [],
        runtimeRuleIds: [],
        proofTimeRuleIds: [],
        reuseExistingSectionCategory: true,
        reuseGenericOuterLfBeta: true,
        reuseDirected1bTelescopeFibreRule: true,
        emittedShadowDeclarations: false,
        defaultLfProfileChange: false,
        browserEntryPoint: false,
        deployedManifestChange: false,
        directedGraduate1Preapproved: false,
        newMetatheoryClaim: false
    }
};

export const CORE_DIRECTED_1C_REVIEW = deepFreeze(rawReview);

export function validateCoreDirected1cReview(
    review: CoreDirected1cReviewInput = CORE_DIRECTED_1C_REVIEW
): void {
    if (
        review.revision !== 'DIRECTED-1C-REVIEWED' ||
        review.gate !== 'H-DTTLF-02/DIRECTED-1C' ||
        review.decision !== 'approved-as-proposed' ||
        review.reviewedOn !== '2026-07-24' ||
        review.decisionEvidence !==
            'Approve H-DTTLF-02/DIRECTED-1C as proposed.'
    ) {
        throw new CoreDirected1cReviewError(
            'INVALID_REVIEW_DECISION',
            'The DIRECTED-1C review must preserve the exact ' +
            'H-DTTLF-02 approval'
        );
    }

    try {
        validateCoreDirected1cProposal(review.proposal);
    } catch (error: unknown) {
        throw new CoreDirected1cReviewError(
            'REVIEW_PREREQUISITE_DRIFT',
            'The DIRECTED-1C reviewed prerequisites or proposal drifted: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
    if (!sameData(review.proposal, CORE_DIRECTED_1C_PROPOSAL)) {
        throw new CoreDirected1cReviewError(
            'REVIEW_PROPOSAL_DRIFT',
            'The reviewed DIRECTED-1C proposal snapshot is not exact'
        );
    }

    if (
        !sameData(review.authorization, rawReview.authorization) ||
        !sameData(review, rawReview)
    ) {
        throw new CoreDirected1cReviewError(
            'REVIEW_AUTHORIZATION_DRIFT',
            'The DIRECTED-1C H-DTTLF-02 authorization boundary drifted'
        );
    }
}

validateCoreDirected1cReview();
