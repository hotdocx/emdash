/**
 * Separate immutable approval record for
 * H-DTTLF-USABILITY-DEPENDENT/D-DTTLF-USABILITY-003.
 *
 * The pre-review proposal remains unchanged and non-self-authorizing. This
 * artifact authorizes only its semantic architecture and bounded
 * USABILITY-DEPENDENT-1A witness.
 */

import {
    CORE_CATEGORICAL_DEPENDENT_USABILITY_PROPOSAL,
    CoreCategoricalDependentUsabilityProposalInput,
    validateCoreCategoricalDependentUsabilityProposal
} from './categorical_dependent_usability_proposal';

export interface CoreCategoricalDependentUsabilityReviewInput {
    readonly revision: 'USABILITY-DEPENDENT-PLAN-0-REVIEWED';
    readonly status: 'reviewed-approved';
    readonly approval: {
        readonly gate: 'H-DTTLF-USABILITY-DEPENDENT';
        readonly decisionId: 'D-DTTLF-USABILITY-003';
        readonly decision: 'approved-as-proposed';
        readonly reviewedOn: '2026-07-26';
        readonly decisionEvidence:
            'Approve H-DTTLF-USABILITY-DEPENDENT/D-DTTLF-USABILITY-003 as proposed.';
    };
    /**
     * Immutable snapshot of the exact pre-review proposal. Its nested
     * `authorityAuthorized: false` remains historical evidence.
     */
    readonly proposal:
        CoreCategoricalDependentUsabilityProposalInput;
    readonly authorization: {
        readonly semanticArchitecture:
            'dependent-first-with-classified-constant-family-bridge';
        readonly algorithmPolicy:
            'shared-or-distinct-is-evidence-driven';
        readonly implementationUniformityRequired: false;
        readonly implementationSeparationRequired: false;
        readonly authorizedSlice: 'USABILITY-DEPENDENT-1A';
        readonly authorizedWitness:
            'λ k :^n K. FF[k](s[k])';
        readonly authorizedLowering:
            'generic-comp_fapp0-at-Catd_cat-K';
        readonly transferExistingActiveClosureAuthorized: true;
        readonly newLambdapiOwnerOrMathematicalRuleAuthorized: false;
        readonly generalDependentBracketAuthorized: false;
        readonly browserOrProductProfilePromotionAuthorized: false;
        readonly parserOrAcquisitionSelectionAuthorized: false;
        readonly bulkTransferResumptionAuthorized: false;
    };
    readonly successCriterion: {
        readonly endUserUsability:
            'natural-scalable-generalizable';
        readonly authorityCorrectness: 'required';
        readonly firstOrderScopedRepresentation: 'required';
        readonly genericLfChecking: 'required';
        readonly boundedConformance: 'required';
        readonly sharedImplementationShape: 'not-a-gate';
    };
    readonly retainedAlternatives:
        CoreCategoricalDependentUsabilityProposalInput[
            'architectureAlternativesRetained'
        ];
    readonly nonEffects:
        CoreCategoricalDependentUsabilityProposalInput['nonEffects'];
    readonly nextDependencyState:
        'implement-and-validate-usability-dependent-1a-only';
}

export type CoreCategoricalDependentUsabilityReviewErrorCode =
    | 'DEPENDENT_USABILITY_REVIEW_DECISION_DRIFT'
    | 'DEPENDENT_USABILITY_REVIEW_PROPOSAL_DRIFT'
    | 'DEPENDENT_USABILITY_REVIEW_AUTHORIZATION_DRIFT';

export class CoreCategoricalDependentUsabilityReviewError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDependentUsabilityReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDependentUsabilityReviewError';
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
    CORE_CATEGORICAL_DEPENDENT_USABILITY_PROPOSAL
);

const rawReview: CoreCategoricalDependentUsabilityReviewInput = {
    revision: 'USABILITY-DEPENDENT-PLAN-0-REVIEWED',
    status: 'reviewed-approved',
    approval: {
        gate: 'H-DTTLF-USABILITY-DEPENDENT',
        decisionId: 'D-DTTLF-USABILITY-003',
        decision: 'approved-as-proposed',
        reviewedOn: '2026-07-26',
        decisionEvidence:
            'Approve H-DTTLF-USABILITY-DEPENDENT/D-DTTLF-USABILITY-003 as proposed.'
    },
    proposal: proposalSnapshot,
    authorization: {
        semanticArchitecture:
            'dependent-first-with-classified-constant-family-bridge',
        algorithmPolicy:
            'shared-or-distinct-is-evidence-driven',
        implementationUniformityRequired: false,
        implementationSeparationRequired: false,
        authorizedSlice: 'USABILITY-DEPENDENT-1A',
        authorizedWitness:
            'λ k :^n K. FF[k](s[k])',
        authorizedLowering:
            'generic-comp_fapp0-at-Catd_cat-K',
        transferExistingActiveClosureAuthorized: true,
        newLambdapiOwnerOrMathematicalRuleAuthorized: false,
        generalDependentBracketAuthorized: false,
        browserOrProductProfilePromotionAuthorized: false,
        parserOrAcquisitionSelectionAuthorized: false,
        bulkTransferResumptionAuthorized: false
    },
    successCriterion: {
        endUserUsability:
            'natural-scalable-generalizable',
        authorityCorrectness: 'required',
        firstOrderScopedRepresentation: 'required',
        genericLfChecking: 'required',
        boundedConformance: 'required',
        sharedImplementationShape: 'not-a-gate'
    },
    retainedAlternatives:
        cloneData(
            CORE_CATEGORICAL_DEPENDENT_USABILITY_PROPOSAL
                .architectureAlternativesRetained
        ),
    nonEffects:
        cloneData(
            CORE_CATEGORICAL_DEPENDENT_USABILITY_PROPOSAL
                .nonEffects
        ),
    nextDependencyState:
        'implement-and-validate-usability-dependent-1a-only'
};

export const CORE_CATEGORICAL_DEPENDENT_USABILITY_REVIEW =
    deepFreeze(rawReview);

export function validateCoreCategoricalDependentUsabilityReview(
    review: CoreCategoricalDependentUsabilityReviewInput =
        CORE_CATEGORICAL_DEPENDENT_USABILITY_REVIEW
): void {
    try {
        validateCoreCategoricalDependentUsabilityProposal();
    } catch (error: unknown) {
        throw new CoreCategoricalDependentUsabilityReviewError(
            'DEPENDENT_USABILITY_REVIEW_PROPOSAL_DRIFT',
            'Dependent usability proposal prerequisite drifted: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
    if (
        review.approval.gate !==
            'H-DTTLF-USABILITY-DEPENDENT' ||
        review.approval.decisionId !==
            'D-DTTLF-USABILITY-003' ||
        review.approval.decisionEvidence !==
            'Approve H-DTTLF-USABILITY-DEPENDENT/' +
            'D-DTTLF-USABILITY-003 as proposed.'
    ) {
        throw new CoreCategoricalDependentUsabilityReviewError(
            'DEPENDENT_USABILITY_REVIEW_DECISION_DRIFT',
            'D-DTTLF-USABILITY-003 exact approval evidence drifted'
        );
    }
    if (
        !sameData(review.proposal, proposalSnapshot) ||
        review.proposal.recommendation.authorityAuthorized
    ) {
        throw new CoreCategoricalDependentUsabilityReviewError(
            'DEPENDENT_USABILITY_REVIEW_PROPOSAL_DRIFT',
            'The immutable non-authorizing proposal snapshot drifted'
        );
    }
    if (
        review.authorization.implementationUniformityRequired ||
        review.authorization.implementationSeparationRequired ||
        review.authorization.generalDependentBracketAuthorized ||
        review.authorization
            .newLambdapiOwnerOrMathematicalRuleAuthorized ||
        review.authorization
            .browserOrProductProfilePromotionAuthorized ||
        review.authorization
            .parserOrAcquisitionSelectionAuthorized ||
        review.authorization.bulkTransferResumptionAuthorized ||
        review.authorization.algorithmPolicy !==
            'shared-or-distinct-is-evidence-driven'
    ) {
        throw new CoreCategoricalDependentUsabilityReviewError(
            'DEPENDENT_USABILITY_REVIEW_AUTHORIZATION_DRIFT',
            'D-003 authorization broadened or lost algorithm neutrality'
        );
    }
    if (!sameData(review, rawReview)) {
        throw new CoreCategoricalDependentUsabilityReviewError(
            'DEPENDENT_USABILITY_REVIEW_AUTHORIZATION_DRIFT',
            'D-003 review record drifted'
        );
    }
}

validateCoreCategoricalDependentUsabilityReview();
