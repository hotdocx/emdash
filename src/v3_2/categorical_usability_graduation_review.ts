/**
 * Separate immutable record for
 * H-DTTLF-USABILITY-GRADUATE/D-DTTLF-USABILITY-002.
 *
 * The pre-review USABILITY-GRADUATE-1 proposal remains unchanged and
 * non-self-authorizing. This artifact settles only the exact qualified
 * frontend architecture envelope approved by the user. It does not install
 * semantic authority, promote a product profile, or select follow-on
 * transfer work.
 */

import {
    CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL,
    CoreCategoricalUsabilityGraduationProposalInput,
    validateCoreCategoricalUsabilityGraduationProposal
} from './categorical_usability_graduation_proposal';

export interface CoreCategoricalUsabilityGraduationReviewInput {
    readonly revision: 'USABILITY-GRADUATE-1-REVIEWED';
    readonly status: 'reviewed-approved';
    readonly approval: {
        readonly gate: 'H-DTTLF-USABILITY-GRADUATE';
        readonly decisionId: 'D-DTTLF-USABILITY-002';
        readonly decision: 'approved-as-proposed';
        readonly reviewedOn: '2026-07-26';
        readonly decisionEvidence:
            'Approve H-DTTLF-USABILITY-GRADUATE/D-DTTLF-USABILITY-002 as proposed';
    };
    /**
     * Immutable snapshot of the exact pre-review proposal. Its nested
     * `authorityAuthorized: false` field remains historical evidence.
     */
    readonly recommendation:
        CoreCategoricalUsabilityGraduationProposalInput;
    readonly authorization: {
        readonly qualifiedFrontendArchitecture:
            'settled-exact-first-order-envelope';
        readonly architectureEnvelope:
            'outer-lf-plus-ordinary-bracket-plus-indexed-section-eta';
        readonly mechanicallyReusableWithinEnvelope: true;
        readonly outerLf:
            'settled-existing-general-dependent-lambda-pi';
        readonly ordinaryFunctorial:
            'settled-first-order-structural-bracket';
        readonly naturalIndexed:
            'settled-direct-slot-section-eta-only';
        readonly generalDependentBracketAuthorized: false;
        readonly additionalSemanticOwnerOrRuleAuthorized: false;
        readonly browserProfilePromotionAuthorized: false;
        readonly bulkTransferResumptionAuthorized: false;
        readonly parserOrGeneratorSelected: false;
    };
    readonly binderFeasibility: {
        readonly outerLfDependentBinding:
            'implemented-general-dependent-lambda-pi';
        readonly ordinaryCategoricalBinding:
            'implemented-and-qualified-first-order-structural-bracket';
        readonly displayedDependentCategoricalBinding:
            'implemented-and-qualified-direct-slot-section-eta-only';
        readonly generalDisplayedDependentBracket:
            'not-implemented-and-not-yet-mechanically-confirmed';
        readonly productRequirement:
            'required-for-general-displayed-dependent-binder-usability';
    };
    readonly retainedBoundaries: {
        readonly contextualIr:
            CoreCategoricalUsabilityGraduationProposalInput['contextualIr'];
        readonly surfaceApplicationPartition:
            CoreCategoricalUsabilityGraduationProposalInput[
                'surfaceApplicationPartition'
            ];
        readonly activeButUntransferred:
            CoreCategoricalUsabilityGraduationProposalInput[
                'activeButUntransferred'
            ];
        readonly authorityGaps:
            CoreCategoricalUsabilityGraduationProposalInput[
                'authorityGaps'
            ];
        readonly frontendAlgorithmGaps:
            CoreCategoricalUsabilityGraduationProposalInput[
                'frontendAlgorithmGaps'
            ];
        readonly separateDeferredWork:
            CoreCategoricalUsabilityGraduationProposalInput[
                'separateDeferredWork'
            ];
        readonly trustBoundary:
            CoreCategoricalUsabilityGraduationProposalInput[
                'trustBoundary'
            ];
        readonly claimBoundary:
            CoreCategoricalUsabilityGraduationProposalInput[
                'claimBoundary'
            ];
    };
    readonly validation: {
        readonly proposalRevision: 'USABILITY-GRADUATE-1';
        readonly proposalCheckpoint:
            'f77af05a8f58cbef74d2008fb445a4e7af707f07';
        readonly focusedReviewGate: '10-tests-pass';
        readonly rootGate:
            '665-tests-624-pass-41-opt-in-skip';
        readonly ordinaryLambdapiGate: '7-tests-pass';
        readonly indexedLambdapiGate: '8-tests-pass';
        readonly activeKernelGate: 'passed';
    };
    readonly nonEffects: readonly [
        'does-not-mutate-the-pre-review-proposal',
        'does-not-authorize-general-dependent-bracket-abstraction',
        'does-not-add-or-promote-a-semantic-owner-or-rule',
        'does-not-promote-a-browser-or-product-profile',
        'does-not-resume-bulk-library-transfer',
        'does-not-select-parser-or-generator-acquisition',
        'does-not-complete-groupoidal-dtt-closure',
        'does-not-broaden-a-metatheory-or-performance-claim',
        'does-not-make-lambdapi-a-production-runtime-dependency'
    ];
    readonly nextDependencyState:
        'requires-updated-plan-selection-no-automatic-follow-on';
}

export type CoreCategoricalUsabilityGraduationReviewErrorCode =
    | 'USABILITY_GRADUATION_REVIEW_DECISION_DRIFT'
    | 'USABILITY_GRADUATION_REVIEW_PREREQUISITE_DRIFT'
    | 'USABILITY_GRADUATION_REVIEW_PROPOSAL_DRIFT'
    | 'USABILITY_GRADUATION_REVIEW_AUTHORIZATION_DRIFT';

export class CoreCategoricalUsabilityGraduationReviewError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalUsabilityGraduationReviewErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalUsabilityGraduationReviewError';
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

const proposal = CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL;

const rawReview: CoreCategoricalUsabilityGraduationReviewInput = {
    revision: 'USABILITY-GRADUATE-1-REVIEWED',
    status: 'reviewed-approved',
    approval: {
        gate: 'H-DTTLF-USABILITY-GRADUATE',
        decisionId: 'D-DTTLF-USABILITY-002',
        decision: 'approved-as-proposed',
        reviewedOn: '2026-07-26',
        decisionEvidence:
            'Approve H-DTTLF-USABILITY-GRADUATE/D-DTTLF-USABILITY-002 as proposed'
    },
    recommendation: cloneData(proposal),
    authorization: {
        qualifiedFrontendArchitecture:
            'settled-exact-first-order-envelope',
        architectureEnvelope:
            proposal.recommendation.architectureEnvelope,
        mechanicallyReusableWithinEnvelope:
            proposal.recommendation.mechanicallyReusableWithinEnvelope,
        outerLf:
            'settled-existing-general-dependent-lambda-pi',
        ordinaryFunctorial:
            'settled-first-order-structural-bracket',
        naturalIndexed:
            'settled-direct-slot-section-eta-only',
        generalDependentBracketAuthorized: false,
        additionalSemanticOwnerOrRuleAuthorized: false,
        browserProfilePromotionAuthorized: false,
        bulkTransferResumptionAuthorized: false,
        parserOrGeneratorSelected: false
    },
    binderFeasibility: {
        outerLfDependentBinding:
            'implemented-general-dependent-lambda-pi',
        ordinaryCategoricalBinding:
            'implemented-and-qualified-first-order-structural-bracket',
        displayedDependentCategoricalBinding:
            'implemented-and-qualified-direct-slot-section-eta-only',
        generalDisplayedDependentBracket:
            'not-implemented-and-not-yet-mechanically-confirmed',
        productRequirement:
            'required-for-general-displayed-dependent-binder-usability'
    },
    retainedBoundaries: {
        contextualIr: cloneData(proposal.contextualIr),
        surfaceApplicationPartition: cloneData(
            proposal.surfaceApplicationPartition
        ),
        activeButUntransferred: cloneData(
            proposal.activeButUntransferred
        ),
        authorityGaps: cloneData(proposal.authorityGaps),
        frontendAlgorithmGaps: cloneData(
            proposal.frontendAlgorithmGaps
        ),
        separateDeferredWork: cloneData(
            proposal.separateDeferredWork
        ),
        trustBoundary: cloneData(proposal.trustBoundary),
        claimBoundary: cloneData(proposal.claimBoundary)
    },
    validation: {
        proposalRevision: 'USABILITY-GRADUATE-1',
        proposalCheckpoint:
            'f77af05a8f58cbef74d2008fb445a4e7af707f07',
        focusedReviewGate: '10-tests-pass',
        rootGate: '665-tests-624-pass-41-opt-in-skip',
        ordinaryLambdapiGate: '7-tests-pass',
        indexedLambdapiGate: '8-tests-pass',
        activeKernelGate: 'passed'
    },
    nonEffects: [
        'does-not-mutate-the-pre-review-proposal',
        'does-not-authorize-general-dependent-bracket-abstraction',
        'does-not-add-or-promote-a-semantic-owner-or-rule',
        'does-not-promote-a-browser-or-product-profile',
        'does-not-resume-bulk-library-transfer',
        'does-not-select-parser-or-generator-acquisition',
        'does-not-complete-groupoidal-dtt-closure',
        'does-not-broaden-a-metatheory-or-performance-claim',
        'does-not-make-lambdapi-a-production-runtime-dependency'
    ],
    nextDependencyState:
        'requires-updated-plan-selection-no-automatic-follow-on'
};

export const CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW =
    deepFreeze(rawReview);

export function validateCoreCategoricalUsabilityGraduationReview(
    review: CoreCategoricalUsabilityGraduationReviewInput =
        CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW
): void {
    if (
        review.revision !== 'USABILITY-GRADUATE-1-REVIEWED' ||
        review.status !== 'reviewed-approved' ||
        review.approval.gate !==
            'H-DTTLF-USABILITY-GRADUATE' ||
        review.approval.decisionId !== 'D-DTTLF-USABILITY-002' ||
        review.approval.decision !== 'approved-as-proposed' ||
        review.approval.reviewedOn !== '2026-07-26' ||
        review.approval.decisionEvidence !==
            'Approve H-DTTLF-USABILITY-GRADUATE/' +
            'D-DTTLF-USABILITY-002 as proposed'
    ) {
        throw new CoreCategoricalUsabilityGraduationReviewError(
            'USABILITY_GRADUATION_REVIEW_DECISION_DRIFT',
            'The categorical usability review must preserve the exact ' +
                'H-DTTLF-USABILITY-GRADUATE/D-DTTLF-USABILITY-002 approval'
        );
    }

    try {
        validateCoreCategoricalUsabilityGraduationProposal(proposal);
    } catch (error: unknown) {
        throw new CoreCategoricalUsabilityGraduationReviewError(
            'USABILITY_GRADUATION_REVIEW_PREREQUISITE_DRIFT',
            'The approved categorical usability prerequisites drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        !sameData(review.recommendation, proposal) ||
        review.recommendation.recommendation.authorityAuthorized !== false
    ) {
        throw new CoreCategoricalUsabilityGraduationReviewError(
            'USABILITY_GRADUATION_REVIEW_PROPOSAL_DRIFT',
            'The reviewed categorical usability recommendation is not exact'
        );
    }

    if (
        !sameData(review.authorization, rawReview.authorization) ||
        !sameData(
            review.binderFeasibility,
            rawReview.binderFeasibility
        ) ||
        !sameData(
            review.retainedBoundaries,
            rawReview.retainedBoundaries
        ) ||
        !sameData(review, rawReview)
    ) {
        throw new CoreCategoricalUsabilityGraduationReviewError(
            'USABILITY_GRADUATION_REVIEW_AUTHORIZATION_DRIFT',
            'The H-DTTLF-USABILITY-GRADUATE/' +
                'D-DTTLF-USABILITY-002 authorization boundary drifted'
        );
    }
}

validateCoreCategoricalUsabilityGraduationReview();
