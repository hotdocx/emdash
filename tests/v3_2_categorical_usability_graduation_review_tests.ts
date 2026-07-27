/**
 * Focused review tests for
 * H-DTTLF-USABILITY-GRADUATE/D-DTTLF-USABILITY-002.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL,
    CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW,
    CoreCategoricalUsabilityGraduationReviewError,
    CoreCategoricalUsabilityGraduationReviewInput,
    validateCoreCategoricalUsabilityGraduationReview
} from '../src/v3_2';

const cloneReview =
(): CoreCategoricalUsabilityGraduationReviewInput =>
    JSON.parse(JSON.stringify(
        CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW
    )) as CoreCategoricalUsabilityGraduationReviewInput;

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const assertReviewError = (
    mutate: (review: any) => void,
    expected: CoreCategoricalUsabilityGraduationReviewError['code']
): void => {
    const review = cloneReview() as any;
    mutate(review);
    assert.throws(
        () => validateCoreCategoricalUsabilityGraduationReview(review),
        error =>
            error instanceof
                CoreCategoricalUsabilityGraduationReviewError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 reviewed categorical frontend architecture', () => {
    it('records the exact approval separately from the proposal', () => {
        const review =
            CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW;
        assert.equal(
            review.revision,
            'USABILITY-GRADUATE-1-REVIEWED'
        );
        assert.equal(review.status, 'reviewed-approved');
        assert.deepEqual(review.approval, {
            gate: 'H-DTTLF-USABILITY-GRADUATE',
            decisionId: 'D-DTTLF-USABILITY-002',
            decision: 'approved-as-proposed',
            reviewedOn: '2026-07-26',
            decisionEvidence:
                'Approve H-DTTLF-USABILITY-GRADUATE/' +
                'D-DTTLF-USABILITY-002 as proposed'
        });
        assert.notEqual(
            review.recommendation,
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL
        );
        assert.deepEqual(
            review.recommendation,
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL
        );
        assert.equal(
            review.recommendation.recommendation.authorityAuthorized,
            false
        );
    });

    it('settles only the exact qualified first-order envelope', () => {
        const review =
            CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW;
        const authorization = review.authorization;
        assert.deepEqual(authorization, {
            qualifiedFrontendArchitecture:
                'settled-exact-first-order-envelope',
            architectureEnvelope:
                'outer-lf-plus-ordinary-bracket-plus-indexed-section-eta',
            mechanicallyReusableWithinEnvelope: true,
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
        });
        assert.deepEqual(review.binderFeasibility, {
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
        });
    });

    it('retains the exact contextual IR and complete application partition', () => {
        const boundaries =
            CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW
                .retainedBoundaries;
        assert.deepEqual(
            boundaries.contextualIr,
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL.contextualIr
        );
        assert.deepEqual(
            boundaries.surfaceApplicationPartition,
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL
                .surfaceApplicationPartition
        );
        assert.equal(
            boundaries.surfaceApplicationPartition
                .totalApplicationJudgments,
            16
        );
    });

    it('retains active transfers separately from authority gaps', () => {
        const boundaries =
            CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW
                .retainedBoundaries;
        assert.deepEqual(
            boundaries.activeButUntransferred,
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL
                .activeButUntransferred
        );
        assert.deepEqual(
            boundaries.authorityGaps,
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL.authorityGaps
        );
        assert.equal(boundaries.activeButUntransferred.length, 4);
        assert.equal(boundaries.authorityGaps.length, 2);
    });

    it('retains every algorithm, acquisition, and notation boundary', () => {
        const boundaries =
            CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW
                .retainedBoundaries;
        assert.deepEqual(
            boundaries.frontendAlgorithmGaps,
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL
                .frontendAlgorithmGaps
        );
        assert.deepEqual(
            boundaries.separateDeferredWork,
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL
                .separateDeferredWork
        );
        assert.equal(
            boundaries.separateDeferredWork.stringParser,
            'optional-and-deferred'
        );
    });

    it('retains the exact trust and metatheory non-claims', () => {
        const boundaries =
            CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW
                .retainedBoundaries;
        assert.deepEqual(
            boundaries.trustBoundary,
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL.trustBoundary
        );
        assert.deepEqual(
            boundaries.claimBoundary,
            CORE_CATEGORICAL_USABILITY_GRADUATION_PROPOSAL.claimBoundary
        );
        assert.equal(
            boundaries.trustBoundary.productionLambdapiDependency,
            false
        );
        assert.equal(
            boundaries.claimBoundary.wholeDevelopmentTransfer,
            'withheld'
        );
    });

    it('stays root-only and outside the browser entry point', () => {
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_usability_graduation|USABILITY_GRADUATE/u
        );
        assert.equal(
            CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW
                .authorization.browserProfilePromotionAuthorized,
            false
        );
    });

    it('selects no automatic follow-on work', () => {
        const review =
            CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW;
        assert.equal(
            review.nextDependencyState,
            'requires-updated-plan-selection-no-automatic-follow-on'
        );
        assert.equal(
            review.authorization.bulkTransferResumptionAuthorized,
            false
        );
        assert.equal(
            review.authorization.parserOrGeneratorSelected,
            false
        );
    });

    it('is deeply frozen and validates unchanged', () => {
        assertDeepFrozen(
            CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW
        );
        assert.doesNotThrow(
            () => validateCoreCategoricalUsabilityGraduationReview()
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                review.approval.decision = 'revised';
            },
            'USABILITY_GRADUATION_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                review.recommendation.frontendAlgorithmGaps.pop();
            },
            'USABILITY_GRADUATION_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                review.authorization
                    .generalDependentBracketAuthorized = true;
            },
            'USABILITY_GRADUATION_REVIEW_AUTHORIZATION_DRIFT'
        );
        assertReviewError(
            review => {
                review.retainedBoundaries
                    .activeButUntransferred.pop();
            },
            'USABILITY_GRADUATION_REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
