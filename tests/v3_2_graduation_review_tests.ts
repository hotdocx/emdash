/**
 * Focused GRADUATE-1B tests for the reviewed H-05 authority boundary.
 */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CORE_MVP_GRADUATION_RECOMMENDATION,
    CORE_MVP_GRADUATION_REVIEW,
    CORE_MVP_MANIFEST,
    CoreMvpGraduationError,
    CoreMvpGraduationReviewInput,
    validateCoreMvpGraduationReview
} from '../src/v3_2';

const cloneReview = (): CoreMvpGraduationReviewInput =>
    JSON.parse(JSON.stringify(CORE_MVP_GRADUATION_REVIEW));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    for (const child of Object.values(value as Record<string, unknown>)) {
        assertDeepFrozen(child);
    }
};

const expectReviewError = (
    mutate: (review: any) => void,
    code: CoreMvpGraduationError['code']
): CoreMvpGraduationError => {
    const review = cloneReview() as any;
    mutate(review);
    try {
        validateCoreMvpGraduationReview(review);
    } catch (error) {
        assert.ok(error instanceof CoreMvpGraduationError);
        assert.equal(error.code, code);
        return error;
    }
    assert.fail(`Expected ${code}`);
};

describe('TypeScript v3.2 GRADUATE-1B reviewed H-05 boundary', () => {
    it('records the exact H-05/D-039 approval separately', () => {
        assert.equal(CORE_MVP_GRADUATION_REVIEW.revision, 'GRADUATE-1B');
        assert.equal(
            CORE_MVP_GRADUATION_REVIEW.status,
            'reviewed-approved'
        );
        assert.deepEqual(CORE_MVP_GRADUATION_REVIEW.approval, {
            gate: 'H-05',
            decision: 'approved-as-proposed',
            decisionId: 'D-039',
            reviewedOn: '2026-07-24'
        });
        assert.notEqual(
            CORE_MVP_GRADUATION_REVIEW.recommendation,
            CORE_MVP_GRADUATION_RECOMMENDATION
        );
        assert.deepEqual(
            CORE_MVP_GRADUATION_REVIEW.recommendation,
            CORE_MVP_GRADUATION_RECOMMENDATION
        );
    });

    it('authorizes only the exact frozen TypeScript deployment profile', () => {
        const review = CORE_MVP_GRADUATION_REVIEW;
        assert.equal(
            review.authorization.typescriptDeployedRuntimeAuthority,
            'authorized-exact-frozen-profile'
        );
        assert.equal(
            review.manifestRevision,
            CORE_MVP_MANIFEST.revision
        );
        assert.equal(
            review.manifestContentHash,
            CORE_MVP_MANIFEST.contentHash
        );
        assert.deepEqual(
            review.ownerIds,
            CORE_MVP_MANIFEST.owners.map(entry => entry.owner)
        );
        assert.deepEqual(
            review.runtimeRuleIds,
            CORE_MVP_MANIFEST.rules.map(rule => rule.id)
        );
        assert.equal(review.additionalOwnersOrRulesAuthorized, false);
    });

    it('retains every approved Lambdapi role without runtime coupling', () => {
        assert.deepEqual(CORE_MVP_GRADUATION_REVIEW.authorization, {
            typescriptDeployedRuntimeAuthority:
                'authorized-exact-frozen-profile',
            lambdapiProductionRuntimeDependency: 'forbidden',
            lambdapiMathematicalSpecification: 'retained',
            frozenCorpusCiOracle: 'required',
            subjectReductionOracle: 'required',
            selectedChangeAcceptanceAuthority: 'retained',
            perTermProductionCheck: 'not-required'
        });
        assert.deepEqual(
            CORE_MVP_GRADUATION_REVIEW.acceptanceTriggers,
            CORE_MVP_GRADUATION_RECOMMENDATION
                .lambdapiPolicy.acceptanceTriggers
        );
        assert.deepEqual(
            CORE_MVP_GRADUATION_REVIEW
                .changesNotRequiringNewAuthorityReview,
            CORE_MVP_GRADUATION_RECOMMENDATION
                .lambdapiPolicy.changesNotRequiringNewAuthorityReview
        );
    });

    it('preserves the theorem and release non-claims', () => {
        const review = CORE_MVP_GRADUATION_REVIEW;
        assert.equal(review.generalConfluence, 'withheld');
        assert.equal(review.typescriptSubjectReduction, 'withheld');
        assert.equal(review.performanceSlaAuthorized, false);
        assert.equal(review.releaseReady, false);
        assert.equal(review.nextSlice, 'RELEASE-READY');
        assert.equal(
            review.recommendation.authorityAuthorized,
            false
        );
    });

    it('is deeply frozen and validates unchanged', () => {
        assertDeepFrozen(CORE_MVP_GRADUATION_REVIEW);
        assert.doesNotThrow(() =>
            validateCoreMvpGraduationReview(
                CORE_MVP_GRADUATION_REVIEW
            )
        );
    });

    it('rejects approval, proposal, or authorization drift', () => {
        assert.match(
            expectReviewError(
                review => {
                    review.approval.decision = 'revised';
                },
                'GRADUATION_REVIEW_APPROVAL_MISMATCH'
            ).message,
            /exact H-05 approval/
        );
        assert.match(
            expectReviewError(
                review => {
                    review.recommendation.productAuthority.ownerIds.pop();
                },
                'GRADUATION_REVIEW_RECOMMENDATION_MISMATCH'
            ).message,
            /approved D-039 recommendation/
        );
        assert.match(
            expectReviewError(
                review => {
                    review.authorization
                        .lambdapiProductionRuntimeDependency = 'required';
                },
                'GRADUATION_REVIEW_BOUNDARY_MISMATCH'
            ).message,
            /authorization boundary/
        );
        assert.match(
            expectReviewError(
                review => {
                    review.generalConfluence = 'authorized';
                },
                'GRADUATION_REVIEW_BOUNDARY_MISMATCH'
            ).message,
            /authorization boundary/
        );
    });
});
