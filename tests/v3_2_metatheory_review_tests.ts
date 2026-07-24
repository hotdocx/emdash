/**
 * Focused TSK-2C2 tests for the reviewed H-04 claim boundary.
 */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CORE_MVP_MANIFEST,
    CORE_MVP_RUNTIME_PROGRAM,
    CORE_RUNTIME_H04_RECOMMENDATION,
    CORE_RUNTIME_H04_REVIEW,
    CoreRuntimeH04ReviewInput,
    CoreRuntimeMetatheoryError,
    validateCoreRuntimeH04Review
} from '../src/v3_2';

const cloneReview = (): CoreRuntimeH04ReviewInput =>
    JSON.parse(JSON.stringify(CORE_RUNTIME_H04_REVIEW));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    for (const child of Object.values(value as Record<string, unknown>)) {
        assertDeepFrozen(child);
    }
};

const expectReviewError = (
    mutate: (review: any) => void,
    code: CoreRuntimeMetatheoryError['code']
): CoreRuntimeMetatheoryError => {
    const review = cloneReview() as any;
    mutate(review);
    try {
        validateCoreRuntimeH04Review(review);
    } catch (error) {
        assert.ok(error instanceof CoreRuntimeMetatheoryError);
        assert.equal(error.code, code);
        return error;
    }
    assert.fail(`Expected ${code}`);
};

describe('TypeScript v3.2 TSK-2C2 reviewed H-04 boundary', () => {
    it('records the exact H-04/D-030 approval as a distinct artifact', () => {
        assert.equal(CORE_RUNTIME_H04_REVIEW.status, 'reviewed-approved');
        assert.deepEqual(CORE_RUNTIME_H04_REVIEW.approval, {
            gate: 'H-04',
            decision: 'approved-as-proposed',
            decisionId: 'D-030',
            reviewedOn: '2026-07-24'
        });
        assert.notEqual(
            CORE_RUNTIME_H04_REVIEW.recommendation,
            CORE_RUNTIME_H04_RECOMMENDATION
        );
        assert.deepEqual(
            CORE_RUNTIME_H04_REVIEW.recommendation,
            CORE_RUNTIME_H04_RECOMMENDATION
        );
        assert.doesNotThrow(() =>
            validateCoreRuntimeH04Review(CORE_RUNTIME_H04_REVIEW)
        );
    });

    it('authorizes only the exact termination and trusted-rule boundary', () => {
        assert.deepEqual(CORE_RUNTIME_H04_REVIEW.authorization, {
            termination: 'authorized-exact-fragment',
            deterministicBoundedEvaluationAndComparison: 'authorized',
            trustedRuntimeRules:
                'authorized-exact-h03-runtime-set-only',
            generalConfluence: 'withheld',
            typescriptSubjectReduction: 'withheld'
        });
        assert.deepEqual(
            CORE_RUNTIME_H04_REVIEW.executableRuleIds,
            CORE_MVP_RUNTIME_PROGRAM.rules.map(rule => rule.id)
        );
        assert.equal(
            CORE_RUNTIME_H04_REVIEW.additionalRuntimeRulesAuthorized,
            false
        );
    });

    it('preserves both withheld claims and the Lambdapi oracle', () => {
        assert.equal(
            CORE_RUNTIME_H04_REVIEW.authorization.generalConfluence,
            'withheld'
        );
        assert.equal(
            CORE_RUNTIME_H04_REVIEW
                .authorization.typescriptSubjectReduction,
            'withheld'
        );
        assert.equal(
            CORE_RUNTIME_H04_REVIEW.subjectReductionOracle,
            'lambdapi'
        );
    });

    it('keeps every unselected mechanism outside authorization', () => {
        assert.deepEqual(
            CORE_RUNTIME_H04_REVIEW.mechanismsOutsideAuthorization,
            [
                'proof-time-comparison',
                'intentional-runtime-non-conversion',
                'excluded-owner-rules',
                'declaration-unfolding',
                'generic-call-beta'
            ]
        );
        assert.deepEqual(
            CORE_RUNTIME_H04_REVIEW
                .recommendation.nonExecutableEvidenceIds,
            [
                'comparison.constant-section',
                'nonconversion.constant-section.runtime'
            ]
        );
    });

    it('does not rewrite the historical H-03 or pre-review artifacts', () => {
        assert.equal(
            CORE_RUNTIME_H04_RECOMMENDATION.claimsAuthorized,
            false
        );
        assert.equal(
            CORE_RUNTIME_H04_REVIEW.recommendation.claimsAuthorized,
            false
        );
        assert.equal(
            CORE_MVP_RUNTIME_PROGRAM.safety.claimsAuthorized,
            false
        );
        assert.equal(CORE_MVP_MANIFEST.status, 'frozen-reviewed');
        assert.equal(CORE_MVP_MANIFEST.revision, 'emdash-v3.2-mvp-1');
        assert.equal(
            CORE_MVP_MANIFEST.contentHash,
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0'
        );
    });

    it('is deeply frozen and rejects approval, source, or boundary drift', () => {
        assertDeepFrozen(CORE_RUNTIME_H04_REVIEW);

        assert.match(
            expectReviewError(
                review => {
                    review.approval.decision = 'revised';
                },
                'H04_REVIEW_APPROVAL_MISMATCH'
            ).message,
            /exact H-04 approval/
        );
        assert.match(
            expectReviewError(
                review => {
                    review.recommendation.claims
                        .confluence.recommendation = 'authorize';
                },
                'H04_REVIEW_RECOMMENDATION_MISMATCH'
            ).message,
            /approved D-030 recommendation/
        );
        assert.match(
            expectReviewError(
                review => {
                    review.authorization.generalConfluence = 'authorized';
                },
                'H04_REVIEW_BOUNDARY_MISMATCH'
            ).message,
            /authorization boundary/
        );
        assert.match(
            expectReviewError(
                review => {
                    review.executableRuleIds.push(
                        'comparison.constant-section'
                    );
                },
                'H04_REVIEW_BOUNDARY_MISMATCH'
            ).message,
            /authorization boundary/
        );
    });
});
