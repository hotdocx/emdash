/**
 * Focused separate-review tests for comparison normal-form closure.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL
} from '../src/v3_2/lf_conversion_normal_form_closure_proposal';
import {
    CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW,
    CoreLfComparisonNormalFormClosureReview,
    CoreLfComparisonNormalFormClosureReviewError,
    validateCoreLfComparisonNormalFormClosureReview
} from '../src/v3_2/lf_conversion_normal_form_closure_review';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CoreLfComparisonNormalFormClosureReview =>
    JSON.parse(JSON.stringify(
        CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW
    )) as CoreLfComparisonNormalFormClosureReview;

const assertReviewError = (
    mutate: (review: CoreLfComparisonNormalFormClosureReview) => void,
    expected: CoreLfComparisonNormalFormClosureReviewError['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCoreLfComparisonNormalFormClosureReview(review),
        error =>
            error instanceof CoreLfComparisonNormalFormClosureReviewError &&
            error.code === expected
    );
};

describe('Core LF comparison normal-form closure separate review', () => {
    it('approves only checkpoint cf8ed76 under delegated authority', () => {
        const review = validateCoreLfComparisonNormalFormClosureReview();
        assert.equal(Object.isFrozen(review), true);
        assert.deepEqual(
            [
                review.approval.approvedProposalCheckpoint,
                review.approval.approvedProposalSha256,
                review.approval.authority,
                review.approval.humanDecisionSupersedes
            ],
            [
                'cf8ed76',
                'b0711d2185b3f3fcf2ca35e6507c548f86c8f10d4252ab140f8b8ffa45bf7f4a',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact frozen non-authorizing proposal', () => {
        const review = CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW;
        assert.deepEqual(
            review.recommendation,
            CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL
        );
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
    });

    it('authorizes closure only and denies semantic expansion', () => {
        const authorization =
            CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW.authorization;
        assert.deepEqual(
            [
                authorization.terminalClosureOnlyAfterNotEqual,
                authorization.oneGlobalBudgetRequired,
                authorization.deterministicLeftThenRightRequired,
                authorization.traceSplicingRequired,
                authorization.exactKernelEqualityRequired,
                authorization.newRuntimeRuleAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.newCoreNodeAuthorized,
                authorization.checkerBranchAuthorized,
                authorization.budgetResetAuthorized,
                authorization.pathIndSpecificCommutingRewriteAuthorized,
                authorization.publicSurfaceChangeAuthorized
            ],
            [true, true, true, true, true, false, false, false, false,
                false, false, false]
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (review.recommendation.exactCorrection as {
                    newReductionRuleCount: number;
                }).newReductionRuleCount = 1;
            },
            'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    budgetResetAuthorized: boolean;
                }).budgetResetAuthorized = true;
            },
            'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, workspace, or browser barrels',
        () => {
            for (
                const path of [
                    'src/v3_2/index.ts',
                    'src/v3_2/package_core.ts',
                    'src/v3_2/package_authoring.ts',
                    'src/v3_2/package_workspace.ts',
                    'src/v3_2/browser.ts'
                ]
            ) {
                assert.doesNotMatch(
                    readFileSync(resolve(repositoryRoot, path), 'utf8'),
                    /lf_conversion_normal_form_closure_review/u,
                    path
                );
            }
        });
});
