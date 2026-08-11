/**
 * Focused separate-review tests for comparison source-root replay v2.
 */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2
} from '../src/v3_2/lf_conversion_normal_form_closure_proposal_v2';
import {
    CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2,
    CoreLfComparisonNormalFormClosureReviewV2,
    CoreLfComparisonNormalFormClosureReviewV2Error,
    validateCoreLfComparisonNormalFormClosureReviewV2
} from '../src/v3_2/lf_conversion_normal_form_closure_review_v2';

const clone = (): CoreLfComparisonNormalFormClosureReviewV2 =>
    JSON.parse(JSON.stringify(
        CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2
    )) as CoreLfComparisonNormalFormClosureReviewV2;

const assertReviewError = (
    mutate: (review: CoreLfComparisonNormalFormClosureReviewV2) => void,
    expected: CoreLfComparisonNormalFormClosureReviewV2Error['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCoreLfComparisonNormalFormClosureReviewV2(review),
        error =>
            error instanceof
                CoreLfComparisonNormalFormClosureReviewV2Error &&
            error.code === expected
    );
};

describe('Core LF comparison normal-form closure review v2', () => {
    it('approves only checkpoint a42ffc9 under delegated authority', () => {
        const review = validateCoreLfComparisonNormalFormClosureReviewV2();
        assert.equal(Object.isFrozen(review), true);
        assert.deepEqual(
            [
                review.approval.approvedProposalCheckpoint,
                review.approval.approvedProposalSha256,
                review.approval.supersededProposalCheckpoint,
                review.approval.supersededReviewCheckpoint,
                review.approval.authority,
                review.approval.humanDecisionSupersedes
            ],
            [
                'a42ffc9',
                'a79d5c632301456c395602d0a692af2c9dd21719969aa949289318efffa2f49c',
                'cf8ed76',
                '778da06',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('embeds the exact immutable non-authorizing v2 proposal', () => {
        const review =
            CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2;
        assert.deepEqual(
            review.recommendation,
            CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2
        );
        assert.equal(review.recommendation.decision.status, 'proposal-only');
        assert.equal(
            review.recommendation.decision.implementationAuthorized,
            false
        );
    });

    it('authorizes only original-root same-budget replay', () => {
        const authorization =
            CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2.authorization;
        assert.deepEqual(
            [
                authorization.originalSourceRootsRequired,
                authorization.pairedOutcomeRootsAsClosureInputsAuthorized,
                authorization.pairedOutcomeRetainedForFallbackDiagnostic,
                authorization.oneGlobalBudgetRequired,
                authorization.pairedConsumptionRetained,
                authorization.budgetResetAuthorized,
                authorization.deterministicLeftThenRightRequired,
                authorization.replayedTraceSplicingRequired,
                authorization.traceDeduplicationAuthorized
            ],
            [true, false, true, true, true, false, true, true, false]
        );
    });

    it('denies semantic, trust, public, and release widening', () => {
        const authorization =
            CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2.authorization;
        assert.deepEqual(
            [
                authorization.newRuntimeRuleAuthorized,
                authorization.newProofRuleAuthorized,
                authorization.newCoreNodeAuthorized,
                authorization.checkerBranchAuthorized,
                authorization.memoizationOrCachingAuthorized,
                authorization.proofSearchOrUnificationAuthorized,
                authorization.standaloneNormalizerChangeAuthorized,
                authorization.weakHeadChangeAuthorized,
                authorization.pathIndSpecificCommutingRewriteAuthorized,
                authorization.publicSurfaceChangeAuthorized,
                authorization.activeLambdapiSourceChangeAuthorized,
                authorization.externalIntegrationOrReleaseAuthorized
            ],
            Array.from({ length: 12 }, () => false)
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                (review.approval as {
                    approvedProposalCheckpoint: string;
                }).approvedProposalCheckpoint = 'wrong';
            },
            'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                (review.recommendation.exactCorrection as {
                    closureInputs: string;
                }).closureInputs = 'paired-outcome-roots';
            },
            'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                (review.authorization as {
                    memoizationOrCachingAuthorized: boolean;
                }).memoizationOrCachingAuthorized = true;
            },
            'COMPARISON_NORMAL_FORM_CLOSURE_REVIEW_V2_AUTHORIZATION_DRIFT'
        );
    });
});
