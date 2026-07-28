/**
 * Focused delegated-review tests for
 * H-DTTLF-USABILITY-DISPLAYED-EVAL-OWNER-01/D-DTTLF-USABILITY-011.
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
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW,
    CoreCategoricalDisplayedEvaluationOwnerReviewError,
    validateCoreCategoricalDisplayedEvaluationOwnerReview
} from '../src/v3_2';

const cloneReview = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const assertReviewError = (
    mutate: (review: any) => void,
    expected:
        CoreCategoricalDisplayedEvaluationOwnerReviewError['code']
): void => {
    const review = cloneReview();
    mutate(review);
    assert.throws(
        () =>
            validateCoreCategoricalDisplayedEvaluationOwnerReview(
                review
            ),
        error =>
            error instanceof
                CoreCategoricalDisplayedEvaluationOwnerReviewError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 reviewed displayed evaluation owner slice', () => {
    it('records the delegated D-011 approval separately and exactly', () => {
        const approval =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW
                .approval;
        assert.equal(
            approval.gate,
            'H-DTTLF-USABILITY-DISPLAYED-EVAL-OWNER-01'
        );
        assert.equal(approval.decisionId, 'D-DTTLF-USABILITY-011');
        assert.equal(approval.decision, 'approved-as-proposed');
        assert.equal(
            approval.authority,
            'user-delegated-unattended-approval'
        );
        assert.equal(approval.humanDecisionSupersedes, true);
    });

    it('retains an immutable snapshot of the pending proposal', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW;
        assert.notEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL
        );
        assert.deepEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL
        );
        assert.equal(
            review.recommendation.status,
            'proposal-awaiting-h-dttlf-usability-displayed-eval-owner-01'
        );
    });

    it('authorizes exactly two owners and two component rules', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW
                .authorization;
        assert.deepEqual(authorization.exactKernelOwners, [
            'Eval_funcd',
            'Terminal_funcd'
        ]);
        assert.equal(authorization.exactKernelOwnerCount, 2);
        assert.equal(authorization.exactRuntimeRuleCount, 2);
        assert.equal(
            authorization.activeLambdapiOwnerAndRuleEditAuthorized,
            true
        );
        assert.equal(authorization.intrinsicCoreOwnerAuthorized, false);
    });

    it('authorizes generic transfer and only the mechanical profile repair', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW
                .authorization;
        assert.equal(
            authorization.genericDeclarationAndRuntimeTransferAuthorized,
            true
        );
        assert.equal(
            authorization.dependentTargetFinalRuntimeRecheckAuthorized,
            true
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW
                .retainedBoundaries.profileRepair.ownerOrRuleSemanticChange,
            false
        );
    });

    it('authorizes exactly the two recursive existing-IR judgments', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW
                .authorization;
        assert.deepEqual(
            authorization.recursiveTypedApplicationJudgments,
            [
                'varying-subject-varying-coherent-argument',
                'varying-subject-fixed-argument'
            ]
        );
        assert.equal(
            authorization.existingApplicationNodeReuseRequired,
            true
        );
        assert.equal(
            authorization.deriveFixedArgumentThroughTerminalFuncdRequired,
            true
        );
        assert.equal(
            authorization.thirdFixedEvaluatorOwnerAuthorized,
            false
        );
    });

    it('keeps generic coherence solely at fapp/tapp', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW
                .authorization;
        assert.equal(
            authorization.genericFappTappRemainsSoleCoherenceOwner,
            true
        );
        assert.equal(
            authorization.constructorSpecificCoherenceRulesAuthorized,
            false
        );
        assert.equal(
            authorization.warningDeltaIsDiagnosticNotVeto,
            true
        );
    });

    it('retains the variance and frontend boundaries', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW;
        assert.match(
            review.retainedBoundaries.selectedDomain.stableSubjectFamily,
            /Functor_catd/u
        );
        assert.equal(
            review.authorization.arbitraryMixedDomainEvaluationAuthorized,
            false
        );
        assert.equal(
            review.authorization.rawExprOrSecondCheckerAuthorized,
            false
        );
    });

    it('keeps dependent-chain, nd, parser, browser, and Git scope closed', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW;
        assert.equal(
            review.authorization.genuineDependentChainAuthorized,
            false
        );
        assert.equal(
            review.authorization.generalNdCoherenceAuthorized,
            false
        );
        assert.equal(
            review.authorization.parserOrBulkTransferAuthorized,
            false
        );
        assert.equal(
            review.authorization.browserOrDeployedPromotionAuthorized,
            false
        );
        assert.equal(review.gitBoundary.pushMergePublishAuthorized, false);
        assert.equal(review.gitBoundary.historyRewriteAuthorized, false);
        assert.equal(review.gitBoundary.cleanupAuthorized, false);
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_displayed_evaluation_owner_review/u
        );
    });

    it('is deeply frozen and validates its implementation-ready state', () => {
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW
        );
        assert.doesNotThrow(
            () =>
                validateCoreCategoricalDisplayedEvaluationOwnerReview()
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_REVIEW
                .nextDependencyState,
            'displayed-eval-1a-exact-implementation-ready'
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                review.approval.authority = 'human-review';
            },
            'DISPLAYED_EVALUATION_OWNER_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                review.recommendation.proposedKernelOwners.pop();
            },
            'DISPLAYED_EVALUATION_OWNER_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                review.authorization.thirdFixedEvaluatorOwnerAuthorized =
                    true;
            },
            'DISPLAYED_EVALUATION_OWNER_REVIEW_AUTHORIZATION_DRIFT'
        );
        assertReviewError(
            review => {
                review.gitBoundary.cleanupAuthorized = true;
            },
            'DISPLAYED_EVALUATION_OWNER_REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
