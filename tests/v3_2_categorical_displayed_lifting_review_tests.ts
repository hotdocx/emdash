/**
 * Focused delegated-review tests for
 * H-DTTLF-USABILITY-DISPLAYED-LIFTING-01/D-DTTLF-USABILITY-010.
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
    CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL,
    CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW,
    CoreCategoricalDisplayedLiftingReviewError,
    validateCoreCategoricalDisplayedLiftingReview
} from '../src/v3_2';

const cloneReview = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW
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
    expected: CoreCategoricalDisplayedLiftingReviewError['code']
): void => {
    const review = cloneReview();
    mutate(review);
    assert.throws(
        () => validateCoreCategoricalDisplayedLiftingReview(review),
        error =>
            error instanceof
                CoreCategoricalDisplayedLiftingReviewError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 reviewed displayed lifting audit', () => {
    it('records the delegated D-010 approval separately and exactly', () => {
        const approval =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW.approval;
        assert.equal(
            approval.gate,
            'H-DTTLF-USABILITY-DISPLAYED-LIFTING-01'
        );
        assert.equal(approval.decisionId, 'D-DTTLF-USABILITY-010');
        assert.equal(approval.decision, 'approved-as-proposed');
        assert.equal(
            approval.authority,
            'user-delegated-unattended-approval'
        );
        assert.equal(
            approval.condition,
            'no-immediate-human-response-after-presented-frozen-proposal'
        );
        assert.equal(approval.humanDecisionSupersedes, true);
    });

    it('retains an immutable snapshot of the pending proposal', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW;
        assert.notEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL
        );
        assert.deepEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL
        );
        assert.equal(
            review.recommendation.status,
            'proposal-awaiting-h-dttlf-usability-displayed-lifting-01'
        );
    });

    it('authorizes exactly the read-only DISPLAYED-EVAL-0B row', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW.authorization;
        assert.equal(authorization.evidenceRow, 'DISPLAYED-EVAL-0B');
        assert.equal(authorization.evidenceRowAuthorized, true);
        assert.equal(
            authorization.investigationKind,
            'read-only-owner-position-and-derived-construction-probe'
        );
        assert.equal(
            authorization.activeAuthorityInspectionAuthorized,
            true
        );
        assert.equal(
            authorization.boundedTemporaryLambdapiProbesAuthorized,
            true
        );
    });

    it('retains the corrected recursive architecture', () => {
        const architecture =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW
                .retainedBoundaries.architectureCorrection;
        assert.equal(
            architecture.sourceBoundary,
            'existing-typed-typescript-construction-ir'
        );
        assert.equal(architecture.rawExprLayerAdded, false);
        assert.equal(architecture.bidirectionalCheckerAdded, false);
        assert.equal(architecture.parserSelected, false);
        assert.equal(architecture.wholeBodyRecognizerExtended, false);
    });

    it('retains the exact coherent displayed-evaluation gap', () => {
        const boundaries =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW
                .retainedBoundaries;
        assert.equal(
            boundaries.ownerAuditConclusion
                .genericCoherentDisplayedEvaluationOwnerSelected,
            false
        );
        assert.equal(
            boundaries.ownerAuditConclusion
                .absenceProvesMathematicalImpossibility,
            false
        );
        assert.equal(
            boundaries.recommendedNextRow.id,
            'DISPLAYED-EVAL-0B'
        );
    });

    it('permits either evidence conclusion but no implementation', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW.authorization;
        assert.equal(
            authorization.resultMayFreezeExistingAuthorityProposal,
            true
        );
        assert.equal(
            authorization.resultMayFreezeMinimalOwnerProposal,
            true
        );
        assert.equal(
            authorization
                .semanticDisplayedLifting1AImplementationAuthorized,
            false
        );
        assert.equal(
            authorization.newLambdapiOrCoreOwnerAuthorized,
            false
        );
        assert.equal(
            authorization.newRuntimeOrProofRuleAuthorized,
            false
        );
    });

    it('keeps grammar, profile, browser, acquisition, and Git scope closed', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW;
        assert.equal(
            review.authorization.recursiveGrammarExtensionAuthorized,
            false
        );
        assert.equal(review.authorization.profileJoinAuthorized, false);
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
            /categorical_displayed_lifting|DISPLAYED-LIFTING/u
        );
    });

    it('is deeply frozen and validates its evidence-ready state', () => {
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW
        );
        assert.doesNotThrow(
            () => validateCoreCategoricalDisplayedLiftingReview()
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW
                .nextDependencyState,
            'displayed-eval-0b-read-only-investigation-ready'
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                review.approval.authority = 'human-review';
            },
            'DISPLAYED_LIFTING_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                review.recommendation.displayedMatrix.pop();
            },
            'DISPLAYED_LIFTING_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                review.authorization.newLambdapiOrCoreOwnerAuthorized =
                    true;
            },
            'DISPLAYED_LIFTING_REVIEW_AUTHORIZATION_DRIFT'
        );
        assertReviewError(
            review => {
                review.gitBoundary.cleanupAuthorized = true;
            },
            'DISPLAYED_LIFTING_REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
