/**
 * Focused delegated-review tests for
 * H-DTTLF-USABILITY-FIBRED-GRADUATE/D-DTTLF-USABILITY-008.
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
    CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL,
    CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW,
    CoreCategoricalFibredGraduationReviewError,
    validateCoreCategoricalFibredGraduationReview
} from '../src/v3_2';

const cloneReview = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW
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
    expected: CoreCategoricalFibredGraduationReviewError['code']
): void => {
    const review = cloneReview();
    mutate(review);
    assert.throws(
        () => validateCoreCategoricalFibredGraduationReview(review),
        error =>
            error instanceof
                CoreCategoricalFibredGraduationReviewError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 reviewed fibred architecture', () => {
    it('records the delegated approval separately and exactly', () => {
        const review =
            CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW;
        assert.equal(
            review.status,
            'reviewed-approved-under-delegated-unattended-authority'
        );
        assert.deepEqual(review.approval, {
            gate: 'H-DTTLF-USABILITY-FIBRED-GRADUATE',
            decisionId: 'D-DTTLF-USABILITY-008',
            decision: 'approved-as-proposed',
            authority: 'user-delegated-unattended-approval',
            condition:
                'no-immediate-human-response-after-presented-' +
                'frozen-proposal',
            recordedOn: '2026-07-28',
            humanDecisionSupersedes: true,
            decisionEvidence:
                'The user authorized the coding agent to approve a frozen ' +
                'proposal during unattended continuation when no immediate ' +
                'human response follows, provided the Git checkpoint SOP ' +
                'is followed'
        });
    });

    it('retains an immutable snapshot of the pending proposal', () => {
        const review =
            CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW;
        assert.notEqual(
            review.recommendation,
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL
        );
        assert.deepEqual(
            review.recommendation,
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL
        );
        assert.equal(
            review.recommendation.recommendation
                .semanticAuthorityAuthorized,
            false
        );
    });

    it('settles only the demonstrated existing-authority envelope', () => {
        const authorization =
            CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW
                .authorization;
        assert.equal(
            authorization.qualifiedArchitecture,
            'settled-demonstrated-existing-authority-envelope'
        );
        assert.equal(
            authorization.mechanicallyScalableWithinScope,
            true
        );
        assert.equal(
            authorization.automaticWholeDevelopmentImportAuthorized,
            false
        );
        assert.equal(
            authorization.generalDisplayedBracketCompletionAuthorized,
            false
        );
    });

    it('retains all measured evidence and residual gaps', () => {
        const boundaries =
            CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW
                .retainedBoundaries;
        assert.deepEqual(
            boundaries.transferEvidence,
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL
                .transferEvidence
        );
        assert.deepEqual(
            boundaries.residualGaps,
            CORE_CATEGORICAL_FIBRED_GRADUATION_PROPOSAL.residualGaps
        );
        assert.equal(
            boundaries.transferEvidence.cumulativeSliceCounts
                .representativeSlices,
            7
        );
        assert.equal(
            boundaries.residualGaps.mathematicalOwnerOrTheoremWork
                .length,
            6
        );
    });

    it('keeps acquisition, parsing, and product promotion separate', () => {
        const review =
            CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW;
        assert.equal(
            review.retainedBoundaries.acquisitionBoundary.default,
            'direct-typed-typescript-transcription-or-construction'
        );
        assert.equal(
            review.authorization.parserOrGeneratorSelected,
            false
        );
        assert.equal(
            review.authorization.bulkTransferResumptionAuthorized,
            false
        );
        assert.equal(
            review.authorization
                .browserOrDeployedProfilePromotionAuthorized,
            false
        );
    });

    it('selects no automatic successor or missing mathematics', () => {
        const review =
            CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW;
        assert.equal(
            review.authorization
                .missingMathematicalOwnerWorkDeclaredComplete,
            false
        );
        assert.equal(
            review.authorization.successorImplementationAuthorized,
            false
        );
        assert.equal(
            review.nextDependencyState,
            'requires-separate-bounded-successor-selection'
        );
    });

    it('preserves the checkpoint and Git non-effects', () => {
        const boundary =
            CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW.gitBoundary;
        assert.equal(
            boundary.rollbackEvidence,
            'proposal-and-ledger-checkpoints-recorded-before-delegation'
        );
        assert.equal(boundary.localCheckpointRequired, true);
        assert.equal(boundary.pushMergePublishAuthorized, false);
        assert.equal(boundary.historyRewriteAuthorized, false);
        assert.equal(boundary.cleanupAuthorized, false);
    });

    it('is deeply frozen and remains outside the browser', () => {
        assertDeepFrozen(
            CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW
        );
        assert.doesNotThrow(
            () => validateCoreCategoricalFibredGraduationReview()
        );
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_fibred_graduation|FIBRED-GRADUATE/u
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                review.approval.authority = 'human-review';
            },
            'FIBRED_GRADUATION_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                review.recommendation.residualGaps
                    .frontendAndErgonomics.pop();
            },
            'FIBRED_GRADUATION_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                review.authorization
                    .successorImplementationAuthorized = true;
            },
            'FIBRED_GRADUATION_REVIEW_AUTHORIZATION_DRIFT'
        );
        assertReviewError(
            review => {
                review.gitBoundary.cleanupAuthorized = true;
            },
            'FIBRED_GRADUATION_REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
