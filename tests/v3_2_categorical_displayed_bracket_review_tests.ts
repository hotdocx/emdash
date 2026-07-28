/**
 * Focused delegated-review tests for
 * H-DTTLF-USABILITY-DISPLAYED-BRACKET-01/D-DTTLF-USABILITY-009.
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
    CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL,
    CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW,
    CoreCategoricalDisplayedBracketReviewError,
    validateCoreCategoricalDisplayedBracketReview
} from '../src/v3_2';

const cloneReview = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW
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
    expected: CoreCategoricalDisplayedBracketReviewError['code']
): void => {
    const review = cloneReview();
    mutate(review);
    assert.throws(
        () => validateCoreCategoricalDisplayedBracketReview(review),
        error =>
            error instanceof
                CoreCategoricalDisplayedBracketReviewError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 reviewed displayed bracket', () => {
    it('records the delegated approval separately and exactly', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW;
        assert.deepEqual(review.approval, {
            gate: 'H-DTTLF-USABILITY-DISPLAYED-BRACKET-01',
            decisionId: 'D-DTTLF-USABILITY-009',
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
            CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW;
        assert.notEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL
        );
        assert.deepEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL
        );
        assert.equal(
            review.recommendation.status,
            'proposal-awaiting-h-dttlf-usability-displayed-bracket-01'
        );
    });

    it('authorizes exactly the selected root-only first row', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW.authorization;
        assert.equal(
            authorization.selectedArchitecture,
            'generic-displayed-contextual-compiler'
        );
        assert.equal(
            authorization.implementationRow,
            'DISPLAYED-BRACKET-1A'
        );
        assert.equal(authorization.implementationAuthorized, true);
        assert.equal(authorization.visibility, 'root-only');
        assert.equal(
            authorization.profile,
            'fibred-displayed-bracket-1'
        );
    });

    it('preserves the finite independent-sibling contract', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW.authorization;
        assert.equal(
            authorization.contextScope,
            'finite-nonempty-independent-sibling-block-over-common-base'
        );
        assert.equal(
            authorization.typedPairFrontendNodeAuthorized,
            true
        );
        assert.equal(
            authorization.existingDisplayedAuthorityOnly,
            true
        );
    });

    it('retains the complete positive and negative corpus', () => {
        const row =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW
                .retainedBoundaries.firstImplementationRow;
        assert.equal(row.positiveCorpus.length, 6);
        assert.equal(row.negativeCorpus.length, 7);
        assert.equal(
            row.positiveCorpus.includes(
                'lambda-(b,c)-pair-of-FF-b-and-GG-c'
            ),
            true
        );
        assert.equal(
            row.negativeCorpus.includes(
                'genuine-dependency-edge-in-requested-sibling-block'
            ),
            true
        );
    });

    it('authorizes no owner, chain, nd, or total-category work', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW.authorization;
        assert.equal(
            authorization.additionalSemanticOwnerOrRuleAuthorized,
            false
        );
        assert.equal(
            authorization.displayedChainImplementationAuthorized,
            false
        );
        assert.equal(
            authorization.generalNdCoherenceAuthorized,
            false
        );
        assert.equal(
            authorization.sigmaArrowActionAuthorized,
            false
        );
        assert.equal(
            authorization.totalCategoryComparisonAuthorized,
            false
        );
    });

    it('keeps browser, acquisition, and broad Git effects excluded', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW;
        assert.equal(
            review.authorization
                .browserOrDeployedProfilePromotionAuthorized,
            false
        );
        assert.equal(
            review.authorization.parserOrBulkTransferAuthorized,
            false
        );
        assert.equal(review.gitBoundary.localCheckpointRequired, true);
        assert.equal(review.gitBoundary.pushMergePublishAuthorized, false);
        assert.equal(review.gitBoundary.historyRewriteAuthorized, false);
        assert.equal(review.gitBoundary.cleanupAuthorized, false);
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_displayed_bracket|DISPLAYED-BRACKET/u
        );
    });

    it('is deeply frozen and validates its implementation-ready state', () => {
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW
        );
        assert.doesNotThrow(
            () => validateCoreCategoricalDisplayedBracketReview()
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_BRACKET_REVIEW
                .nextDependencyState,
            'displayed-bracket-1a-implementation-ready'
        );
    });

    it('rejects decision, proposal, and authorization drift', () => {
        assertReviewError(
            review => {
                review.approval.authority = 'human-review';
            },
            'DISPLAYED_BRACKET_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                review.recommendation.firstImplementationRow
                    .positiveCorpus.pop();
            },
            'DISPLAYED_BRACKET_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                review.authorization
                    .displayedChainImplementationAuthorized = true;
            },
            'DISPLAYED_BRACKET_REVIEW_AUTHORIZATION_DRIFT'
        );
        assertReviewError(
            review => {
                review.gitBoundary.cleanupAuthorized = true;
            },
            'DISPLAYED_BRACKET_REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
