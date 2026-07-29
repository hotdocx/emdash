/**
 * Focused delegated-review tests for
 * H-DTTLF-USABILITY-DISPLAYED-ND-HIGHER-01/D-DTTLF-USABILITY-019.
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
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_REVIEW,
    CoreCategoricalDisplayedNdHigherReviewError,
    validateCoreCategoricalDisplayedNdHigherReview
} from '../src/v3_2';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_REVIEW
));

const assertReviewError = (
    mutate: (review: any) => void,
    expected: CoreCategoricalDisplayedNdHigherReviewError['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCoreCategoricalDisplayedNdHigherReview(review),
        error =>
            error instanceof
                CoreCategoricalDisplayedNdHigherReviewError &&
            error.code === expected
    );
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe('DISPLAYED-ND-HIGHER-1B exact delegated review', () => {
    it('records D-019 separately with human supersession', () => {
        const approval =
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_REVIEW.approval;
        assert.deepEqual(
            [
                approval.decisionId,
                approval.decision,
                approval.authority,
                approval.humanDecisionSupersedes
            ],
            [
                'D-DTTLF-USABILITY-019',
                'approved-as-proposed',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('retains the exact non-authorizing proposal snapshot', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_REVIEW;
        assert.notEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
        );
        assert.deepEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
        );
        assert.equal(
            review.recommendation.prerequisite
                .semanticImplementationAuthorized,
            false
        );
    });

    it('authorizes only the exact rule-free foundation', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_REVIEW
                .authorization;
        assert.deepEqual(
            [
                authorization.implementationRow,
                authorization.implementationAuthorized,
                authorization.exactDeclarations.length,
                authorization.checkedTransparentDefinitionCount,
                authorization.opaqueSignatureCount,
                authorization.exactRuntimeRules.length,
                authorization.exactProofRules.length
            ],
            [
                'DISPLAYED-ND-HIGHER-FOUNDATION-1A',
                true,
                13,
                5,
                8,
                0,
                0
            ]
        );
        assert.deepEqual(
            [
                authorization.targetOwnersAuthorized,
                authorization.targetProjectionRulesAuthorized,
                authorization.richSurfaceConsumerAuthorized,
                authorization.newMathematicalOwnerAuthorized,
                authorization.intrinsicCoreOwnerAuthorized,
                authorization.ownerSpecificCheckerBranchAuthorized
            ],
            [false, false, false, false, false, false]
        );
    });

    it('pins rollback evidence and remains outside the browser', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_REVIEW;
        assert.equal(
            review.validation.proposalCheckpoint,
            '4db1ce8a80725c0030ac8908f416d412591620bd'
        );
        assert.equal(
            review.validation.proposalLedgerCheckpoint,
            '07ce033c34527f1e2cbd4b2f065634a1bb424eca'
        );
        assert.equal(
            review.gitBoundary.pushMergePublishAuthorized,
            false
        );
        assert.doesNotMatch(
            readFileSync('src/v3_2/browser.ts', 'utf8'),
            /categorical_displayed_nd_higher_review|HIGHER-1B-REVIEWED/u
        );
    });

    it('is deeply frozen, validates, and rejects drift', () => {
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_REVIEW
        );
        assert.doesNotThrow(
            () => validateCoreCategoricalDisplayedNdHigherReview()
        );
        assertReviewError(
            review => {
                review.approval.authority = 'explicit-human-decision';
            },
            'DISPLAYED_ND_HIGHER_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                review.recommendation
                    .measuredClosure.targetDeclarations.pop();
            },
            'DISPLAYED_ND_HIGHER_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                review.authorization.targetOwnersAuthorized = true;
            },
            'DISPLAYED_ND_HIGHER_REVIEW_AUTHORIZATION_DRIFT'
        );
        assertReviewError(
            review => {
                review.gitBoundary.cleanupAuthorized = true;
            },
            'DISPLAYED_ND_HIGHER_REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
