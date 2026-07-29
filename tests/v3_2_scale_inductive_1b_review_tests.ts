/**
 * Focused delegated-review tests for
 * H-DTTLF-SCALE-INDUCTIVE-01/D-DTTLF-SCALE-INDUCTIVE-001.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_INDUCTIVE_1B1_PROPOSAL,
    CORE_LF_SCALE_INDUCTIVE_1B1_REVIEW,
    CoreLfScaleInductive1b1ReviewError,
    validateCoreLfScaleInductive1b1Review
} from '../src/v3_2';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_LF_SCALE_INDUCTIVE_1B1_REVIEW
));

const assertReviewError = (
    mutate: (review: any) => void,
    expected: CoreLfScaleInductive1b1ReviewError['code']
): void => {
    const review = clone();
    mutate(review);
    assert.throws(
        () => validateCoreLfScaleInductive1b1Review(review),
        error =>
            error instanceof CoreLfScaleInductive1b1ReviewError &&
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

describe('SCALE-INDUCTIVE-1B1 exact delegated review', () => {
    it('records D-DTTLF-SCALE-INDUCTIVE-001 with supersession', () => {
        const approval =
            CORE_LF_SCALE_INDUCTIVE_1B1_REVIEW.approval;
        assert.deepEqual(
            [
                approval.decisionId,
                approval.decision,
                approval.authority,
                approval.humanDecisionSupersedes
            ],
            [
                'D-DTTLF-SCALE-INDUCTIVE-001',
                'approved-as-proposed',
                'user-delegated-unattended-approval',
                true
            ]
        );
    });

    it('retains an immutable copy of the non-authorizing proposal', () => {
        const recommendation =
            CORE_LF_SCALE_INDUCTIVE_1B1_REVIEW.recommendation;
        assert.notEqual(
            recommendation,
            CORE_LF_SCALE_INDUCTIVE_1B1_PROPOSAL
        );
        assert.deepEqual(
            recommendation,
            CORE_LF_SCALE_INDUCTIVE_1B1_PROPOSAL
        );
        assert.equal(recommendation.decision.status, 'proposal-only');
    });

    it('authorizes only the required nonrecursive indexed contract', () => {
        const authorization =
            CORE_LF_SCALE_INDUCTIVE_1B1_REVIEW.authorization;
        assert.deepEqual(
            [
                authorization.implementationRow,
                authorization.correctedIndices,
                authorization.generatedOwner,
                authorization.generatedRuntimeRuleCount,
                authorization.nonrecursiveIndexedOnly
            ],
            [
                'SCALE-INDUCTIVE-1B1',
                ['a', 'P'],
                'ind_τΣ_',
                1,
                true
            ]
        );
        assert.deepEqual(
            [
                authorization.directRecursionAuthorized,
                authorization.automaticEliminatorSynthesisAuthorized,
                authorization
                    .endUserInductiveDeclarationFacadeAuthorized,
                authorization.parserOrSurfaceSyntaxAuthorized
            ],
            [false, false, false, false]
        );
    });

    it('pins rollback evidence and stays outside the browser API', () => {
        const review = CORE_LF_SCALE_INDUCTIVE_1B1_REVIEW;
        assert.equal(
            review.validation.proposalCheckpoint,
            '830fb975756d1d13d8ddcb516690ea88b19d51d6'
        );
        assert.equal(
            review.validation.proposalLedgerCheckpoint,
            'ecc0cf32b3b5a96662cca2b9e1fff283e65f9d59'
        );
        assert.equal(
            review.gitBoundary.pushMergePublishAuthorized,
            false
        );
        assert.doesNotMatch(
            readFileSync('src/v3_2/browser.ts', 'utf8'),
            /scale_inductive_1b_review|INDUCTIVE-1B1-REVIEWED/u
        );
    });

    it('is deeply frozen, validates, and rejects drift', () => {
        assertDeepFrozen(CORE_LF_SCALE_INDUCTIVE_1B1_REVIEW);
        assert.doesNotThrow(
            () => validateCoreLfScaleInductive1b1Review()
        );
        assertReviewError(
            review => {
                review.approval.authority = 'explicit-human-decision';
            },
            'INDUCTIVE_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                review.recommendation
                    .representationCorrection.correctedIndices.pop();
            },
            'INDUCTIVE_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                review.authorization
                    .endUserInductiveDeclarationFacadeAuthorized = true;
            },
            'INDUCTIVE_REVIEW_AUTHORIZATION_DRIFT'
        );
        assertReviewError(
            review => {
                review.gitBoundary.cleanupAuthorized = true;
            },
            'INDUCTIVE_REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
