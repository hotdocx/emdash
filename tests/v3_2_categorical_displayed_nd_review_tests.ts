/**
 * Focused delegated-review tests for
 * H-DTTLF-USABILITY-DISPLAYED-ND-01/D-DTTLF-USABILITY-018.
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
    CORE_CATEGORICAL_DISPLAYED_ND_AUDIT,
    CORE_CATEGORICAL_DISPLAYED_ND_REVIEW,
    CoreCategoricalDisplayedNdReviewError,
    validateCoreCategoricalDisplayedNdReview
} from '../src/v3_2';

const cloneReview = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_ND_REVIEW
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

const assertReviewError = (
    mutate: (review: any) => void,
    expected: CoreCategoricalDisplayedNdReviewError['code']
): void => {
    const review = cloneReview();
    mutate(review);
    assert.throws(
        () => validateCoreCategoricalDisplayedNdReview(review),
        error =>
            error instanceof CoreCategoricalDisplayedNdReviewError &&
            error.code === expected
    );
};

describe('DISPLAYED-ND-0A exact delegated review', () => {
    it('records the separate delegated D-018 approval exactly', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_ND_REVIEW.approval,
            {
                gate: 'H-DTTLF-USABILITY-DISPLAYED-ND-01',
                decisionId: 'D-DTTLF-USABILITY-018',
                decision: 'approved-as-proposed',
                authority: 'user-delegated-unattended-approval',
                condition:
                    'no-immediate-human-response-after-presented-' +
                    'frozen-proposal',
                recordedOn: '2026-07-29',
                humanDecisionSupersedes: true,
                decisionEvidence:
                    'The user authorized the coding agent to approve a ' +
                    'frozen dependency-ready proposal during unattended ' +
                    'continuation when no immediate human response ' +
                    'follows, provided the Git checkpoint SOP is followed'
            }
        );
    });

    it('retains the exact non-authorizing proposal snapshot', () => {
        const review = CORE_CATEGORICAL_DISPLAYED_ND_REVIEW;
        assert.notEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_ND_AUDIT
        );
        assert.deepEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_ND_AUDIT
        );
        assert.equal(
            review.recommendation.prerequisite
                .semanticImplementationAuthorized,
            false
        );
        assert.equal(
            review.recommendation.nonEffects.includes(
                'does-not-authorize-DISPLAYED-ND-1A'
            ),
            true
        );
    });

    it('authorizes only generic indexed cell composition', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_ND_REVIEW.authorization;
        assert.equal(
            authorization.implementationRow,
            'DISPLAYED-ND-1A'
        );
        assert.equal(authorization.implementationAuthorized, true);
        assert.equal(authorization.surfaceMethod, 'composeCells');
        assert.equal(
            authorization.irTag,
            'typed-cell-composition'
        );
        assert.equal(
            authorization.firstAcceptedClassifier,
            'indexed-transfor'
        );
        assert.equal(
            authorization.lowering,
            'recursive-factorization-to-comp_fapp0-at-Functord_cat'
        );
    });

    it('keeps kernel, transfer, checker, and residual cases unchanged',
        () => {
            const authorization =
                CORE_CATEGORICAL_DISPLAYED_ND_REVIEW.authorization;
            assert.deepEqual(
                [
                    authorization.activeLambdapiOwnerDelta,
                    authorization.activeLambdapiRuleDelta,
                    authorization.typescriptTransferEntryDelta,
                    authorization.intrinsicCoreOwnerDelta,
                    authorization.ownerSpecificCheckerBranchDelta
                ],
                [0, 0, 0, 0, 0]
            );
            assert.equal(authorization.nextHomTransferIncluded, false);
            assert.equal(authorization.identitySyntaxAuthorized, false);
            assert.equal(
                authorization.arbitraryPointwiseCoherenceAuthorized,
                false
            );
            assert.equal(
                authorization.mixedVarianceBridgeAuthorized,
                false
            );
            assert.equal(
                authorization.compositeBaseArrowCellBetaAuthorized,
                false
            );
        });

    it('pins exact rollback and validation evidence', () => {
        const review = CORE_CATEGORICAL_DISPLAYED_ND_REVIEW;
        assert.equal(
            review.validation.proposalCheckpoint,
            'bc29f0d98de32fe0fdbad992859e97711e493e5c'
        );
        assert.equal(
            review.validation.proposalLedgerCheckpoint,
            '0047ee1761d48d80fd71ab9ec5ac157ad08779f4'
        );
        assert.equal(review.gitBoundary.localCheckpointRequired, true);
        assert.equal(
            review.gitBoundary.pushMergePublishAuthorized,
            false
        );
        assert.equal(review.gitBoundary.cleanupAuthorized, false);
    });

    it('is deeply frozen, validates, and stays out of the browser', () => {
        assertDeepFrozen(CORE_CATEGORICAL_DISPLAYED_ND_REVIEW);
        assert.doesNotThrow(
            () => validateCoreCategoricalDisplayedNdReview()
        );
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_displayed_nd_review|DISPLAYED-ND-0A-REVIEWED/u
        );
    });

    it('rejects decision, proposal, authorization, and Git drift', () => {
        assertReviewError(
            review => {
                review.approval.authority = 'explicit-human-decision';
            },
            'DISPLAYED_ND_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                review.recommendation.observationMatrix.pop();
            },
            'DISPLAYED_ND_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                review.authorization.identitySyntaxAuthorized = true;
            },
            'DISPLAYED_ND_REVIEW_AUTHORIZATION_DRIFT'
        );
        assertReviewError(
            review => {
                review.retainedBoundary.computationBoundary
                    .verticalCompositeBaseArrowCellBetaActive = true;
            },
            'DISPLAYED_ND_REVIEW_AUTHORIZATION_DRIFT'
        );
        assertReviewError(
            review => {
                review.gitBoundary.cleanupAuthorized = true;
            },
            'DISPLAYED_ND_REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
