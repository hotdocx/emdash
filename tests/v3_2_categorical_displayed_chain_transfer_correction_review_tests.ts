/**
 * Focused unattended-review tests for
 * H-DTTLF-USABILITY-DISPLAYED-CHAIN-02/D-DTTLF-USABILITY-013.
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
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW,
    CoreCategoricalDisplayedChainTransferCorrectionReviewError,
    validateCoreCategoricalDisplayedChainTransferCorrectionReview
} from '../src/v3_2';

const cloneReview = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW
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
        CoreCategoricalDisplayedChainTransferCorrectionReviewError['code']
): void => {
    const review = cloneReview();
    mutate(review);
    assert.throws(
        () =>
            validateCoreCategoricalDisplayedChainTransferCorrectionReview(
                review
            ),
        error =>
            error instanceof
                CoreCategoricalDisplayedChainTransferCorrectionReviewError &&
            error.code === expected
    );
};

describe(
    'TypeScript v3.2 reviewed displayed-chain transfer correction',
    () => {
        it('records delegated D-013 with human supersession', () => {
            const approval =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW
                    .approval;
            assert.equal(
                approval.gate,
                'H-DTTLF-USABILITY-DISPLAYED-CHAIN-02'
            );
            assert.equal(approval.decisionId, 'D-DTTLF-USABILITY-013');
            assert.equal(
                approval.authority,
                'user-delegated-unattended-approval'
            );
            assert.equal(approval.humanDecisionSupersedes, true);
        });

        it('snapshots the unchanged pending proposal', () => {
            const review =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW;
            assert.notEqual(
                review.recommendation,
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL
            );
            assert.deepEqual(
                review.recommendation,
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL
            );
            assert.equal(
                review.recommendation.decisionEffects
                    .implementationAuthorized,
                false
            );
        });

        it('authorizes exactly one ambient signature', () => {
            const authorization =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW
                    .authorization;
            assert.deepEqual(
                authorization.ambientDeclarationPrerequisites,
                ['Terminal_obj']
            );
            assert.equal(
                authorization.ambientDeclarationPrerequisiteCount,
                1
            );
            assert.equal(
                authorization.chainSpecificDeclarationPrerequisiteCountRemains,
                3
            );
            assert.equal(
                authorization.totalExistingDeclarationsCompiledForSlice,
                4
            );
        });

        it('preserves the one-owner/six-rule mathematical boundary', () => {
            const authorization =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW
                    .authorization;
            assert.equal(authorization.mathematicalOwnerCountRemains, 1);
            assert.equal(
                authorization.mathematicalRuntimeRuleCountRemains,
                6
            );
            assert.equal(authorization.activeLambdapiEditAuthorized, false);
            assert.equal(
                authorization.genericDeclarationTransferRequired,
                true
            );
            assert.equal(authorization.intrinsicCoreOwnerAuthorized, false);
            assert.equal(
                authorization.wildcardOrRuleBroadeningAuthorized,
                false
            );
        });

        it('pins proposal evidence and keeps broad scope closed', () => {
            const review =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW;
            assert.equal(
                review.validation.proposalCheckpoint,
                '6a46dea169ec358a3882f9ec86a04be9af713963'
            );
            assert.equal(
                review.validation.liveCanonicalExportGate,
                '14-tests-pass'
            );
            assert.equal(
                review.authorization.parserRawExprOrSecondCheckerAuthorized,
                false
            );
            assert.equal(
                review.authorization.browserOrBulkTransferAuthorized,
                false
            );
            assert.equal(review.gitBoundary.pushMergePublishAuthorized, false);
            assert.doesNotMatch(
                readFileSync('src/v3_2/browser.ts', 'utf8'),
                /displayed_chain_transfer_correction|D-DTTLF-USABILITY-013/u
            );
        });

        it('is deeply frozen and rejects decision, proposal, and scope drift', () => {
            const review =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW;
            assertDeepFrozen(review);
            assert.doesNotThrow(
                () =>
                    validateCoreCategoricalDisplayedChainTransferCorrectionReview()
            );
            assertReviewError(
                changed => {
                    changed.approval.humanDecisionSupersedes = false;
                },
                'DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW_DECISION_DRIFT'
            );
            assertReviewError(
                changed => {
                    changed.recommendation.proposedCorrection
                        .ambientDeclarationPrerequisites.push('tt');
                },
                'DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW_PROPOSAL_DRIFT'
            );
            assertReviewError(
                changed => {
                    changed.authorization.intrinsicCoreOwnerAuthorized = true;
                },
                'DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW_SCOPE_DRIFT'
            );
            assertReviewError(
                changed => {
                    changed.gitBoundary.cleanupAuthorized = true;
                },
                'DISPLAYED_CHAIN_TRANSFER_CORRECTION_REVIEW_SCOPE_DRIFT'
            );
        });
    }
);
