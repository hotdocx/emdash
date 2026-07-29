/**
 * Focused unattended-review tests for
 * H-DTTLF-USABILITY-DISPLAYED-CHAIN-03/D-DTTLF-USABILITY-014.
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
    CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_REVIEW,
    CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewError,
    validateCoreCategoricalDisplayedChainConstantFunctorCorrectionReview
} from '../src/v3_2';

const cloneReview = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_REVIEW
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
        CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewError[
            'code'
        ]
): void => {
    const review = cloneReview();
    mutate(review);
    assert.throws(
        () =>
            validateCoreCategoricalDisplayedChainConstantFunctorCorrectionReview(
                review
            ),
        error =>
            error instanceof
                CoreCategoricalDisplayedChainConstantFunctorCorrectionReviewError &&
            error.code === expected
    );
};

describe(
    'TypeScript v3.2 reviewed final displayed-chain dependency correction',
    () => {
        it('records delegated D-014 with human supersession', () => {
            const approval =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_REVIEW
                    .approval;
            assert.equal(
                approval.gate,
                'H-DTTLF-USABILITY-DISPLAYED-CHAIN-03'
            );
            assert.equal(approval.decisionId, 'D-DTTLF-USABILITY-014');
            assert.equal(
                approval.authority,
                'user-delegated-unattended-approval'
            );
            assert.equal(approval.humanDecisionSupersedes, true);
        });

        it('snapshots the unchanged pending proposal', () => {
            const review =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_REVIEW;
            assert.notEqual(
                review.recommendation,
                CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL
            );
            assert.deepEqual(
                review.recommendation,
                CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL
            );
            assert.equal(
                review.recommendation.decisionEffects
                    .implementationAuthorized,
                false
            );
        });

        it('authorizes exactly the final Const_func ambient signature', () => {
            const authorization =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_REVIEW
                    .authorization;
            assert.deepEqual(
                authorization.additionalAmbientDeclarationPrerequisites,
                ['Const_func']
            );
            assert.deepEqual(
                authorization.totalAmbientDeclarationPrerequisites,
                ['Terminal_obj', 'Const_func']
            );
            assert.equal(
                authorization.totalExistingDeclarationsCompiledForSlice,
                5
            );
        });

        it('preserves object and arrow semantics without adding mathematics', () => {
            const authorization =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_REVIEW
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
                CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL
                    .validationPlan.objectAndInternalizedArrowEvidenceRequired,
                true
            );
        });

        it('pins evidence and keeps broad scope and browser exposure closed', () => {
            const review =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_REVIEW;
            assert.equal(
                review.validation.proposalCheckpoint,
                'fe20a7af2b5ad8835a98f0acce987953c29d33de'
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
                /constant_functor_correction|D-DTTLF-USABILITY-014/u
            );
        });

        it('is deeply frozen and rejects decision, proposal, and scope drift', () => {
            const review =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_REVIEW;
            assertDeepFrozen(review);
            assert.doesNotThrow(
                () =>
                    validateCoreCategoricalDisplayedChainConstantFunctorCorrectionReview()
            );
            assertReviewError(
                changed => {
                    changed.approval.humanDecisionSupersedes = false;
                },
                'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_REVIEW_DECISION_DRIFT'
            );
            assertReviewError(
                changed => {
                    changed.recommendation.exhaustiveLinkageAudit
                        .missingAfterD013 = [];
                },
                'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_REVIEW_PROPOSAL_DRIFT'
            );
            assertReviewError(
                changed => {
                    changed.authorization.intrinsicCoreOwnerAuthorized = true;
                },
                'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_REVIEW_SCOPE_DRIFT'
            );
            assertReviewError(
                changed => {
                    changed.gitBoundary.cleanupAuthorized = true;
                },
                'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_REVIEW_SCOPE_DRIFT'
            );
        });
    }
);
