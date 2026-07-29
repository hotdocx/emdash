/**
 * Focused delegated-review tests for
 * H-DTTLF-USABILITY-DISPLAYED-CHAIN-2A-CLOSURE-01/
 * D-DTTLF-USABILITY-017.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_REVIEW,
    CoreCategoricalDisplayedChain2aClosureReviewError,
    validateCoreCategoricalDisplayedChain2aClosureReview
} from '../src/v3_2';

const cloneReview = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_REVIEW
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
        CoreCategoricalDisplayedChain2aClosureReviewError['code']
): void => {
    const review = cloneReview();
    mutate(review);
    assert.throws(
        () =>
            validateCoreCategoricalDisplayedChain2aClosureReview(
                review
            ),
        error =>
            error instanceof
                CoreCategoricalDisplayedChain2aClosureReviewError &&
            error.code === expected
    );
};

describe('displayed-chain-2a exact closure delegated review', () => {
    it('records the separate delegated D-017 approval exactly', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_REVIEW
                .approval,
            {
                gate:
                    'H-DTTLF-USABILITY-DISPLAYED-CHAIN-2A-' +
                    'CLOSURE-01',
                decisionId: 'D-DTTLF-USABILITY-017',
                decision: 'approved-as-proposed',
                authority: 'user-delegated-unattended-approval',
                condition:
                    'no-immediate-human-response-after-presented-' +
                    'frozen-proposal',
                recordedOn: '2026-07-29',
                humanDecisionSupersedes: true,
                decisionEvidence:
                    'The user authorized the coding agent to approve a ' +
                    'frozen proposal during unattended continuation when ' +
                    'no immediate human response follows, provided the ' +
                    'Git checkpoint SOP is followed'
            }
        );
    });

    it('retains the exact pending proposal as an immutable snapshot', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_REVIEW;
        assert.notEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL
        );
        assert.deepEqual(
            review.recommendation,
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL
        );
        assert.equal(
            review.recommendation.decisionEffects
                .implementationAuthorized,
            false
        );
    });

    it('authorizes exactly one existing-owner kernel rule', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_REVIEW
                .authorization;
        assert.equal(authorization.activeLambdapiSymbolDelta, 0);
        assert.equal(authorization.activeLambdapiRuntimeRuleDelta, 1);
        assert.equal(authorization.activeLambdapiProofRuleDelta, 0);
        assert.equal(
            authorization.exactLambdapiOwner,
            'fdapp1_int_cell'
        );
        assert.equal(
            authorization.exactLambdapiPairedOwner,
            'Product_pair_funcd'
        );
    });

    it('authorizes the exact isolated three-declaration/nine-rule closure',
        () => {
            const authorization =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_REVIEW
                    .authorization;
            assert.equal(
                authorization
                    .typescriptExistingDeclarationTransferCount,
                3
            );
            assert.equal(authorization.typescriptRuntimeRuleCount, 9);
            assert.equal(
                authorization.typescriptExactExistingRuntimeRuleCount,
                6
            );
            assert.equal(
                authorization.typescriptDerivedRuntimeRuleCount,
                2
            );
            assert.equal(
                authorization.typescriptNewRuntimeRuleCount,
                1
            );
            assert.deepEqual(
                authorization.exactExistingDeclarations,
                ['sigma_Fst', 'sigma_Snd', 'Product_grpd']
            );
            assert.equal(
                authorization.isolatedProfile,
                'fibred-displayed-chain-2a'
            );
        });

    it('keeps checking generic, bounded, and oracle-free', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_REVIEW
                .authorization;
        assert.equal(
            authorization.genericCheckerBudgetPlumbingCount,
            1
        );
        assert.equal(authorization.defaultCoreComparisonBudget, 256);
        assert.equal(authorization.continuationComparisonBudget, 512);
        assert.equal(authorization.intrinsicCoreOwnerDelta, 0);
        assert.equal(
            authorization.ownerSpecificCheckerEvaluatorDelta,
            0
        );
        assert.equal(authorization.externalOracleDelta, 0);
    });

    it('retains the exact corpus, withheld claims, and Git boundary', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_REVIEW;
        assert.deepEqual(
            review.retainedBoundary.prototypeEvidence,
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL
                .prototypeEvidence
        );
        assert.equal(
            review.authorization.generalNdImplementationAuthorized,
            false
        );
        assert.equal(
            review.authorization.bulkWholeLibraryTransferAuthorized,
            false
        );
        assert.equal(review.gitBoundary.localCheckpointRequired, true);
        assert.equal(
            review.gitBoundary.pushMergePublishAuthorized,
            false
        );
        assert.equal(review.gitBoundary.cleanupAuthorized, false);
    });

    it('is deeply frozen and validates against the proposal checkpoint',
        () => {
            const review =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_REVIEW;
            assertDeepFrozen(review);
            assert.equal(
                review.validation.proposalCheckpoint,
                'f647791281095e02c6ebe3f1490e272b4e58c7a0'
            );
            assert.doesNotThrow(
                () =>
                    validateCoreCategoricalDisplayedChain2aClosureReview()
            );
        });

    it('rejects decision, proposal, closure, and Git drift', () => {
        assertReviewError(
            review => {
                review.approval.authority = 'explicit-human-decision';
            },
            'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_DECISION_DRIFT'
        );
        assertReviewError(
            review => {
                review.recommendation.typescriptClosure
                    .existingDeclarations.pop();
            },
            'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_PROPOSAL_DRIFT'
        );
        assertReviewError(
            review => {
                review.authorization.typescriptRuntimeRuleCount = 10;
            },
            'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_AUTHORIZATION_DRIFT'
        );
        assertReviewError(
            review => {
                review.gitBoundary.cleanupAuthorized = true;
            },
            'DISPLAYED_CHAIN_2A_CLOSURE_REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
