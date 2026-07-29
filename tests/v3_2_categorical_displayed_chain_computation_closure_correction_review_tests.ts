/**
 * Focused delegated review tests for
 * H-DTTLF-USABILITY-DISPLAYED-CHAIN-04/D-DTTLF-USABILITY-015.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_REVIEW,
    CoreCategoricalDisplayedChainComputationClosureCorrectionReviewError,
    validateCoreCategoricalDisplayedChainComputationClosureCorrectionReview
} from '../src/v3_2/categorical_displayed_chain_computation_closure_correction_review';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_REVIEW
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

describe('reviewed displayed-chain computation closure', () => {
    it('records the exact delegated D-015 decision', () => {
        const approval =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_REVIEW
                .approval;
        assert.equal(
            approval.gate,
            'H-DTTLF-USABILITY-DISPLAYED-CHAIN-04'
        );
        assert.equal(approval.decisionId, 'D-DTTLF-USABILITY-015');
        assert.equal(approval.decision, 'approved-as-proposed');
        assert.equal(
            approval.authority,
            'user-delegated-unattended-approval'
        );
        assert.equal(approval.humanDecisionSupersedes, true);
    });

    it('snapshots the unchanged pending proposal', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_REVIEW;
        assert.equal(
            review.recommendation.revision,
            'DISPLAYED-CHAIN-COMPUTATION-CLOSURE-CORRECTION-0A-PROPOSAL-1'
        );
        assert.equal(
            review.recommendation.status,
            'proposal-awaiting-h-dttlf-usability-displayed-chain-04'
        );
        assert.equal(
            review.retainedBoundaries.preReviewDecisionEffects
                .implementationAuthorized,
            false
        );
    });

    it('authorizes only the exact transparent computation closure', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_REVIEW
                .authorization;
        assert.deepEqual(
            authorization.restoredTransparentDefinitions,
            [
                'functord_transport_lhs_func',
                'functord_transport_rhs_func'
            ]
        );
        assert.deepEqual(
            authorization.checkedTransparentMirrorDeclarations,
            ['Obj_func__displayed_chain_mirror']
        );
        assert.deepEqual(
            authorization.typedNormalFormSpecializationOwners,
            ['piapp0']
        );
        assert.equal(authorization.exactExistingRuntimeEquationCount, 5);
    });

    it('preserves the mathematical and trusted boundaries', () => {
        const authorization =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_REVIEW
                .authorization;
        assert.equal(authorization.mathematicalOwnerCountRemains, 1);
        assert.equal(authorization.mathematicalRuntimeRuleCountRemains, 6);
        assert.equal(authorization.activeLambdapiEditAuthorized, false);
        assert.equal(
            authorization.completedWeakeningTransferMutationAuthorized,
            false
        );
        assert.equal(
            authorization.externalSubjectOracleAuthorized,
            false
        );
        assert.equal(
            authorization.semanticRuleRewriteOrBroadeningAuthorized,
            false
        );
    });

    it('pins the proposal gates and local Git boundary', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_REVIEW;
        assert.equal(
            review.validation.proposalCheckpoint,
            'adc7bcc5677ec64efcb400b43e3182c40bf6ff10'
        );
        assert.equal(
            review.validation.proposalLedgerCheckpoint,
            'babce5302f964e20c928d88323ee951a5997ef04'
        );
        assert.equal(
            review.validation.rootProposalGate,
            '952-tests-905-pass-47-intentional-skip-zero-fail'
        );
        assert.equal(review.gitBoundary.pushMergePublishAuthorized, false);
        assert.equal(review.gitBoundary.historyRewriteAuthorized, false);
        assert.equal(review.gitBoundary.cleanupAuthorized, false);
    });

    it('is deeply frozen and validates unchanged', () => {
        const review =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_REVIEW;
        assertDeepFrozen(review);
        assert.doesNotThrow(
            () =>
                validateCoreCategoricalDisplayedChainComputationClosureCorrectionReview()
        );
    });

    it('rejects decision, proposal, and scope drift', () => {
        const decision = clone();
        decision.approval.decision = 'revise';
        assert.throws(
            () =>
                validateCoreCategoricalDisplayedChainComputationClosureCorrectionReview(
                    decision
                ),
            error =>
                error instanceof
                    CoreCategoricalDisplayedChainComputationClosureCorrectionReviewError &&
                error.code ===
                    'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_REVIEW_DECISION_DRIFT'
        );

        const proposal = clone();
        proposal.recommendation.proposedCorrection
            .typedNormalFormSpecializationCount = 2;
        assert.throws(
            () =>
                validateCoreCategoricalDisplayedChainComputationClosureCorrectionReview(
                    proposal
                ),
            error =>
                error instanceof
                    CoreCategoricalDisplayedChainComputationClosureCorrectionReviewError &&
                error.code ===
                    'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_REVIEW_PROPOSAL_DRIFT'
        );

        const scope = clone();
        scope.authorization.activeLambdapiEditAuthorized = true;
        assert.throws(
            () =>
                validateCoreCategoricalDisplayedChainComputationClosureCorrectionReview(
                    scope
                ),
            error =>
                error instanceof
                    CoreCategoricalDisplayedChainComputationClosureCorrectionReviewError &&
                error.code ===
                    'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_REVIEW_SCOPE_DRIFT'
        );
    });
});
