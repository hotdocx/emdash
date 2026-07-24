/**
 * Exact post-review records for H-DTTLF-01 and H-DTTLF-02.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_DIRECTED_1A_REVIEW,
    CORE_LF_CONTINUATION_PROFILE_REVIEW,
    CoreContinuationReviewError,
    validateCoreDirected1aReview,
    validateCoreLfContinuationProfileReview
} from '../src/v3_2/continuation_review';
import {
    CORE_DIRECTED_1A_PROPOSAL
} from '../src/v3_2/directed_1a_proposal';
import {
    CORE_LF_CONTINUATION_PROFILE_PROPOSAL
} from '../src/v3_2/lf_profile_proposal';

const clone = <T>(value: T): any =>
    JSON.parse(JSON.stringify(value));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

describe('TypeScript v3.2 reviewed DTT/LF continuation gates', () => {
    it('records both exact approvals without rewriting either proposal', () => {
        assert.equal(
            CORE_LF_CONTINUATION_PROFILE_REVIEW.decision,
            'approved-as-proposed'
        );
        assert.equal(
            CORE_DIRECTED_1A_REVIEW.decision,
            'approved-as-proposed'
        );
        assert.equal(
            CORE_LF_CONTINUATION_PROFILE_REVIEW.decisionEvidence,
            'Approve H-DTTLF-01 and H-DTTLF-02 as proposed.'
        );
        assert.equal(
            CORE_DIRECTED_1A_REVIEW.decisionEvidence,
            CORE_LF_CONTINUATION_PROFILE_REVIEW.decisionEvidence
        );
        assert.equal(
            CORE_LF_CONTINUATION_PROFILE_PROPOSAL.status,
            'proposal-awaiting-h-dttlf-01'
        );
        assert.equal(
            CORE_DIRECTED_1A_PROPOSAL.status,
            'proposal-awaiting-h-dttlf-02'
        );
    });

    it('authorizes only the continuation LF integration boundary', () => {
        assert.deepEqual(
            CORE_LF_CONTINUATION_PROFILE_REVIEW.authorization,
            {
                activeContinuationCheckerApi: true,
                directedCandidateUse: true,
                browserEntryPoint: false,
                deployedManifestChange: false,
                arbitraryUserRules: false,
                newMetatheoryClaim: false
            }
        );
    });

    it('authorizes exactly three directed signatures and zero rules', () => {
        assert.deepEqual(
            CORE_DIRECTED_1A_REVIEW.authorization,
            {
                isolatedCandidateCatalogIntegration: true,
                ownerIds: [
                    'displayed-functor-category',
                    'sigma-category',
                    'sigma-telescope-family'
                ],
                runtimeRuleIds: [],
                proofTimeRuleIds: [],
                browserEntryPoint: false,
                deployedManifestChange: false,
                directed1bRulesPreapproved: false
            }
        );
    });

    it('deep-freezes and validates both reviewed artifacts', () => {
        assertDeepFrozen(CORE_LF_CONTINUATION_PROFILE_REVIEW);
        assertDeepFrozen(CORE_DIRECTED_1A_REVIEW);
        assert.doesNotThrow(
            () => validateCoreLfContinuationProfileReview()
        );
        assert.doesNotThrow(() => validateCoreDirected1aReview());
    });

    it('rejects decision and proposal drift', () => {
        const lfDecision = clone(CORE_LF_CONTINUATION_PROFILE_REVIEW);
        lfDecision.decision = 'revised';
        assert.throws(
            () => validateCoreLfContinuationProfileReview(lfDecision),
            error =>
                error instanceof CoreContinuationReviewError &&
                error.code === 'INVALID_REVIEW_DECISION'
        );

        const directedProposal = clone(CORE_DIRECTED_1A_REVIEW);
        directedProposal.proposal.owners.pop();
        assert.throws(
            () => validateCoreDirected1aReview(directedProposal),
            error =>
                error instanceof CoreContinuationReviewError &&
                error.code === 'REVIEW_PROPOSAL_DRIFT'
        );
    });

    it('rejects authorization expansion independently at each gate', () => {
        const lf = clone(CORE_LF_CONTINUATION_PROFILE_REVIEW);
        lf.authorization.browserEntryPoint = true;
        assert.throws(
            () => validateCoreLfContinuationProfileReview(lf),
            error =>
                error instanceof CoreContinuationReviewError &&
                error.code === 'REVIEW_AUTHORIZATION_DRIFT'
        );

        const directed = clone(CORE_DIRECTED_1A_REVIEW);
        directed.authorization.runtimeRuleIds.push('unreviewed');
        assert.throws(
            () => validateCoreDirected1aReview(directed),
            error =>
                error instanceof CoreContinuationReviewError &&
                error.code === 'REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
