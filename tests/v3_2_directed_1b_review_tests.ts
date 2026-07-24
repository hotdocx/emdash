/**
 * Exact post-review record for H-DTTLF-02/DIRECTED-1B.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_DIRECTED_1B_PROPOSAL,
    CORE_DIRECTED_1B_REVIEW,
    CoreDirected1bReviewError,
    validateCoreDirected1bReview
} from '../src/v3_2';

const clone = <T>(value: T): any =>
    JSON.parse(JSON.stringify(value));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

describe('TypeScript v3.2 reviewed DIRECTED-1B gate', () => {
    it('records the exact approval without rewriting the proposal', () => {
        assert.equal(
            CORE_DIRECTED_1B_REVIEW.decisionEvidence,
            'Approve H-DTTLF-02/DIRECTED-1B as proposed.'
        );
        assert.equal(
            CORE_DIRECTED_1B_REVIEW.decision,
            'approved-as-proposed'
        );
        assert.equal(
            CORE_DIRECTED_1B_PROPOSAL.status,
            'proposal-awaiting-h-dttlf-02'
        );
        assert.deepEqual(
            CORE_DIRECTED_1B_REVIEW.proposal,
            CORE_DIRECTED_1B_PROPOSAL
        );
    });

    it('authorizes exactly five owners and one transparent mirror', () => {
        assert.deepEqual(
            CORE_DIRECTED_1B_REVIEW.authorization.ownerIds,
            [
                'decoded-dependent-pair',
                'dependent-pair',
                'sigma-first-projection',
                'sigma-transport-arrow',
                'sigma-telescope-transport'
            ]
        );
        assert.deepEqual(
            CORE_DIRECTED_1B_REVIEW.authorization
                .checkedTransparentDefinitionIds,
            ['sigma-telescope-transport']
        );
    });

    it('authorizes exactly three scoped runtime rules and zero proof rules', () => {
        assert.deepEqual(
            CORE_DIRECTED_1B_REVIEW.authorization.runtimeRuleIds,
            [
                'directed.sigma-object.decode',
                'directed.sigma-first-projection.evaluate',
                'directed.sigma-telescope-fibre.evaluate'
            ]
        );
        assert.deepEqual(
            CORE_DIRECTED_1B_REVIEW.authorization.proofTimeRuleIds,
            []
        );
        assert.equal(
            CORE_DIRECTED_1B_REVIEW.authorization.runtimeScope,
            'directed-catalog-local'
        );
        assert.equal(
            CORE_DIRECTED_1B_REVIEW.authorization.sharedOuterLfBudget,
            true
        );
    });

    it('preserves every product, deferral, and metatheory exclusion', () => {
        assert.deepEqual(
            {
                defaultLfProfileChange:
                    CORE_DIRECTED_1B_REVIEW.authorization
                        .defaultLfProfileChange,
                browserEntryPoint:
                    CORE_DIRECTED_1B_REVIEW.authorization.browserEntryPoint,
                deployedManifestChange:
                    CORE_DIRECTED_1B_REVIEW.authorization
                        .deployedManifestChange,
                generalSigmaHomPreapproved:
                    CORE_DIRECTED_1B_REVIEW.authorization
                        .generalSigmaHomPreapproved,
                directed1cPreapproved:
                    CORE_DIRECTED_1B_REVIEW.authorization
                        .directed1cPreapproved,
                newMetatheoryClaim:
                    CORE_DIRECTED_1B_REVIEW.authorization
                        .newMetatheoryClaim
            },
            {
                defaultLfProfileChange: false,
                browserEntryPoint: false,
                deployedManifestChange: false,
                generalSigmaHomPreapproved: false,
                directed1cPreapproved: false,
                newMetatheoryClaim: false
            }
        );
    });

    it('is deeply frozen and validates unchanged', () => {
        assertDeepFrozen(CORE_DIRECTED_1B_REVIEW);
        assert.doesNotThrow(() => validateCoreDirected1bReview());
    });

    it('rejects decision, proposal, and authorization drift', () => {
        const decision = clone(CORE_DIRECTED_1B_REVIEW);
        decision.decisionEvidence = 'Approve something else.';
        assert.throws(
            () => validateCoreDirected1bReview(decision),
            error =>
                error instanceof CoreDirected1bReviewError &&
                error.code === 'INVALID_REVIEW_DECISION'
        );

        const proposal = clone(CORE_DIRECTED_1B_REVIEW);
        proposal.proposal.runtimeRules.pop();
        assert.throws(
            () => validateCoreDirected1bReview(proposal),
            error =>
                error instanceof CoreDirected1bReviewError &&
                error.code === 'REVIEW_PROPOSAL_DRIFT'
        );

        const authorization = clone(CORE_DIRECTED_1B_REVIEW);
        authorization.authorization.generalSigmaHomPreapproved = true;
        assert.throws(
            () => validateCoreDirected1bReview(authorization),
            error =>
                error instanceof CoreDirected1bReviewError &&
                error.code === 'REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
