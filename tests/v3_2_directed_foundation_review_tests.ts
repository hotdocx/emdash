/**
 * Focused tests for the approved DIRECTED-FOUNDATION-1 gate.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_DIRECTED_1B_REVIEW,
    CORE_DIRECTED_FOUNDATION_PROPOSAL,
    CORE_DIRECTED_FOUNDATION_REVIEW,
    CoreDirectedFoundationReviewError,
    validateCoreDirectedFoundationReview
} from '../src/v3_2';

const clone = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

describe('TypeScript v3.2 reviewed DIRECTED foundation gate', () => {
    it('records the exact approval without rewriting either prerequisite artifact', () => {
        assert.equal(
            CORE_DIRECTED_FOUNDATION_REVIEW.decisionEvidence,
            'Approve H-DTTLF-02/DIRECTED-FOUNDATION-1 as proposed.'
        );
        assert.deepEqual(
            CORE_DIRECTED_FOUNDATION_REVIEW.proposal,
            CORE_DIRECTED_FOUNDATION_PROPOSAL
        );
        assert.equal(
            CORE_DIRECTED_FOUNDATION_REVIEW.authorization
                .approvedDirected1bArtifactChange,
            false
        );
        assert.equal(
            CORE_DIRECTED_1B_REVIEW.decision,
            'approved-as-proposed'
        );
    });

    it('authorizes exactly the three prerequisite runtime rules', () => {
        assert.deepEqual(
            CORE_DIRECTED_FOUNDATION_REVIEW.authorization.runtimeRuleIds,
            [
                'directed.category-object.decode',
                'directed.displayed-family.decode',
                'directed.displayed-functor.decode'
            ]
        );
        assert.deepEqual(
            CORE_DIRECTED_FOUNDATION_REVIEW.authorization.ownerIds,
            []
        );
        assert.deepEqual(
            CORE_DIRECTED_FOUNDATION_REVIEW.authorization
                .proofTimeRuleIds,
            []
        );
    });

    it('preserves the exact runtime order, scope, budget, and non-effects', () => {
        const authorization =
            CORE_DIRECTED_FOUNDATION_REVIEW.authorization;
        assert.equal(
            authorization.runtimeOrder,
            'foundation-before-directed-1b-before-frozen-mvp'
        );
        assert.equal(
            authorization.runtimeScope,
            'directed-catalog-local'
        );
        assert.equal(authorization.sharedOuterLfBudget, true);
        assert.equal(authorization.stableCategoryHeadRewrites, false);
        assert.equal(authorization.defaultLfProfileChange, false);
        assert.equal(authorization.browserEntryPoint, false);
        assert.equal(authorization.deployedManifestChange, false);
        assert.equal(authorization.arbitraryUserRules, false);
        assert.equal(authorization.newMetatheoryClaim, false);
    });

    it('is deeply frozen and validates unchanged', () => {
        assert.equal(
            Object.isFrozen(CORE_DIRECTED_FOUNDATION_REVIEW),
            true
        );
        assert.equal(
            Object.isFrozen(
                CORE_DIRECTED_FOUNDATION_REVIEW.authorization
                    .runtimeRuleIds
            ),
            true
        );
        assert.doesNotThrow(() =>
            validateCoreDirectedFoundationReview()
        );
    });

    it('rejects decision, proposal, and authorization drift independently', () => {
        const decision = clone(CORE_DIRECTED_FOUNDATION_REVIEW);
        (
            decision as unknown as {
                decision: string;
            }
        ).decision = 'changed';
        assert.throws(
            () => validateCoreDirectedFoundationReview(decision),
            error =>
                error instanceof CoreDirectedFoundationReviewError &&
                error.code === 'INVALID_REVIEW_DECISION'
        );

        const proposal = clone(CORE_DIRECTED_FOUNDATION_REVIEW);
        (
            proposal.proposal.runtimeRules as unknown as {
                id: string;
            }[]
        )[0].id = 'changed';
        assert.throws(
            () => validateCoreDirectedFoundationReview(proposal),
            error =>
                error instanceof CoreDirectedFoundationReviewError &&
                error.code === 'REVIEW_PROPOSAL_DRIFT'
        );

        const authorization = clone(
            CORE_DIRECTED_FOUNDATION_REVIEW
        );
        (
            authorization.authorization as unknown as {
                defaultLfProfileChange: boolean;
            }
        ).defaultLfProfileChange = true;
        assert.throws(
            () => validateCoreDirectedFoundationReview(authorization),
            error =>
                error instanceof CoreDirectedFoundationReviewError &&
                error.code === 'REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
