/**
 * Focused tests for the approved DIRECTED-FOUNDATION-2 gate.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_DIRECTED_1B_REVIEW,
    CORE_DIRECTED_FOUNDATION_2_PROPOSAL,
    CORE_DIRECTED_FOUNDATION_2_REVIEW,
    CORE_DIRECTED_FOUNDATION_REVIEW,
    CoreDirectedFoundation2ReviewError,
    validateCoreDirectedFoundation2Review
} from '../src/v3_2';

const clone = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

describe('TypeScript v3.2 reviewed DIRECTED foundation 2 gate', () => {
    it('records the exact approval without rewriting prerequisite artifacts', () => {
        assert.equal(
            CORE_DIRECTED_FOUNDATION_2_REVIEW.decisionEvidence,
            'Approve H-DTTLF-02/DIRECTED-FOUNDATION-2 as proposed.'
        );
        assert.equal(
            CORE_DIRECTED_FOUNDATION_2_REVIEW.decision,
            'approved-as-proposed'
        );
        assert.deepEqual(
            CORE_DIRECTED_FOUNDATION_2_REVIEW.proposal,
            CORE_DIRECTED_FOUNDATION_2_PROPOSAL
        );
        assert.equal(
            CORE_DIRECTED_FOUNDATION_REVIEW.decision,
            'approved-as-proposed'
        );
        assert.equal(
            CORE_DIRECTED_1B_REVIEW.decision,
            'approved-as-proposed'
        );
    });

    it('authorizes exactly one decoded Cat-hom runtime rule', () => {
        const authorization =
            CORE_DIRECTED_FOUNDATION_2_REVIEW.authorization;
        assert.deepEqual(
            authorization.runtimeRuleIds,
            ['directed.category-hom.decode']
        );
        assert.deepEqual(authorization.ownerIds, []);
        assert.deepEqual(authorization.proofTimeRuleIds, []);
        assert.equal(
            authorization.redexScope,
            'decoded-category-hom-only'
        );
        assert.equal(authorization.rawClassifierRewrite, false);
        assert.equal(authorization.categoryHeadRewrite, false);
    });

    it('preserves exact order, shared budget, and product non-effects', () => {
        const authorization =
            CORE_DIRECTED_FOUNDATION_2_REVIEW.authorization;
        assert.equal(
            authorization.runtimeOrder,
            'foundation-1-before-foundation-2-before-directed-1b-before-frozen-mvp'
        );
        assert.equal(
            authorization.runtimeScope,
            'directed-catalog-local'
        );
        assert.equal(authorization.sharedOuterLfBudget, true);
        assert.equal(authorization.defaultLfProfileChange, false);
        assert.equal(authorization.browserEntryPoint, false);
        assert.equal(authorization.deployedManifestChange, false);
        assert.equal(authorization.arbitraryUserRules, false);
        assert.equal(authorization.approvedArtifactChange, false);
        assert.equal(authorization.newMetatheoryClaim, false);
    });

    it('is deeply frozen and validates unchanged', () => {
        assertDeepFrozen(CORE_DIRECTED_FOUNDATION_2_REVIEW);
        assert.doesNotThrow(() =>
            validateCoreDirectedFoundation2Review()
        );
    });

    it('rejects decision, proposal, and authorization drift independently', () => {
        const decision = clone(CORE_DIRECTED_FOUNDATION_2_REVIEW);
        (
            decision as unknown as {
                decisionEvidence: string;
            }
        ).decisionEvidence = 'Approve something else.';
        assert.throws(
            () => validateCoreDirectedFoundation2Review(decision),
            error =>
                error instanceof CoreDirectedFoundation2ReviewError &&
                error.code === 'INVALID_REVIEW_DECISION'
        );

        const proposal = clone(CORE_DIRECTED_FOUNDATION_2_REVIEW);
        (
            proposal.proposal.runtimeRules as unknown as {
                id: string;
            }[]
        )[0].id = 'changed';
        assert.throws(
            () => validateCoreDirectedFoundation2Review(proposal),
            error =>
                error instanceof CoreDirectedFoundation2ReviewError &&
                error.code === 'REVIEW_PROPOSAL_DRIFT'
        );

        const authorization = clone(
            CORE_DIRECTED_FOUNDATION_2_REVIEW
        );
        (
            authorization.authorization as unknown as {
                rawClassifierRewrite: boolean;
            }
        ).rawClassifierRewrite = true;
        assert.throws(
            () => validateCoreDirectedFoundation2Review(authorization),
            error =>
                error instanceof CoreDirectedFoundation2ReviewError &&
                error.code === 'REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
