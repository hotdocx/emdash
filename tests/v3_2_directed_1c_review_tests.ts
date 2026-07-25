/**
 * Exact post-review record for H-DTTLF-02/DIRECTED-1C.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_DIRECTED_1C_PROPOSAL,
    CORE_DIRECTED_1C_REVIEW,
    CoreDirected1cReviewError,
    validateCoreDirected1cReview
} from '../src/v3_2';

const clone = <T>(value: T): any =>
    JSON.parse(JSON.stringify(value));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

describe('TypeScript v3.2 reviewed DIRECTED-1C gate', () => {
    it('records the exact approval without rewriting the proposal', () => {
        assert.equal(
            CORE_DIRECTED_1C_REVIEW.decisionEvidence,
            'Approve H-DTTLF-02/DIRECTED-1C as proposed.'
        );
        assert.equal(
            CORE_DIRECTED_1C_REVIEW.decision,
            'approved-as-proposed'
        );
        assert.equal(
            CORE_DIRECTED_1C_PROPOSAL.status,
            'proposal-awaiting-h-dttlf-02'
        );
        assert.deepEqual(
            CORE_DIRECTED_1C_REVIEW.proposal,
            CORE_DIRECTED_1C_PROPOSAL
        );
    });

    it('authorizes exactly one opaque signature import', () => {
        assert.deepEqual(
            CORE_DIRECTED_1C_REVIEW.authorization.ownerIds,
            ['section-object-evaluation']
        );
        assert.deepEqual(
            CORE_DIRECTED_1C_REVIEW.authorization.opaqueImportOwnerIds,
            ['section-object-evaluation']
        );
        assert.deepEqual(
            CORE_DIRECTED_1C_REVIEW.authorization
                .activeTransparentDefinitionIds,
            ['section-object-evaluation']
        );
        assert.deepEqual(
            CORE_DIRECTED_1C_REVIEW.authorization
                .transferredDefinitionBodyIds,
            []
        );
    });

    it('authorizes no new computation rule', () => {
        assert.deepEqual(
            CORE_DIRECTED_1C_REVIEW.authorization.runtimeRuleIds,
            []
        );
        assert.deepEqual(
            CORE_DIRECTED_1C_REVIEW.authorization.proofTimeRuleIds,
            []
        );
        assert.equal(
            CORE_DIRECTED_1C_REVIEW.authorization
                .reuseGenericOuterLfBeta,
            true
        );
        assert.equal(
            CORE_DIRECTED_1C_REVIEW.authorization
                .reuseDirected1bTelescopeFibreRule,
            true
        );
    });

    it('preserves product and metatheory exclusions', () => {
        assert.deepEqual(
            {
                emittedShadowDeclarations:
                    CORE_DIRECTED_1C_REVIEW.authorization
                        .emittedShadowDeclarations,
                defaultLfProfileChange:
                    CORE_DIRECTED_1C_REVIEW.authorization
                        .defaultLfProfileChange,
                browserEntryPoint:
                    CORE_DIRECTED_1C_REVIEW.authorization.browserEntryPoint,
                deployedManifestChange:
                    CORE_DIRECTED_1C_REVIEW.authorization
                        .deployedManifestChange,
                directedGraduate1Preapproved:
                    CORE_DIRECTED_1C_REVIEW.authorization
                        .directedGraduate1Preapproved,
                newMetatheoryClaim:
                    CORE_DIRECTED_1C_REVIEW.authorization
                        .newMetatheoryClaim
            },
            {
                emittedShadowDeclarations: false,
                defaultLfProfileChange: false,
                browserEntryPoint: false,
                deployedManifestChange: false,
                directedGraduate1Preapproved: false,
                newMetatheoryClaim: false
            }
        );
    });

    it('is deeply frozen and validates unchanged', () => {
        assertDeepFrozen(CORE_DIRECTED_1C_REVIEW);
        assert.doesNotThrow(() => validateCoreDirected1cReview());
    });

    it('rejects decision, proposal, and authorization drift', () => {
        const decision = clone(CORE_DIRECTED_1C_REVIEW);
        decision.decisionEvidence = 'Approve something else.';
        assert.throws(
            () => validateCoreDirected1cReview(decision),
            error =>
                error instanceof CoreDirected1cReviewError &&
                error.code === 'INVALID_REVIEW_DECISION'
        );

        const proposal = clone(CORE_DIRECTED_1C_REVIEW);
        proposal.proposal.owners[0].candidateDisposition =
            'transparent-checked-definition';
        assert.throws(
            () => validateCoreDirected1cReview(proposal),
            error =>
                error instanceof CoreDirected1cReviewError &&
                error.code === 'REVIEW_PREREQUISITE_DRIFT'
        );

        const authorization = clone(CORE_DIRECTED_1C_REVIEW);
        authorization.authorization.directedGraduate1Preapproved = true;
        assert.throws(
            () => validateCoreDirected1cReview(authorization),
            error =>
                error instanceof CoreDirected1cReviewError &&
                error.code === 'REVIEW_AUTHORIZATION_DRIFT'
        );
    });
});
