/**
 * SCALE-INDUCTIVE-1B2 minimal expanded-symbol decision evidence.
 */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_INDUCTIVE_1B2_PROPOSAL,
    CoreLfScaleInductive1b2Proposal,
    CoreLfScaleInductive1b2ProposalError,
    validateCoreLfScaleInductive1b2Proposal
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

const mutableCopy = (
    proposal: CoreLfScaleInductive1b2Proposal
): CoreLfScaleInductive1b2Proposal =>
    JSON.parse(JSON.stringify(proposal)) as
        CoreLfScaleInductive1b2Proposal;

describe('SCALE-INDUCTIVE-1B2 expanded-symbol proposal', () => {
    it('freezes the exact decision and selected lean architecture', () => {
        const proposal =
            validateCoreLfScaleInductive1b2Proposal();
        assertDeepFrozen(proposal);
        assert.equal(
            proposal.decision.question,
            'Approve H-DTTLF-SCALE-INDUCTIVE-02/' +
                'D-DTTLF-SCALE-INDUCTIVE-002 as proposed?'
        );
        assert.equal(
            proposal.selectedArchitecture.associationDependency,
            'none'
        );
        assert.equal(
            proposal.selectedArchitecture
                .typescriptPositivityDependency,
            'none'
        );
    });

    it('defers source-inductive convenience and stronger validation', () => {
        const proposal =
            validateCoreLfScaleInductive1b2Proposal();
        assert.deepEqual(proposal.deferredAlternatives, [
            'recursive-generated-owner-association',
            'typescript-source-inductive-generation',
            'typescript-positivity-checker',
            'automatic-eliminator-synthesis',
            'end-user-inductive-declaration-api',
            'mutual-and-higher-order-inductives'
        ]);
        assert.deepEqual(
            proposal.qualificationEvidence.productEffects,
            []
        );
    });

    it('rejects any attempted proposal promotion or drift', () => {
        const promoted = mutableCopy(
            CORE_LF_SCALE_INDUCTIVE_1B2_PROPOSAL
        );
        (promoted as { status: string }).status = 'approved';
        assert.throws(
            () => validateCoreLfScaleInductive1b2Proposal(promoted),
            error =>
                error instanceof
                    CoreLfScaleInductive1b2ProposalError &&
                error.code === 'PROPOSAL_BOUNDARY_DRIFT'
        );
    });

    it('keeps the proposal outside the browser API', () => {
        assert.equal(
            'CORE_LF_SCALE_INDUCTIVE_1B2_PROPOSAL' in browser,
            false
        );
        assert.equal(
            'validateCoreLfScaleInductive1b2Proposal' in browser,
            false
        );
    });
});
