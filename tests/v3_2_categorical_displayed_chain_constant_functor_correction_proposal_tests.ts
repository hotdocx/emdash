/**
 * Focused D-014 proposal tests for the final Const_func ambient dependency.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL,
    CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalError,
    validateCoreCategoricalDisplayedChainConstantFunctorCorrectionProposal
} from '../src/v3_2';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

describe('displayed-chain final ambient correction proposal', () => {
    it('records the exhaustive two-symbol audit and one residual', () => {
        const audit =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL
                .exhaustiveLinkageAudit;
        assert.deepEqual(
            audit.missingBeforeAmbientCorrections,
            ['Terminal_obj', 'Const_func']
        );
        assert.deepEqual(audit.missingAfterD013, ['Const_func']);
        assert.deepEqual(audit.missingAfterProposedCorrection, []);
        assert.equal(audit.furtherUndeclaredGlobalsExpected, false);
    });

    it('selects only the exact active Const_func signature', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL;
        assert.equal(proposal.discoveredGap.symbol, 'Const_func');
        assert.equal(proposal.discoveredGap.occurrenceCount, 1);
        assert.deepEqual(
            proposal.proposedCorrection
                .additionalAmbientDeclarationPrerequisites,
            ['Const_func']
        );
        assert.equal(
            proposal.proposedCorrection
                .totalExistingDeclarationsCompiledForSlice,
            5
        );
    });

    it('preserves all mathematical and product boundaries', () => {
        const correction =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL
                .proposedCorrection;
        assert.equal(correction.existingRuntimeRulePrerequisiteCountRemains, 2);
        assert.equal(correction.mathematicalOwnerCountRemains, 1);
        assert.equal(correction.mathematicalRuntimeRuleCountRemains, 6);
        assert.equal(correction.activeLambdapiEditCount, 0);
        assert.equal(correction.intrinsicCoreOwnerCountRemains, 0);
    });

    it('remains pending and deeply frozen', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL;
        assert.equal(proposal.decisionEffects.authorityAuthorized, false);
        assert.equal(proposal.decisionEffects.implementationAuthorized, false);
        assertDeepFrozen(proposal);
        assert.doesNotThrow(
            () =>
                validateCoreCategoricalDisplayedChainConstantFunctorCorrectionProposal()
        );
    });

    it('rejects linkage, boundary, and authority drift', () => {
        const linkage = clone();
        linkage.exhaustiveLinkageAudit.missingAfterD013 = [];
        assert.throws(
            () =>
                validateCoreCategoricalDisplayedChainConstantFunctorCorrectionProposal(
                    linkage
                ),
            error =>
                error instanceof
                    CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalError &&
                error.code ===
                    'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_PREREQUISITE_DRIFT'
        );

        const boundary = clone();
        boundary.proposedCorrection.mathematicalRuntimeRuleCountRemains = 7;
        assert.throws(
            () =>
                validateCoreCategoricalDisplayedChainConstantFunctorCorrectionProposal(
                    boundary
                ),
            error =>
                error instanceof
                    CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalError &&
                error.code ===
                    'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_BOUNDARY_DRIFT'
        );

        const authority = clone();
        authority.decisionEffects.implementationAuthorized = true;
        assert.throws(
            () =>
                validateCoreCategoricalDisplayedChainConstantFunctorCorrectionProposal(
                    authority
                ),
            error =>
                error instanceof
                    CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalError &&
                error.code ===
                    'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_AUTHORITY_DRIFT'
        );
    });
});
