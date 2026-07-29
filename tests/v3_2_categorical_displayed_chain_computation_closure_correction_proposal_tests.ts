/**
 * Focused D-015 proposal tests for displayed-chain computation closure.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_PROPOSAL,
    CoreCategoricalDisplayedChainComputationClosureCorrectionProposalError,
    validateCoreCategoricalDisplayedChainComputationClosureCorrectionProposal
} from '../src/v3_2/categorical_displayed_chain_computation_closure_correction_proposal';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_PROPOSAL
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

describe('displayed-chain computation-closure correction proposal', () => {
    it('records the staged post-linkage subject-check audit', () => {
        const audit =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_PROPOSAL
                .compilationAudit;
        assert.deepEqual(audit.linkageResidualAfterD014, []);
        assert.equal(audit.stagedFailures.length, 5);
        assert.equal(
            audit.compiledSemanticRuleIds.length,
            6
        );
        assert.equal(
            audit.allApprovedSemanticRulesCompileAfterCandidateCorrection,
            true
        );
        assert.equal(audit.furtherComputationResidualExpected, false);
    });

    it('selects two exact bodies, one mirror, and one specialization', () => {
        const authority =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_PROPOSAL
                .authorityCorrections;
        assert.deepEqual(
            authority.restoredTransparentDefinitions.map(
                entry => entry.owner
            ),
            [
                'functord_transport_lhs_func',
                'functord_transport_rhs_func'
            ]
        );
        assert.deepEqual(
            authority.checkedTransparentMirrors.map(entry => entry.owner),
            ['Obj_func']
        );
        assert.equal(
            authority.checkedTransparentMirrors[0].backendName,
            'Obj_func'
        );
        assert.equal(authority.exactExistingRuntimeEquationCount, 5);
        assert.equal(
            authority.normalFormSpecialization.owner,
            'piapp0'
        );
        assert.equal(
            authority.normalFormSpecialization
                .typedExplicitCoreSpecialization,
            true
        );
        assert.equal(
            authority.normalFormSpecialization
                .globalDirected1cOpacityRetained,
            true
        );
    });

    it('preserves the one-owner/six-rule mathematical delta', () => {
        const correction =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_PROPOSAL
                .proposedCorrection;
        assert.equal(
            correction.approvedExistingDeclarationPrerequisiteCountRemains,
            5
        );
        assert.equal(correction.totalGenericTransferDeclarationCount, 6);
        assert.equal(correction.totalPrerequisiteRuntimeClauseCount, 6);
        assert.equal(correction.exactExistingRuntimeEquationCount, 5);
        assert.equal(correction.typedNormalFormSpecializationCount, 1);
        assert.equal(correction.mathematicalOwnerCountRemains, 1);
        assert.equal(correction.mathematicalRuntimeRuleCountRemains, 6);
        assert.equal(correction.activeLambdapiEditCount, 0);
    });

    it('records the typed-capture and dependency-placement corrections', () => {
        const authority =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_PROPOSAL
                .authorityCorrections;
        assert.equal(
            authority.patternRepresentationCorrection.matcherBroadening,
            false
        );
        assert.equal(
            authority.patternRepresentationCorrection
                .selectedNormalFormChanged,
            false
        );
        assert.equal(
            authority.dependencyPlacementPreservation.owner,
            'Const_func'
        );
        assert.equal(
            authority.dependencyPlacementPreservation
                .declarationTransferredExactlyOnce,
            true
        );
        assert.equal(
            authority.dependencyPlacementPreservation
                .completedWeakeningTransferMutated,
            false
        );
    });

    it('remains pending and deeply frozen', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_COMPUTATION_CLOSURE_CORRECTION_PROPOSAL;
        assert.equal(proposal.decisionEffects.authorityAuthorized, false);
        assert.equal(proposal.decisionEffects.implementationAuthorized, false);
        assertDeepFrozen(proposal);
        assert.doesNotThrow(
            () =>
                validateCoreCategoricalDisplayedChainComputationClosureCorrectionProposal()
        );
    });

    it('rejects prerequisite, boundary, and authority drift', () => {
        const prerequisite = clone();
        prerequisite.compilationAudit
            .allApprovedSemanticRulesCompileAfterCandidateCorrection = false;
        assert.throws(
            () =>
                validateCoreCategoricalDisplayedChainComputationClosureCorrectionProposal(
                    prerequisite
                ),
            error =>
                error instanceof
                    CoreCategoricalDisplayedChainComputationClosureCorrectionProposalError &&
                error.code ===
                    'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_PREREQUISITE_DRIFT'
        );

        const boundary = clone();
        boundary.proposedCorrection.typedNormalFormSpecializationCount = 2;
        assert.throws(
            () =>
                validateCoreCategoricalDisplayedChainComputationClosureCorrectionProposal(
                    boundary
                ),
            error =>
                error instanceof
                    CoreCategoricalDisplayedChainComputationClosureCorrectionProposalError &&
                error.code ===
                    'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_BOUNDARY_DRIFT'
        );

        const authority = clone();
        authority.decisionEffects.implementationAuthorized = true;
        assert.throws(
            () =>
                validateCoreCategoricalDisplayedChainComputationClosureCorrectionProposal(
                    authority
                ),
            error =>
                error instanceof
                    CoreCategoricalDisplayedChainComputationClosureCorrectionProposalError &&
                error.code ===
                    'DISPLAYED_CHAIN_COMPUTATION_CLOSURE_AUTHORITY_DRIFT'
        );
    });
});
