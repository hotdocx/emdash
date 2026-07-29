/**
 * Focused D-017 proposal tests for the DISPLAYED-CHAIN-2A closure drift.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL,
    CoreCategoricalDisplayedChain2aClosureProposalError,
    validateCoreCategoricalDisplayedChain2aClosureProposal
} from '../src/v3_2/categorical_displayed_chain_2a_closure_proposal';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

describe('displayed-chain-2a closure proposal', () => {
    it('records the D-016 zero-delta stop without rewriting history', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL;
        assert.equal(
            proposal.prerequisite.d016ReviewRevision,
            'DISPLAYED-BRACKET-GRADUATE-1-REVIEWED-1'
        );
        assert.equal(proposal.prerequisite.mandatoryStopHonored, true);
        assert.equal(
            proposal.auditVerdict.zeroDeltaAssumptionFalsified,
            true
        );
        assert.equal(
            proposal.auditVerdict.firstStuckEvidence,
            'recursive-pair-b-c-internalized-arrow-cell'
        );
        assert.equal(
            proposal.auditVerdict.architectureRedesignRequired,
            false
        );
    });

    it('freezes exactly one existing-owner Lambdapi rule', () => {
        const candidate =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL
                .activeLambdapiCandidate;
        assert.equal(candidate.newSymbolCount, 0);
        assert.equal(candidate.newRuntimeRuleCount, 1);
        assert.equal(candidate.newProofRuleCount, 0);
        assert.equal(candidate.owner, 'fdapp1_int_cell');
        assert.equal(candidate.pairedOwner, 'Product_pair_funcd');
        assert.equal(candidate.inferredTargetSlotRetainedAsWildcard, true);
        assert.equal(
            candidate.ownerPositionProbe.positiveGenericConversion,
            'passed'
        );
        assert.equal(
            candidate.ownerPositionProbe.negativeOpaqueCellNoncollapse,
            'passed'
        );
        assert.equal(candidate.warningComparison.warningDelta, 0);
    });

    it('partitions the TypeScript closure as 3 declarations and 9 rules', () => {
        const closure =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL
                .typescriptClosure;
        assert.deepEqual(
            closure.existingDeclarations,
            ['sigma_Fst', 'sigma_Snd', 'Product_grpd']
        );
        assert.equal(closure.exactExistingRuntimeRuleCount, 6);
        assert.equal(closure.derivedRuntimeRuleCount, 2);
        assert.equal(closure.newRuntimeRuleCount, 1);
        assert.equal(closure.totalContinuationRuntimeRuleCount, 9);
        assert.equal(closure.broadSigmaConstructorBetasImported, false);
        assert.equal(closure.typedPatternCorrectionCount, 2);
        assert.equal(
            closure.completedChain1ProfileMutatedInPlace,
            false
        );
    });

    it('keeps checking generic, bounded, and oracle-free', () => {
        const closure =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL
                .typescriptClosure;
        assert.equal(closure.checkerBudgetPlumbing.generic, true);
        assert.equal(closure.checkerBudgetPlumbing.ownerSpecific, false);
        assert.equal(
            closure.checkerBudgetPlumbing.defaultCoreBudgetRemains,
            256
        );
        assert.equal(
            closure.checkerBudgetPlumbing.selectedContinuationBudget,
            512
        );
        assert.equal(closure.subjectValidation, 'typescript-checked');
        assert.equal(closure.externalSubjectReductionOracleCount, 0);
        assert.equal(closure.ownerSpecificCheckerBranchCount, 0);
        assert.equal(closure.ownerSpecificEvaluatorBranchCount, 0);
    });

    it('records object, internalized-arrow, and noncollapse evidence', () => {
        const evidence =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL
                .prototypeEvidence;
        assert.deepEqual(
            evidence.objectComparisons.map(entry => entry.term),
            ['a', 'b', 'c', 'd', 'pair(b,c)']
        );
        assert.equal(
            evidence.objectComparisons.every(
                entry => entry.status === 'equal'
            ),
            true
        );
        assert.deepEqual(
            evidence.internalizedArrowIndependence.map(
                entry => entry.term
            ),
            ['a', 'b', 'c', 'd', 'pair(b,c)']
        );
        assert.equal(
            evidence.internalizedArrowIndependence.every(
                entry => entry.status === 'equal'
            ),
            true
        );
        assert.equal(evidence.pairedInternalCellUsesNewRule, true);
        assert.equal(evidence.noncollapseComparisons.length, 3);
        assert.equal(
            evidence.reindexingCorpusStillRequiredDuringImplementation,
            true
        );
    });

    it('remains pending, non-self-authorizing, and deeply frozen', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_PROPOSAL;
        assert.equal(
            proposal.reviewGate,
            'H-DTTLF-USABILITY-DISPLAYED-CHAIN-2A-CLOSURE-01'
        );
        assert.equal(proposal.decisionId, 'D-DTTLF-USABILITY-017');
        assert.equal(proposal.decisionEffects.authorityAuthorized, false);
        assert.equal(
            proposal.decisionEffects.implementationAuthorized,
            false
        );
        assertDeepFrozen(proposal);
        assert.doesNotThrow(
            () =>
                validateCoreCategoricalDisplayedChain2aClosureProposal()
        );
    });

    it('rejects prerequisite, boundary, and authority drift', () => {
        const prerequisite = clone();
        prerequisite.prerequisite.mandatoryStopHonored = false;
        assert.throws(
            () =>
                validateCoreCategoricalDisplayedChain2aClosureProposal(
                    prerequisite
                ),
            error =>
                error instanceof
                    CoreCategoricalDisplayedChain2aClosureProposalError &&
                error.code ===
                    'DISPLAYED_CHAIN_2A_CLOSURE_PREREQUISITE_DRIFT'
        );

        const boundary = clone();
        boundary.typescriptClosure.totalContinuationRuntimeRuleCount = 8;
        assert.throws(
            () =>
                validateCoreCategoricalDisplayedChain2aClosureProposal(
                    boundary
                ),
            error =>
                error instanceof
                    CoreCategoricalDisplayedChain2aClosureProposalError &&
                error.code ===
                    'DISPLAYED_CHAIN_2A_CLOSURE_BOUNDARY_DRIFT'
        );

        const authority = clone();
        authority.decisionEffects.implementationAuthorized = true;
        assert.throws(
            () =>
                validateCoreCategoricalDisplayedChain2aClosureProposal(
                    authority
                ),
            error =>
                error instanceof
                    CoreCategoricalDisplayedChain2aClosureProposalError &&
                error.code ===
                    'DISPLAYED_CHAIN_2A_CLOSURE_AUTHORITY_DRIFT'
        );
    });
});
