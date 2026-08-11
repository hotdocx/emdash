/**
 * Focused proposal-v2 tests for generic comparison source-root replay.
 */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2,
    CoreLfComparisonNormalFormClosureProposalV2,
    CoreLfComparisonNormalFormClosureProposalV2Error,
    validateCoreLfComparisonNormalFormClosureProposalV2
} from '../src/v3_2/lf_conversion_normal_form_closure_proposal_v2';

const clone = (): CoreLfComparisonNormalFormClosureProposalV2 =>
    JSON.parse(JSON.stringify(
        CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2
    )) as CoreLfComparisonNormalFormClosureProposalV2;

const assertProposalError = (
    mutate: (proposal: CoreLfComparisonNormalFormClosureProposalV2) => void,
    expected: CoreLfComparisonNormalFormClosureProposalV2Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCoreLfComparisonNormalFormClosureProposalV2(proposal),
        error =>
            error instanceof
                CoreLfComparisonNormalFormClosureProposalV2Error &&
            error.code === expected
    );
};

describe('Core LF comparison normal-form closure proposal v2', () => {
    it('pins the exact v1 counterexample without a retained observer', () => {
        const proposal =
            validateCoreLfComparisonNormalFormClosureProposalV2();
        assert.equal(Object.isFrozen(proposal), true);
        const evidence = proposal.parent.counterevidence;
        assert.deepEqual(
            [
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                evidence.pairedComparisonSteps,
                evidence.pairedMismatchCode,
                evidence.pairedReturnedLeftAdditionalSteps,
                evidence.pairedReturnedRightAdditionalSteps,
                evidence.pairedReturnedNormalFormsExactlyEqual,
                evidence.originalLeftNormalizationSteps,
                evidence.originalRightNormalizationSteps,
                evidence.originalSourceNormalFormsExactlyEqual,
                evidence.repositorySourceObserverAdded,
                evidence.retainedObserver
            ],
            [
                'cf8ed76',
                '778da06',
                125,
                'TAG_MISMATCH',
                0,
                0,
                false,
                58,
                68,
                true,
                false,
                false
            ]
        );
    });

    it('selects original roots with the consumed budget retained', () => {
        const proposal =
            CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2;
        const correction = proposal.exactCorrection;
        const budget = proposal.budgetAndFailureContract;
        assert.deepEqual(
            [
                correction.closureInputs,
                correction.pairedOutcomeRootsUsedAsClosureInputs,
                correction.pairedOutcomeRetainedForFallbackDiagnostic,
                correction.replayedReductionsCountAgainstOriginalBudget,
                correction.repeatedReductionWorkMayAppearInTrace,
                budget.pairedPhaseConsumptionRetained,
                budget.sourceReplayReceivesOnlyRemainingBudget,
                budget.noMemoizationOrTraceDeduplication
            ],
            [
                'original-comparison-source-roots',
                false,
                true,
                true,
                true,
                true,
                true,
                true
            ]
        );
    });

    it('keeps the generic trust and public boundary unchanged', () => {
        const correction =
            CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2
                .exactCorrection;
        assert.deepEqual(
            [
                correction.newCoreNodeCount,
                correction.newReductionRuleCount,
                correction.checkerBranchDelta,
                correction.comparisonClosureBranchDelta,
                correction.runtimeRuleSetUnchanged,
                correction.proofRuleSetUnchanged,
                correction.unificationNotInvoked
            ],
            [0, 0, 0, 1, true, true, true]
        );
    });

    it('requires the over-normalization and PathInd regressions', () => {
        const required =
            CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL_V2
                .requiredEvidence;
        assert.equal(required.focusedGenericRegression.length, 9);
        assert.equal(
            required.focusedGenericRegression.includes(
                'paired-over-normalization-loses-intermediate-parent-redex'
            ),
            true
        );
        assert.equal(required.reviewedPathIndV5ConsumerMustCompile, true);
        assert.equal(required.fullTypeScriptGateRequiredBeforeSemanticCheckpoint,
            true);
        assert.equal(required.repositoryWideCheckAllRequired, false);
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent.counterevidence as {
                    pairedComparisonSteps: number;
                }).pairedComparisonSteps = 124;
            },
            'COMPARISON_NORMAL_FORM_CLOSURE_V2_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.exactCorrection as {
                    closureInputs: string;
                }).closureInputs = 'paired-outcome-roots';
            },
            'COMPARISON_NORMAL_FORM_CLOSURE_V2_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'COMPARISON_NORMAL_FORM_CLOSURE_V2_AUTHORIZATION_DRIFT'
        );
    });
});
