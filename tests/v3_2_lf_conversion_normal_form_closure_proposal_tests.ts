/**
 * Focused proposal tests for generic comparison normal-form closure.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL,
    CoreLfComparisonNormalFormClosureProposal,
    CoreLfComparisonNormalFormClosureProposalError,
    validateCoreLfComparisonNormalFormClosureProposal
} from '../src/v3_2/lf_conversion_normal_form_closure_proposal';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CoreLfComparisonNormalFormClosureProposal =>
    JSON.parse(JSON.stringify(
        CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL
    )) as CoreLfComparisonNormalFormClosureProposal;

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

const assertProposalError = (
    mutate: (proposal: CoreLfComparisonNormalFormClosureProposal) => void,
    expected: CoreLfComparisonNormalFormClosureProposalError['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCoreLfComparisonNormalFormClosureProposal(proposal),
        error =>
            error instanceof
                CoreLfComparisonNormalFormClosureProposalError &&
            error.code === expected
    );
};

describe('Core LF comparison normal-form closure proposal', () => {
    it('pins the measured paired-comparison counterevidence', () => {
        const proposal =
            validateCoreLfComparisonNormalFormClosureProposal();
        assertDeepFrozen(proposal);
        const evidence = proposal.measuredCounterevidence;
        assert.deepEqual(
            [
                evidence.consumerRow,
                evidence.consumerRule,
                evidence.earlierLocalRulesSubjectChecked,
                evidence.candidatePiPullbackProjectionSubjectChecked,
                evidence.candidatePiPullbackProjectionProofRuleRequired,
                evidence.pairedComparisonStatus,
                evidence.pairedComparisonSteps,
                evidence.independentlyNormalizedLeftSteps,
                evidence.independentlyNormalizedRightSteps,
                evidence.independentlyNormalizedFormsExactlyEqual,
                evidence.temporaryObserversRetained,
                evidence.genericSourceDiffEmpty
            ],
            [
                'PATHOUT-LIBRARY-INTERNALIZED-1D',
                'pathind.internalized.path-ind-transfd-component',
                6,
                true,
                false,
                'not-equal',
                125,
                58,
                68,
                true,
                false,
                true
            ]
        );
    });

    it('adds only terminal same-budget comparison closure', () => {
        const correction =
            CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL
                .exactCorrection;
        const budget =
            CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL
                .budgetAndFailureContract;
        assert.deepEqual(
            [
                correction.owner,
                correction.trigger,
                correction.deterministicSideOrder,
                correction.directEqualFastPathUnchanged,
                correction.existingPairedTraversalRetained,
                correction.runtimeRuleSetUnchanged,
                correction.proofRuleSetUnchanged,
                correction.newCoreNodeCount,
                correction.newReductionRuleCount,
                correction.comparisonClosureBranchDelta,
                budget.oneGlobalBudgetAcrossPairedAndClosurePhases,
                budget.noBudgetResetBetweenSides,
                budget.distinctNormalFormsRemainNotEqual
            ],
            [
                'coreLfDefinitionalCompare',
                'existing-paired-outcome-is-not-equal',
                ['left', 'right'],
                true,
                true,
                true,
                true,
                0,
                0,
                1,
                true,
                true,
                true
            ]
        );
    });

    it('requires positive, symmetric, negative, budget, and trace gates',
        () => {
            assert.deepEqual(
                CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL
                    .requiredEvidence.focusedGenericRegression,
                [
                    'nested-paired-miss-normalizes-to-one-exact-form',
                    'same-case-with-operands-reversed',
                    'distinct-normal-forms-remain-not-equal',
                    'closure-budget-exhaustion-is-reported',
                    'trace-is-deterministic-and-budget-accounted'
                ]
            );
            assert.equal(
                CORE_LF_COMPARISON_NORMAL_FORM_CLOSURE_PROPOSAL
                    .requiredEvidence.repositoryWideCheckAllRequired,
                false
            );
        });

    it('rejects decision, evidence, and scope drift', () => {
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'COMPARISON_NORMAL_FORM_CLOSURE_DECISION_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.measuredCounterevidence as {
                    independentlyNormalizedFormsExactlyEqual: boolean;
                }).independentlyNormalizedFormsExactlyEqual = false;
            },
            'COMPARISON_NORMAL_FORM_CLOSURE_EVIDENCE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.exactCorrection as {
                    newReductionRuleCount: number;
                }).newReductionRuleCount = 1;
            },
            'COMPARISON_NORMAL_FORM_CLOSURE_SCOPE_DRIFT'
        );
    });

    it('does not enter contributor, npm, workspace, or browser barrels',
        () => {
            for (
                const path of [
                    'src/v3_2/index.ts',
                    'src/v3_2/package_core.ts',
                    'src/v3_2/package_authoring.ts',
                    'src/v3_2/package_workspace.ts',
                    'src/v3_2/browser.ts'
                ]
            ) {
                assert.doesNotMatch(
                    readFileSync(resolve(repositoryRoot, path), 'utf8'),
                    /lf_conversion_normal_form_closure_proposal/u,
                    path
                );
            }
        });
});
