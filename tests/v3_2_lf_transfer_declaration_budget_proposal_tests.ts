/**
 * Focused proposal tests for declaration-checker budget propagation.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_TRANSFER_DECLARATION_BUDGET_PROPOSAL,
    CoreLfTransferDeclarationBudgetProposal,
    CoreLfTransferDeclarationBudgetProposalError,
    validateCoreLfTransferDeclarationBudgetProposal
} from '../src/v3_2/lf_transfer_declaration_budget_proposal';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CoreLfTransferDeclarationBudgetProposal =>
    JSON.parse(JSON.stringify(
        CORE_LF_TRANSFER_DECLARATION_BUDGET_PROPOSAL
    )) as CoreLfTransferDeclarationBudgetProposal;

const expectError = (
    mutate: (proposal: CoreLfTransferDeclarationBudgetProposal) => void,
    code: CoreLfTransferDeclarationBudgetProposalError['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCoreLfTransferDeclarationBudgetProposal(proposal),
        error =>
            error instanceof CoreLfTransferDeclarationBudgetProposalError &&
            error.code === code
    );
};

describe('Core LF transfer declaration budget proposal', () => {
    it('pins the ignored 512 versus 256 PathInd counterexample', () => {
        const proposal = validateCoreLfTransferDeclarationBudgetProposal();
        assert.equal(Object.isFrozen(proposal), true);
        const evidence = proposal.parentCounterevidence;
        assert.deepEqual(
            [
                evidence.pathIndProposalCheckpoint,
                evidence.pathIndReviewCheckpoint,
                evidence.requestedComparisonStepLimit,
                evidence.reportedComparisonStepLimit,
                evidence.firstTransparentDefinitionCompiled,
                evidence.failingTransparentDefinition,
                evidence.failureCode,
                evidence.mathematicalMismatchObserved
            ],
            [
                '19eb941',
                '2112543',
                512,
                256,
                'pathout_motive_transport_obj',
                'pathout_motive_transport_arrow',
                'CONVERSION_STEP_LIMIT',
                false
            ]
        );
    });

    it('selects only default-preserving internal budget propagation', () => {
        const correction =
            CORE_LF_TRANSFER_DECLARATION_BUDGET_PROPOSAL.exactCorrection;
        assert.deepEqual(
            [
                correction.publicOptionNameUnchanged,
                correction.publicFactorySignatureUnchanged,
                correction.exportedDefaultUnchanged,
                correction.perCompilationLimitAlreadyRequestedByCallers,
                correction.boundedOnly,
                correction.genericCheckerBranchDelta,
                correction.trustedCoreNodeDelta,
                correction.reductionEquationDelta
            ],
            [true, true, true, true, true, 0, 0, 0]
        );
        assert.equal(correction.algorithm.length, 6);
    });

    it('requires exact low-budget, default, and PathInd regressions', () => {
        const evidence =
            CORE_LF_TRANSFER_DECLARATION_BUDGET_PROPOSAL.requiredEvidence;
        assert.deepEqual(evidence.focusedRegression, [
            'one-delta-transparent-body-fails-with-explicit-zero-limit',
            'same-one-delta-transparent-body-passes-with-limit-one',
            'result-records-the-exact-selected-limit',
            'omitted-option-retains-the-256-step-default',
            'invalid-option-remains-rejected'
        ]);
        assert.equal(evidence.reviewedPathIndV6ConsumerReplayRequired, true);
        assert.equal(
            evidence.requiredFullTypeScriptGateBeforeSemanticCheckpoint,
            true
        );
        assert.equal(evidence.repositoryWideAggregateRequired, false);
    });

    it('rejects authority, scope, and authorization drift', () => {
        expectError(
            proposal => {
                (proposal.parentCounterevidence as {
                    reportedComparisonStepLimit: number;
                }).reportedComparisonStepLimit = 512;
            },
            'LF_TRANSFER_DECLARATION_BUDGET_AUTHORITY_DRIFT'
        );
        expectError(
            proposal => {
                (proposal.exactCorrection as {
                    exportedDefaultUnchanged: boolean;
                }).exportedDefaultUnchanged = false;
            },
            'LF_TRANSFER_DECLARATION_BUDGET_SCOPE_DRIFT'
        );
        expectError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'LF_TRANSFER_DECLARATION_BUDGET_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, package, workspace, or browser barrels',
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
                    /lf_transfer_declaration_budget_proposal/u,
                    path
                );
            }
        });
});
