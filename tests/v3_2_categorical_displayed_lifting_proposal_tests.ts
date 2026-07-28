/**
 * Executable DISPLAYED-LIFTING-0A owner/action proposal tests.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL,
    CoreCategoricalDisplayedLiftingProposalError,
    validateCoreCategoricalDisplayedLiftingProposal
} from '../src/v3_2';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const assertProposalError = (
    mutate: (proposal: any) => void,
    expected: CoreCategoricalDisplayedLiftingProposalError['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCoreCategoricalDisplayedLiftingProposal(proposal),
        error =>
            error instanceof
                CoreCategoricalDisplayedLiftingProposalError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 DISPLAYED-LIFTING-0A proposal', () => {
    it('starts from the exact implemented bracket checkpoint', () => {
        const prerequisite =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL.prerequisite;
        assert.equal(
            prerequisite.displayedBracketDecision,
            'D-DTTLF-USABILITY-009'
        );
        assert.equal(
            prerequisite.displayedBracketImplementationCheckpoint,
            'd4e0e9bc5ca4dc07dcdfa44e2cb048545f3ee8ab'
        );
        assert.deepEqual(prerequisite.measuredRootGate, {
            tests: 841,
            passed: 795,
            skipped: 46,
            failed: 0
        });
        assert.equal(prerequisite.successorAutomaticallyAuthorized, false);
    });

    it('corrects the architecture without adding a second elaborator', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL;
        assert.equal(
            proposal.clarifiedGoal.bracketMeaning,
            'internal-syntax-directed-contextual-lifting-operation'
        );
        assert.equal(
            proposal.clarifiedGoal.explicitBracketPunctuationRequired,
            false
        );
        assert.equal(proposal.architectureCorrection.rawExprLayerAdded, false);
        assert.equal(
            proposal.architectureCorrection.bidirectionalCheckerAdded,
            false
        );
        assert.equal(proposal.architectureCorrection.parserSelected, false);
        assert.equal(
            proposal.architectureCorrection.unsupportedNodePolicy,
            'fail-closed-with-source-provenance'
        );
    });

    it('records that no earlier recursive categorical bracket was lost', () => {
        const migration =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL
                .migrationAssessment;
        assert.equal(migration.legacyGenericLfFrontendPhysicallyDeleted, true);
        assert.equal(migration.legacyMechanismsRecoverableFromMainAndHistory, true);
        assert.equal(
            migration.priorRecursiveCategoricalBracketSolutionDeleted,
            false
        );
        assert.equal(
            migration.staleCategorySpecificApiRestorationSelected,
            false
        );
    });

    it('freezes the complete implemented ordinary recursion matrix', () => {
        const rows =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL.ordinaryMatrix;
        assert.equal(rows.length, 6);
        assert.equal(
            rows.every(row => row.status.startsWith('implemented')),
            true
        );
        const fixed = rows.find(
            row => row.id ===
                'ordinary-open-subject-closed-argument'
        );
        assert.equal(fixed?.example, 'lambda x :^f A. F x y0');
        assert.match(fixed?.lowering ?? '', /Eval_func/u);
        assert.equal(fixed?.specializedActiveOwner, 'fapp0_func');
    });

    it('distinguishes implemented displayed recursion from exact gaps', () => {
        const rows =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL.displayedMatrix;
        const byId = (id: string): any =>
            rows.find(row => row.id === id);
        assert.equal(byId('displayed-slot').status, 'implemented');
        assert.equal(
            byId('displayed-closed-subject-open-argument').status,
            'implemented'
        );
        assert.equal(byId('displayed-fibre-pair').status, 'implemented');
        assert.equal(
            byId('displayed-open-subject-closed-argument').status,
            'authority-or-derived-construction-unresolved'
        );
        assert.equal(
            byId('displayed-open-subject-open-argument').status,
            'authority-or-derived-construction-unresolved'
        );
        assert.match(
            byId('displayed-open-subject-open-argument').exactGap,
            /reindexing-laws/u
        );
    });

    it('does not confuse active ingredients with a selected evaluator', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL;
        assert.equal(
            proposal.ownerAuditConclusion
                .genericCoherentDisplayedEvaluationOwnerSelected,
            false
        );
        assert.equal(
            proposal.ownerAuditConclusion
                .genericCoherentDisplayedEvaluationLexicallyPresent,
            false
        );
        assert.equal(
            proposal.ownerAuditConclusion
                .absenceProvesMathematicalImpossibility,
            false
        );
        const fixed = proposal.displayedMatrix.find(
            row => row.id ===
                'displayed-open-subject-closed-argument'
        );
        assert.equal(fixed?.activeIngredients.includes('Functor_catd'), true);
        assert.equal(fixed?.activeIngredients.includes('Eval_func'), true);
    });

    it('separates variance, higher cells, chains, and profile diagnosis', () => {
        const rows =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL.displayedMatrix;
        const byId = (id: string): any =>
            rows.find(row => row.id === id);
        assert.equal(
            byId('displayed-contravariant-action').status,
            'frontend-route-unselected'
        );
        assert.equal(
            byId('displayed-higher-transformation-action').status,
            'separate-displayed-nd-0a'
        );
        assert.equal(
            byId('displayed-genuine-dependent-chain').status,
            'separate-displayed-chain-0a'
        );
        assert.equal(
            byId('displayed-profile-composition').diagnostic,
            'TYPE_MISMATCH'
        );
        assert.equal(
            byId('displayed-profile-composition')
                .semanticPatchAuthorized,
            false
        );
    });

    it('selects only a read-only evaluator probe as the next row', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL;
        assert.equal(proposal.recommendedNextRow.id, 'DISPLAYED-EVAL-0B');
        assert.equal(
            proposal.recommendedNextRow
                .implementationAuthorizedByThisProposal,
            false
        );
        assert.equal(
            proposal.decisionEffects.authorizesDisplayedEval0B,
            true
        );
        assert.equal(
            proposal.decisionEffects.authorizesSemanticDisplayedLifting1A,
            false
        );
        assert.equal(
            proposal.ownerAuditConclusion.newOwnerRequiresSeparateGate,
            true
        );
    });

    it('adds no mathematics, checker, browser, acquisition, or Git scope', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL;
        assert.equal(
            Object.values(proposal.semanticDelta).some(Boolean),
            false
        );
        assert.equal(
            proposal.decisionEffects.authorizesNewKernelOwnerOrRule,
            false
        );
        assert.equal(
            proposal.decisionEffects.authorizesParserOrBulkTransfer,
            false
        );
        assert.equal(
            proposal.decisionEffects.broadensGitAuthority,
            false
        );
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_displayed_lifting|DISPLAYED-LIFTING/u
        );
    });

    it('is deeply frozen, asks one exact question, and fails closed', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_LIFTING_PROPOSAL;
        assertDeepFrozen(proposal);
        assert.match(
            proposal.decisionQuestion,
            /^Approve H-DTTLF-USABILITY-DISPLAYED-LIFTING-01\//u
        );
        assertProposalError(
            value => {
                value.architectureCorrection.rawExprLayerAdded = true;
            },
            'DISPLAYED_LIFTING_ARCHITECTURE_DRIFT'
        );
        assertProposalError(
            value => {
                value.displayedMatrix[4].status = 'implemented';
            },
            'DISPLAYED_LIFTING_MATRIX_DRIFT'
        );
        assertProposalError(
            value => {
                value.semanticDelta.newLambdapiOwners = 1;
            },
            'DISPLAYED_LIFTING_AUTHORITY_DRIFT'
        );
        assertProposalError(
            value => {
                value.decisionId = 'D-DTTLF-USABILITY-999';
            },
            'DISPLAYED_LIFTING_PROPOSAL_DRIFT'
        );
    });
});
