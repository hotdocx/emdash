/**
 * Executable DISPLAYED-BRACKET-0A successor proposal tests.
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
    CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL,
    CoreCategoricalDisplayedBracketProposalError,
    validateCoreCategoricalDisplayedBracketProposal
} from '../src/v3_2';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL
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
    expected: CoreCategoricalDisplayedBracketProposalError['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCoreCategoricalDisplayedBracketProposal(proposal),
        error =>
            error instanceof
                CoreCategoricalDisplayedBracketProposalError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 DISPLAYED-BRACKET-0A proposal', () => {
    it('starts only after the qualified graduation review', () => {
        const prerequisite =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL.prerequisite;
        assert.equal(
            prerequisite.graduationDecision,
            'D-DTTLF-USABILITY-008'
        );
        assert.equal(prerequisite.qualifiedArchitectureSettled, true);
        assert.equal(prerequisite.successorAutomaticallyAuthorized, false);
    });

    it('selects the generic compiler over three shortcuts', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL;
        assert.deepEqual(
            proposal.alternatives.map(alternative => [
                alternative.id,
                alternative.status
            ]),
            [
                ['extend-rigid-body-recognizer', 'rejected'],
                [
                    'generic-displayed-contextual-compiler',
                    'selected'
                ],
                [
                    'total-context-ordinary-bracket-only',
                    'deferred-not-selected'
                ],
                [
                    'new-kernel-displayed-bracket-owner',
                    'rejected-unnecessary'
                ]
            ]
        );
    });

    it('freezes one first-order independent-sibling row', () => {
        const row =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL
                .firstImplementationRow;
        assert.equal(row.id, 'DISPLAYED-BRACKET-1A');
        assert.equal(
            row.contextScope,
            'finite-nonempty-independent-sibling-block-over-common-base'
        );
        assert.deepEqual(row.bodyGrammar, [
            'displayed-slot-reference',
            'closed-displayed-functor-application',
            'typed-fibre-pair'
        ]);
        assert.equal(row.requiredNewFrontendNode, 'typed-pair');
        assert.equal(row.typedCompositionNodeRequiredInitially, false);
    });

    it('routes variable usage through existing displayed structure', () => {
        const row =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL
                .firstImplementationRow;
        assert.equal(row.lowering.singleSlot, 'id_funcd');
        assert.match(row.lowering.siblingSelection, /Product_projL_funcd/u);
        assert.equal(row.lowering.pair, 'Product_pair_funcd');
        assert.match(row.lowering.contraction, /repeated-compiled-branch/u);
        assert.match(row.lowering.exchange, /reordered-projections/u);
    });

    it('includes finite scaling and the important negative corpus', () => {
        const row =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL
                .firstImplementationRow;
        assert.equal(
            row.positiveCorpus.includes(
                'lambda-(a,b,c)-finite-left-associated-projection-and-pair'
            ),
            true
        );
        assert.equal(
            row.negativeCorpus.includes(
                'genuine-dependency-edge-in-requested-sibling-block'
            ),
            true
        );
        assert.equal(
            row.negativeCorpus.includes(
                'arbitrary-pointwise-coherence'
            ),
            true
        );
    });

    it('keeps genuine chains and nd coherence as separate rows', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL;
        assert.deepEqual(
            proposal.followOnRows.map(row => [
                row.id,
                row.implementationAuthorized
            ]),
            [
                ['DISPLAYED-CHAIN-0A', false],
                ['DISPLAYED-ND-0A', false],
                ['DISPLAYED-BRACKET-GRADUATE-1', false]
            ]
        );
        assert.equal(
            proposal.scalabilityBoundary.notProvenByFirstRow.includes(
                'genuine-dependent-chain-body-compilation'
            ),
            true
        );
    });

    it('adds no mathematical, browser, acquisition, or Git authority', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL;
        assert.equal(
            Object.values(
                proposal.firstImplementationRow.semanticDelta
            ).some(Boolean),
            false
        );
        assert.equal(
            proposal.decisionEffects.addsKernelMathematicsByDecision,
            false
        );
        assert.equal(
            proposal.decisionEffects.authorizesParsingOrBulkTransfer,
            false
        );
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_displayed_bracket|DISPLAYED-BRACKET/u
        );
    });

    it('is deeply frozen, asks one exact question, and fails closed', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL;
        assertDeepFrozen(proposal);
        assert.match(
            proposal.decisionQuestion,
            /^Approve H-DTTLF-USABILITY-DISPLAYED-BRACKET-01\//u
        );
        assertProposalError(
            value => {
                value.alternatives[0].status = 'selected';
            },
            'DISPLAYED_BRACKET_SELECTION_DRIFT'
        );
        assertProposalError(
            value => {
                value.firstImplementationRow.semanticDelta
                    .newLambdapiOwners = 1;
            },
            'DISPLAYED_BRACKET_AUTHORITY_DRIFT'
        );
        assertProposalError(
            value => {
                value.decisionId = 'D-DTTLF-USABILITY-999';
            },
            'DISPLAYED_BRACKET_PROPOSAL_DRIFT'
        );
    });
});
