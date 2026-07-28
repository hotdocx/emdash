/**
 * Executable DISPLAYED-CHAIN-0A proposal tests.
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
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_REVISION,
    CoreCategoricalDisplayedChainProposalError,
    CoreCategoricalProgram,
    validateCoreCategoricalDisplayedChainProposal
} from '../src/v3_2';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL
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
    expected: CoreCategoricalDisplayedChainProposalError['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCoreCategoricalDisplayedChainProposal(proposal),
        error =>
            error instanceof CoreCategoricalDisplayedChainProposalError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 DISPLAYED-CHAIN-0A proposal', () => {
    it('starts from the exact completed displayed-evaluation boundary', () => {
        const prerequisite =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL.prerequisite;
        assert.equal(
            prerequisite.displayedEvaluationTransferRevision,
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_REVISION
        );
        assert.equal(
            prerequisite.displayedEvaluationImplementationCheckpoint,
            '1a7ce3f023391aa22c34dc5626057710429bc7c3'
        );
        assert.equal(
            prerequisite.displayedEvaluationLedgerCheckpoint,
            '0ae40ba0f0a904d0005eebe0385e9d1e9a56aac7'
        );
        assert.deepEqual(prerequisite.measuredRootGate, {
            tests: 904,
            passed: 857,
            skipped: 47,
            failed: 0
        });
        assert.equal(
            prerequisite.implementationAuthorizedBeforeDecision,
            false
        );
    });

    it('selects complementary presentations rather than an equivalence', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL;
        assert.equal(proposal.alternatives.length, 4);
        assert.deepEqual(
            proposal.alternatives.map(alternative => [
                alternative.id,
                alternative.disposition
            ]),
            [
                [
                    'sequential-totalization-only',
                    'retain-as-context-layout-not-complete-lowering'
                ],
                [
                    'repeated-pullback-sigma-only',
                    'retain-as-substitution-recursion-not-complete-lowering'
                ],
                [
                    'proof-time-direct-reinterpretation',
                    'reject-subject-reduction-failure'
                ],
                [
                    'hybrid-sequential-recursive-direct',
                    'recommend'
                ]
            ]
        );
        assert.equal(
            proposal.clarifiedArchitecture.relationship,
            'complementary-presentations-not-a-total-category-equivalence'
        );
        assert.equal(
            proposal.selectedClosure.newOwner
                .genericTotalEquivalenceClaimed,
            false
        );
    });

    it('freezes exactly one owner and six measured runtime rules', () => {
        const closure =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL.selectedClosure;
        assert.equal(closure.newOwner.name, 'sigma_functord_sec');
        assert.equal(
            closure.newOwner.necessityEvidence,
            'generic-unwrapped-rule-fails-subject-reduction'
        );
        assert.equal(closure.newMathematicalOwnerCount, 1);
        assert.equal(closure.newMathematicalRuntimeRuleCount, 6);
        assert.equal(closure.newMathematicalProofRuleCount, 0);
        assert.equal(closure.genericFappTappRuleCount, 0);
        assert.deepEqual(
            closure.runtimeRules.map(rule => rule.id),
            [
                'sigma-first-projection-structured-arrow',
                'sigma-projection-pullback-structured-arrow',
                'sigma-functord-section-object-component',
                'sigma-functord-section-arrow-component',
                'section-pullback-direct-object-component',
                'section-pullback-direct-arrow-component'
            ]
        );
    });

    it('separates existing transfer prerequisites from new semantics', () => {
        const transfer =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL.transferClosure;
        assert.deepEqual(
            transfer.existingDeclarationPrerequisites,
            [
                'sigma_map_func',
                'fdapp1_int_cell',
                'fdapp1_int_hom_fapp0'
            ]
        );
        assert.deepEqual(
            transfer.existingRuntimeRulePrerequisites,
            [
                'sigma_map_func-object-action',
                'sigma_map_func-structured-arrow-action'
            ]
        );
        assert.equal(
            transfer.allDeclarationsUseGenericTransferCompiler,
            true
        );
        assert.equal(
            transfer.allRuntimeRulesUseGenericRuntimeCompiler,
            true
        );
        assert.equal(transfer.intrinsicCoreCaseRequired, false);
        assert.equal(transfer.genericLambdapiParserRequired, false);
    });

    it('records the exact owner-position warning comparison', () => {
        const warning =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL.warningEvidence;
        assert.deepEqual(warning.baseline, {
            total: 1171,
            unjoinableCriticalPairs: 1012,
            replaceablePatternVariables: 159
        });
        assert.deepEqual(warning.candidate, {
            total: 1179,
            unjoinableCriticalPairs: 1020,
            replaceablePatternVariables: 159
        });
        assert.deepEqual(warning.delta, {
            total: 8,
            unjoinableCriticalPairs: 8,
            replaceablePatternVariables: 0
        });
        assert.equal(warning.warningIsSelectionVeto, false);
        assert.equal(
            warning.strictLhsAudit.unreviewedCompoundSlots,
            0
        );
    });

    it('executes the current sequential two-edge context representation', () => {
        const emdash = new CoreCategoricalProgram({
            sourceFile:
                'tests/fixtures/categorical-displayed-chain-proposal.ts',
            profile: 'fibred-comprehension-1a'
        });
        const K = emdash.category('chain_K', { line: 1 });
        const A = emdash.displayedFamily('chain_A', K, { line: 2 });
        const k = emdash.object('chain_k', K, { line: 3 });
        const fibreA = emdash.fibre(A, k, { line: 4 });
        const a = emdash.object('chain_a', fibreA, { line: 5 });
        const ka = emdash.dependentPair(A, k, a, { line: 6 });
        const totalA = emdash.totalCategory(A, { line: 7 });
        const B = emdash.displayedFamily('chain_B', totalA, {
            line: 8
        });
        const fibreB = emdash.fibre(B, ka, { line: 9 });
        const b = emdash.object('chain_b', fibreB, { line: 10 });
        const kab = emdash.dependentPair(B, ka, b, { line: 11 });
        const compiled = emdash.compile(kab);

        assert.equal(compiled.surfaceType.tag, 'object');
        assert.equal(
            (
                compiled.explicitCore.match(
                    /emdash\.categorical\.dependent-pair/gu
                ) ?? []
            ).length,
            2
        );
    });

    it('executes recursive pullback totalization at the next edge', () => {
        const emdash = new CoreCategoricalProgram({
            sourceFile:
                'tests/fixtures/categorical-displayed-chain-substitution.ts',
            profile: 'fibred-comprehension-1a'
        });
        const X = emdash.category('chain_X', { line: 1 });
        const K = emdash.category('chain_K', { line: 2 });
        const F = emdash.functor('chain_F', X, K, { line: 3 });
        const A = emdash.displayedFamily('chain_A', K, { line: 4 });
        const totalF = emdash.pullbackTotal(F, A, { line: 5 });
        const totalA = emdash.totalCategory(A, { line: 6 });
        const B = emdash.displayedFamily('chain_B', totalA, {
            line: 7
        });
        const pulledB = emdash.pullbackFamily(B, totalF, {
            line: 8
        });
        const totalB = emdash.pullbackTotal(totalF, B, { line: 9 });
        const compiled = emdash.compile(totalB);

        assert.equal(compiled.surfaceType.tag, 'functor');
        assert.match(
            compiled.explicitCore,
            /emdash\.categorical\.sigma-pullback-total-functor/u
        );
        assert.match(
            emdash.compile(
                emdash.object(
                    'chain_b',
                    emdash.fibre(
                        pulledB,
                        emdash.object(
                            'chain_xa',
                            emdash.totalCategory(
                                emdash.pullbackFamily(A, F),
                                { line: 10 }
                            ),
                            { line: 11 }
                        ),
                        { line: 12 }
                    ),
                    { line: 13 }
                )
            ).explicitExpectedType,
            /displayed-pullback/u
        );
    });

    it('freezes object, arrow, recursion, reindexing, and negatives', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL;
        assert.equal(
            Object.values(proposal.recursiveEvidence)
                .filter(value => typeof value === 'boolean')
                .every(Boolean),
            true
        );
        assert.equal(
            proposal.positiveCorpus.includes(
                'outer-variable-arrow-under-one-dependent-binder'
            ),
            true
        );
        assert.equal(
            proposal.negativeCorpus.includes(
                'generic-section-does-not-collapse-without-explicit-wrapper'
            ),
            true
        );
        assert.equal(
            proposal.feasibilityAssessment
                .architectureForOneGenuineEdgeSettledByProposal,
            true
        );
        assert.equal(
            proposal.feasibilityAssessment
                .proofOfArbitraryTelescopeDepthClaimed,
            false
        );
    });

    it('keeps the existing recursive TypeScript pipeline and no parser', () => {
        const consumer =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL.typescriptConsumer;
        assert.equal(
            consumer.proposedMethod,
            'displayedDependentContextLambda'
        );
        assert.equal(consumer.callbackEvaluationCount, 1);
        assert.equal(consumer.recursiveNodeCompilation, true);
        assert.equal(
            consumer.tokenOccurrenceMayAppearUnderSupportedSubexpressions,
            true
        );
        assert.equal(consumer.newAstLayerRequired, false);
        assert.equal(consumer.newCheckerRequired, false);
        assert.equal(consumer.stringParserRequired, false);
        assert.deepEqual(consumer.pipeline, [
            'typed-typescript-construction-ir',
            'recursive-contextual-occurrence-compiler',
            'sequential-sigma-and-direct-displayed-lowering',
            'backend-neutral-explicit-core',
            'generic-checker-and-evaluator'
        ]);
    });

    it('is deeply frozen, non-self-authorizing, and fails closed', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL;
        assertDeepFrozen(proposal);
        validateCoreCategoricalDisplayedChainProposal();
        assert.match(
            proposal.decisionQuestion,
            /^Approve H-DTTLF-USABILITY-DISPLAYED-CHAIN-01\//u
        );
        assert.equal(
            Object.values(proposal.decisionEffects).some(Boolean),
            false
        );

        assertProposalError(
            value => {
                value.prerequisite.measuredRootGate.tests = 905;
            },
            'DISPLAYED_CHAIN_PREREQUISITE_DRIFT'
        );
        assertProposalError(
            value => {
                value.clarifiedArchitecture.rawExprLayerAdded = true;
            },
            'DISPLAYED_CHAIN_ARCHITECTURE_DRIFT'
        );
        assertProposalError(
            value => {
                value.selectedClosure.newMathematicalRuntimeRuleCount = 5;
            },
            'DISPLAYED_CHAIN_AUTHORITY_DRIFT'
        );
        assertProposalError(
            value => {
                value.warningEvidence.candidate
                    .unjoinableCriticalPairs = 1019;
            },
            'DISPLAYED_CHAIN_EVIDENCE_DRIFT'
        );
        assertProposalError(
            value => {
                value.decisionEffects.proposalSelfAuthorizesImplementation =
                    true;
            },
            'DISPLAYED_CHAIN_BOUNDARY_DRIFT'
        );

        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_displayed_chain|DISPLAYED-CHAIN/u
        );
    });
});
