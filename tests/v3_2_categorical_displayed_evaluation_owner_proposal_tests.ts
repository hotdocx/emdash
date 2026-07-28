/**
 * Focused DISPLAYED-EVAL-OWNER-0C proposal tests.
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
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL,
    CoreCategoricalDisplayedEvaluationOwnerProposalError,
    validateCoreCategoricalDisplayedEvaluationOwnerProposal
} from '../src/v3_2';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL
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
    expected:
        CoreCategoricalDisplayedEvaluationOwnerProposalError['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () =>
            validateCoreCategoricalDisplayedEvaluationOwnerProposal(
                proposal
            ),
        error =>
            error instanceof
                CoreCategoricalDisplayedEvaluationOwnerProposalError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 DISPLAYED-EVAL-OWNER-0C proposal', () => {
    it('snapshots the exact completed read-only audit', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL;
        assert.notEqual(
            proposal.prerequisite,
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
        );
        assert.deepEqual(
            proposal.prerequisite,
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
        );
        assert.equal(
            proposal.reviewGate,
            'H-DTTLF-USABILITY-DISPLAYED-EVAL-OWNER-01'
        );
        assert.equal(proposal.decisionId, 'D-DTTLF-USABILITY-011');
    });

    it('selects the exact variance-correct constant-domain family', () => {
        const domain =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL
                .selectedDomain;
        assert.match(domain.stableSubjectFamily, /Functor_catd/u);
        assert.match(domain.stableSubjectFamily, /Const_catd/u);
        assert.equal(
            domain.varyingArgumentFamily,
            'Const_catd(K,A)'
        );
        assert.match(domain.excludedGeneralization, /Catd\(Op_cat K\)/u);
    });

    it('selects exactly Eval_funcd and Terminal_funcd', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL;
        assert.deepEqual(
            proposal.proposedKernelOwners.map(owner => owner.name),
            ['Eval_funcd', 'Terminal_funcd']
        );
        assert.equal(
            proposal.proposedKernelOwners.every(
                owner => owner.kind ===
                    'injective-stable-displayed-functor'
            ),
            true
        );
        assert.match(
            proposal.proposedKernelOwners[0].signature,
            /Functor_catd/u
        );
        assert.match(
            proposal.proposedKernelOwners[1].signature,
            /Terminal_cat/u
        );
    });

    it('selects only two point-component rules', () => {
        const rules =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL
                .proposedRuntimeRules;
        assert.equal(rules.length, 2);
        assert.deepEqual(rules.map(rule => rule.right), [
            'Eval_func(A,Fibre_cat(B,k))',
            'Terminal_func(Fibre_cat(E,k))'
        ]);
        assert.equal(
            rules.some(rule => rule.genericFunctorialityDuplicated),
            false
        );
    });

    it('derives both varying and fixed application without extra owners', () => {
        const derived =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL
                .derivedConstructions;
        assert.match(
            derived.varyingArgument.result,
            /Product_pair_funcd/u
        );
        assert.equal(derived.varyingArgument.newOwnerRequired, false);
        assert.match(
            derived.fixedArgument.constantMap,
            /Terminal_funcd/u
        );
        assert.match(
            derived.fixedArgument.fixedEvaluator,
            /Eval_funcd/u
        );
        assert.equal(
            derived.fixedArgument.newFixedEvaluatorOwnerRequired,
            false
        );
        assert.equal(
            derived.fixedArgument.objectBeta,
            'Eval_at_funcd(B,a)[k][F] -> F[a]'
        );
    });

    it('keeps all generic coherence at fapp/tapp', () => {
        const coherence =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL
                .coherenceContract;
        assert.equal(coherence.pointEvaluationComputes, true);
        assert.equal(coherence.baseArrowActionRepresented, true);
        assert.equal(coherence.higherActionRemainsIterable, true);
        assert.equal(coherence.specializedIdentityRulesAdded, false);
        assert.equal(coherence.specializedCompositionRulesAdded, false);
        assert.equal(coherence.specializedNaturalityRulesAdded, false);
        assert.equal(
            coherence.genericIdentityCompositionNaturalityOwner,
            'global-fapp-tapp-calculus'
        );
    });

    it('proposes only the standard mechanical profile repair', () => {
        const repair =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL
                .profileRepair;
        assert.equal(
            repair.classification,
            'mechanical-transfer-runtime-wiring'
        );
        assert.match(repair.change, /final-declaration-compilation/u);
        assert.equal(repair.ownerOrRuleSemanticChange, false);
        assert.equal(repair.requiredBeforeJoinedConsumer, true);
        assert.equal(repair.precedent.length, 3);
    });

    it('extends recursive typed application, not the language/checker stack', () => {
        const slice =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL
                .typedFrontendSlice;
        assert.equal(
            slice.sourceBoundary,
            'existing-typed-typescript-construction-ir'
        );
        assert.equal(slice.existingApplicationNodeReused, true);
        assert.match(slice.bothOpenJudgment.lowering, /Eval_funcd/u);
        assert.match(slice.fixedArgumentJudgment.lowering, /Terminal_funcd/u);
        assert.equal(slice.rawExprAdded, false);
        assert.equal(slice.secondCheckerAdded, false);
        assert.equal(slice.parserAdded, false);
        assert.equal(slice.bracketPunctuationAdded, false);
        assert.equal(slice.wholeBodyRecognizerAdded, false);
    });

    it('retains alternatives and the measured warning interaction', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL;
        assert.equal(
            proposal.alternativesRetained.find(
                alternative =>
                    alternative.id === 'universe-natural-evaluation'
            )?.status,
            'feasible-not-selected-for-this-slice'
        );
        assert.equal(
            proposal.validationPlan.knownWarningDelta
                .unjoinableCriticalPairs,
            2
        );
        assert.equal(
            proposal.validationPlan.knownWarningDelta
                .replaceablePatternVariables,
            0
        );
        assert.match(
            proposal.validationPlan.knownWarningDelta.policy,
            /diagnostic-not-veto/u
        );
    });

    it('is non-self-authorizing and absent from the browser profile', () => {
        const proposal =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL;
        assert.equal(
            Object.values(proposal.decisionEffects).some(Boolean),
            false
        );
        assert.equal(
            proposal.nextDependencyState,
            'awaiting-exact-displayed-eval-owner-review'
        );
        assert.match(
            proposal.decisionQuestion,
            /H-DTTLF-USABILITY-DISPLAYED-EVAL-OWNER-01/u
        );
        assertDeepFrozen(proposal);
        assert.doesNotThrow(
            () =>
                validateCoreCategoricalDisplayedEvaluationOwnerProposal()
        );
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_displayed_evaluation|DISPLAYED-EVAL/u
        );
    });

    it('rejects prerequisite, owner/rule, and authorization drift', () => {
        assertProposalError(
            proposal => {
                proposal.prerequisite.revision = 'drift';
            },
            'DISPLAYED_EVALUATION_OWNER_PREREQUISITE_DRIFT'
        );
        assertProposalError(
            proposal => {
                proposal.proposedKernelOwners.pop();
            },
            'DISPLAYED_EVALUATION_OWNER_SIGNATURE_DRIFT'
        );
        assertProposalError(
            proposal => {
                proposal.decisionEffects.authorizesExactTwoKernelOwners =
                    true;
            },
            'DISPLAYED_EVALUATION_OWNER_SCOPE_DRIFT'
        );
    });
});
