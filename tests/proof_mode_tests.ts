/**
 * @file tests/proof_mode_tests.ts
 * @description Tests for the interactive proof mode functionality.
 */

import {
    Term, Context, Icit, Type, Var, Lam, App, Pi, Hole,
} from '../src/types';
import {
    emptyCtx, getTermRef, globalDefs, printTerm, setDebugVerbose, addConstraint, resetHoleId, freshHoleName
} from '../src/state';
import {
    defineGlobal
} from '../src/globals';
import {
    resetMyLambdaPi
} from './../src/stdlib';
import { elaborate } from '../src/elaboration';
import { assert } from './utils';
import { describe, it, beforeEach } from 'node:test';
import { areEqual } from '../src/equality';
import { normalize, whnf } from '../src/reduction';
import { findHoles, intro, exact, apply, reportProofState } from '../src/proof';

describe("Interactive Proof Mode Tests", () => {

    beforeEach(() => {
        resetMyLambdaPi();
        // setDebugVerbose(true);
    });

    it("should correctly manage a simple proof with intro and exact", () => {
        // Goal: Prove `Nat -> Nat` by constructing the identity function.
        
        // 1. Define globals for Nat and the identity function type
        defineGlobal("Nat", Type(), undefined, true, true);
        const Nat = Var("Nat");
        const IdNatType = Pi("n", Icit.Expl, Nat, _ => Nat);

        // 2. Start the proof by defining a global with a hole as its value.
        const goalHoleId = freshHoleName();
        defineGlobal("proof_id_nat", IdNatType, Hole(goalHoleId));
        
        // The proof term starts as a variable pointing to our definition.
        let proofTerm = Var("proof_id_nat");

        // 3. Check the initial state.
        let holes = findHoles(proofTerm);
        assert(holes.length === 1 && holes[0].id === goalHoleId, `Expected one initial hole. Found ${holes.length}`);
        
        const initialStateReport = reportProofState(proofTerm);
        assert(initialStateReport.includes(`⊢ (Π (n : Nat). Nat)`), `Initial state report is incorrect.`);

        // 4. Use the `intro` tactic.
        proofTerm = intro(proofTerm, goalHoleId, "n");
        
        // 5. Check the state after `intro`. The original hole should be solved.
        const termAfterIntro: Term = whnf(proofTerm, emptyCtx);
        assert(termAfterIntro.tag === 'Lam', `Proof term should be a lambda after intro. Got ${termAfterIntro.tag}`);

        // There should be a new hole in the body.
        holes = findHoles(proofTerm);
        assert(holes.length === 1, `Expected one hole after intro. Found ${holes.length}`);
        const subgoalId = holes[0].id;

        const afterIntroReport = reportProofState(proofTerm);
        assert(afterIntroReport.includes('n : Nat'), `Context in report after intro is incorrect.`);
        assert(afterIntroReport.includes('⊢ Nat'), `Goal type in report after intro is incorrect.`);

        // 6. Use the `exact` tactic to solve the subgoal.
        proofTerm = exact(proofTerm, subgoalId, Var("n"));

        // 7. Check the final state. There should be no more holes.
        holes = findHoles(proofTerm);
        assert(holes.length === 0, `Expected zero holes after exact. Found ${holes.length}`);
        assert(reportProofState(proofTerm).includes("Proof complete"), `Final report is incorrect.`);

        // 8. Verify the final term is correct by elaborating it.
        const finalResult1 = elaborate(proofTerm);
        const expectedTerm1: Term = Lam("n", Icit.Expl, Nat, n => n);

        assert(areEqual(finalResult1.term, expectedTerm1, emptyCtx), `Final term is not the expected identity function.`);
        assert(areEqual(finalResult1.type, IdNatType, emptyCtx), `Final type is not correct.`);
    });

    it("should use 'apply' to use a function in a proof", () => {
        // Goal: Prove `Nat` by applying the successor function `s` to zero `z`.

        // 1. Define Nat, z, and s
        defineGlobal("Nat", Type(), undefined, true, true);
        const Nat = Var("Nat");
        defineGlobal("z", Nat, undefined, true, true);
        defineGlobal("s", Pi("n", Icit.Expl, Nat, _ => Nat), undefined, true, true);

        // 2. Start the proof for the goal `Nat`.
        const goalHoleId = freshHoleName();
        defineGlobal("proof_of_one", Nat, Hole(goalHoleId));
        let proofTerm = Var("proof_of_one");

        // 3. Check initial state
        let holes = findHoles(proofTerm);
        assert(holes.length === 1 && holes[0].id === goalHoleId, "Should have one hole at start.");

        // 4. Apply the successor function `s`. This should create a new goal for `s`'s argument.
        proofTerm = apply(proofTerm, goalHoleId, Var("s"));

        // 5. Check state after `apply`
        holes = findHoles(proofTerm);
        assert(holes.length === 1, "Should have one new subgoal after apply.");
        const subgoalId = holes[0].id;
        
        const afterApplyReport = reportProofState(proofTerm);
        assert(afterApplyReport.includes("⊢ Nat"), "The new subgoal should be of type Nat.");

        // 6. Solve the new goal with `z`.
        proofTerm = exact(proofTerm, subgoalId, Var("z"));

        // 7. Final check
        holes = findHoles(proofTerm);
        assert(holes.length === 0, "Proof should be complete.");

        const finalResult2 = elaborate(proofTerm);
        const expectedTerm2: Term = App(Var("s"), Var("z"), Icit.Expl);
        assert(areEqual(finalResult2.term, expectedTerm2, emptyCtx), "Final term is not s(z).");
    });
}); 