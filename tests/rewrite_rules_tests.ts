import {
    Term, Context, Icit, Type, Var, Lam, App, Pi, Hole
} from '../src/types';
import {
    emptyCtx, getTermRef, globalDefs, printTerm, userRewriteRules
} from '../src/state';
import {
    defineGlobal, addRewriteRule
} from '../src/globals';
import {
    resetMyLambdaPi
} from '../src/stdlib';
import {
    areEqual
} from '../src/equality';
import {
    normalize, whnf
} from '../src/reduction';
import { assert } from './utils';
import { describe, it, beforeEach } from 'node:test';

describe("Rewrite Rule Tests", () => {
    let ctx: Context;

    beforeEach(() => {
        resetMyLambdaPi();
        ctx = emptyCtx;
        
        // Setup Nat-like types for testing rules
        defineGlobal("Nat", Type(), undefined, true, true);
        const Nat = Var("Nat");
        defineGlobal("z", Nat, undefined, true, true);
        defineGlobal("s", Pi("n", Icit.Expl, Nat, _ => Nat), undefined, true, true);
        defineGlobal("add", Pi("n", Icit.Expl, Nat, _ => Pi("m", Icit.Expl, Nat, _ => Nat)));
    });

    it("Test 1: Simple rewrite rule add(z, n) -> n", () => {
        const Nat = Var("Nat");
        const z = Var("z");
        const add = Var("add");

        addRewriteRule(
            "add_zero_r",
            ["$n"],
            App(App(add, z, Icit.Expl), Var("$n"), Icit.Expl), // add z $n
            Var("$n"), // -> $n
            ctx
        );
        
        const one = App(Var("s"), z, Icit.Expl);
        // Term to test: add z (s z)
        const termToReduce = App(App(add, z, Icit.Expl), one, Icit.Expl);
        
        const reducedTerm = normalize(termToReduce, ctx);
        
        assert(areEqual(reducedTerm, one, ctx), `Test 1: add(z, s(z)) should reduce to s(z). Got ${printTerm(reducedTerm)}`);
    });

    it("Test 2: Recursive rewrite rule add(s m, n) -> s(add m n)", () => {
        const Nat = Var("Nat");
        const z = Var("z");
        const s = Var("s");
        const add = Var("add");

        // First rule: add z $n = $n
        addRewriteRule( "add_zero", ["$n"], App(App(add, z, Icit.Expl), Var("$n"), Icit.Expl), Var("$n"), ctx );
        
        // Second rule: add (s $m) $n = s (add $m $n)
        addRewriteRule(
            "add_succ",
            ["$m", "$n"],
            App(App(add, App(s, Var("$m"), Icit.Expl), Icit.Expl), Var("$n"), Icit.Expl),
            App(s, App(App(add, Var("$m"), Icit.Expl), Var("$n"), Icit.Expl), Icit.Expl),
            ctx
        );

        const one = App(s, z, Icit.Expl);
        const two = App(s, one, Icit.Expl);
        
        // Test: add (s z) (s z)  ==> s (add z (s z)) ==> s (s z)
        const termToReduce = App(App(add, one, Icit.Expl), one, Icit.Expl);
        const reducedTerm = normalize(termToReduce, ctx);
        
        assert(areEqual(reducedTerm, two, ctx), `Test 2: add(1, 1) should reduce to 2. Got ${printTerm(reducedTerm)}`);
    });

    it("Test 3: addRewriteRule should fail for ill-typed RHS", () => {
        const Nat = Var("Nat");
        const add = Var("add");

        defineGlobal("Bool", Type(), undefined, true, true);
        const boolTrue = Var("Bool"); // Using a type as a term to cause error

        const originalRuleCount = userRewriteRules.length;
        
        try {
            addRewriteRule(
                "ill_typed_rule",
                ["$n"],
                App(App(add, Var("z"), Icit.Expl), Var("$n"), Icit.Expl), // LHS type is Nat
                boolTrue, // RHS has type Type, not Nat
                ctx
            );
        } catch (e) {
            // Error is expected, but addRewriteRule catches it and logs.
            // We just check that the rule was not added.
        }

        assert(userRewriteRules.length === originalRuleCount, `Test 3: Ill-typed rule should not be added. Rule count: ${userRewriteRules.length}`);
    });
    
    it("Test 4: A non-terminating rule should not cause infinite loop in whnf", () => {
        defineGlobal("loop", Var("Nat"), undefined, false); // A non-constant global
        const loop = Var("loop");

        addRewriteRule(
            "loop_rule",
            [],
            loop,
            loop,
            ctx
        );
        
        // whnf should terminate due to its internal checks for non-productive steps
        const result = whnf(loop, ctx);
        
        // We just assert that whnf completed without throwing a stack overflow or timeout.
        // The result should be the term itself.
        assert(areEqual(result, loop, ctx), "Test 4: whnf should terminate on a non-productive rule.");
    });
}); 