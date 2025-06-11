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
import { elaborate } from '../src/elaboration';

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
    it("Test 2: Global defs and Recursive rewrite rule add(s m, n) -> s(add m n)", () => {
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
        defineGlobal("one", Nat, one);
        defineGlobal("two", Nat, two);

        // Test: add (s z) (s z)  ==> s (add z (s z)) ==> s (s z)
        let termToReduce = App(App(add, Var("one"), Icit.Expl), Var("one"), Icit.Expl);
        let reducedTerm = normalize(termToReduce, ctx);
        
        assert(areEqual(reducedTerm, two, ctx), `Test 2.0: add(1, 1) should reduce to 2. Got ${printTerm(reducedTerm)}`);

        // Test: add (add (s z) (s z)) (s z)   ==> s (s (s z))
        termToReduce = App(App(add, App(App(add, Var("one"), Icit.Expl), Var("one"), Icit.Expl), Icit.Expl), Var("one"), Icit.Expl);
        reducedTerm = normalize(termToReduce, ctx);
        console.log("Test 2.1: printTerm(reducedTerm)", printTerm(reducedTerm));
        console.log("Test 2.1: printTerm(normalize(reducedTerm, ctx))", printTerm(normalize(reducedTerm, ctx)));
        console.log("Test 2.1: printTerm(normalize(normalize(reducedTerm, ctx), ctx))", printTerm(normalize(normalize(reducedTerm, ctx), ctx)));
        assert(areEqual(reducedTerm, App(s, Var("two"), Icit.Expl), ctx), `Test 2.1: add(add(1, 1), 1) should reduce to s(s(s(z))). Got ${printTerm(reducedTerm)}`);
    });
}); 