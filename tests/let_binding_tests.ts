/**
 * @file tests/let_binding_tests.ts
 * @description Tests for the let-binding (local definition) mechanism.
 */
import {
    Term, Context, Icit, Type, Var, Lam, App, Pi, Let
} from '../src/types';
import {
    emptyCtx, extendCtx,
    printTerm
} from '../src/state';
import {
    defineGlobal, addRewriteRule
} from '../src/globals';
import {
    resetMyLambdaPi
} from '../src/stdlib';
import {
    elaborate
} from '../src/elaboration';
import { assert } from './utils';
import { describe, it, beforeEach } from 'node:test';
import { areEqual } from '../src/equality';
import { normalize } from '../src/reduction';

describe("Let-Binding (Local Definition) Tests", () => {
    beforeEach(() => {
        resetMyLambdaPi();

        // Define Nat and some basic arithmetic for tests
        defineGlobal("Nat", Type(), undefined, true, true);
        const Nat = Var("Nat");
        defineGlobal("z", Nat, undefined, true, true);
        defineGlobal("s", Pi("n", Icit.Expl, Nat, _ => Nat), undefined, true, true);
        const z = Var("z");
        const s = Var("s");
        
        const one = App(s, z);
        const two = App(s, one);
        defineGlobal("one", Nat, one);
        defineGlobal("two", Nat, two);

        // Define `add` using rewrite rules for evaluation
        const addType = Pi("n", Icit.Expl, Nat, _ => Pi("m", Icit.Expl, Nat, _ => Nat));
        defineGlobal("add", addType);
        addRewriteRule("add_z", ["$m"], App(App(Var("add"), z), Var("$m")), Var("$m"), emptyCtx);
        addRewriteRule("add_s", ["$n", "$m"], App(App(Var("add"), App(s, Var("$n"))), Var("$m")), App(s, App(App(Var("add"), Var("$n")), Var("$m"))), emptyCtx);

        
        // Test: add (s z) (s z)  ==> s (add z (s z)) ==> s (s z)
        console.log("normalize(top level, emptyCtx)", printTerm(normalize(App(App(Var("add"), two, Icit.Expl), two, Icit.Expl), emptyCtx)));

        const termToReduce = App(App(Var("add"), two, Icit.Expl), two, Icit.Expl);
        const reducedTerm = normalize(termToReduce, emptyCtx);
        assert(areEqual(reducedTerm, App(s,App(s,two)), emptyCtx), `Test 0: add(2, 2) should reduce to 4. Got ${printTerm(reducedTerm)}`);
    });

    it("should unfold a simple let-binding", () => {
        // let x : Nat = one in x
        const Nat = Var("Nat");
        const one = Var("one");
        
        const term = Let("x", Nat, one, x_bv => x_bv);
        const result = elaborate(term);

        assert(areEqual(result.term, one, emptyCtx), "let x=1 in x should evaluate to 1");
        assert(areEqual(result.type, Nat, emptyCtx), "The type of (let x=1 in x) should be Nat");
    });

    it("should unfold a let-binding within an expression", () => {
        // let x : Nat = one in add x x
        const Nat = Var("Nat");
        const one = Var("one");
        const two = Var("two");
        const add = Var("add");

        const term = Let("x", Nat, one, x_bv => App(App(add, x_bv), x_bv));
        const result = elaborate(term);
        
        // Expected result is `add one one` which should reduce to `two`
        assert(areEqual(result.term, two, emptyCtx), "let x=1 in add x x should evaluate to 2");
    });

    it("should handle shadowing of a global variable", () => {
        // Define global `x_global` with value `two`
        defineGlobal("x_global", Var("Nat"), Var("two"));

        // let x_global : Nat = one in x_global
        const Nat = Var("Nat");
        const one = Var("one");

        const term = Let("x_global", Nat, one, x_bv => x_bv);
        const result = elaborate(term);

        // The result should be `one`, from the local let, not `two` from the global
        assert(areEqual(result.term, one, emptyCtx), "Local let-binding should shadow global variable");
    });

    it("should handle shadowing of a lambda parameter", () => {
        // λ(x:Nat). let x : Nat = one in x
        const Nat = Var("Nat");
        const one = Var("one");
        
        const term = Lam("x", Icit.Expl, Nat, 
            _ => Let("x", Nat, one, x_inner_bv => x_inner_bv)
        );
        const elabLam = elaborate(term);

        // Apply the lambda to something, e.g., `two`, and see if we get `one`.
        // (λ(x:Nat). let x : Nat = one in x) two ==> one
        const finalTerm = App(elabLam.term, Var("two"));
        const finalResult = elaborate(finalTerm);

        assert(areEqual(finalResult.term, one, emptyCtx), "Inner let-binding should shadow lambda parameter");
    });

    it("let-binding definition can refer to outer binders", () => {
        // λ(y:Nat). let x:Nat = add y y in x
        const Nat = Var("Nat");
        const add = Var("add");
        
        const term = Lam("y", Icit.Expl, Nat, 
            y_bv => Let("x", Nat, App(App(add, y_bv), y_bv), x_bv => x_bv)
        );
        const elabLam = elaborate(term);

        // Apply this lambda to `one`. The let-def becomes `add one one` = `two`. The body `x` becomes `two`.
        const finalTerm = App(elabLam.term, Var("one"));
        const finalResult = elaborate(finalTerm);

        assert(areEqual(finalResult.term, Var("two"), emptyCtx), "Final result of (λy. let x=add y y in x) 1 should be 2");
    });

    // it("should work with dependent types", () => {
    //     // let n : Nat = two in v : Vec A n
    //     const Nat = Var("Nat");
    //     const two = Var("two");
    //     defineGlobal("A_type", Type(), undefined, true, true);
    //     const A = Var("A_type");
    //     const VecType = Pi("n", Icit.Expl, Nat, _ => Type());
    //     defineGlobal("Vec", Pi("A", Icit.Impl, Type(), _ => VecType));
    //     const Vec = Var("Vec");

    //     const VecA = App(Vec, A, Icit.Impl);
    //     const VecA2 = App(VecA, two);

    //     // We check the type of a placeholder term `v_dep` which is typed by `Vec A n`
    //     // where `n` is the let-bound variable.
    //     const letTerm = Let("n", Nat, two, n_bv => {
    //         // Define a term inside the let body whose type depends on `n_bv`
    //         const v_dep_type = App(VecA, n_bv);
    //         defineGlobal("v_dep", v_dep_type);
    //         return Var("v_dep");
    //     });

    //     const result = elaborate(letTerm);
        
    //     // The type of the `let` expression is the type of its body.
    //     // The body is `v_dep`. Inside the `let`, `v_dep` has type `Vec A n`.
    //     // When the `let` is evaluated, `n` becomes `two`.
    //     // So the type of `v_dep` becomes `Vec A two`.
    //     assert(areEqual(result.type, VecA2, emptyCtx), "Let-binding should be unfolded in dependent types");
    // });

    it("should handle nested let-bindings", () => {
        // let x=1 in let y = add x x in add y x
        const Nat = Var("Nat");
        const one = Var("one");
        const two = Var("two");
        const three = App(Var("s"), two);
        const add = Var("add");
        const s = Var("s");

        const term = Let("x", Nat, one, x_bv => 
                        Let("y", Nat, App(App(add, x_bv), x_bv), y_bv =>
                            App(App(add, y_bv), x_bv)
                        )
                    );
        
        const result = elaborate(term, undefined, emptyCtx, { normalizeResultTerm: true });
        // x=1. y = add 1 1 = 2. body = add 2 1 = 3.
        addRewriteRule("add_s", ["$n", "$m"], App(App(Var("add"), App(s, Var("$n"))), Var("$m")), App(s, App(App(Var("add"), Var("$n")), Var("$m"))), emptyCtx);

        console.log("normalize(four, emptyCtx)", printTerm(normalize(App(App(Var("add"), two, Icit.Expl), two, Icit.Expl), emptyCtx)));

        console.log("normalize(result.term, emptyCtx)", printTerm(normalize(result.term, emptyCtx)));
        assert(areEqual(result.term, three, emptyCtx), "Nested let-bindings should evaluate correctly. Expected 3, got " + printTerm(result.term));
    });

    it("should correctly elaborate unannotated let", () => {
        // let x = one in add x x
        const one = Var("one");
        const two = Var("two");
        const add = Var("add");

        const term = Let("x", one, x_bv => App(App(add, x_bv), x_bv));
        const result = elaborate(term);

        assert(areEqual(result.term, two, emptyCtx), "Unannotated let should evaluate correctly");
        assert(areEqual(result.type, Var("Nat"), emptyCtx), "Type of unannotated let should be inferred correctly");
    });
});