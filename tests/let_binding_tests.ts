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

        // Define Vec for dependent type tests
        const VecType = Pi("A", Icit.Impl, Type(), A => Pi("n", Icit.Expl, Nat, _ => Type()));
        defineGlobal("Vec", VecType);
        const Vec = Var("Vec");

        // vnil : {A:Type} -> Vec A z
        const vnilType = Pi("A", Icit.Impl, Type(), A => App(App(Vec, A, Icit.Impl), z, Icit.Expl));
        defineGlobal("vnil", vnilType);

        // vcons : {A:Type} -> {n:Nat} -> A -> Vec A n -> Vec A (s n)
        const vconsType = Pi("A", Icit.Impl, Type(), A =>
            Pi("n", Icit.Impl, Nat, n =>
                Pi("head", Icit.Expl, A, _ =>
                    Pi("tail", Icit.Expl, App(App(Vec, A, Icit.Impl), n, Icit.Expl), _ =>
                        App(App(Vec, A, Icit.Impl), App(s, n, Icit.Expl), Icit.Expl)
                    )
                )
            )
        );
        defineGlobal("vcons", vconsType);
        
        // Test: add (s z) (s z)  ==> s (add z (s z)) ==> s (s z)
        console.log("TEST>> beforeEach: (normalize(App(App(Var(add), two), two), emptyCtx)):", printTerm(normalize(App(App(Var("add"), two), two), emptyCtx)));
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

    it("should handle nested let-bindings", () => {
        console.log("TEST>> should handle nested let-bindings: (normalize(App(App(Var(add), two), two), emptyCtx)):", 
            printTerm(normalize(App(App(Var("add"), Var("two")), Var("two")), emptyCtx)));
        
        // let x=1 in let y = add x x in add y x
        const Nat = Var("Nat");
        const z = Var("z");
        const s = Var("s");
        
        // const one = App(s, z);
        // const two = App(s, one);
        const one = Var("one");
        const two = Var("two");
        const three = App(Var("s"), two);
        const add = Var("add");

        const term = Let("x", Nat, one, x_bv => 
                        Let("y", Nat, App(App(add, x_bv), x_bv), y_bv =>
                            App(App(add, y_bv), x_bv)
                        )
                    );
        
        const result = elaborate(term, undefined, emptyCtx);
        // x=1. y = add 1 1 = 2. body = add 2 1 = 3.
        console.log("TEST>> should handle nested let-bindings: normalize(result.term, emptyCtx)", printTerm(normalize(result.term, emptyCtx)));
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

    it("should handle let-bindings within type expressions (Pi)", () => {
        // Π (x : let T = Nat in T). let T = Nat in T
        const Nat = Var("Nat");
        
        const term = Pi("x", Icit.Expl,
            Let("T", Type(), Nat, T_bv => T_bv),
            _ => Let("T", Type(), Nat, T_bv => T_bv)
        );

        // This term is a type, so we elaborate it against Type
        const result = elaborate(term, Type());

        // The elaborated term should be equivalent to Π (x:Nat).Nat
        const expectedType = Pi("x", Icit.Expl, Nat, _ => Nat);

        assert(areEqual(result.term, expectedType, emptyCtx), "Let-bindings in Pi types should be unfolded");
        assert(areEqual(result.type, Type(), emptyCtx), "The type of this Pi-with-lets should be Type");
    });

    it("should work with dependent types in let-bindings", () => {
        // let n = two in Vec Nat n
        const Nat = Var("Nat");
        const two = Var("two");
        const Vec = Var("Vec");

        // The term is a type, so we check it against Type()
        const term = Let("n", Nat, two, n_bv => App(App(Vec, Nat, Icit.Impl), n_bv));
        const result = elaborate(term, Type());

        const expectedType = App(App(Vec, Nat, Icit.Impl), two);
        assert(areEqual(result.term, expectedType, emptyCtx), "let n=2 in Vec Nat n should be equal to Vec Nat 2");
        assert(areEqual(result.type, Type(), emptyCtx), "The type of (let n=2 in Vec Nat n) should be Type");
    });

    it("should unfold let-binding for a dependent-typed term", () => {
        // let my_one_vec = vcons {Nat} {z} one (vnil {Nat}) in my_one_vec
        const Nat = Var("Nat");
        const one = Var("one");
        const z = Var("z");
        const s = Var("s");
        const Vec = Var("Vec");
        const vnil = Var("vnil");
        const vcons = Var("vcons");

        const one_vec_def = App(App(App(App(vcons, Nat, Icit.Impl), z, Icit.Impl), one, Icit.Expl), App(vnil, Nat, Icit.Impl), Icit.Expl);
        const one_vec_type = App(App(Vec, Nat, Icit.Impl), App(s, z));

        const term = Let("my_one_vec", one_vec_type, one_vec_def, vec_bv => vec_bv);
        const result = elaborate(term);

        assert(areEqual(result.term, one_vec_def, emptyCtx), "let vec = ... in vec should evaluate to the vector definition");
        assert(areEqual(result.type, one_vec_type, emptyCtx), "The type of the let-bound vector should be correct");
    });

    it("let-binding definition can refer to outer binders in a more complex way", () => {
        // λ(y:Nat). let x:Nat = add y y in add x y
        const Nat = Var("Nat");
        const add = Var("add");
        const one = Var("one");
        const two = Var("two");
        const three = App(Var("s"), two);
        
        const term = Lam("y", Icit.Expl, Nat, 
            y_bv => Let("x", Nat, App(App(add, y_bv), y_bv), 
                x_bv => App(App(add, x_bv), y_bv)
            )
        );
        const elabLam = elaborate(term);

        // Apply this lambda to `one`. 
        // y becomes one.
        // let-def becomes `add one one` => x is `two`. 
        // body becomes `add x y` => `add two one` => `three`.
        const finalTerm = App(elabLam.term, one);
        const finalResult = elaborate(finalTerm);

        assert(areEqual(finalResult.term, three, emptyCtx), "Final result of (λy. let x=add y y in add x y) 1 should be 3");
    });
});