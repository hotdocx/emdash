/**
 * @file tests/dependent_types_tests.ts
 * @description Tests for dependent types, using length-indexed vectors (Vec) as the primary example.
 */
import {
    Term, Context, Icit, Type, Var, Lam, App, Pi, Hole,
    CatTerm, FunctorTypeTerm, ObjTerm, HomTerm, SetTerm,
} from '../src/types';
import {
    emptyCtx, getTermRef, globalDefs, printTerm, setDebugVerbose, addConstraint
} from '../src/state';
import {
    defineGlobal
} from '../src/globals';
import {
    resetMyLambdaPi,
    resetMyLambdaPi_Emdash
} from './../src/stdlib';
import {
    elaborate,
    CoherenceError
} from '../src/elaboration';
import assert from 'node:assert';
import { describe, it, beforeEach } from 'node:test';
import { areEqual } from '../src/equality';
import { normalize } from '../src/reduction';

describe("Dependent Types Tests: Length-Indexed Vectors (Vec)", () => {
    let Nat: Term, z: Term, s: Term;
    let Vec: Term, vnil: Term, vcons: Term;

    beforeEach(() => {
        resetMyLambdaPi();
        // setDebugVerbose(true); // Uncomment for debugging

        // 1. Define Natural Numbers (Nat)
        defineGlobal("Nat", Type(), undefined, true, true);
        const Nat = Var("Nat");
        defineGlobal("z", Nat, undefined, true, true);
        defineGlobal("s", Pi("n", Icit.Expl, Nat, _ => Nat), undefined, true, true);
        const z = Var("z");
        const s = Var("s");

        const one = App(s, z, Icit.Expl);
        const two = App(s, one, Icit.Expl);
        defineGlobal("one", Nat, one);
        defineGlobal("two", Nat, two);

        // 2. Define Length-Indexed Vectors (Vec)
        // Vec : {A:Type} -> Nat -> Type
        const VecType = Pi("A", Icit.Impl, Type(), A => Pi("n", Icit.Expl, Nat, _ => Type()));
        defineGlobal("Vec", VecType);
        const Vec = Var("Vec");

        // 3. Define Vector Constructors (vnil, vcons)
        
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
    });

    it("should elaborate vnil for a specific type", () => {
        defineGlobal("Bool", Type(), undefined, true, true);
        const Bool = Var("Bool");
        const vnil = Var("vnil");
        const Vec = Var("Vec");
        const z = Var("z");
        const term = App(vnil, Bool, Icit.Impl); // vnil {Bool}
        const result = elaborate(term);
        
        const expectedType = App(App(Vec, Bool, Icit.Impl), z, Icit.Expl); // Vec Bool z
        assert.ok(areEqual(result.type, expectedType, emptyCtx), `vnil {Bool} should have type Vec Bool z. Got ${printTerm(result.type)}`);
    });

    it("should elaborate a Vec of length 1", () => {
        defineGlobal("Bool", Type(), undefined, true, true);
        const Bool = Var("Bool");
        defineGlobal("true", Bool, undefined, true, true);
        const vcons = Var("vcons");
        const z = Var("z");
        const s = Var("s");
        const vnil = Var("vnil");
        const Vec = Var("Vec");
        
        // vcons {Bool} {z} true (vnil {Bool})
        const term = 
            App(
                App(
                    App(
                        App(vcons, Bool, Icit.Impl),
                        z, Icit.Impl),
                    Var("true"), Icit.Expl),
                App(vnil, Bool, Icit.Impl), Icit.Expl);
        
        const result = elaborate(term);
        const expectedType = App(App(Vec, Bool, Icit.Impl), App(s, z, Icit.Expl), Icit.Expl); // Vec Bool (s z)
        assert.ok(areEqual(result.type, expectedType, emptyCtx), `Vec of length 1 has wrong type. Got ${printTerm(result.type)}`);
    });

    describe("Vector Append Function", () => {
        let append: Term;

        beforeEach(() => {
            const Nat = Var("Nat");
            const Vec = Var("Vec");
            // append : {A:Type} -> {n m:Nat} -> Vec A n -> Vec A m -> Vec A (add n m)
            // For simplicity, we define 'add' as a placeholder function for this test.
            // A full implementation would define it recursively over Nat.
            defineGlobal("add", Pi("n", Icit.Expl, Nat, _ => Pi("m", Icit.Expl, Nat, _ => Nat)));
            const add = Var("add");

            const appendType = Pi("A", Icit.Impl, Type(), A =>
                Pi("n", Icit.Impl, Nat, n =>
                    Pi("m", Icit.Impl, Nat, m =>
                        Pi("v1", Icit.Expl, App(App(Vec, A, Icit.Impl), n, Icit.Expl), _ =>
                            Pi("v2", Icit.Expl, App(App(Vec, A, Icit.Impl), m, Icit.Expl), _ =>
                                App(App(Vec, A, Icit.Impl), App(App(add, n, Icit.Expl), m, Icit.Expl), Icit.Expl)
                            )
                        )
                    )
                )
            );
            
            // The body of append would be a recursive function. For this test,
            // we will just define it as a global and check if it can be applied correctly.
            defineGlobal("append", appendType);
        });

        it("should correctly type-check an application of append", () => {
            defineGlobal("Bool", Type(), undefined, true, true);
            const Bool = Var("Bool");
            defineGlobal("true", Bool, undefined, true, true);
            defineGlobal("false", Bool, undefined, true, true);
            const s = Var("s");
            const z = Var("z");
            const vcons = Var("vcons");
            const vnil = Var("vnil");
            const append = Var("append");
            const one = Var("one");

            // vec1 = vcons {Bool} {z} true (vnil {Bool})  : Vec Bool (s z)
            const vec1 = App(App(App(App(vcons, Bool, Icit.Impl), z, Icit.Impl), Var("true"), Icit.Expl), App(vnil, Bool, Icit.Impl), Icit.Expl);
            
            // vec2 = vnil {Bool} : Vec Bool z
            const vec2 = App(vnil, Bool, Icit.Impl);

            // append {Bool} {s z} {z} vec1 vec2
            const term = App(
                App(
                    App(
                        App(
                            App(append, Bool, Icit.Impl),
                            App(s, z, Icit.Expl), Icit.Impl),
                        z, Icit.Impl),
                    vec1, Icit.Expl),
                vec2, Icit.Expl
            );

            const result = elaborate(term, undefined, emptyCtx, { normalizeResultTerm: false });
            
            const Vec = Var("Vec");
            const add = Var("add");
            const expectedType = App(
                App(Vec, Bool, Icit.Impl),
                App(App(add, App(s, z, Icit.Expl), Icit.Expl), z, Icit.Expl),
                Icit.Expl
            ); // Vec Bool (add (s z) z)

            assert.ok(areEqual(result.type, expectedType, emptyCtx), `Append type check failed. Got ${printTerm(result.type)}`);
        });
    });
});
