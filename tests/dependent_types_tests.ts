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
        defineGlobal("true", Bool, undefined, true);
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
            defineGlobal("true", Bool, undefined, true);
            defineGlobal("false", Bool, undefined, true);
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

describe("Functorial Elaboration", () => {
    beforeEach(() => {
        resetMyLambdaPi_Emdash();
        // setDebugVerbose(true);
    });

    it("should correctly elaborate a valid constant functor", () => {
        // Define a simple category D2 with two objects and only identity arrows
        // We can't use mkCat_ directly here as it's not fully implemented for elaboration yet.
        // Instead, we define D2 axiomatically.
        defineGlobal("D2", CatTerm());
        const D2 = Var("D2");
        defineGlobal("O1", ObjTerm(D2));
        defineGlobal("O2", ObjTerm(D2));
        const O1 = Var("O1");
        const O2 = Var("O2");
        
        // Define Nat and Bool for the codomain Set
        defineGlobal("Nat", Type());
        defineGlobal("Bool", Type());
        const Nat = Var("Nat");
        const Bool = Var("Bool");

        // Define the object map: λ(x : Obj D2), if x is O1 then Nat else Bool
        // For testing, a simpler constant map is sufficient and easier to write.
        // fmap0 := λ(_ : Obj D2), Nat
        const fmap0 = Lam("x", Icit.Expl, ObjTerm(D2), _ => Nat);

        // Define the arrow map: λ {X Y} (a : Hom X Y), id_Nat
        // id_Nat = λ(n:Nat), n
        const id_Nat = Lam("n", Icit.Expl, Nat, n => n);
        const fmap1 = Lam("X", Icit.Impl, ObjTerm(D2), _ => 
                      Lam("Y", Icit.Impl, ObjTerm(D2), _ => 
                      Lam("a", Icit.Expl, HomTerm(D2, Var("X", true), Var("Y", true)), _ => id_Nat)));

        // Construct the functor using the kernel maker
        const mkFunctor_ = Var("mkFunctor_");
        const Set = Var("Set");

        const constFunctor = App(App(App(App(mkFunctor_, D2, Icit.Impl), Set, Icit.Impl), fmap0, Icit.Expl), fmap1, Icit.Expl);
        
        const result = elaborate(constFunctor);

        const expectedType = FunctorTypeTerm(D2, Set);
        assert.ok(areEqual(result.type, expectedType, emptyCtx), `Functor should have type Functor D2 Set. Got ${printTerm(result.type)}`);
    });

    it("should throw CoherenceError for a functor that fails the law", () => {
        // We'll define a category C3 with three objects and a composition chain
        // C3 = { O1, O2, O3 }, homs = { id's, f: O1->O2, g: O2->O3, h: O1->O3 }
        // Law: h = g . f
        defineGlobal("C3", CatTerm());
        const C3 = Var("C3");
        defineGlobal("Ob1", ObjTerm(C3));
        defineGlobal("Ob2", ObjTerm(C3));
        defineGlobal("Ob3", ObjTerm(C3));
        const Ob1 = Var("Ob1");
        const Ob2 = Var("Ob2");
        const Ob3 = Var("Ob3");

        defineGlobal("f", HomTerm(C3, Ob1, Ob2));
        defineGlobal("g", HomTerm(C3, Ob2, Ob3));
        
        // Define h as the composition of g and f
        const compose_morph = Var("compose_morph");
        const h_def = App(App(App(App(App(App(compose_morph, C3, Icit.Impl), Ob1, Icit.Impl), Ob2, Icit.Impl), Ob3, Icit.Impl), Var("g"), Icit.Expl), Var("f"), Icit.Expl);
        defineGlobal("h", HomTerm(C3, Ob1, Ob3), h_def, false, true);

        // Functor F: C3 -> Set
        // fmap0: maps all objects to Nat
        defineGlobal("Nat", Type());
        const Nat = Var("Nat");
        const fmap0 = Lam("_", Icit.Expl, ObjTerm(C3), _ => Nat);
        
        // fmap1: This is where we break the law.
        // We define fmap1 to be a function that ignores the input morphism and
        // always returns the successor function `s`.
        // The coherence check will then attempt to verify `s ∘ s = s`, which is false.
        const s_body = Lam("n", Icit.Expl, Nat, n => App(Var("s_prim"), n, Icit.Expl));
        defineGlobal("s_prim", Pi("_", Icit.Expl, Nat, _ => Nat), s_body);
        const s_func = Var("s_prim");

        const fmap1 = Lam("X", Icit.Impl, ObjTerm(C3), _ => 
                      Lam("Y", Icit.Impl, ObjTerm(C3), _ => 
                      Lam("a", Icit.Expl, HomTerm(C3, Var("X", true), Var("Y", true)), _ => s_func)));

        const mkFunctor_ = Var("mkFunctor_");
        const Set = Var("Set");
        const badFunctor = App(App(App(App(mkFunctor_, C3, Icit.Impl), Set, Icit.Impl), fmap0, Icit.Expl), fmap1, Icit.Expl);
        
        assert.throws(
            () => elaborate(badFunctor),
            (err: any) => {
                return err instanceof Error && err.name === 'CoherenceError' && err.message.includes("Functoriality check failed");
            },
            "Elaboration of a non-functorial map should throw a CoherenceError."
        );
    });
}); 