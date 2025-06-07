/**
 * @file tests/dependent_types_tests.ts
 * @description Tests for dependent types, using length-indexed vectors (Vec) as the primary example.
 */
import {
    Term, Context, Icit, Type, Var, Lam, App, Pi, Hole,
    CatTerm, FunctorTypeTerm, ObjTerm, HomTerm, SetTerm,
    MkFunctorTerm,
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

        // const constFunctor = App(App(App(App(mkFunctor_, D2, Icit.Impl), Set, Icit.Impl), fmap0, Icit.Expl), fmap1, Icit.Expl);
        const constFunctor = MkFunctorTerm(D2, Set, fmap0, fmap1);
        console.log("constFunctor>>>",printTerm(constFunctor));
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
        defineGlobal("Nat", Type(), undefined, true, true);
        const Nat = Var("Nat");
        defineGlobal("s", Pi("_", Icit.Expl, Nat, _ => Nat), undefined, true, true);
        defineGlobal("z", Nat, undefined, true, true);
        const fmap0 = Lam("_", Icit.Expl, ObjTerm(C3), _ => Nat);
        
        // fmap1: This is where we break the law.
        // We define fmap1 to be a function that ignores the input morphism and
        // always returns the successor function `s`.
        // The coherence check will then attempt to verify `s ∘ s = s`, which is false.
        const s_func = Var("s");

        const fmap1 = Lam("X", Icit.Impl, ObjTerm(C3), _ => 
                      Lam("Y", Icit.Impl, ObjTerm(C3), _ => 
                      Lam("a", Icit.Expl, HomTerm(C3, Var("X", true), Var("Y", true)), _ => s_func)));

        const mkFunctor_ = Var("mkFunctor_");
        const Set = Var("Set");
        // const badFunctor = App(App(App(App(mkFunctor_, C3, Icit.Impl), Set, Icit.Impl), fmap0, Icit.Expl), fmap1, Icit.Expl);
        const badFunctor = MkFunctorTerm(C3, Set, fmap0, fmap1);

        assert.throws(
            () => elaborate(badFunctor),
            (err: any) => {
                return err instanceof Error && err.name === 'CoherenceError' && err.message.includes("Functoriality check failed");
            },
            "Elaboration of a non-functorial map should throw a CoherenceError."
        );
    });
}); 