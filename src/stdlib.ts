/**
 * @file stdlib.ts
 * @description Defines the standard library for emdash, including primitive types,
 * constants, and fundamental rewrite/unification rules for category theory.
 * Also includes system reset functionalities.
 */

import {
    Term, Context, Icit, Type, Var, Lam, App, Pi, Hole,
    CatTerm, ObjTerm, HomTerm,
    FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm, NatTransComponentTerm,
    SetTerm, HomCovFunctorIdentity, FunctorTypeTerm, MkFunctorTerm
} from './types';
import {
    globalDefs, userRewriteRules, userUnificationRules, constraints, emptyCtx,
    resetVarId, resetHoleId, getTermRef, setDebugVerbose, consoleLog, resetFlags
} from './state';
import { defineGlobal, addRewriteRule, addUnificationRule } from './globals';

/**
 * Resets the entire emdash system state to its initial configuration.
 * Clears all global definitions, rules, constraints, and resets ID generators.
 */
export function resetMyLambdaPi() {
    globalDefs.clear();
    userRewriteRules.length = 0;
    userUnificationRules.length = 0;
    constraints.length = 0;
    resetVarId();
    resetHoleId();
    resetFlags();
    setDebugVerbose(false);

    setupPhase1GlobalsAndRules();
}

/**
 * Sets up Phase 1 global definitions and rewrite rules.
 * This includes basic types like NatType, BoolType, Cat, Obj, Hom,
 * and rules for evaluating mkCat_ constructs.
 */
export function setupPhase1GlobalsAndRules() {
    // Basic Types (assumed to be Type itself, not elaborated here, so toElaborateType = false)
    defineGlobal("NatType", Type(), undefined, true, true);
    defineGlobal("BoolType", Type(), undefined, true, true);

    // Core Category Theory Primitives
    defineGlobal("Cat", Type(), CatTerm(), false, true);
    defineGlobal("Set", CatTerm(), SetTerm(), false, true);

    defineGlobal("Obj",
        Pi("A", Icit.Expl, CatTerm(), _A => Type()),
        Lam("A_val", Icit.Expl, CatTerm(), A_term => ObjTerm(A_term)),
        false, true
    );

    defineGlobal("Hom",
        Pi("A", Icit.Impl, CatTerm(), A_val =>
            Pi("X", Icit.Expl, ObjTerm(A_val), _X =>
                Pi("Y", Icit.Expl, ObjTerm(A_val), _Y => Type()))),
        Lam("A_val", Icit.Impl, CatTerm(), A_term =>
            Lam("X_val", Icit.Expl, ObjTerm(A_term), X_term =>
                Lam("Y_val", Icit.Expl, ObjTerm(A_term), Y_term =>
                    HomTerm(A_term, X_term, Y_term)))),
        false, true
    );

    defineGlobal("Functor",
        Pi("A", Icit.Expl, CatTerm(), _A =>
            Pi("B", Icit.Expl, CatTerm(), _B => Type())),
        Lam("A_val", Icit.Expl, CatTerm(), A_term =>
            Lam("B_val", Icit.Expl, CatTerm(), B_term =>
                FunctorTypeTerm(A_term, B_term))),
        false, true
    );

    defineGlobal("Functor_cat",
        Pi("A", Icit.Expl, CatTerm(), _A =>
            Pi("B", Icit.Expl, CatTerm(), _B => CatTerm())),
        Lam("A_val", Icit.Expl, CatTerm(), A_term =>
            Lam("B_val", Icit.Expl, CatTerm(), B_term =>
                FunctorCategoryTerm(A_term, B_term))),
        false, true
    );

    defineGlobal("Transf",
        Pi("A", Icit.Impl, CatTerm(), A =>
        Pi("B", Icit.Impl, CatTerm(), B =>
        Pi("F", Icit.Expl, FunctorTypeTerm(A, B), _ =>
        Pi("G", Icit.Expl, FunctorTypeTerm(A, B), _ =>
            Type()
        )))),
        undefined, true, false
    );

    defineGlobal("tapp",
        Pi("A", Icit.Impl, CatTerm(), catA =>
        Pi("B", Icit.Impl, CatTerm(), catB =>
        Pi("F", Icit.Impl, FunctorTypeTerm(catA, catB), F =>
        Pi("G", Icit.Impl, FunctorTypeTerm(catA, catB), G =>
        Pi("eps", Icit.Expl, Var("Transf",true), _ =>
        Pi("X", Icit.Expl, ObjTerm(catA), X =>
            HomTerm(catB, FMap0Term(F, X), FMap0Term(G, X))
        )))))),
        undefined, false, false, true
    );

    defineGlobal("compose_morph",
        Pi("A", Icit.Impl, CatTerm(), A_val =>
            Pi("X", Icit.Impl, ObjTerm(A_val), X_val =>
                Pi("Y", Icit.Impl, ObjTerm(A_val), Y_val =>
                    Pi("Z", Icit.Impl, ObjTerm(A_val), Z_val =>
                        Pi("g", Icit.Expl, HomTerm(A_val, Y_val, Z_val), _ =>
                            Pi("f", Icit.Expl, HomTerm(A_val, X_val, Y_val), _ =>
                                HomTerm(A_val, X_val, Z_val)
                            )
                        )
                    )
                )
            )
        ),
        undefined
    );
}

/**
 * Sets up further category theory primitives, like the hom_cov functor and naturality rules.
 * @param ctx The context for defining these primitives (usually emptyCtx).
 */
export function setupCatTheoryPrimitives(ctx: Context) {
    // Covariant Hom Functor: Hom_A(W, -) : A -> Set
    defineGlobal("hom_cov",
        Pi("A", Icit.Impl, CatTerm(), A_cat_val =>
            Pi("W", Icit.Expl, ObjTerm(A_cat_val), _W_obj_val =>
                FunctorTypeTerm(A_cat_val, SetTerm())
            )
        ),
        Lam("A_cat_impl_arg", Icit.Impl, CatTerm(), A_cat_term =>
            Lam("W_obj_expl_arg", Icit.Expl, ObjTerm(A_cat_term), W_obj_term =>
                HomCovFunctorIdentity(A_cat_term, W_obj_term)
            )
        ),
    );

    // Functorial Elaboration Makers
    defineGlobal("mkFunctor_",
        Pi("A", Icit.Impl, CatTerm(), A =>
        Pi("B", Icit.Impl, CatTerm(), B =>
        Pi("fmap0", Icit.Expl, Pi("_", Icit.Expl, ObjTerm(A), _ => ObjTerm(B)), fmap0_val =>
        Pi("fmap1", Icit.Expl,
            Pi("X", Icit.Impl, ObjTerm(A), X =>
            Pi("Y", Icit.Impl, ObjTerm(A), Y =>
            Pi("a", Icit.Expl, HomTerm(A, X, Y), _ =>
                HomTerm(B, App(fmap0_val, X, Icit.Expl), App(fmap0_val, Y, Icit.Expl))
            ))), _ =>
            FunctorTypeTerm(A, B)
        )))),
        // Value: λ {A} {B} fmap0 fmap1. MkFunctorTerm(A, B, fmap0, fmap1)
        Lam("A", Icit.Impl, CatTerm(), A =>
        Lam("B", Icit.Impl, CatTerm(), B =>
        Lam("fmap0", Icit.Expl, Pi("_", Icit.Expl, ObjTerm(A), _ => ObjTerm(B)), fmap0_val =>
        Lam("fmap1", Icit.Expl,
            Pi("X", Icit.Impl, ObjTerm(A), X =>
            Pi("Y", Icit.Impl, ObjTerm(A), Y =>
            Pi("a", Icit.Expl, HomTerm(A, X, Y), _ =>
                HomTerm(B, App(fmap0_val, X, Icit.Expl), App(fmap0_val, Y, Icit.Expl))
            ))),
            fmap1_val => MkFunctorTerm(A, B, fmap0_val, fmap1_val)
        )))),
        false, false, true
    );


    // --- Set Category Primitives ---
    // Set is a category where objects are types and morphisms are functions
    const Set = Var("Set");

    // Obj Set should be Type
    addRewriteRule("Obj_Set_eval", [], ObjTerm(Set), Type(), ctx);

    // Hom Set T U should be T -> U (Pi type)
    addRewriteRule(
        "Hom_Set_eval", ["$T", "$U"],
        HomTerm(Set, Var("$T"), Var("$U")),
        Pi("_", Icit.Expl, Var("$T"), _ => Var("$U")),
        ctx
    );

    // compose_morph in Set is function composition: λ g f x. g (f x)
    addRewriteRule(
        "compose_Set_eval", ["$T", "$U", "$V"],
        App(App(App(App(Var("compose_morph"), Set, Icit.Impl), Var("$T"), Icit.Impl), Var("$U"), Icit.Impl), Var("$V"), Icit.Impl),
        Lam("g", Icit.Expl, Pi("_", Icit.Expl, Var("$U"), _ => Var("$V")), g_val =>
            Lam("f", Icit.Expl, Pi("_", Icit.Expl, Var("$T"), _ => Var("$U")), f_val =>
                Lam("x", Icit.Expl, Var("$T"), x_val =>
                    App(g_val, App(f_val, x_val, Icit.Expl), Icit.Expl)
                )
            )
        ),
        ctx
    );
}

/**
 * Resets the emdash system and sets up all standard library globals and rules.
 * This is the main entry point for initializing a fresh emdash environment.
 */
export function resetMyLambdaPi_Emdash() {
    resetMyLambdaPi();
    setupPhase1GlobalsAndRules();
    setupCatTheoryPrimitives(emptyCtx); // Primitives are typically defined in an empty context
} 