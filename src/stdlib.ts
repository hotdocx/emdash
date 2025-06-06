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
    SetTerm, HomCovFunctorIdentity, FunctorTypeTerm
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
    // `Cat` itself is a type. Its "value" CatTerm() is also a type.
    // This means CatTerm() is a specific term of type Type().
    defineGlobal("Cat", Type(), CatTerm(), false, true);

    // `Set` is a specific category (a term of type Cat). Its value is SetTerm().
    defineGlobal("Set", CatTerm(), SetTerm(), false, true);

    // `Obj` is a function from Cat to Type.
    // The type given to defineGlobal needs to be elaborated itself.
    defineGlobal("Obj",
        Pi("A", Icit.Expl, CatTerm(), _A => Type()), // Obj : Cat -> Type
        Lam("A_val", Icit.Expl, CatTerm(), A_term => ObjTerm(A_term)), // A |-> Obj A
        false, true
    );

    // `Hom` is a function {A:Cat} -> Obj A -> Obj A -> Type.
    defineGlobal("Hom",
        Pi("A", Icit.Impl, CatTerm(), A_val =>      // {A : Cat}
            Pi("X", Icit.Expl, ObjTerm(A_val), _X =>  // (X : Obj A)
                Pi("Y", Icit.Expl, ObjTerm(A_val), _Y => Type()))), // (Y : Obj A) -> Type
        Lam("A_val", Icit.Impl, CatTerm(), A_term =>
            Lam("X_val", Icit.Expl, ObjTerm(A_term), X_term =>
                Lam("Y_val", Icit.Expl, ObjTerm(A_term), Y_term =>
                    HomTerm(A_term, X_term, Y_term)))), // {A} X Y |-> Hom A X Y
        false, true
    );

    // `Functor` is a function Cat -> Cat -> Type (the type of functors).
    defineGlobal("Functor",
        Pi("A", Icit.Expl, CatTerm(), _A =>      // (A : Cat)
            Pi("B", Icit.Expl, CatTerm(), _B => Type())), // (B : Cat) -> Type
        Lam("A_val", Icit.Expl, CatTerm(), A_term =>
            Lam("B_val", Icit.Expl, CatTerm(), B_term =>
                FunctorTypeTerm(A_term, B_term))), // A B |-> FunctorType A B
        false, true
    );

    // `Functor_cat` is a function Cat -> Cat -> Cat (the functor category).
    defineGlobal("Functor_cat",
        Pi("A", Icit.Expl, CatTerm(), _A =>      // (A : Cat)
            Pi("B", Icit.Expl, CatTerm(), _B => CatTerm())), // (B : Cat) -> Cat
        Lam("A_val", Icit.Expl, CatTerm(), A_term =>
            Lam("B_val", Icit.Expl, CatTerm(), B_term =>
                FunctorCategoryTerm(A_term, B_term))), // A B |-> FunctorCategory A B
        false, true
    );

    // `Transf` is the type of natural transformations.
    defineGlobal("Transf",
        Pi("A", Icit.Impl, CatTerm(), A_val =>          // {A : Cat}
            Pi("B", Icit.Impl, CatTerm(), B_val =>      // {B : Cat}
                Pi("F", Icit.Expl, FunctorTypeTerm(A_val, B_val), _F => // (F : Functor A B)
                    Pi("G", Icit.Expl, FunctorTypeTerm(A_val, B_val), _G => Type())))), // (G : Functor A B) -> Type
        Lam("A_val", Icit.Impl, CatTerm(), A_term =>
            Lam("B_val", Icit.Impl, CatTerm(), B_term =>
                Lam("F_val", Icit.Expl, FunctorTypeTerm(A_term, B_term), F_term =>
                    Lam("G_val", Icit.Expl, FunctorTypeTerm(A_term, B_term), G_term =>
                        NatTransTypeTerm(A_term, B_term, F_term, G_term))))),
        false, true
    );

    // Category constructor `mkCat_`.
    defineGlobal("mkCat_",
        Pi("Obj_repr", Icit.Expl, Type(), O_repr =>
            Pi("Hom_repr", Icit.Expl, Pi("X", Icit.Expl, O_repr, _ => Pi("Y", Icit.Expl, O_repr, _ => Type())), H_repr =>
                Pi("compose_impl", Icit.Expl,
                    Pi("X_obj", Icit.Impl, O_repr, Xobj_term =>
                    Pi("Y_obj", Icit.Impl, O_repr, Yobj_term =>
                    Pi("Z_obj", Icit.Impl, O_repr, Zobj_term =>
                    Pi("g_morph", Icit.Expl, App(App(H_repr, Yobj_term, Icit.Expl), Zobj_term, Icit.Expl), _ =>
                    Pi("f_morph", Icit.Expl, App(App(H_repr, Xobj_term, Icit.Expl), Yobj_term, Icit.Expl), _ =>
                    App(App(H_repr, Xobj_term, Icit.Expl), Zobj_term, Icit.Expl)
                    ))))), _ => CatTerm()
                )
            )
        ),
        undefined, true, true
    );

    defineGlobal("identity_morph",
        Pi("A", Icit.Impl, CatTerm(), A_val =>
            Pi("X", Icit.Expl, App(Var("Obj"), A_val, Icit.Expl), X_val =>
                HomTerm(A_val, X_val, X_val)
            )
        ),
        undefined, true, true
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

    // Rewrite Rules for mkCat_
    addRewriteRule(
        "Obj_mkCat_eval",
        ["$O", "$H", "$C"],
        ObjTerm(App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl)),
        Var("$O"),
        emptyCtx
    );

    addRewriteRule(
        "Hom_mkCat_eval",
        ["$O", "$H", "$C", "$X", "$Y"],
        HomTerm(App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl), Var("$X"), Var("$Y")),
        App(App(Var("$H"), Var("$X"), Icit.Expl), Var("$Y"), Icit.Expl),
        emptyCtx
    );

    addRewriteRule(
        "compose_mkCat_eval",
        ["$O", "$H", "$C"],
        App(Var("compose_morph"), App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl), Icit.Impl),
        Var("$C"),
        emptyCtx
    );

    // Identity and Composition Axioms as rewrite rules
    addRewriteRule(
        "comp_f_idX_fwd",
        ["$A_cat", "$X_obj", "$Y_obj", "$f_morph"],
        App(App(App(App(App(App(Var("compose_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl),
            Var("$f_morph"), Icit.Expl),
            App(App(Var("identity_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Expl), Icit.Expl),
        Var("$f_morph"),
        emptyCtx
    );

    addRewriteRule(
        "comp_idY_f_fwd_new",
        ["$A_cat", "$X_obj", "$Y_obj", "$f_morph"],
        App(App(App(App(App(App(Var("compose_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl),
            App(App(Var("identity_morph"), Var("$A_cat"), Icit.Impl), Var("$Y_obj"), Icit.Expl), Icit.Expl),
            Var("$f_morph"), Icit.Expl),
        Var("$f_morph"),
        emptyCtx
    );

    // Unification rule: (fapp1 (hom_cov $W) $a) $f  ≡  compose_morph $a $f
    const unifRule_homCov_compose_PatternVars = ["$A_cat", "$W_obj", "$X_obj", "$Y_obj", "$Z_obj", "$a_morph", "$f_morph"];
    const unifRule_LHS1 = App(
        FMap1Term(
            HomCovFunctorIdentity(Var("$A_cat"), Var("$W_obj")), // hom_cov $A_cat $W_obj
            Var("$a_morph"),                                   // $a_morph
            Var("$A_cat"),                                     // catA_IMPLICIT
            SetTerm(),                                         // catB_IMPLICIT
            Var("$Y_obj"),                                     // objX_A_IMPLICIT (domain of $a_morph)
            Var("$Z_obj")                                      // objY_A_IMPLICIT (codomain of $a_morph)
        ),
        Var("$f_morph")                                        // argument $f_morph
    );
    const unifRule_LHS2 = App(App(App(App(App(App(Var("compose_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl), Var("$Z_obj"), Icit.Impl),
        Var("$a_morph"), Icit.Expl),
        Var("$f_morph"), Icit.Expl);

    addUnificationRule({
        name: "unif_hom_cov_fapp1_compose",
        patternVars: unifRule_homCov_compose_PatternVars,
        lhsPattern1: unifRule_LHS1,
        lhsPattern2: unifRule_LHS2,
        rhsNewConstraints: [{ t1: Type(), t2: Type() }] // Placeholder for "these are equal"
    });
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

    // Naturality Rewrite Rule (Direct version from LambdAPI spec)
    // rule fapp1 (hom_cov _) (@fapp1 _ _ $G $X $X' $a) (@tapp _ _ $F $G $ϵ $X)
    //   ↪ fapp1 (hom_cov _) (tapp $ϵ $X') (fapp1 $F $a);
    // This translates to:
    // (tapp ϵ X) _∘> (G a)  ↪  (F a) _∘> (tapp ϵ X')
    // The explicit pattern variables for categories ensure the correct hom_cov is used.

    const userPatternVars_NatDirect = [
        "$A_cat", "$B_cat",         // Domain and Codomain categories for F, G
        "$F_func", "$G_func",       // Functors F, G : A -> B
        "$eps_transf",             // Natural transformation epsilon : F => G
        "$X_obj", "$X_prime_obj",   // Objects X, X' in A (domain of epsilon)
        "$a_morph"                 // Morphism a : X -> X' in A
    ];

    // LHS: (tapp eps X) _∘> (G a)
    // = fapp1( hom_cov B (F X) , G a , tapp eps X )
    const LHS_NatDirect = App(
        FMap1Term( // This is the outer application, representing `_∘>`
            HomCovFunctorIdentity(Var("$B_cat"), FMap0Term(Var("$F_func"), Var("$X_obj"), Var("$A_cat"), Var("$B_cat"))), // Functor part of _∘>: hom_cov B (F X)
            FMap1Term( // First argument to _∘>: G a
                Var("$G_func"), Var("$a_morph"),
                Var("$A_cat"), Var("$B_cat"), Var("$X_obj"), Var("$X_prime_obj")
            ),
            // Implicit args for the outer FMap1Term (representing _∘>)
            Var("$B_cat"), // catA for hom_cov B (F X) is B (codomain of F, G)
            SetTerm(),     // catB for hom_cov B (F X) is Set
            FMap0Term(Var("$G_func"), Var("$X_obj"), Var("$A_cat"), Var("$B_cat")),      // objX_A for (G a) (domain in B)
            FMap0Term(Var("$G_func"), Var("$X_prime_obj"), Var("$A_cat"), Var("$B_cat")) // objY_A for (G a) (codomain in B)
        ),
        NatTransComponentTerm( // Second argument to _∘>: tapp eps X
            Var("$eps_transf"), Var("$X_obj"),
            Var("$A_cat"), Var("$B_cat"), Var("$F_func"), Var("$G_func")
        )
    );

    // RHS: (F a) _∘> (tapp eps X')
    // = fapp1( hom_cov B (F X) , tapp eps X' , F a )
    // Correction: The LambdAPI rule is `fapp1 (hom_cov _) (tapp $ϵ $X') (fapp1 $F $a)`
    // This means the functor for `_∘>` is `hom_cov _ (F X)`.
    const RHS_NatDirect = App(
        FMap1Term( // Outer application
            HomCovFunctorIdentity(Var("$B_cat"), FMap0Term(Var("$F_func"), Var("$X_obj"), Var("$A_cat"), Var("$B_cat"))), // Functor part of _∘>: hom_cov B (F X)
            NatTransComponentTerm( // First argument to _∘>: tapp eps X'
                Var("$eps_transf"), Var("$X_prime_obj"),
                Var("$A_cat"), Var("$B_cat"), Var("$F_func"), Var("$G_func")
            ),
             // Implicit args for the outer FMap1Term (representing _∘>)
            Var("$B_cat"), // catA for hom_cov B (F X) is B
            SetTerm(),     // catB for hom_cov B (F X) is Set
            FMap0Term(Var("$F_func"), Var("$X_prime_obj"), Var("$A_cat"), Var("$B_cat")), // objX_A for (tapp eps X') (domain in B is F X)
            FMap0Term(Var("$G_func"), Var("$X_prime_obj"), Var("$A_cat"), Var("$B_cat"))  // objY_A for (tapp eps X') (codomain in B is G X)
        ),
        FMap1Term( // Second argument to _∘>: F a
            Var("$F_func"), Var("$a_morph"),
            Var("$A_cat"), Var("$B_cat"), Var("$X_obj"), Var("$X_prime_obj")
        )
    );

    addRewriteRule(
        "naturality_direct_hom_cov_fapp1_tapp",
        userPatternVars_NatDirect,
        LHS_NatDirect,
        RHS_NatDirect,
        ctx // Rule defined in this context
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