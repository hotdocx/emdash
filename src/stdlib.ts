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
}

/**
 * Sets up Phase 1 global definitions and rewrite rules.
 * This includes basic types like NatType, BoolType, Cat, Obj, Hom,
 * and rules for evaluating mkCat_ constructs.
 */
export function setupPhase1GlobalsAndRules() {
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
    // TODO : add the definition value for mkCat_ which unfolds to the kernel term
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

    // Rewrite Rules for mkCat_
    // TODO: those rewrite rules should be on the kernel term instead of the global constant
    addRewriteRule(
        "Obj_mkCat_eval",
        ["$O", "$H", "$C"],
        ObjTerm(App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl)),
        Var("$O"),
        emptyCtx
    );

    // TODO: those rewrite rules should be on the kernel term instead of the global constant
    addRewriteRule(
        "Hom_mkCat_eval",
        ["$O", "$H", "$C", "$X", "$Y"],
        HomTerm(App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl), Var("$X"), Var("$Y")),
        App(App(Var("$H"), Var("$X"), Icit.Expl), Var("$Y"), Icit.Expl),
        emptyCtx
    );

    // TODO : add the definition value for tapp which unfolds to the kernel term
    defineGlobal("tapp",
        Pi("A", Icit.Impl, CatTerm(), catA =>
        Pi("B", Icit.Impl, CatTerm(), catB =>
        Pi("F", Icit.Impl, FunctorTypeTerm(catA, catB), F =>
        Pi("G", Icit.Impl, FunctorTypeTerm(catA, catB), G =>
        Pi("eps", Icit.Expl, NatTransTypeTerm(catA, catB, F, G), _ =>
        Pi("X", Icit.Expl, ObjTerm(catA), X =>
            HomTerm(catB, FMap0Term(F, X), FMap0Term(G, X))
        )))))),
        undefined, false, false
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

    // Functoriality of composition: F(a) ∘ F(a') ↪ F(a ∘ a')
    const functoriality_vars = ["$A_cat", "$B_cat", "$F", "$X", "$Y", "$Z", "$a", "$a_prime"];

    const fmap1_F_a = FMap1Term(Var("$F"), Var("$a"), Var("$A_cat"), Var("$B_cat"), Var("$Y"), Var("$Z"));
    const fmap1_F_a_prime = FMap1Term(Var("$F"), Var("$a_prime"), Var("$A_cat"), Var("$B_cat"), Var("$X"), Var("$Y"));

    const FX = FMap0Term(Var("$F"), Var("$X"), Var("$A_cat"), Var("$B_cat"));
    const FY = FMap0Term(Var("$F"), Var("$Y"), Var("$A_cat"), Var("$B_cat"));
    const FZ = FMap0Term(Var("$F"), Var("$Z"), Var("$A_cat"), Var("$B_cat"));

    // LHS: compose_morph {B} {F X} {F Y} {F Z} (fmap1 F a) (fmap1 F a')
    const LHS_functoriality = App(App(App(App(App(App(
        Var("compose_morph"), Var("$B_cat"), Icit.Impl),
        FX, Icit.Impl),
        FY, Icit.Impl),
        FZ, Icit.Impl),
        fmap1_F_a, Icit.Expl),
        fmap1_F_a_prime, Icit.Expl
    );

    // compose_morph {A} {X} {Y} {Z} a a'
    const compose_a_a_prime = App(App(App(App(App(App(
        Var("compose_morph"), Var("$A_cat"), Icit.Impl),
        Var("$X"), Icit.Impl),
        Var("$Y"), Icit.Impl),
        Var("$Z"), Icit.Impl),
        Var("$a"), Icit.Expl),
        Var("$a_prime"), Icit.Expl
    );
    
    // RHS: fmap1 F (compose_morph a a')
    const RHS_functoriality = FMap1Term(Var("$F"), compose_a_a_prime, Var("$A_cat"), Var("$B_cat"), Var("$X"), Var("$Z"));

    addRewriteRule(
        "functoriality_composition",
        functoriality_vars,
        LHS_functoriality,
        RHS_functoriality,
        ctx
    );

    // // Functorial Elaboration Makers
    // // TODO only later, after adding an identity/equation in context
    // defineGlobal("mkFunctor_",
    //     Pi("A", Icit.Impl, CatTerm(), A =>
    //     Pi("B", Icit.Impl, CatTerm(), B =>
    //     Pi("fmap0", Icit.Expl, Pi("_", Icit.Expl, ObjTerm(A), _ => ObjTerm(B)), fmap0_val =>
    //     Pi("fmap1", Icit.Expl,
    //         Pi("X", Icit.Impl, ObjTerm(A), X =>
    //         Pi("Y", Icit.Impl, ObjTerm(A), Y =>
    //         Pi("a", Icit.Expl, HomTerm(A, X, Y), _ =>
    //             HomTerm(B, App(fmap0_val, X, Icit.Expl), App(fmap0_val, Y, Icit.Expl))
    //         ))), _ =>
    //         FunctorTypeTerm(A, B)
    //     )))),
    //     // Value: λ {A} {B} fmap0 fmap1. MkFunctorTerm(A, B, fmap0, fmap1)
    //     Lam("A", Icit.Impl, CatTerm(), A =>
    //     Lam("B", Icit.Impl, CatTerm(), B =>
    //     Lam("fmap0", Icit.Expl, Pi("_", Icit.Expl, ObjTerm(A), _ => ObjTerm(B)), fmap0_val =>
    //     Lam("fmap1", Icit.Expl,
    //         Pi("X", Icit.Impl, ObjTerm(A), X =>
    //         Pi("Y", Icit.Impl, ObjTerm(A), Y =>
    //         Pi("a", Icit.Expl, HomTerm(A, X, Y), _ =>
    //             HomTerm(B, App(fmap0_val, X, Icit.Expl), App(fmap0_val, Y, Icit.Expl))
    //         ))),
    //         fmap1_val => MkFunctorTerm(A, B, fmap0_val, fmap1_val)
    //     )))),
    //     false, true
    // );


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

    // Associativity of composition (for unification)
    const assoc_pvars = ['$C', '$X', '$Y', '$Z', '$W', '$a', '$f', '$g'];
    const p_C_assoc = Var('$C');
    const p_X_assoc = Var('$X');
    const p_Y_assoc = Var('$Y');
    const p_Z_assoc = Var('$Z');
    const p_W_assoc = Var('$W');
    const p_a_assoc = Var('$a');
    const p_f_assoc = Var('$f');
    const p_g_assoc = Var('$g');
    const v_compose_morph_assoc = Var("compose_morph");

    // g : Z -> W, f : Y -> Z  => g o f : Y -> W
    const compose_g_f = App(App(App(App(App(App(v_compose_morph_assoc, p_C_assoc, Icit.Impl), p_Y_assoc, Icit.Impl), p_Z_assoc, Icit.Impl), p_W_assoc, Icit.Impl), p_g_assoc, Icit.Expl), p_f_assoc, Icit.Expl);
    // a : X -> Y => (g o f) o a : X -> W
    const assoc_lhs1 = App(App(App(App(App(App(v_compose_morph_assoc, p_C_assoc, Icit.Impl), p_X_assoc, Icit.Impl), p_Y_assoc, Icit.Impl), p_W_assoc, Icit.Impl), compose_g_f, Icit.Expl), p_a_assoc, Icit.Expl);
    
    // f : Y -> Z, a : X -> Y => f o a : X -> Z
    const compose_f_a = App(App(App(App(App(App(v_compose_morph_assoc, p_C_assoc, Icit.Impl), p_X_assoc, Icit.Impl), p_Y_assoc, Icit.Impl), p_Z_assoc, Icit.Impl), p_f_assoc, Icit.Expl), p_a_assoc, Icit.Expl);
    // g: Z -> W => g o (f o a) : X -> W
    const assoc_lhs2 = App(App(App(App(App(App(v_compose_morph_assoc, p_C_assoc, Icit.Impl), p_X_assoc, Icit.Impl), p_Z_assoc, Icit.Impl), p_W_assoc, Icit.Impl), p_g_assoc, Icit.Expl), compose_f_a, Icit.Expl);

    addUnificationRule({
        name: 'assoc_compose_morph',
        patternVars: assoc_pvars,
        lhsPattern1: assoc_lhs1,
        lhsPattern2: assoc_lhs2,
        rhsNewConstraints: [], // Corresponds to [ tt = tt ]
    });

    // Rewrite rules for projecting from a functor created with the kernel primitive
    addRewriteRule(
        "fmap0_of_mkFunctor",
        ['$A', '$B', '$fmap0', '$fmap1', '$X'],
        FMap0Term(MkFunctorTerm(Var('$A'), Var('$B'), Var('$fmap0'), Var('$fmap1')), Var('$X')),
        App(Var('$fmap0'), Var('$X'), Icit.Expl),
        ctx
    );

    // This rule was failing, now it is OK because the insertion of implicits in the `check` function
    // is now conditioned using options.disableMaximallyInsertedImplicits for the LHS of a rewrite rule
    addRewriteRule(
        "fmap1_of_mkFunctor",
        ['$A', '$B', '$fmap0', '$fmap1', '$a', '$X', '$Y'],
        FMap1Term(
            MkFunctorTerm(Var('$A'), Var('$B'), Var('$fmap0'), Var('$fmap1')), 
            Var('$a'), 
            Var('$A'), 
            Var('$B'), 
            Var('$X'), 
            Var('$Y')
        ),
        App(App(App(Var('$fmap1'), Var('$X'), Icit.Impl), Var('$Y'), Icit.Impl), Var('$a'), Icit.Expl),
        ctx
    );


    // --- Phase 3: Yoneda Primitives ---
    
    // // Hom-functor: Hom_A(W, -)
    // defineGlobal("hom_cov",
    //     Pi("A", Icit.Impl, CatTerm(), A_cat_val =>
    //         Pi("W", Icit.Expl, ObjTerm(A_cat_val), _W_obj_val =>
    //             FunctorTypeTerm(A_cat_val, SetTerm())
    //         )
    //     ),
    //     Lam("A_cat_impl_arg", Icit.Impl, CatTerm(), A_cat_term =>
    //         Lam("W_obj_expl_arg", Icit.Expl, ObjTerm(A_cat_term), W_obj_term =>
    //             HomCovFunctorIdentity(A_cat_term, W_obj_term)
    //         )
    //     ),
    // );
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