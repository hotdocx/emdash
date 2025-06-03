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
    freshHoleName, freshVarName, resetVarId, resetHoleId, setDebugVerbose,
    FH // FH (Fresh Hole) shorthand
} from './state';
import { defineGlobal, addRewriteRule, addUnificationRule } from './globals';

/**
 * Resets the entire emdash system state to its initial configuration.
 * Clears all global definitions, rules, constraints, and resets ID generators.
 */
export function resetMyLambdaPi() {
    constraints.length = 0;
    globalDefs.clear();
    userRewriteRules.length = 0;
    userUnificationRules.length = 0;
    resetVarId();
    resetHoleId();
    setDebugVerbose(false); // Default to non-verbose
    // solveConstraintsControl.depth = 0; // Already handled by solveConstraints itself typically
}

/**
 * Sets up Phase 1 global definitions and rewrite rules.
 * This includes basic types like NatType, BoolType, Cat, Obj, Hom,
 * and rules for evaluating mkCat_ constructs.
 */
export function setupPhase1GlobalsAndRules() {
    // Basic Types (assumed to be Type itself, not elaborated)
    defineGlobal("NatType", Type(), undefined, true, true, true, false);
    defineGlobal("BoolType", Type(), undefined, true, true, true, false);

    // Core Category Theory Primitives
    defineGlobal("Cat", Type(), CatTerm(), false, true, true, false); // Cat is a type, its value is CatTerm which is a Type

    defineGlobal("Set", CatTerm(), SetTerm(), false, true, true, false); // Set is a Cat, its value is SetTerm

    defineGlobal("Obj",
        Pi("A", Icit.Expl, CatTerm(), _A => Type()), // Obj : Cat -> Type
        Lam("A_val", Icit.Expl, CatTerm(), A_term => ObjTerm(A_term)), // A |-> Obj A
        false, true, false, true // Type needs elaboration
    );

    defineGlobal("Hom",
        Pi("A", Icit.Impl, CatTerm(), A_val =>      // {A : Cat}
            Pi("X", Icit.Expl, ObjTerm(A_val), _X =>  // (X : Obj A)
                Pi("Y", Icit.Expl, ObjTerm(A_val), _Y => Type()))), // (Y : Obj A) -> Type
        Lam("A_val", Icit.Impl, CatTerm(), A_term =>
            Lam("X_val", Icit.Expl, ObjTerm(A_term), X_term =>
                Lam("Y_val", Icit.Expl, ObjTerm(A_term), Y_term =>
                    HomTerm(A_term, X_term, Y_term)))), // {A} X Y |-> Hom A X Y
        false, true, false, true // Type needs elaboration
    );

    defineGlobal("Functor",
        Pi("A", Icit.Expl, CatTerm(), _A =>      // (A : Cat)
            Pi("B", Icit.Expl, CatTerm(), _B => Type())), // (B : Cat) -> Type
        Lam("A_val", Icit.Expl, CatTerm(), A_term =>
            Lam("B_val", Icit.Expl, CatTerm(), B_term =>
                FunctorTypeTerm(A_term, B_term))), // A B |-> FunctorType A B
        false, true, false, true // Type needs elaboration
    );

    defineGlobal("Functor_cat", // The functor category [A, B]
        Pi("A", Icit.Expl, CatTerm(), _A =>      // (A : Cat)
            Pi("B", Icit.Expl, CatTerm(), _B => CatTerm())), // (B : Cat) -> Cat
        Lam("A_val", Icit.Expl, CatTerm(), A_term =>
            Lam("B_val", Icit.Expl, CatTerm(), B_term =>
                FunctorCategoryTerm(A_term, B_term))), // A B |-> FunctorCategory A B
        false, true, false, true // Type needs elaboration
    );

    defineGlobal("Transf", // Type of natural transformations
        Pi("A", Icit.Impl, CatTerm(), A_val =>          // {A : Cat}
            Pi("B", Icit.Impl, CatTerm(), B_val =>      // {B : Cat}
                Pi("F", Icit.Expl, FunctorTypeTerm(A_val, B_val), _F => // (F : Functor A B)
                    Pi("G", Icit.Expl, FunctorTypeTerm(A_val, B_val), _G => Type())))), // (G : Functor A B) -> Type
        Lam("A_val", Icit.Impl, CatTerm(), A_term =>
            Lam("B_val", Icit.Impl, CatTerm(), B_term =>
                Lam("F_val", Icit.Expl, FunctorTypeTerm(A_term, B_term), F_term =>
                    Lam("G_val", Icit.Expl, FunctorTypeTerm(A_term, B_term), G_term =>
                        NatTransTypeTerm(A_term, B_term, F_term, G_term))))),
        false, true, false, true // Type needs elaboration
    );

    // Category constructor (mkCat_) - a constant symbol representing the formation of a category
    // Its "value" is effectively handled by rewrite rules for Obj(mkCat_ ...) and Hom(mkCat_ ...).
    // The type indicates it takes representations of objects, homs, and composition, and yields a Cat.
    defineGlobal("mkCat_",
        Pi("Obj_repr", Icit.Expl, Type(), O_repr =>                           // (Obj_repr : Type) ->
            Pi("Hom_repr", Icit.Expl, Pi("X", Icit.Expl, O_repr, _ => Pi("Y", Icit.Expl, O_repr, _ => Type())), H_repr => // (Hom_repr : (X Y : Obj_repr) -> Type) ->
                Pi("compose_impl", Icit.Expl,                               // (compose_impl : forall X Y Z, Hom_repr Y Z -> Hom_repr X Y -> Hom_repr X Z) ->
                    Pi("X_obj", Icit.Impl, O_repr, Xobj_term =>
                    Pi("Y_obj", Icit.Impl, O_repr, Yobj_term =>
                    Pi("Z_obj", Icit.Impl, O_repr, Zobj_term =>
                    Pi("g_morph", Icit.Expl, App(App(H_repr, Yobj_term, Icit.Expl), Zobj_term, Icit.Expl), _ =>
                    Pi("f_morph", Icit.Expl, App(App(H_repr, Xobj_term, Icit.Expl), Yobj_term, Icit.Expl), _ =>
                    App(App(H_repr, Xobj_term, Icit.Expl), Zobj_term, Icit.Expl)
                    ))))), _ => CatTerm()                                     // Cat
                )
            )
        ),
        undefined, // No direct value; behavior defined by rules
        true,      // Is a constant symbol
        true,      // Is injective (if mkCat_ O H C = mkCat_ O' H' C', then O=O', H=H', C=C')
        false,     // Not a type name like NatType (it constructs a term of type Cat)
        true       // The provided type needs elaboration itself
    );

    defineGlobal("identity_morph",
        Pi("A", Icit.Impl, CatTerm(), A_val =>                    // {A : Cat} ->
            Pi("X", Icit.Expl, App(Var("Obj"), A_val, Icit.Expl), X_val => // (X : Obj A) ->
                HomTerm(A_val, X_val, X_val)                      // Hom A X X
            )
        ),
        undefined, // Axiom / primitive constructor
        true,      // Constant symbol
        true,      // Injective (identity for a specific object is unique)
        false,
        true       // Type needs elaboration
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
        undefined, // Axiom / primitive constructor
        false,     // Not a constant symbol (it's a function with rules)
        false,     // Not injective in general
        false,
        true       // Type needs elaboration
    );

    // Rewrite Rules for mkCat_
    // Obj (mkCat_ O H C) X  ~>  O  (where X is an Obj_repr, not Obj (mkCat_ ...))
    // This rule is tricky. The ObjTerm on LHS should have mkCat_ as its category.
    // The pattern variable $X in ObjTerm($CAT, $X) would match the object representation,
    // but ObjTerm expects a term of type Obj $CAT.
    // The intent of mkCat_ is that its Obj_repr IS the type of objects for the category being built.
    // So, Obj (mkCat_ $O $H $C) should reduce to $O.
    // This means a rule like: apply(Obj, mkCat_ $O $H $C) --> $O, if Obj is a global.
    // Or, more directly as ObjTerm(mkCat_ $O $H $C) --> ??? (this form is ill-typed if ObjTerm's argument is the object itself)
    // The definition of `Obj` is `Lam("A_val", ..., ObjTerm(A_term))`.
    // So, `App(Var("Obj"), mkCat_ $O $H $C)` should reduce using `ObjTerm(mkCat_ $O $H $C)`.
    // This suggests a rule: ObjTerm(mkCat_ $O $H $C) --> $O (where $O is the type, and objects are terms of this type)
    // This is not quite right. The rule Obj (mkCat_ O H C) X ↪ X matches LambdAPI spec if X is an object from O.
    // The Obj_mkCat_eval below is for Obj(mkCat_ O H C) applied to some term representing an object in the new cat.
    // This seems to be a common pattern in theorem provers: `Obj C` is the type of objects *in* category C.
    // Let's assume the rules define how `Obj` and `Hom` interact with `mkCat_`.

    // Obj (mkCat_ $O $H $Comp)  ~>  $O
    // This rule means that the "type of objects" of a category defined by mkCat_
    // is the first argument $O given to mkCat_.
    addRewriteRule(
        "Obj_mkCat_eval",
        ["$O", "$H", "$C"], // Pattern variables
        // LHS: Obj (mkCat_ $O $H $C)
        App(Var("Obj"), App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl), Icit.Expl),
        // RHS: $O
        Var("$O"),
        emptyCtx
    );

    // Hom (mkCat_ $O $H $Comp) $X $Y  ~>  $H $X $Y
    // This rule means that the "type of morphisms" between $X and $Y$ in a category defined by mkCat_
    // is given by applying the second argument $H$ of mkCat_ to $X$ and $Y$.
    addRewriteRule(
        "Hom_mkCat_eval",
        ["$O", "$H", "$C", "$X", "$Y"], // Pattern variables
        // LHS: Hom (mkCat_ $O $H $C) $X $Y
        App(App(App(Var("Hom"),
                App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl), Icit.Impl), // Category argument
            Var("$X"), Icit.Expl), // Domain argument
            Var("$Y"), Icit.Expl), // Codomain argument
        // RHS: $H $X $Y
        App(App(Var("$H"), Var("$X"), Icit.Expl), Var("$Y"), Icit.Expl),
        emptyCtx
    );

    // compose_morph (mkCat_ $O $H $Comp) {X}{Y}{Z} g f ~> $Comp {X}{Y}{Z} g f
    // This means composition in a category defined by mkCat_ is the third argument $Comp$.
    // The pattern needs to match `compose_morph` applied to the category and then other args.
    addRewriteRule(
        "compose_mkCat_eval",
        ["$O", "$H", "$C"], // Implicit args X,Y,Z and explicit g,f are handled by `compose_morph` structure
        // LHS: compose_morph {mkCat_ $O $H $C}
        // This should match the `compose_morph` where its *first implicit argument* (the category) is `mkCat_ $O $H $C`.
        // The structure of App(Var("compose_morph"), App(App(App(Var("mkCat_")...)))) is for the first argument.
        App(Var("compose_morph"), App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl), Icit.Impl),
        // RHS: $C (the composition function provided to mkCat_)
        Var("$C"),
        emptyCtx
    );

    // Identity and Composition Axioms (as rewrite rules if they are definitional)
    // These are often taken as axioms or proved from a more primitive definition of category.
    // Here, we add them as directed rewrite rules for now.
    // comp_f_idX: f ∘ id_X = f
    // compose_morph {A} {X} {X} {Y} f (identity_morph {A} X)  ~>  f
    addRewriteRule(
        "comp_f_idX_fwd",
        ["$A_cat", "$X_obj", "$Y_obj", "$f_morph"],
        App(App(App(App(App(App(Var("compose_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl),
            Var("$f_morph"), Icit.Expl),
            App(App(Var("identity_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Expl), Icit.Expl),
        Var("$f_morph"),
        emptyCtx
    );

    // comp_idY_f: id_Y ∘ f = f
    // compose_morph {A} {X} {Y} {Y} (identity_morph {A} Y) f  ~>  f
    addRewriteRule(
        "comp_idY_f_fwd_new",
        ["$A_cat", "$X_obj", "$Y_obj", "$f_morph"],
        App(App(App(App(App(App(Var("compose_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl),
            App(App(Var("identity_morph"), Var("$A_cat"), Icit.Impl), Var("$Y_obj"), Icit.Expl), Icit.Expl),
            Var("$f_morph"), Icit.Expl),
        Var("$f_morph"),
        emptyCtx
    );

    // Unification rule for hom_cov and compose_morph
    // (fapp1 (hom_cov $W) $a) $f  ≡  compose_morph $a $f
    // This means the action of HomCovFunctor on morphisms is standard composition.
    const unifRule_homCov_compose_PatternVars = ["$A_cat", "$W_obj", "$X_obj", "$Y_obj", "$Z_obj", "$a_morph", "$f_morph"];
    const unifRule_LHS1 = App(
        FMap1Term( // This represents (fapp1 (hom_cov $A_cat $W_obj) $a_morph)
            HomCovFunctorIdentity(Var("$A_cat"), Var("$W_obj")),
            Var("$a_morph"),
            // Implicit args for FMap1Term: catA, catB, objX_A, objY_A
            Var("$A_cat"), // catA (domain of hom_cov functor)
            SetTerm(),     // catB (codomain of hom_cov functor is Set)
            Var("$Y_obj"), // objX_A (domain of $a_morph)
            Var("$Z_obj")  // objY_A (codomain of $a_morph)
        ),
        Var("$f_morph") // Argument to the resulting function: $f
    );
    const unifRule_LHS2 = App(App(App(App(App(App(Var("compose_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl), Var("$Z_obj"), Icit.Impl),
        Var("$a_morph"), Icit.Expl),
        Var("$f_morph"), Icit.Expl);

    addUnificationRule({
        name: "unif_hom_cov_fapp1_compose",
        patternVars: unifRule_homCov_compose_PatternVars,
        lhsPattern1: unifRule_LHS1,
        lhsPattern2: unifRule_LHS2,
        rhsNewConstraints: [{ t1: Type(), t2: Type() }] // Placeholder constraint, means "these are definitionally equal"
    });
}

/**
 * Sets up further category theory primitives, like the hom_cov functor and naturality rules.
 * @param ctx The context for defining these primitives (usually emptyCtx).
 */
export function setupCatTheoryPrimitives(ctx: Context) {
    // Define Set again if not already. Here, assuming it's defined in Phase1.
    // defineGlobal("Set", CatTerm(), SetTerm(), false, true, true, false);

    // Covariant Hom Functor: Hom_A(W, -) : A -> Set
    defineGlobal("hom_cov",
        Pi("A", Icit.Impl, CatTerm(), A_cat_val =>            // {A : Cat} ->
            Pi("W", Icit.Expl, ObjTerm(A_cat_val), _W_obj_val => // (W : Obj A) ->
                FunctorTypeTerm(A_cat_val, SetTerm())        // Functor A Set
            )
        ),
        Lam("A_cat_impl_arg", Icit.Impl, CatTerm(), A_cat_term =>
            Lam("W_obj_expl_arg", Icit.Expl, ObjTerm(A_cat_term), W_obj_term =>
                HomCovFunctorIdentity(A_cat_term, W_obj_term) // Value is the kernel HomCovFunctorIdentity term
            )
        ),
        false, true, false, true // Type needs elaboration
    );

    // Naturality Rewrite Rule (Direct version from LambdAPI spec)
    // rule fapp1 (hom_cov _) (@fapp1 _ _ $G $X $X' $a) (@tapp _ _ $F $G $ϵ $X)
    //   ↪ fapp1 (hom_cov _) (tapp $ϵ $X') (fapp1 $F $a);
    // This translates to:
    // (tapp ϵ X) _∘> (G a)  ↪  (F a) _∘> (tapp ϵ X')
    // where `_∘>` is `fapp1 (hom_cov _)`
    // LHS: fapp1 (hom_cov B (FX)) (fapp1 G a) (tapp ϵ X)
    // RHS: fapp1 (hom_cov B (FX')) (tapp ϵ X') (fapp1 F a)
    // The implicit arguments for FMap1Term and NatTransComponentTerm need to be filled with Holes (FH())
    // if they are not captured by pattern variables.

    const userPatternVars_NatDirect = [
        "$A_cat", "$B_cat", // Categories for F, G, epsilon
        "$F_func", "$G_func", // Functors F, G : A -> B
        "$eps_transf",       // Natural transformation epsilon : F => G
        "$X_obj", "$X_prime_obj", // Objects X, X' in A
        "$a_morph"           // Morphism a : X -> X' in A
    ];

    // LHS: (tapp eps X) _∘> (G a)
    // which is fapp1( hom_cov B (FX) , G a , tapp eps X ) if we assume B is codomain of G, FX is F(X)
    // Let's use FH() for implicit arguments not covered by pattern variables.
    const LHS_NatDirect = App(
        FMap1Term( // This is the outer application, representing `_∘>`
            HomCovFunctorIdentity(Var("$B_cat"), FMap0Term(Var("$F_func"), Var("$X_obj"), Var("$A_cat"), Var("$B_cat"))), // Functor: hom_cov B (FX)
            FMap1Term( // Argument 1: G a
                Var("$G_func"), Var("$a_morph"),
                Var("$A_cat"), Var("$B_cat"), Var("$X_obj"), Var("$X_prime_obj")
            ),
            // Implicits for outer FMap1Term
            Var("$B_cat"), // catA for hom_cov B (FX) is B
            SetTerm(),     // catB for hom_cov B (FX) is Set
            FMap0Term(Var("$G_func"), Var("$X_obj"), Var("$A_cat"), Var("$B_cat")), // objX_A for G a (as object in B) = G(X)
            FMap0Term(Var("$G_func"), Var("$X_prime_obj"), Var("$A_cat"), Var("$B_cat"))  // objY_A for G a (as object in B) = G(X')
        ),
        NatTransComponentTerm( // Argument 2: tapp eps X
            Var("$eps_transf"), Var("$X_obj"),
            Var("$A_cat"), Var("$B_cat"), Var("$F_func"), Var("$G_func")
        )
    );

    // RHS: (F a) _∘> (tapp eps X')
    // which is fapp1( hom_cov B (FX') , tapp eps X' , F a )
    const RHS_NatDirect = App(
        FMap1Term( // Outer application
            HomCovFunctorIdentity(Var("$B_cat"), FMap0Term(Var("$F_func"), Var("$X_prime_obj"), Var("$A_cat"), Var("$B_cat"))), // Functor: hom_cov B (FX')
            NatTransComponentTerm( // Argument 1: tapp eps X'
                Var("$eps_transf"), Var("$X_prime_obj"),
                Var("$A_cat"), Var("$B_cat"), Var("$F_func"), Var("$G_func")
            ),
            // Implicits for outer FMap1Term
            Var("$B_cat"), // catA for hom_cov B (FX') is B
            SetTerm(),     // catB for hom_cov B (FX') is Set
            FMap0Term(Var("$F_func"), Var("$X_prime_obj"), Var("$A_cat"), Var("$B_cat")), // objX_A for tapp (as object in B) = F(X')
            FMap0Term(Var("$G_func"), Var("$X_prime_obj"), Var("$A_cat"), Var("$B_cat"))  // objY_A for tapp (as object in B) = G(X')
        ),
        FMap1Term( // Argument 2: F a
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