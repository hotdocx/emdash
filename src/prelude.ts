/**
 * @file prelude.ts
 *
 * Defines the initial set of global symbols, rewrite rules, and unification rules
 * that form the Emdash standard library and category theory primitives.
 * This sets up the foundational theory for users.
 */

import {
    Term, Context, Icit, Type, Var, Lam, App, Pi,
    CatTerm, ObjTerm, HomTerm,
    FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm, NatTransComponentTerm, SetTerm, HomCovFunctorIdentity, FunctorTypeTerm
} from './types';
import { emptyCtx, FH } from './state';
import { defineGlobal, addRewriteRule, addUnificationRule, resetMyLambdaPi } from './runtime';
import { consoleLog } from './utils';

/**
 * Sets up Phase 1 globals and rules: basic types, category constructors, and their evaluation rules.
 * This includes Cat, Obj, Hom, Functor, Transf, and rules for mkCat_ evaluation.
 */
function setupPhase1GlobalsAndRules() {
    // Basic Types
    defineGlobal("NatType", Type(), undefined, true, true, true); // isTypeNameLike = true
    defineGlobal("BoolType", Type(), undefined, true, true, true); // isTypeNameLike = true

    // Category Primitives
    defineGlobal("Cat", Type(), CatTerm(), false, true, true); // Cat is a type name, but also has a value CatTerm()

    // Set Category as a specific instance of Cat
    // Note: "Set" is defined again in setupCatTheoryPrimitives, ensuring it uses the SetTerm() value.
    // This early definition is more about establishing "Set" as a known global early if needed.
    // The later one will correctly set its value.
    defineGlobal("Set_type_placeholder", Type(), undefined, true, true, true);


    defineGlobal("Obj",
        Pi("A", Icit.Expl, CatTerm(), _A => Type()), // Obj : Cat -> Type
        Lam("A_val", Icit.Expl, CatTerm(), A_term => ObjTerm(A_term)), // A => ObjTerm(A)
        false, true, true // Not a constant symbol, is injective, is typeNameLike for its application Obj(C)
    );

    defineGlobal("Hom",
        Pi("A", Icit.Impl, CatTerm(), A_val =>          // {A : Cat} ->
            Pi("X", Icit.Expl, ObjTerm(A_val), _X =>    //  (X : Obj A) ->
                Pi("Y", Icit.Expl, ObjTerm(A_val), _Y => Type()))), // (Y : Obj A) -> Type
        Lam("A_val", Icit.Impl, CatTerm(), A_term =>
            Lam("X_val", Icit.Expl, ObjTerm(A_term), X_term =>
                Lam("Y_val", Icit.Expl, ObjTerm(A_term), Y_term =>
                    HomTerm(A_term, X_term, Y_term)))),
        false, true, true // Not constant, injective in its structure, typeNameLike for Hom C X Y
    );

    defineGlobal("Functor",
        Pi("A", Icit.Expl, CatTerm(), _A =>         // (A : Cat) ->
            Pi("B", Icit.Expl, CatTerm(), _B => Type())), // (B : Cat) -> Type
        Lam("A_val", Icit.Expl, CatTerm(), A_term =>
            Lam("B_val", Icit.Expl, CatTerm(), B_term =>
                FunctorTypeTerm(A_term, B_term))),
        false, true, true
    );

    // Functor_cat [A,B] is the category of functors from A to B. Its objects are Functors, its Homs are NatTransfs.
    defineGlobal("Functor_cat",
        Pi("A", Icit.Expl, CatTerm(), _A =>         // (A : Cat) ->
            Pi("B", Icit.Expl, CatTerm(), _B => CatTerm())), // (B : Cat) -> Cat
        Lam("A_val", Icit.Expl, CatTerm(), A_term =>
            Lam("B_val", Icit.Expl, CatTerm(), B_term =>
                FunctorCategoryTerm(A_term, B_term))),
        false, true, true // This constructs a Category, so it's typeNameLike in that sense.
    );

    defineGlobal("Transf",
        Pi("A", Icit.Impl, CatTerm(), A_val =>           // {A : Cat} ->
            Pi("B", Icit.Impl, CatTerm(), B_val =>         // {B : Cat} ->
                Pi("F", Icit.Expl, FunctorTypeTerm(A_val, B_val), _F => // (F : Functor A B) ->
                    Pi("G", Icit.Expl, FunctorTypeTerm(A_val, B_val), _G => Type())))), // (G : Functor A B) -> Type
        Lam("A_val", Icit.Impl, CatTerm(), A_term =>
            Lam("B_val", Icit.Impl, CatTerm(), B_term =>
                Lam("F_val", Icit.Expl, FunctorTypeTerm(A_term, B_term), F_term =>
                    Lam("G_val", Icit.Expl, FunctorTypeTerm(A_term, B_term), G_term =>
                        NatTransTypeTerm(A_term, B_term, F_term, G_term))))),
        false, true, true
    );

    // Constructor for categories (simplified, without laws for now)
    // mkCat_ ObjRepr HomRepr ComposeImpl : Cat
    defineGlobal("mkCat_",
        Pi("Obj_repr", Icit.Expl, Type(), O_repr =>                     // (Obj_repr : Type) ->
            Pi("Hom_repr", Icit.Expl, Pi("X", Icit.Expl, O_repr, _ => Pi("Y", Icit.Expl, O_repr, _ => Type())), H_repr => // (Hom_repr : Obj_repr -> Obj_repr -> Type) ->
                Pi("compose_impl", Icit.Expl,                           // (compose_impl : ...) -> Cat
                    Pi("X_obj", Icit.Impl, O_repr, Xobj_term =>
                    Pi("Y_obj", Icit.Impl, O_repr, Yobj_term =>
                    Pi("Z_obj", Icit.Impl, O_repr, Zobj_term =>
                    Pi("g_morph", Icit.Expl, App(App(H_repr, Yobj_term, Icit.Expl), Zobj_term, Icit.Expl), _ => // g : Hom_repr Y Z
                    Pi("f_morph", Icit.Expl, App(App(H_repr, Xobj_term, Icit.Expl), Yobj_term, Icit.Expl), _ => // f : Hom_repr X Y
                    App(App(H_repr, Xobj_term, Icit.Expl), Zobj_term, Icit.Expl) // Hom_repr X Z
                    ))))), _ => CatTerm()
                )
            )
        ),
        undefined, // Value is the term itself, it's a constructor
        true, // isConstantSymbol: mkCat_ is a fixed constructor
        true, // isInjective: If mkCat_ O H C = mkCat_ O' H' C', then O=O', H=H', C=C'
        false // Not typeNameLike in the sense of Obj/Hom; it constructs a CatTerm value.
    );

    // Identity and Composition Morphisms (as global constants with Pi types)
    defineGlobal("identity_morph",
        Pi("A", Icit.Impl, CatTerm(), A_val =>                  // {A : Cat} ->
            Pi("X", Icit.Expl, ObjTerm(A_val), X_val =>         // (X : Obj A) ->
                HomTerm(A_val, X_val, X_val)                    // Hom A X X
            )
        ),
        undefined, // No specific lambda term value; it's a constant.
        true,  // isConstantSymbol
        true,  // isInjective (identity_morph for A,X is unique)
        false  // Not typeNameLike
    );

    defineGlobal("compose_morph",
        Pi("A", Icit.Impl, CatTerm(), A_val =>
            Pi("X", Icit.Impl, ObjTerm(A_val), X_val =>
                Pi("Y", Icit.Impl, ObjTerm(A_val), Y_val =>
                    Pi("Z", Icit.Impl, ObjTerm(A_val), Z_val =>
                        Pi("g", Icit.Expl, HomTerm(A_val, Y_val, Z_val), _g_val =>
                            Pi("f", Icit.Expl, HomTerm(A_val, X_val, Y_val), _f_val =>
                                HomTerm(A_val, X_val, Z_val)
                            )
                        )
                    )
                )
            )
        ),
        undefined, // No specific lambda term value for the general constant.
        false, // Not a constant symbol (it's a complex operation that can compute)
        false, // Not generally injective as a symbol. Specific instances might be.
        false  // Not typeNameLike
    );

    // --- Rewrite Rules for mkCat_ ---
    // Obj (mkCat_ O H C) X  ==>  O  (where X is an object of the category, but for Obj it's just the representation)
    // This rule means: (Obj (mkCat_ O H C)) reduces to O
    addRewriteRule(
        "Obj_mkCat_eval",
        ["$O", "$H", "$C"], // Pattern variables
        ObjTerm(App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl)), // LHS: Obj (mkCat_ $O $H $C)
        Var("$O"), // RHS: $O
        emptyCtx
    );

    // Hom (mkCat_ O H C) X Y  ==>  H X Y
    addRewriteRule(
        "Hom_mkCat_eval",
        ["$O", "$H", "$C", "$X", "$Y"],
        HomTerm(
            App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl), // Cat argument
            Var("$X"), // Dom argument
            Var("$Y")  // Cod argument
        ),
        App(App(Var("$H"), Var("$X"), Icit.Expl), Var("$Y"), Icit.Expl), // RHS: $H $X $Y
        emptyCtx
    );

    // compose_morph {mkCat_ O H C} g f ==> C g f (if C is the compose_impl for mkCat_)
    // This rule means: compose_morph applied to a category defined by mkCat_ uses the provided compose_impl.
    // LHS: compose_morph {A = mkCat_ $O $H $C} ...
    // The implicit arguments for compose_morph for X,Y,Z are tricky to represent directly in simple rule LHS if they depend on mkCat_.
    // A simpler rule: compose_morph {mkCat_ $O $H $C} (g) (f)
    // The `compose_impl` argument to `mkCat_` is $C.
    // So, `compose_morph` for a category `mkCat_ $O $H $C` should effectively be `$C`.
    // We define `compose_morph {A=mkCat_ O H Comp}` to be `Comp`.
    addRewriteRule(
        "compose_mkCat_eval",
        ["$O", "$H", "$C"], // $C is the compose_impl
        // LHS: (compose_morph {mkCat_ $O $H $C}) - this is the function part, before args X,Y,Z,g,f
        // This rule targets the instance of compose_morph for a specific category.
        App(Var("compose_morph"), // compose_morph
            App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl), // {catA = mkCat_ $O $H $C}
            Icit.Impl), // Specify implicit application for the category argument
        Var("$C"), // RHS: The compose_impl function $C itself
        emptyCtx
    );


    // --- Basic Category Laws (as rewrite rules) ---
    // f ∘ idX = f  (compose_morph f (identity_morph X))
    addRewriteRule(
        "comp_f_idX_fwd",
        ["$A_cat", "$X_obj", "$Y_obj", "$f_morph"],
        App(App(App(App(App(App( // compose_morph {A} {X} {X} {Y} f (identity_morph {A} X)
            Var("compose_morph"), Var("$A_cat"), Icit.Impl),
            Var("$X_obj"), Icit.Impl),
            Var("$X_obj"), Icit.Impl), // Y argument to compose_morph is X_obj here
            Var("$Y_obj"), Icit.Impl),
            Var("$f_morph"), Icit.Expl), // g argument (f in f o id)
            App(App(Var("identity_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Expl), Icit.Expl), // f argument (idX in f o id)
        Var("$f_morph"), // RHS
        emptyCtx
    );

    // idY ∘ f = f  (compose_morph (identity_morph Y) f)
    addRewriteRule(
        "comp_idY_f_fwd", // Renamed from "comp_idY_f_fwd_new"
        ["$A_cat", "$X_obj", "$Y_obj", "$f_morph"],
        App(App(App(App(App(App( // compose_morph {A} {X} {Y} {Y} (identity_morph {A} Y) f
            Var("compose_morph"), Var("$A_cat"), Icit.Impl),
            Var("$X_obj"), Icit.Impl),
            Var("$Y_obj"), Icit.Impl),
            Var("$Y_obj"), Icit.Impl), // Z argument to compose_morph is Y_obj here
            App(App(Var("identity_morph"), Var("$A_cat"), Icit.Impl), Var("$Y_obj"), Icit.Expl), Icit.Expl), // g argument (idY in idY o f)
            Var("$f_morph"), Icit.Expl), // f argument
        Var("$f_morph"), // RHS
        emptyCtx
    );

    // Unification rule example (from original core_context_globals)
    // This rule states that if (fmap1 (hom_cov A W) a f) is unified with (compose_morph a f),
    // it's a match, and a trivial constraint (Type=Type) is added (effect_Empty_Constraint).
    // This essentially makes them definitionally equal for unification purposes.
    const unifRule_homCov_compose_PatternVars = ["$A_cat", "$W_obj", "$X_obj", "$Y_obj", "$Z_obj", "$a_morph", "$f_morph"];
    // LHS1: fmap1 (HomCovFunctorIdentity $A_cat $W_obj) $a_morph $f_morph
    // Assuming implicit arguments for fmap1 are filled correctly by the system or are holes.
    // FMap1Term(functor, morphism_a, catA, catB, objX_A, objY_A)
    // Functor is HomCovFunctorIdentity $A_cat $W_obj
    // Morphism_a is $a_morph (type Hom $A_cat $Y_obj $Z_obj)
    // The $f_morph is the argument to this resulting function.
    // So it's App ( FMap1Term(HomCovFunctorIdentity $A_cat $W_obj, $a_morph, $A_cat, Set, $Y_obj, $Z_obj) , $f_morph)
    const unifRule_LHS1 = App(
        FMap1Term(
            HomCovFunctorIdentity(Var("$A_cat"), Var("$W_obj")), // Functor part
            Var("$a_morph"), // Morphism part (a) that HomCovFunctor acts on
            Var("$A_cat"), SetTerm(), // Implicit catA, catB
            Var("$Y_obj"), Var("$Z_obj") // Implicit objX_A, objY_A (domain/codomain of $a_morph)
        ),
        Var("$f_morph") // Argument f to the result of FMap1
    );
    // LHS2: compose_morph {$A_cat} {$X_obj} {$Y_obj} {$Z_obj} $a_morph $f_morph
    const unifRule_LHS2 = App(App(App(App(App(App(
        Var("compose_morph"), Var("$A_cat"), Icit.Impl),
        Var("$X_obj"), Icit.Impl),
        Var("$Y_obj"), Icit.Impl),
        Var("$Z_obj"), Icit.Impl),
        Var("$a_morph"), Icit.Expl),
        Var("$f_morph"), Icit.Expl
    );

    addUnificationRule({
        name: "unif_hom_cov_fapp1_compose_vs_compose_morph",
        patternVars: unifRule_homCov_compose_PatternVars,
        lhsPattern1: unifRule_LHS1,
        lhsPattern2: unifRule_LHS2,
        rhsNewConstraints: [{ t1: Type(), t2: Type() }] // Trivial constraint
    });
}

/**
 * Sets up Category Theory primitives like Set category, hom_cov functor, and naturality rules.
 * @param ctx Context (usually emptyCtx for global setup).
 */
function setupCatTheoryPrimitives(ctx: Context) {
    // Define Set as a category with value SetTerm()
    // This ensures "Set" refers to the kernel SetTerm.
    defineGlobal("Set", CatTerm(), SetTerm(), false, true, true, false);
                // name, type,    value, isConst, isInj, isTypeNameLike, elabType

    // hom_cov Functor: Hom_A(W, -) : A -> Set
    defineGlobal("hom_cov",
        Pi("A", Icit.Impl, CatTerm(), A_cat_val =>              // {A : Cat} ->
            Pi("W", Icit.Expl, ObjTerm(A_cat_val), _W_obj_val => // (W : Obj A) ->
                FunctorTypeTerm(A_cat_val, SetTerm())           // Functor A Set
            )
        ),
        Lam("A_cat_impl_arg", Icit.Impl, CatTerm(), A_cat_term => // {A_val} =>
            Lam("W_obj_expl_arg", Icit.Expl, ObjTerm(A_cat_term), W_obj_term => // W_val =>
                HomCovFunctorIdentity(A_cat_term, W_obj_term) // HomCovFunctorIdentity(A_val, W_val)
            )
        ),
        false, true, false, false // Not constant, is injective, not typeNameLike, type is already fine
    );

    // Naturality rule (direct version from Lambdapi spec):
    // ϵ._X _∘> G a  ↪  (F a) _∘> ϵ._X'
    // Lambdapi: rule fapp1 (hom_cov _) (@fapp1 _ _ $G $X $X' $a) (@tapp _ _ $F $G $ϵ $X)
    //             ↪ fapp1 (hom_cov _) (tapp $ϵ $X') (fapp1 $F $a);
    // Translation:
    // LHS: App( FMap1Term(HomCovFunctorIdentity FH FH, FH(), FH(), FH(), FH(), FH()),   -- hom_cov _ (outermost application)
    //            FMap1Term(Var("$G_func"), Var("$a_morph"), FH(), FH(), Var("$X_obj"), Var("$X_prime_obj")), -- G a
    //            NatTransComponentTerm(Var("$eps_transf"), Var("$X_obj"), FH(), FH(), Var("$F_func"), Var("$G_func")) -- ϵ._X
    //          )
    // RHS: App( FMap1Term(HomCovFunctorIdentity FH FH, FH(), FH(), FH(), FH(), FH()),
    //            NatTransComponentTerm(Var("$eps_transf"), Var("$X_prime_obj"), FH(), FH(), Var("$F_func"), Var("$G_func")), -- ϵ._X'
    //            FMap1Term(Var("$F_func"), Var("$a_morph"), FH(), FH(), Var("$X_obj"), Var("$X_prime_obj")) -- F a
    //          )
    // The FH() are placeholders for implicit category/object arguments that should be filled by unification
    // during rule matching or inferred during rule elaboration.
    // For rewrite rule definition, these need to be consistent or use pattern variables if they vary.
    // The Lambdapi rule `fapp1 (hom_cov _)` implies the outer structure is `App (fmap1 (hom_cov W) Y_Z_morph) X_morph`
    // The rule `fapp1 (hom_cov _)` is for `Hom Set (hom_cov W Y) (hom_cov W Z)`.
    // `fapp1 (hom_cov W) a` is `λf. a ∘ f`.
    // So `(fapp1 (hom_cov W) Ga) (eps_X)` is `Ga ∘ eps_X`. (Here W is target of eps_X, domain of Ga).
    // `(fapp1 (hom_cov W) eps_X') (Fa)` is `eps_X' ∘ Fa`.

    const userPatternVars_NatDirect = [
        "$A_cat", "$B_cat", // Domain and codomain categories for F, G
        "$F_func", "$G_func", // Functors F, G : A -> B
        "$eps_transf",        // Natural transformation eps : F => G
        "$X_obj", "$X_prime_obj", // Objects X, X' in A
        "$a_morph",           // Morphism a : X -> X' in A
        // Implicitly, there's an object W in B involved in hom_cov B W.
        // Let's make W explicit if needed or use FH() if it's truly "any W".
        // The rule `fapp1 (hom_cov _)` in Lambdapi refers to `fapp1` of `Functor A Set`.
        // The `hom_cov _` is the functor `Hom_B(W,-) : B -> Set`.
        // So the first argument to `fapp1` (the functor) is `HomCovFunctorIdentity(Var("$B_cat"), SOME_OBJECT_IN_B)`.
        // Let this `SOME_OBJECT_IN_B` be `FMap0Term(Var("$F_func"), Var("$X_obj"))` based on the rule structure.
        "$W_obj_in_B" // Represents F(X) or similar, object in B for Hom_B(W,-)
    ];

    // LHS: compose_morph {B} {F X} {G X} {G X'} (G a) (eps_X)
    // This means: NatTransComponent(eps, X) : Hom B (F X) (G X)
    //             FMap1(G, a)             : Hom B (G X) (G X')
    // The composition is in category B.
    const LHS_NatDirect = App(App(App(App(App(App(
        Var("compose_morph"), Var("$B_cat"), Icit.Impl),                                   // compose_morph {B}
        FMap0Term(Var("$F_func"), Var("$X_obj"), Var("$A_cat"), Var("$B_cat")), Icit.Impl), // {FX}
        FMap0Term(Var("$G_func"), Var("$X_obj"), Var("$A_cat"), Var("$B_cat")), Icit.Impl), // {GX}
        FMap0Term(Var("$G_func"), Var("$X_prime_obj"), Var("$A_cat"), Var("$B_cat")), Icit.Impl), // {GX'}
        FMap1Term(Var("$G_func"), Var("$a_morph"), Var("$A_cat"), Var("$B_cat"), Var("$X_obj"), Var("$X_prime_obj")), Icit.Expl), // (G a)
        NatTransComponentTerm(Var("$eps_transf"), Var("$X_obj"), Var("$A_cat"), Var("$B_cat"), Var("$F_func"), Var("$G_func")), Icit.Expl); // (eps_X)
    

    // RHS: compose_morph {B} {F X} {F X'} {G X'} (eps_X') (F a)
    const RHS_NatDirect = App(App(App(App(App(App(
        Var("compose_morph"), Var("$B_cat"), Icit.Impl),                                   // compose_morph {B}
        FMap0Term(Var("$F_func"), Var("$X_obj"), Var("$A_cat"), Var("$B_cat")), Icit.Impl), // {FX}
        FMap0Term(Var("$F_func"), Var("$X_prime_obj"), Var("$A_cat"), Var("$B_cat")), Icit.Impl), // {FX'}
        FMap0Term(Var("$G_func"), Var("$X_prime_obj"), Var("$A_cat"), Var("$B_cat")), Icit.Impl), // {GX'}
        NatTransComponentTerm(Var("$eps_transf"), Var("$X_prime_obj"), Var("$A_cat"), Var("$B_cat"), Var("$F_func"), Var("$G_func")), Icit.Expl), // (eps_X')
        FMap1Term(Var("$F_func"), Var("$a_morph"), Var("$A_cat"), Var("$B_cat"), Var("$X_obj"), Var("$X_prime_obj")), Icit.Expl); // (F a)
    

    addRewriteRule(
        "naturality_direct_compose", // Name reflects structure from LP spec
        userPatternVars_NatDirect,
        LHS_NatDirect,
        RHS_NatDirect,
        ctx // emptyCtx for global rules
    );
}


/**
 * Resets the Emdash system and sets up all predefined globals and rules.
 * This is the main function to initialize a standard Emdash environment.
 */
export function resetMyLambdaPi_Emdash() {
    resetMyLambdaPi(); // Basic reset
    setupPhase1GlobalsAndRules(); // Core category definitions
    setupCatTheoryPrimitives(emptyCtx); // More category theory, e.g. Set, hom_cov
    consoleLog("Emdash system initialized with prelude.");
}