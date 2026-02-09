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
    SetTerm, HomCovFunctorIdentity, FunctorTypeTerm, MkFunctorTerm, BinderMode, LamMode, PiMode, TApp1FApp0Term,
    CatCategoryTerm, CatdCategoryTerm, FunctordCategoryTerm, FunctorCatdTerm, TransfCategoryTerm, TransfCatdTerm, TransfdCategoryTerm
} from './types';
import {
    globalDefs, userRewriteRules, userUnificationRules, constraints, emptyCtx,
    resetVarId, resetHoleId, getTermRef, setDebugVerbose, consoleLog, resetFlags,
    printTerm
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
    defineGlobal("Cat_cat", CatTerm(), CatCategoryTerm(), false, true);
    defineGlobal("Catd_cat",
        Pi("Z", Icit.Expl, CatTerm(), Z => CatTerm()),
        Lam("Z_val", Icit.Expl, CatTerm(), Z_term => CatdCategoryTerm(Z_term)),
        false, true
    );

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

    defineGlobal("Transf_cat",
        Pi("A", Icit.Expl, CatTerm(), A =>
        Pi("B", Icit.Expl, CatTerm(), B =>
        Pi("F", Icit.Expl, ObjTerm(FunctorCategoryTerm(A, B)), F =>
        Pi("G", Icit.Expl, ObjTerm(FunctorCategoryTerm(A, B)), G =>
            CatTerm())))),
        Lam("A_val", Icit.Expl, CatTerm(), A_term =>
            Lam("B_val", Icit.Expl, CatTerm(), B_term =>
                Lam("F_val", Icit.Expl, ObjTerm(FunctorCategoryTerm(A_term, B_term)), F_term =>
                    Lam("G_val", Icit.Expl, ObjTerm(FunctorCategoryTerm(A_term, B_term)), G_term =>
                        TransfCategoryTerm(A_term, B_term, F_term, G_term)
                    )))),
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

    // Minimal displayed shell (emdash2-oriented typing interface).
    defineGlobal("Catd",
        Pi("Z", Icit.Expl, CatTerm(), _ => Type()),
        undefined, true, true
    );

    const CatdOf = (Z: Term): Term => App(Var("Catd"), Z, Icit.Expl);
    const FibreOf = (Z: Term, E: Term, z: Term): Term =>
        App(App(App(Var("Fibre"), Z, Icit.Expl), E, Icit.Expl), z, Icit.Expl);
    const FunctordOf = (Z: Term, E: Term, D: Term): Term =>
        App(App(App(Var("Functord"), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl);
    const CatConstCatdOf = (Z: Term): Term =>
        App(Var("CatConst_catd"), Z, Icit.Expl);
    const CatAtOf = (Z: Term, z: Term): Term =>
        ObjTerm(FibreOf(Z, CatConstCatdOf(Z), z));

    // Constant displayed family of categories over a base.
    // Temporary hardcoded surrogate for a weakening-based construction.
    defineGlobal("CatConst_catd",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
            CatdOf(Z)),
        undefined, true, true
    );

    defineGlobal("Fibre",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), _E =>
        Pi("z", Icit.Expl, ObjTerm(Z), _z =>
            CatTerm()))),
        undefined, true, true
    );

    defineGlobal("Functord",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), _E =>
        Pi("D", Icit.Expl, CatdOf(Z), _D =>
            Type()))),
        undefined, true, true
    );

    defineGlobal("Functord_cat",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
        Pi("D", Icit.Expl, CatdOf(Z), D =>
            CatTerm()))),
        Lam("Z_val", Icit.Expl, CatTerm(), Z_term =>
            Lam("E_val", Icit.Expl, CatdOf(Z_term), E_term =>
                Lam("D_val", Icit.Expl, CatdOf(Z_term), D_term =>
                    FunctordCategoryTerm(Z_term, E_term, D_term)
                ))),
        false, true
    );

    defineGlobal("Functor_catd",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
        Pi("D", Icit.Expl, CatdOf(Z), D =>
            CatdOf(Z)))),
        Lam("Z_val", Icit.Expl, CatTerm(), Z_term =>
            Lam("E_val", Icit.Expl, CatdOf(Z_term), E_term =>
                Lam("D_val", Icit.Expl, CatdOf(Z_term), D_term =>
                    FunctorCatdTerm(Z_term, E_term, D_term)
                ))),
        false, true
    );

    defineGlobal("Fibre_func",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
        Pi("D", Icit.Expl, CatdOf(Z), D =>
        Pi("FF", Icit.Expl, FunctordOf(Z, E, D), FF =>
        Pi("z", Icit.Expl, ObjTerm(Z), z =>
            ObjTerm(
                FunctorCategoryTerm(
                    FibreOf(Z, E, z),
                    FibreOf(Z, D, z)
                )
            )))))),
        undefined, true, true
    );

    defineGlobal("fdapp0",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
        Pi("D", Icit.Expl, CatdOf(Z), D =>
        Pi("FF", Icit.Expl, FunctordOf(Z, E, D), _FF =>
        Pi("z", Icit.Expl, ObjTerm(Z), z =>
        Pi("e", Icit.Expl, ObjTerm(FibreOf(Z, E, z)), _e =>
            ObjTerm(FibreOf(Z, D, z)))))))),
        undefined, true, true
    );

    defineGlobal("Transfd",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
        Pi("D", Icit.Expl, CatdOf(Z), D =>
        Pi("FF", Icit.Expl, FunctordOf(Z, E, D), FF =>
        Pi("GG", Icit.Expl, FunctordOf(Z, E, D), _GG =>
            Type()))))),
        undefined, true, true
    );

    defineGlobal("Transfd_cat",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
        Pi("D", Icit.Expl, CatdOf(Z), D =>
        Pi("FF", Icit.Expl, ObjTerm(FunctordCategoryTerm(Z, E, D)), FF =>
        Pi("GG", Icit.Expl, ObjTerm(FunctordCategoryTerm(Z, E, D)), GG =>
            CatTerm()))))),
        Lam("Z_val", Icit.Expl, CatTerm(), Z_term =>
            Lam("E_val", Icit.Expl, CatdOf(Z_term), E_term =>
                Lam("D_val", Icit.Expl, CatdOf(Z_term), D_term =>
                    Lam("FF_val", Icit.Expl, ObjTerm(FunctordCategoryTerm(Z_term, E_term, D_term)), FF_term =>
                        Lam("GG_val", Icit.Expl, ObjTerm(FunctordCategoryTerm(Z_term, E_term, D_term)), GG_term =>
                            TransfdCategoryTerm(Z_term, E_term, D_term, FF_term, GG_term)
                        ))))),
        false, true
    );

    defineGlobal("Transf_catd",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
        Pi("D", Icit.Expl, CatdOf(Z), D =>
        Pi("FF", Icit.Expl, ObjTerm(FunctordCategoryTerm(Z, E, D)), FF =>
        Pi("GG", Icit.Expl, ObjTerm(FunctordCategoryTerm(Z, E, D)), GG =>
            CatdOf(Z)))))),
        Lam("Z_val", Icit.Expl, CatTerm(), Z_term =>
            Lam("E_val", Icit.Expl, CatdOf(Z_term), E_term =>
                Lam("D_val", Icit.Expl, CatdOf(Z_term), D_term =>
                    Lam("FF_val", Icit.Expl, ObjTerm(FunctordCategoryTerm(Z_term, E_term, D_term)), FF_term =>
                        Lam("GG_val", Icit.Expl, ObjTerm(FunctordCategoryTerm(Z_term, E_term, D_term)), GG_term =>
                            TransfCatdTerm(Z_term, E_term, D_term, FF_term, GG_term)
                        ))))),
        false, true
    );

    defineGlobal("tdapp0_fapp0",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
        Pi("D", Icit.Expl, CatdOf(Z), D =>
        Pi("FF", Icit.Expl, FunctordOf(Z, E, D), FF =>
        Pi("GG", Icit.Expl, FunctordOf(Z, E, D), GG =>
        Pi("z", Icit.Expl, ObjTerm(Z), z =>
        Pi("e", Icit.Expl, ObjTerm(FibreOf(Z, E, z)), e =>
        Pi("eps", Icit.Expl, App(App(App(App(App(Var("Transfd"), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), GG, Icit.Expl), _eps =>
            HomTerm(
                FibreOf(Z, D, z),
                App(App(App(App(App(App(Var("fdapp0"), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), z, Icit.Expl), e, Icit.Expl),
                App(App(App(App(App(App(Var("fdapp0"), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), GG, Icit.Expl), z, Icit.Expl), e, Icit.Expl)
            ))))))))),
        undefined, true, true
    );

    // homd_curry-style dependent-hom declaration (type-only milestone).
    const homdCurryBodyType = (Z: Term, E: Term): Term =>
        PiMode("b0", Icit.Expl, ObjTerm(Z), b0 =>
        PiMode("e0", Icit.Expl, ObjTerm(FibreOf(Z, E, b0)), _e0 =>
        PiMode("b1", Icit.Expl, ObjTerm(Z), b1 =>
        PiMode("f", Icit.Expl, HomTerm(Z, b0, b1), _f =>
        PiMode("e1", Icit.Expl, ObjTerm(FibreOf(Z, E, b1)), _e1 =>
            CatAtOf(Z, b1),
            { mode: BinderMode.Natural, controllerCat: Z }
        ), { mode: BinderMode.Natural, controllerCat: Z }
        ), { mode: BinderMode.Functorial, controllerCat: Z }
        ), { mode: BinderMode.Natural, controllerCat: Z }
        ), { mode: BinderMode.Functorial, controllerCat: Z });

    const homdCurryOf = (Z: Term, E: Term, b0: Term, e0: Term, b1: Term, f: Term, e1: Term): Term =>
        App(
            App(
                App(
                    App(
                        App(
                            App(
                                App(Var("homd_curry"), Z, Icit.Expl),
                                E, Icit.Expl
                            ),
                            b0, Icit.Expl
                        ),
                        e0, Icit.Expl
                    ),
                    b1, Icit.Expl
                ),
                f, Icit.Expl
            ),
            e1, Icit.Expl
        );

    defineGlobal("homd_curry",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
            homdCurryBodyType(Z, E))),
        undefined, true, true
    );

    // Stress-test alias: should stay type-identical to homd_curry.
    defineGlobal("alias_homd_",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
            homdCurryBodyType(Z, E))),
        undefined, true, true
    );

    // Displayed off-diagonal action of a displayed functor: FF1[sigma].
    defineGlobal("fdapp1_fapp0",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
        Pi("D", Icit.Expl, CatdOf(Z), D =>
        Pi("FF", Icit.Expl, FunctordOf(Z, E, D), FF =>
        Pi("z", Icit.Expl, ObjTerm(Z), z =>
        Pi("e", Icit.Expl, ObjTerm(FibreOf(Z, E, z)), e =>
        Pi("z'", Icit.Expl, ObjTerm(Z), zPrime =>
        Pi("f", Icit.Expl, HomTerm(Z, z, zPrime), f =>
        Pi("e'", Icit.Expl, ObjTerm(FibreOf(Z, E, zPrime)), ePrime =>
        Pi("sigma", Icit.Expl, ObjTerm(homdCurryOf(Z, E, z, e, zPrime, f, ePrime)), _sigma =>
            ObjTerm(
                homdCurryOf(
                    Z, D,
                    z,
                    App(App(App(App(App(App(Var("fdapp0"), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), z, Icit.Expl), e, Icit.Expl),
                    zPrime,
                    f,
                    App(App(App(App(App(App(Var("fdapp0"), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), zPrime, Icit.Expl), ePrime, Icit.Expl)
                )
            ))))))))))),
        undefined, true, true
    );

    // Displayed off-diagonal component of a displayed transfor: eps_(sigma).
    defineGlobal("tdapp1_fapp0",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
        Pi("D", Icit.Expl, CatdOf(Z), D =>
        Pi("FF", Icit.Expl, FunctordOf(Z, E, D), FF =>
        Pi("GG", Icit.Expl, FunctordOf(Z, E, D), GG =>
        Pi("z", Icit.Expl, ObjTerm(Z), z =>
        Pi("e", Icit.Expl, ObjTerm(FibreOf(Z, E, z)), e =>
        Pi("z'", Icit.Expl, ObjTerm(Z), zPrime =>
        Pi("f", Icit.Expl, HomTerm(Z, z, zPrime), f =>
        Pi("e'", Icit.Expl, ObjTerm(FibreOf(Z, E, zPrime)), ePrime =>
        Pi("sigma", Icit.Expl, ObjTerm(homdCurryOf(Z, E, z, e, zPrime, f, ePrime)), _sigma =>
        Pi("eps", Icit.Expl, App(App(App(App(App(Var("Transfd"), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), GG, Icit.Expl), _eps =>
            ObjTerm(
                homdCurryOf(
                    Z, D,
                    z,
                    App(App(App(App(App(App(Var("fdapp0"), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), z, Icit.Expl), e, Icit.Expl),
                    zPrime,
                    f,
                    App(App(App(App(App(App(Var("fdapp0"), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), GG, Icit.Expl), zPrime, Icit.Expl), ePrime, Icit.Expl)
                )
            ))))))))))))),
        undefined, true, true
    );

    // Eta-expanded stress-test copy with explicit mode-aware lambdas.
    const homdCurryEtaValue =
        LamMode("Z", Icit.Expl, CatTerm(), Z =>
            LamMode("E", Icit.Expl, CatdOf(Z), E =>
                LamMode("b0", Icit.Expl, ObjTerm(Z), b0 =>
                    LamMode("e0", Icit.Expl, ObjTerm(FibreOf(Z, E, b0)), e0 =>
                        LamMode("b1", Icit.Expl, ObjTerm(Z), b1 =>
                            LamMode("f", Icit.Expl, HomTerm(Z, b0, b1), f =>
                                LamMode("e1", Icit.Expl, ObjTerm(FibreOf(Z, E, b1)), e1 =>
                                    App(
                                        App(
                                            App(
                                                App(
                                                    App(
                                                        App(
                                                            App(Var("homd_curry"), Z, Icit.Expl),
                                                            E, Icit.Expl
                                                        ),
                                                        b0, Icit.Expl
                                                    ),
                                                    e0, Icit.Expl
                                                ),
                                                b1, Icit.Expl
                                            ),
                                            f, Icit.Expl
                                        ),
                                        e1, Icit.Expl
                                    ),
                                    { mode: BinderMode.Natural, controllerCat: Z }
                                ),
                                { mode: BinderMode.Natural, controllerCat: Z }
                            ),
                            { mode: BinderMode.Functorial, controllerCat: Z }
                        ),
                        { mode: BinderMode.Natural, controllerCat: Z }
                    ),
                    { mode: BinderMode.Functorial, controllerCat: Z }
                ),
                { mode: BinderMode.Functorial, controllerCat: Z }
            ),
            { mode: BinderMode.Functorial }
        );

    defineGlobal("homd_curry_eta_copy",
        Pi("Z", Icit.Expl, CatTerm(), Z =>
        Pi("E", Icit.Expl, CatdOf(Z), E =>
            homdCurryBodyType(Z, E))),
        homdCurryEtaValue
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

    // Strict accumulation (ordinary off-diagonal transfor components, stable head).
    // Postcomposition: (G g) ∘ ϵ_(f) ↪ ϵ_(g ∘ f)
    const accum_post_vars = [
        "$A_cat", "$B_cat",
        "$F_func", "$G_func",
        "$eps_transf",
        "$X_obj", "$Y_obj", "$Z_obj",
        "$f_morph", "$g_morph"
    ];

    const FX_post = FMap0Term(Var("$F_func"), Var("$X_obj"), Var("$A_cat"), Var("$B_cat"));
    const GY_post = FMap0Term(Var("$G_func"), Var("$Y_obj"), Var("$A_cat"), Var("$B_cat"));
    const GZ_post = FMap0Term(Var("$G_func"), Var("$Z_obj"), Var("$A_cat"), Var("$B_cat"));

    const tapp1_eps_f_post = TApp1FApp0Term(
        Var("$eps_transf"),
        Var("$f_morph"),
        Var("$A_cat"),
        Var("$B_cat"),
        Var("$F_func"),
        Var("$G_func"),
        Var("$X_obj"),
        Var("$Y_obj")
    );
    const fmap1_G_g_post = FMap1Term(
        Var("$G_func"),
        Var("$g_morph"),
        Var("$A_cat"),
        Var("$B_cat"),
        Var("$Y_obj"),
        Var("$Z_obj")
    );

    const lhs_accum_post = App(
        App(
            App(
                App(
                    App(
                        App(
                            Var("compose_morph"),
                            Var("$B_cat"),
                            Icit.Impl
                        ),
                        FX_post,
                        Icit.Impl
                    ),
                    GY_post,
                    Icit.Impl
                ),
                GZ_post,
                Icit.Impl
            ),
            fmap1_G_g_post,
            Icit.Expl
        ),
        tapp1_eps_f_post,
        Icit.Expl
    );

    const compose_g_f_post = App(
        App(
            App(
                App(
                    App(
                        App(
                            Var("compose_morph"),
                            Var("$A_cat"),
                            Icit.Impl
                        ),
                        Var("$X_obj"),
                        Icit.Impl
                    ),
                    Var("$Y_obj"),
                    Icit.Impl
                ),
                Var("$Z_obj"),
                Icit.Impl
            ),
            Var("$g_morph"),
            Icit.Expl
        ),
        Var("$f_morph"),
        Icit.Expl
    );

    const rhs_accum_post = TApp1FApp0Term(
        Var("$eps_transf"),
        compose_g_f_post,
        Var("$A_cat"),
        Var("$B_cat"),
        Var("$F_func"),
        Var("$G_func"),
        Var("$X_obj"),
        Var("$Z_obj")
    );

    addRewriteRule(
        "strict_accumulation_post_tapp1",
        accum_post_vars,
        lhs_accum_post,
        rhs_accum_post,
        ctx
    );

    // Precomposition: ϵ_(f) ∘ (F g) ↪ ϵ_(f ∘ g)
    const accum_pre_vars = [
        "$A_cat", "$B_cat",
        "$F_func", "$G_func",
        "$eps_transf",
        "$W_obj", "$X_obj", "$Y_obj",
        "$g_morph", "$f_morph"
    ];

    const FW_pre = FMap0Term(Var("$F_func"), Var("$W_obj"), Var("$A_cat"), Var("$B_cat"));
    const FX_pre = FMap0Term(Var("$F_func"), Var("$X_obj"), Var("$A_cat"), Var("$B_cat"));
    const GY_pre = FMap0Term(Var("$G_func"), Var("$Y_obj"), Var("$A_cat"), Var("$B_cat"));

    const tapp1_eps_f_pre = TApp1FApp0Term(
        Var("$eps_transf"),
        Var("$f_morph"),
        Var("$A_cat"),
        Var("$B_cat"),
        Var("$F_func"),
        Var("$G_func"),
        Var("$X_obj"),
        Var("$Y_obj")
    );
    const fmap1_F_g_pre = FMap1Term(
        Var("$F_func"),
        Var("$g_morph"),
        Var("$A_cat"),
        Var("$B_cat"),
        Var("$W_obj"),
        Var("$X_obj")
    );

    const lhs_accum_pre = App(
        App(
            App(
                App(
                    App(
                        App(
                            Var("compose_morph"),
                            Var("$B_cat"),
                            Icit.Impl
                        ),
                        FW_pre,
                        Icit.Impl
                    ),
                    FX_pre,
                    Icit.Impl
                ),
                GY_pre,
                Icit.Impl
            ),
            tapp1_eps_f_pre,
            Icit.Expl
        ),
        fmap1_F_g_pre,
        Icit.Expl
    );

    const compose_f_g_pre = App(
        App(
            App(
                App(
                    App(
                        App(
                            Var("compose_morph"),
                            Var("$A_cat"),
                            Icit.Impl
                        ),
                        Var("$W_obj"),
                        Icit.Impl
                    ),
                    Var("$X_obj"),
                    Icit.Impl
                ),
                Var("$Y_obj"),
                Icit.Impl
            ),
            Var("$f_morph"),
            Icit.Expl
        ),
        Var("$g_morph"),
        Icit.Expl
    );

    const rhs_accum_pre = TApp1FApp0Term(
        Var("$eps_transf"),
        compose_f_g_pre,
        Var("$A_cat"),
        Var("$B_cat"),
        Var("$F_func"),
        Var("$G_func"),
        Var("$W_obj"),
        Var("$Y_obj")
    );

    addRewriteRule(
        "strict_accumulation_pre_tapp1",
        accum_pre_vars,
        lhs_accum_pre,
        rhs_accum_pre,
        ctx
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

    // --- Equality Primitives ---
    const Eq_type = Pi("A", Icit.Impl, Type(), A =>
        Pi("x", Icit.Expl, A, _ =>
        Pi("y", Icit.Expl, A, _ => Type()))
    );
    defineGlobal("Eq", Eq_type, undefined, true, true);
    const Eq = Var("Eq");

    const refl_type = Pi("A", Icit.Impl, Type(), A =>
        Pi("x", Icit.Impl, A, x =>
            App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), x, Icit.Expl))
    );
    defineGlobal("refl", refl_type, undefined, true, true);
    const refl = Var("refl");

    const Eq_elim_type =
        Pi("A", Icit.Impl, Type(), A =>
        Pi("x", Icit.Impl, A, x =>
        Pi("P", Icit.Expl, Pi("y", Icit.Expl, A, y => Pi("p", Icit.Expl, App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), y, Icit.Expl), _ => Type())), P =>
        Pi("p_refl", Icit.Expl, App(App(P, x, Icit.Expl), App(App(refl, A, Icit.Impl), x, Icit.Impl), Icit.Expl), _ =>
        Pi("y", Icit.Impl, A, y =>
        Pi("p", Icit.Expl, App(App(App(Eq, A, Icit.Impl), x, Icit.Expl), y, Icit.Expl), p_term =>
            App(App(P, y, Icit.Expl), p_term, Icit.Expl)
        ))))));
    defineGlobal("Eq_elim", Eq_elim_type);

    addRewriteRule("Eq_elim_refl", ["$A", "$x", "$P", "$p_refl"],
        App(
            App(
                App(
                    App(
                        App(App(Var("Eq_elim"), Var("$A"), Icit.Impl), Var("$x"), Icit.Impl),
                        Var("$P"), Icit.Expl
                    ),
                    Var("$p_refl"), Icit.Expl
                ),
                Var("$x"), Icit.Impl
            ),
            App(App(refl, Var("$A"), Icit.Impl), Var("$x"), Icit.Impl), Icit.Expl
        ),
        Var("$p_refl"),
        ctx
    );

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

    // Functorial Elaboration Makers
    const Functor_A_B = (A: Term, B: Term) => FunctorTypeTerm(A, B);
    const fmap0_type = (A: Term, B: Term) => Pi("_", Icit.Expl, ObjTerm(A), _ => ObjTerm(B));
    const fmap1_type = (A: Term, B: Term, fmap0_val: Term) => Pi("X", Icit.Impl, ObjTerm(A), X =>
        Pi("Y", Icit.Impl, ObjTerm(A), Y =>
            Pi("a", Icit.Expl, HomTerm(A, X, Y), _ =>
                HomTerm(B, App(fmap0_val, X, Icit.Expl), App(fmap0_val, Y, Icit.Expl))
            )
        )
    );

    const functoriality_proof_type = (A: Term, B: Term, fmap0: Term, fmap1: Term) =>
        Pi("X", Icit.Impl, ObjTerm(A), X =>
        Pi("Y", Icit.Impl, ObjTerm(A), Y =>
        Pi("Z", Icit.Impl, ObjTerm(A), Z =>
        Pi("g", Icit.Expl, HomTerm(A, Y, Z), g_val =>
        Pi("f", Icit.Expl, HomTerm(A, X, Y), f_val => {
            const compose_morph = Var("compose_morph");
            
            // LHS: compose_B (fmap1 g) (fmap1 f)
            const fmap1_g = App(App(App(fmap1, Y, Icit.Impl), Z, Icit.Impl), g_val, Icit.Expl);
            const fmap1_f = App(App(App(fmap1, X, Icit.Impl), Y, Icit.Impl), f_val, Icit.Expl);
            const lhs = App(App(App(App(App(App(compose_morph,
                B, Icit.Impl),
                App(fmap0, X, Icit.Expl), Icit.Impl),
                App(fmap0, Y, Icit.Expl), Icit.Impl),
                App(fmap0, Z, Icit.Expl), Icit.Impl),
                fmap1_g, Icit.Expl),
                fmap1_f, Icit.Expl);

            // RHS: fmap1 (compose_A g f)
            const compose_A_g_f = App(App(App(App(App(App(compose_morph,
                A, Icit.Impl),
                X, Icit.Impl),
                Y, Icit.Impl),
                Z, Icit.Impl),
                g_val, Icit.Expl),
                f_val, Icit.Expl);
            const rhs = App(App(App(fmap1,
                X, Icit.Impl),
                Z, Icit.Impl),
                compose_A_g_f, Icit.Expl);
            
            return App(App(App(Eq, HomTerm(B, App(fmap0, X, Icit.Expl), App(fmap0, Z, Icit.Expl)), Icit.Impl), lhs, Icit.Expl), rhs, Icit.Expl);
        })))));

    defineGlobal("mkFunctor_",
        Pi("A", Icit.Impl, CatTerm(), A =>
        Pi("B", Icit.Impl, CatTerm(), B =>
        Pi("fmap0", Icit.Expl, fmap0_type(A,B), fmap0_val =>
        Pi("fmap1", Icit.Expl, fmap1_type(A, B, fmap0_val), fmap1_val =>
        Pi("functoriality", Icit.Expl, functoriality_proof_type(A, B, fmap0_val, fmap1_val), _ =>
            Functor_A_B(A, B)
        ))))),
        // Value: λ {A} {B} fmap0 fmap1 proof. MkFunctorTerm(A, B, fmap0, fmap1, proof)
        Lam("A", Icit.Impl, CatTerm(), A =>
        Lam("B", Icit.Impl, CatTerm(), B =>
        Lam("fmap0", Icit.Expl, fmap0_type(A,B), fmap0_val =>
        Lam("fmap1", Icit.Expl, fmap1_type(A, B, fmap0_val), fmap1_val =>
        Lam("functoriality", Icit.Expl, functoriality_proof_type(A, B, fmap0_val, fmap1_val), fproof_val =>
            MkFunctorTerm(A, B, fmap0_val, fmap1_val, fproof_val)
        ))))),
        false, true
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
