import {
    Term, Context, GlobalDef, RewriteRule, PatternVarDecl, UnificationRule, Icit,
    Type, Var, Lam, App, Pi, Hole,
    CatTerm, ObjTerm, HomTerm,
    FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm, NatTransComponentTerm, SetTerm, HomCovFunctorIdentity
} from './core_types';
import {
    globalDefs, userRewriteRules, userUnificationRules, constraints, emptyCtx,
    freshHoleName, freshVarName, resetVarId, resetHoleId, setDebugVerbose,
    cloneTerm, getTermRef, extendCtx, consoleLog, printTerm, solveConstraintsControl, // Added printTerm, solveConstraintsControl
    lookupCtx
} from './core_state'; // Import from the new state file
import { whnf, solveConstraints, areEqual } from './core_logic'; // For defineGlobal, addRewriteRule
import { infer, check } from './core_elaboration'; // For defineGlobal, addRewriteRule

// Re-export functions that depend on imports from core_logic and core_elaboration

export function defineGlobal(name: string, type: Term, value?: Term, isConstantSymbol: boolean = false, isInjective?: boolean, isTypeNameLike?: boolean, toElaborateType: boolean = false) {
    if (globalDefs.has(name)) console.warn(`Warning: Redefining global ${name}`);
    if (isConstantSymbol && value !== undefined) {
        throw new Error(`Constant symbol ${name} cannot have a definition/value.`);
    }

    const originalConstraintsBackup = [...constraints];
    constraints.length = 0;

    let elabCtx: Context = emptyCtx;
    globalDefs.forEach(gDef => {
        elabCtx = extendCtx(elabCtx, gDef.name, gDef.type, Icit.Expl, gDef.value);
    });

    let elaboratedType: Term;
    let elaboratedValue: Term | undefined = undefined;

    try {
        elaboratedType = check(elabCtx, type, Type());
        elaboratedType = toElaborateType ? whnf(getTermRef(elaboratedType), elabCtx) : type;

        if (value !== undefined) {
            const valueToCheck = cloneTerm(value);
            constraints.length = 0;
            const checkedValueResult = check(elabCtx, valueToCheck, elaboratedType, 0);

            if (!solveConstraints(elabCtx)) {
                const remaining = constraints.map(c => `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`).join('; ');
                throw new Error(`Global '${name}': Value '${printTerm(value)}' does not type check against declared type '${printTerm(elaboratedType)}'. Unsolved constraints: ${remaining}`);
            }
            elaboratedValue = getTermRef(checkedValueResult);
        }
        
        console.log('defineGlobal> ', { name: name + (isConstantSymbol ? ' (constant symbol)' : '')
            + (isInjective ? ' (injective)' : ''),
            type: printTerm(elaboratedType), value: elaboratedValue ? printTerm(elaboratedValue) : 'undefined' });

        globalDefs.set(name, { name, type: elaboratedType, value: elaboratedValue, isConstantSymbol, isInjective, isTypeNameLike });

    } catch (e) {
        const error = e as Error;
        console.error(`Failed to define global '${name}': ${error.message}. Stack: ${error.stack}`);
        constraints.splice(0, constraints.length, ...originalConstraintsBackup);
        throw e;
    } finally {
        constraints.splice(0, constraints.length, ...originalConstraintsBackup);
    }
}

export function addRewriteRule(
    ruleName: string,
    userPatternVars: PatternVarDecl[],
    rawLhsTerm: Term,
    rawRhsTerm: Term,
    ctx: Context
) {
    const originalConstraintsBackup = [...constraints];
    constraints.length = 0;

    let elaboratedLhs: Term;
    let elaboratedRhs: Term;
    const solvedPatVarTypes = new Map<PatternVarDecl, Term>();

    try {
        const lhsToElaborate = cloneTerm(rawLhsTerm);
        let lhsElabCtx: Context = [...ctx];
        for (const pVarName of userPatternVars) {
            if (!pVarName.startsWith('$')) throw new Error(`Pattern variable ${pVarName} in rule '${ruleName}' must start with '$'.`);
            lhsElabCtx = extendCtx(lhsElabCtx, pVarName, Hole(freshHoleName() + "_type_pvar_" + pVarName.substring(1)), Icit.Expl);
        }

        infer(lhsElabCtx, lhsToElaborate, 0);

        if (!solveConstraints(lhsElabCtx)) {
            const remaining = constraints.map(c => `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`).join('; ');
            throw new Error(`Rule '${ruleName}' LHS pattern (${printTerm(rawLhsTerm)}) is ill-typed or inconsistent. Unsolved constraints: ${remaining}`);
        }
        elaboratedLhs = getTermRef(lhsToElaborate);

        for (const pVarName of userPatternVars) {
            const binding = lookupCtx(lhsElabCtx, pVarName);
            if (binding) {
                 solvedPatVarTypes.set(pVarName, getTermRef(binding.type));
            } else {
                 console.warn(`Pattern variable ${pVarName} not found in LHS elaboration context for rule '${ruleName}'.`);
                 solvedPatVarTypes.set(pVarName, Hole(freshHoleName() + "_type_pvar_unfound_" + pVarName.substring(1)));
            }
        }

        const rhsToElaborate = cloneTerm(rawRhsTerm);
        let rhsElabCtx: Context = [...ctx];
        for (const pVarName of userPatternVars) {
            const pVarType = solvedPatVarTypes.get(pVarName) || Hole(freshHoleName() + "_type_pvar_rhs_missing_" + pVarName.substring(1));
            rhsElabCtx = extendCtx(rhsElabCtx, pVarName, pVarType, Icit.Expl);
        }

        constraints.length = 0;
        const typeOfGlobalLhs = infer(lhsElabCtx, elaboratedLhs, 0);
         if (!solveConstraints(ctx)) {
            throw new Error(`Rule '${ruleName}': Could not establish a consistent global type for the elaborated LHS ${printTerm(elaboratedLhs)}.`);
        }
        const targetRhsType = whnf(getTermRef(typeOfGlobalLhs.type), ctx);

        constraints.length = 0;
        check(rhsElabCtx, rhsToElaborate, targetRhsType, 0);

        if (!solveConstraints(rhsElabCtx)) {
            const remaining = constraints.map(c => `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`).join('; ');
            throw new Error(`Rule '${ruleName}' RHS (${printTerm(rawRhsTerm)}) is ill-typed or does not match LHS type (${printTerm(targetRhsType)}). Unsolved constraints: ${remaining}`);
        }
        elaboratedRhs = getTermRef(rhsToElaborate);

        userRewriteRules.push({ name: ruleName, patternVars: userPatternVars, elaboratedLhs, elaboratedRhs });
        console.log(`Rule '${ruleName}' added and elaborated successfully.`,
            `elaboratedLhs: ${printTerm(elaboratedLhs)}`,
            `elaboratedRhs: ${printTerm(elaboratedRhs)}`
        );

    } catch (e) {
        console.error(`Failed to add rewrite rule '${ruleName}': ${(e as Error).message}. Stack: ${(e as Error).stack}`);
    } finally {
        constraints.splice(0, constraints.length, ...originalConstraintsBackup);
    }
}

export function addUnificationRule(rule: UnificationRule) {
    userUnificationRules.push(rule);
}

export function resetMyLambdaPi() {
    constraints.length = 0;
    globalDefs.clear();
    userRewriteRules.length = 0;
    userUnificationRules.length = 0;
    resetVarId();
    resetHoleId();
    setDebugVerbose(false);
}

export function setupPhase1GlobalsAndRules() {
    defineGlobal("NatType", Type(), undefined, true, true, true);
    defineGlobal("BoolType", Type(), undefined, true, true, true);

    defineGlobal("Cat", Type(), CatTerm(), false, true, false);

    defineGlobal("Set", CatTerm(), SetTerm(), false, true, false);

    defineGlobal("Obj",
        Pi("A", Icit.Expl, CatTerm(), _A => Type()),
        Lam("A_val", Icit.Expl, CatTerm(), A_term => ObjTerm(A_term)),
        false, true, false
    );

    defineGlobal("Hom",
        Pi("A", Icit.Impl, CatTerm(), A_val =>
            Pi("X", Icit.Expl, ObjTerm(A_val), _X =>
                Pi("Y", Icit.Expl, ObjTerm(A_val), _Y => Type()))),
        Lam("A_val", Icit.Impl, CatTerm(), A_term =>
            Lam("X_val", Icit.Expl, ObjTerm(A_term), X_term =>
                Lam("Y_val", Icit.Expl, ObjTerm(A_term), Y_term =>
                    HomTerm(A_term, X_term, Y_term)))),
        false, true, false
    );

    defineGlobal("Functor",
        Pi("A", Icit.Expl, CatTerm(), _A =>
            Pi("B", Icit.Expl, CatTerm(), _B => CatTerm())),
        Lam("A_val", Icit.Expl, CatTerm(), A_term =>
            Lam("B_val", Icit.Expl, CatTerm(), B_term =>
                FunctorCategoryTerm(A_term, B_term))),
        false, true, false
    );

    defineGlobal("Transf",
        Pi("A", Icit.Impl, CatTerm(), A_val =>
            Pi("B", Icit.Impl, CatTerm(), B_val =>
                Pi("F", Icit.Expl, ObjTerm(FunctorCategoryTerm(A_val, B_val)), _F =>
                    Pi("G", Icit.Expl, ObjTerm(FunctorCategoryTerm(A_val, B_val)), _G => Type())))),
        Lam("A_val", Icit.Impl, CatTerm(), A_term =>
            Lam("B_val", Icit.Impl, CatTerm(), B_term =>
                Lam("F_val", Icit.Expl, ObjTerm(FunctorCategoryTerm(A_term, B_term)), F_term =>
                    Lam("G_val", Icit.Expl, ObjTerm(FunctorCategoryTerm(A_term, B_term)), G_term =>
                        NatTransTypeTerm(A_term, B_term, F_term, G_term))))),
        false, true, false
    );

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
        undefined,
        true,
        true,
        false
    );

    defineGlobal("identity_morph",
        Pi("A", Icit.Impl, CatTerm(), A_val =>
            Pi("X", Icit.Expl, App(Var("Obj"), A_val, Icit.Expl), X_val =>
                App(App(App(Var("Hom"), A_val, Icit.Impl), X_val, Icit.Expl), X_val, Icit.Expl)
            )
        ),
        undefined,
        false,
        true,
        false
    );

    defineGlobal("compose_morph",
        Pi("A", Icit.Impl, CatTerm(), A_val =>
            Pi("X", Icit.Impl, App(Var("Obj"), A_val, Icit.Expl), X_val =>
                Pi("Y", Icit.Impl, App(Var("Obj"), A_val, Icit.Expl), Y_val =>
                    Pi("Z", Icit.Impl, App(Var("Obj"), A_val, Icit.Expl), Z_val =>
                        Pi("g", Icit.Expl, App(App(App(Var("Hom"), A_val, Icit.Impl), Y_val, Icit.Expl), Z_val, Icit.Expl), _ =>
                            Pi("f", Icit.Expl, App(App(App(Var("Hom"), A_val, Icit.Impl), X_val, Icit.Expl), Y_val, Icit.Expl), _ =>
                                App(App(App(Var("Hom"), A_val, Icit.Impl), X_val, Icit.Expl), Z_val, Icit.Expl)
                            )
                        )
                    )
                )
            )
        ),
        undefined,
        false,
        false,
        false
    );

    addRewriteRule(
        "Obj_mkCat_eval",
        ["$O", "$H", "$C"],
        // App(Var("Obj"), App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl), Icit.Expl),
        ObjTerm(App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl)),
        Var("$O"),
        emptyCtx
    );

    addRewriteRule(
        "Hom_mkCat_eval",
        ["$O", "$H", "$C", "$X", "$Y"],
        // App(
        //     App(
        //         App(
        //             Var("Hom"),
        //             App(App(App(Var("mkCat_"), Var("$O"), Icit.Expl), Var("$H"), Icit.Expl), Var("$C"), Icit.Expl),
        //             Icit.Impl
        //         ),
        //         Var("$X"),
        //         Icit.Expl
        //     ),
        //     Var("$Y"),
        //     Icit.Expl
        // ),
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

    addRewriteRule(
        "comp_f_idX_fwd",
        ["$A_cat", "$X_obj", "$Y_obj", "$f"],
        App(App(App(App(App(App(Var("compose_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl), Var("$f"), Icit.Expl), App(App(Var("identity_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Expl), Icit.Expl),
        Var("$f"),
        emptyCtx
    );

    addRewriteRule(
        "comp_idY_f_fwd_new",
        ["$A_cat", "$X_obj", "$Y_obj", "$f"],
        App(App(App(App(App(App(Var("compose_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl), App(App(Var("identity_morph"), Var("$A_cat"), Icit.Impl), Var("$Y_obj"), Icit.Expl), Icit.Expl), Var("$f"), Icit.Expl),
        Var("$f"),
        emptyCtx
    );

    const unifRule_homCov_compose_PatternVars = ["$A_cat", "$W_obj", "$X_obj", "$Y_obj", "$Z_obj", "$a_morph", "$f_morph"];
    const unifRule_LHS1 = App(
        FMap1Term(
            App(App(Var("hom_cov"), Var("$A_cat"), Icit.Impl), Var("$W_obj"), Icit.Expl),
            Var("$a_morph"),
            Var("$A_cat"),
            SetTerm(),
            Var("$Y_obj"),
            Var("$Z_obj")
        ),
        Var("$f_morph")
    );
    const unifRule_LHS2 = App(App(App(App(App(App(Var("compose_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl), Var("$Z_obj"), Icit.Impl), Var("$a_morph"), Icit.Expl), Var("$f_morph"), Icit.Expl);

    addUnificationRule({
        name: "unif_hom_cov_fapp1_compose",
        patternVars: unifRule_homCov_compose_PatternVars,
        lhsPattern1: unifRule_LHS1,
        lhsPattern2: unifRule_LHS2,
        rhsNewConstraints: [{ t1: Type(), t2: Type() }]
    });
}

export function setupCatTheoryPrimitives(ctx: Context) {
    defineGlobal("Set", CatTerm(), SetTerm(), false, true, false, false); 

    defineGlobal("hom_cov",
        Pi("A", Icit.Impl, CatTerm(), A_cat_val =>
            Pi("W", Icit.Expl, ObjTerm(A_cat_val), _W_obj_val =>
                ObjTerm(FunctorCategoryTerm(A_cat_val, SetTerm()))
            )
        ),
        Lam("A_cat_impl_arg", Icit.Impl, CatTerm(), A_cat_term =>
            Lam("W_obj_expl_arg", Icit.Expl, ObjTerm(A_cat_term), W_obj_term =>
                HomCovFunctorIdentity(A_cat_term, W_obj_term)
            )
        ),
        false, true, false, false 
    );

    const pva = (name: string) => Var(name, false); 

    const userPatternVars_NatDirect = [
        "$A_cat", "$W_obj", "$F_func", "$G_func",
        "$eps_transf", "$X_obj", "$X_prime_obj", "$a_morph"
    ];

    const LHS_NatDirect = App(
        FMap1Term(
            HomCovFunctorIdentity(pva("$A_cat"), pva("$W_obj")),
            FMap1Term(
                pva("$G_func"), pva("$a_morph"),
                pva("$A_cat"), SetTerm(), pva("$X_obj"), pva("$X_prime_obj")
            ),
            pva("$A_cat"), SetTerm(), 
            FMap0Term(pva("$G_func"), pva("$X_obj"), pva("$A_cat"), SetTerm()),
            FMap0Term(pva("$G_func"), pva("$X_prime_obj"), pva("$A_cat"), SetTerm())
        ),
        NatTransComponentTerm(
            pva("$eps_transf"), pva("$X_obj"),
            pva("$A_cat"), SetTerm(), pva("$F_func"), pva("$G_func")
        ),
        Icit.Expl 
    );

    const RHS_NatDirect = App(
        FMap1Term(
            HomCovFunctorIdentity(pva("$A_cat"), pva("$W_obj")),
            FMap1Term(
                pva("$F_func"), pva("$a_morph"), 
                pva("$A_cat"), SetTerm(), pva("$X_obj"), pva("$X_prime_obj")
            ),
            pva("$A_cat"), SetTerm(),
            FMap0Term(pva("$F_func"), pva("$X_obj"), pva("$A_cat"), SetTerm()),
            FMap0Term(pva("$F_func"), pva("$X_prime_obj"), pva("$A_cat"), SetTerm())
        ),
        NatTransComponentTerm(
            pva("$eps_transf"), pva("$X_prime_obj"), 
            pva("$A_cat"), SetTerm(), pva("$F_func"), pva("$G_func")
        ),
        Icit.Expl
    );

    addRewriteRule(
        "naturality_direct_hom_cov_fapp1_tapp",
        userPatternVars_NatDirect,
        LHS_NatDirect,
        RHS_NatDirect,
        ctx 
    );
}

export function resetMyLambdaPi_Emdash() { 
    resetMyLambdaPi();
    setupPhase1GlobalsAndRules(); 
    setupCatTheoryPrimitives(emptyCtx);
} 

// It seems the following exports were intended to be available for other modules from core_state originally
// but since core_context_globals is the one orchestrating defineGlobal etc., they are re-exported here if needed elsewhere.
export {
    globalDefs, userRewriteRules, userUnificationRules, constraints, emptyCtx,
    freshHoleName, freshVarName, resetVarId, resetHoleId, setDebugVerbose,
    cloneTerm, getTermRef, extendCtx, consoleLog, printTerm, solveConstraintsControl
} from './core_state';