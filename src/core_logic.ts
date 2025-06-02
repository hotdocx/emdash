import { Term, Context, PatternVarDecl, Substitution, UnifyResult, Icit, Hole, App, Lam, Pi, Var, ObjTerm, HomTerm, Type, CatTerm, FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm, NatTransComponentTerm, HomCovFunctorIdentity, SetTerm } from './core_types';
import {
    getTermRef, consoleLog, globalDefs, userRewriteRules, addConstraint, constraints, emptyCtx, extendCtx, lookupCtx,
    isKernelConstantSymbolStructurally, isEmdashUnificationInjectiveStructurally, userUnificationRules, freshVarName, freshHoleName,
    solveConstraintsControl, printTerm // Added printTerm, removed getDebugVerbose
} from './core_state'; // Import from the new state file
import { matchPattern, applySubst, isPatternVarName } from './core_elaboration'; // For WHNF userRewriteRules and Unification rules

export const MAX_WHNF_ITERATIONS = 10000;
export const MAX_STACK_DEPTH = 20000;

export function areStructurallyEqualNoWhnf(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Structural Equality check depth exceeded (areStructurallyEqualNoWhnf depth: ${depth})`);
    const rt1 = getTermRef(t1);
    const rt2 = getTermRef(t2);

    if (rt1.tag === 'Hole' && rt2.tag === 'Hole') return rt1.id === rt2.id;
    if (rt1.tag === 'Hole' || rt2.tag === 'Hole') return false;
    if (rt1.tag !== rt2.tag) return false;

    // Icit check for relevant terms
    if ((rt1.tag === 'App' || rt1.tag === 'Lam' || rt1.tag === 'Pi') &&
        (rt2.tag === rt1.tag) && rt1.icit !== (rt2 as typeof rt1).icit) {
        return false;
    }

    switch (rt1.tag) {
        case 'Type': case 'CatTerm': return true;
        case 'Var': return rt1.name === (rt2 as Term & {tag:'Var'}).name;
        case 'App': {
            const app2 = rt2 as Term & {tag:'App'};
            return areStructurallyEqualNoWhnf(rt1.func, app2.func, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.arg, app2.arg, ctx, depth + 1);
        }
        case 'Lam': {
            const lam2 = rt2 as Term & {tag:'Lam'};
            if (rt1._isAnnotated !== lam2._isAnnotated) return false;
            let paramTypeOk = true;
            if (rt1._isAnnotated) {
                if (!rt1.paramType || !lam2.paramType || !areStructurallyEqualNoWhnf(rt1.paramType, lam2.paramType, ctx, depth + 1)) {
                    paramTypeOk = false;
                }
            }
            if (!paramTypeOk) return false;
            const freshVName = rt1.paramName; 
            const freshV = Var(freshVName, true);
            const paramTypeForCtx = (rt1._isAnnotated && rt1.paramType) ? getTermRef(rt1.paramType) : Hole(freshHoleName()+"_structEq_unannot_lam_param");
            const extendedCtx = extendCtx(ctx, freshVName, paramTypeForCtx, rt1.icit); // No definition for structural check
            return areStructurallyEqualNoWhnf(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            if (!areStructurallyEqualNoWhnf(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            const freshVName = rt1.paramName; 
            const freshV = Var(freshVName, true);
            const extendedCtx = extendCtx(ctx, freshVName, getTermRef(rt1.paramType), rt1.icit); // No definition
            return areStructurallyEqualNoWhnf(rt1.bodyType(freshV), pi2.bodyType(freshV), extendedCtx, depth + 1);
        }
        case 'ObjTerm':
            return areStructurallyEqualNoWhnf(rt1.cat, (rt2 as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
        case 'HomTerm': {
            const hom2 = rt2 as Term & {tag:'HomTerm'};
            return areStructurallyEqualNoWhnf(rt1.cat, hom2.cat, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.dom, hom2.dom, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.cod, hom2.cod, ctx, depth + 1);
        }
        case 'FunctorCategoryTerm': {
            const fc2 = rt2 as Term & {tag:'FunctorCategoryTerm'};
            return areStructurallyEqualNoWhnf(rt1.domainCat, fc2.domainCat, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.codomainCat, fc2.codomainCat, ctx, depth + 1);
        }
        case 'FMap0Term': {
            const fm0_2 = rt2 as Term & {tag:'FMap0Term'};
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areStructurallyEqualNoWhnf(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2;
            };
            if (!implicitsMatch(rt1.catA_IMPLICIT, fm0_2.catA_IMPLICIT) ||
                !implicitsMatch(rt1.catB_IMPLICIT, fm0_2.catB_IMPLICIT)) {
                return false;
            }
            return areStructurallyEqualNoWhnf(rt1.functor, fm0_2.functor, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.objectX, fm0_2.objectX, ctx, depth + 1);
        }
        case 'FMap1Term': {
            const fm1_2 = rt2 as Term & {tag:'FMap1Term'};
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areStructurallyEqualNoWhnf(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2;
            };
            if (!implicitsMatch(rt1.catA_IMPLICIT, fm1_2.catA_IMPLICIT) ||
                !implicitsMatch(rt1.catB_IMPLICIT, fm1_2.catB_IMPLICIT) ||
                !implicitsMatch(rt1.objX_A_IMPLICIT, fm1_2.objX_A_IMPLICIT) ||
                !implicitsMatch(rt1.objY_A_IMPLICIT, fm1_2.objY_A_IMPLICIT)) {
                return false;
            }
            return areStructurallyEqualNoWhnf(rt1.functor, fm1_2.functor, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.morphism_a, fm1_2.morphism_a, ctx, depth + 1);
        }
        case 'NatTransTypeTerm': {
            const nt2 = rt2 as Term & {tag:'NatTransTypeTerm'};
            return areStructurallyEqualNoWhnf(rt1.catA, nt2.catA, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.catB, nt2.catB, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.functorF, nt2.functorF, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.functorG, nt2.functorG, ctx, depth + 1);
        }
        case 'NatTransComponentTerm': {
            const nc2 = rt2 as Term & {tag:'NatTransComponentTerm'};
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areStructurallyEqualNoWhnf(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2;
            };
            if (!implicitsMatch(rt1.catA_IMPLICIT, nc2.catA_IMPLICIT) ||
                !implicitsMatch(rt1.catB_IMPLICIT, nc2.catB_IMPLICIT) ||
                !implicitsMatch(rt1.functorF_IMPLICIT, nc2.functorF_IMPLICIT) ||
                !implicitsMatch(rt1.functorG_IMPLICIT, nc2.functorG_IMPLICIT)) {
                return false;
            }
            return areStructurallyEqualNoWhnf(rt1.transformation, nc2.transformation, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.objectX, nc2.objectX, ctx, depth + 1);
        }
        case 'HomCovFunctorIdentity': {
            const hc2 = rt2 as Term & {tag:'HomCovFunctorIdentity'};
            return areStructurallyEqualNoWhnf(rt1.domainCat, hc2.domainCat, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.objW_InDomainCat, hc2.objW_InDomainCat, ctx, depth + 1);
        }
        case 'SetTerm': return true;
        default:
            const exhaustiveCheck: never = rt1; return false;
    }
}

export function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`WHNF stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    let current = term;
    for (let i = 0; i < MAX_WHNF_ITERATIONS; i++) {
        let changedInThisPass = false;
        const termAtStartOfOuterPass = current; 

        const dereffedCurrent = getTermRef(current);
        if (dereffedCurrent !== current) { 
            current = dereffedCurrent;
            changedInThisPass = true;
        }
        
        const termBeforeInnerReductions = current; 

        // <<< MODIFIED HERE: Check for local definitions first >>>
        if (current.tag === 'Var') {
            const binding = lookupCtx(ctx, current.name);
            if (binding && binding.definition) {
                current = binding.definition; // Substitute with the definition
                changedInThisPass = true;
                continue; // Restart the whnf loop with the new term
            }
            // If no local definition, proceed to check rewrite rules and global definitions
        }

        if (!isKernelConstantSymbolStructurally(current)) {
            for (const rule of userRewriteRules) { 
                const subst = matchPattern(rule.elaboratedLhs, termBeforeInnerReductions, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    const rhsApplied = getTermRef(applySubst(rule.elaboratedRhs, subst, rule.patternVars));
                    if (rhsApplied !== termBeforeInnerReductions && !areStructurallyEqualNoWhnf(rhsApplied, termBeforeInnerReductions, ctx, stackDepth + 1)) {
                        current = rhsApplied;
                        changedInThisPass = true;
                        break; 
                    }
                }
            }
            if (changedInThisPass) continue; 
        }

        let reducedInKernelBlock = false;

        switch (current.tag) {
            case 'App': {
                const func_whnf_ref = getTermRef(whnf(current.func, ctx, stackDepth + 1));
                if (func_whnf_ref.tag === 'Lam' && func_whnf_ref.icit === current.icit) { 
                    // console.log('WHNF>>', i , ' ', {current}, ' ', {func_whnf_ref}, ' current.arg: ', current.arg );

                    // Beta reduction: The body of the lambda is called with the argument.
                    // If the lambda's parameter was meant to be substituted by `current.arg`,
                    // the `body` function itself should handle this, OR
                    // we rely on a later `Var` lookup in `whnf` if body uses `Var(paramName)`.\
                    // With the new local definition handling, if body uses Var(paramName),
                    // it needs to be in a context where paramName is defined as current.arg.
                    // This is more relevant for `normalize` or `infer` when they set up such contexts.
                    // For raw `whnf` of an `App(Lam(...), arg)`, direct application of `body(arg)` is standard.
                    current = func_whnf_ref.body(current.arg);
                    reducedInKernelBlock = true;
                } else if (getTermRef(current.func) !== func_whnf_ref) { 
                    current = App(func_whnf_ref, current.arg, current.icit);
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'ObjTerm': {
                const cat_whnf_ref = getTermRef(whnf(current.cat, ctx, stackDepth + 1));
                if (getTermRef(current.cat) !== cat_whnf_ref) {
                    current = ObjTerm(cat_whnf_ref);
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'HomTerm': {
                const cat_whnf_ref = getTermRef(whnf(current.cat, ctx, stackDepth + 1));
                if (cat_whnf_ref.tag === 'FunctorCategoryTerm') {
                    current = NatTransTypeTerm(cat_whnf_ref.domainCat, cat_whnf_ref.codomainCat, current.dom, current.cod);
                    reducedInKernelBlock = true;
                } else if (getTermRef(current.cat) !== cat_whnf_ref) {
                    current = HomTerm(cat_whnf_ref, current.dom, current.cod);
                    reducedInKernelBlock = true;
                } else { // If cat_for_hom_whnf is not MkCat_ or FunctorCategoryTerm
                    const setGlobal = globalDefs.get("Set");
                    if (setGlobal?.value && areStructurallyEqualNoWhnf(cat_whnf_ref, getTermRef(setGlobal.value), ctx)) {
                         const domWhnf = whnf(current.dom, ctx, stackDepth + 1);
                         const codWhnf = whnf(current.cod, ctx, stackDepth + 1);
                         current = Pi(freshVarName("_x_hom_set"), Icit.Expl, domWhnf, _ => codWhnf);
                         reducedInKernelBlock = true;
                    }
                }
                break;
            }
            case 'Var': { // This is reached if no local definition was found earlier in the loop for this Var.
                const gdef = globalDefs.get(current.name);
                if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol && !gdef.isTypeNameLike) {
                    current = gdef.value; 
                    reducedInKernelBlock = true;
                }
                break;
            }
        }

        if (reducedInKernelBlock) {
             changedInThisPass = true; 
             continue;
        }
        
        const currentAfterPossibleKernelOrRefChange = getTermRef(current);
        if (currentAfterPossibleKernelOrRefChange !== termBeforeInnerReductions && !changedInThisPass) {
            current = currentAfterPossibleKernelOrRefChange;
            changedInThisPass = true;
        }
        
        if (!changedInThisPass) break;

        if (current === termAtStartOfOuterPass && !changedInThisPass && i > 0) break; 

        if (i === MAX_WHNF_ITERATIONS - 1) { 
             if (changedInThisPass || current !== termAtStartOfOuterPass) { 
                console.warn(`[TRACE whnf (${stackDepth})] WHNF reached max iterations for: ${printTerm(term)} -> ${printTerm(current)}`);
             } 
        }
    }
    return current;
}

export function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Normalize stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    const headReduced = whnf(term, ctx, stackDepth + 1);
    const current = getTermRef(headReduced); 
    switch (current.tag) {
        case 'Type': case 'Var' : case 'Hole': case 'CatTerm': return current;
        case 'ObjTerm': return ObjTerm(normalize(current.cat, ctx, stackDepth + 1));
        case 'HomTerm':
            return HomTerm(
                normalize(current.cat, ctx, stackDepth + 1),
                normalize(current.dom, ctx, stackDepth + 1),
                normalize(current.cod, ctx, stackDepth + 1)
            );
        case 'FunctorCategoryTerm':
            return FunctorCategoryTerm(
                normalize(current.domainCat, ctx, stackDepth + 1),
                normalize(current.codomainCat, ctx, stackDepth + 1)
            );
        case 'FMap0Term':
            return FMap0Term(
                normalize(current.functor, ctx, stackDepth + 1),
                normalize(current.objectX, ctx, stackDepth + 1),
                current.catA_IMPLICIT ? normalize(current.catA_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.catB_IMPLICIT ? normalize(current.catB_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'FMap1Term':
            return FMap1Term(
                normalize(current.functor, ctx, stackDepth + 1),
                normalize(current.morphism_a, ctx, stackDepth + 1),
                current.catA_IMPLICIT ? normalize(current.catA_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.catB_IMPLICIT ? normalize(current.catB_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objX_A_IMPLICIT ? normalize(current.objX_A_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objY_A_IMPLICIT ? normalize(current.objY_A_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'NatTransTypeTerm':
            return NatTransTypeTerm(
                normalize(current.catA, ctx, stackDepth + 1),
                normalize(current.catB, ctx, stackDepth + 1),
                normalize(current.functorF, ctx, stackDepth + 1),
                normalize(current.functorG, ctx, stackDepth + 1)
            );
        case 'NatTransComponentTerm':
            return NatTransComponentTerm(
                normalize(current.transformation, ctx, stackDepth + 1),
                normalize(current.objectX, ctx, stackDepth + 1),
                current.catA_IMPLICIT ? normalize(current.catA_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.catB_IMPLICIT ? normalize(current.catB_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.functorF_IMPLICIT ? normalize(current.functorF_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.functorG_IMPLICIT ? normalize(current.functorG_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'HomCovFunctorIdentity':
            return HomCovFunctorIdentity(
                normalize(current.domainCat, ctx, stackDepth + 1),
                normalize(current.objW_InDomainCat, ctx, stackDepth + 1)
            );
        case 'Lam': {
            const currentLam = current;
            const normLamParamType = (currentLam._isAnnotated && currentLam.paramType)
                                     ? normalize(currentLam.paramType, ctx, stackDepth + 1)
                                     : undefined;

            const newBodyFn = (v_arg_placeholder: Term): Term => { 
                // This v_arg_placeholder is typically Var(currentLam.paramName) when the Lam body is instantiated.
                // For normalization, we extend the *original* context `ctx` with the param, NOT defining it as v_arg_placeholder.
                // The v_arg_placeholder is only used to get the structure of the body.
                const paramTypeForBodyCtx = normLamParamType || 
                                            (currentLam.paramType ? getTermRef(currentLam.paramType) : Hole(freshHoleName()+"_norm_lam_body_ctx"));
                const bodyCtx = extendCtx(ctx, currentLam.paramName, paramTypeForBodyCtx, currentLam.icit); // No definition here for the param
                return normalize(currentLam.body(v_arg_placeholder), bodyCtx, stackDepth + 1);
            };
            return {
                tag: 'Lam',
                paramName: currentLam.paramName,
                icit: currentLam.icit,
                paramType: normLamParamType, 
                _isAnnotated: currentLam._isAnnotated, 
                body: newBodyFn 
            };
        }
        case 'App': { // <<< MODIFIED HERE for beta-reduction context
            const normFunc = normalize(current.func, ctx, stackDepth + 1);
            const normArg = normalize(current.arg, ctx, stackDepth + 1);
            const finalNormFunc = getTermRef(normFunc);

            if (finalNormFunc.tag === 'Lam' && finalNormFunc.icit === current.icit) {
                // Beta reduction: The context for normalizing the body is `ctx`
                // extended with `finalNormFunc.paramName` defined as `normArg`.
                const bodyParamType = finalNormFunc.paramType ? 
                                      getTermRef(finalNormFunc.paramType) : 
                                      Hole(freshHoleName() + "_beta_param_type_");
                
                const extendedCtxForBody = extendCtx(
                    ctx, 
                    finalNormFunc.paramName, 
                    bodyParamType, // Type for the context binding
                    finalNormFunc.icit, 
                    normArg        // Definition for the parameter
                );
                // The body `finalNormFunc.body(Var(finalNormFunc.paramName))` will instantiate the body.
                // `whnf` (called by `normalize`) on `Var(finalNormFunc.paramName)` inside this `extendedCtxForBody`
                // will then pick up `normArg` as its definition.
                return normalize(finalNormFunc.body(Var(finalNormFunc.paramName, true)), extendedCtxForBody, stackDepth + 1);
            }
            // console.log('NORMALIZE>>', normFunc, normArg, current.icit);
            return App(normFunc, normArg, current.icit); 
        }
        case 'Pi': {
            const currentPi = current;
            const normPiParamType = normalize(currentPi.paramType, ctx, stackDepth + 1);
            return Pi(currentPi.paramName, currentPi.icit, normPiParamType, (v_arg_placeholder: Term) => {
                // Similar to Lam, for normalizing the Pi's bodyType structure.
                const bodyTypeCtx = extendCtx(ctx, currentPi.paramName, normPiParamType, currentPi.icit); // No definition for param
                return normalize(currentPi.bodyType(v_arg_placeholder), bodyTypeCtx, stackDepth + 1);
            });
        }
        case 'SetTerm': return current;
        default: const exhaustiveCheck: never = current; throw new Error(`Normalize: Unhandled term: ${(exhaustiveCheck as any).tag }`);
    }
}

export function areEqual(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Equality check depth exceeded (areEqual depth: ${depth})`);
    const rt1 = getTermRef(whnf(t1, ctx, depth + 1));
    const rt2 = getTermRef(whnf(t2, ctx, depth + 1));

    if (rt1.tag === 'Hole' && rt2.tag === 'Hole') return rt1.id === rt2.id;
    if (rt1.tag === 'Hole' || rt2.tag === 'Hole') return false; 
    if (rt1.tag !== rt2.tag) return false;

    if ((rt1.tag === 'App' || rt1.tag === 'Lam' || rt1.tag === 'Pi') &&
        (rt2.tag === rt1.tag) && rt1.icit !== (rt2 as typeof rt1).icit) {
        return false;
    }

    switch (rt1.tag) {
        case 'Type': case 'CatTerm': return true;
        case 'Var': return rt1.name === (rt2 as Term & {tag:'Var'}).name;
        case 'App': {
            const app2 = rt2 as Term & {tag:'App'};
            return areEqual(rt1.func, app2.func, ctx, depth + 1) &&
                   areEqual(rt1.arg, app2.arg, ctx, depth + 1);
        }
        case 'Lam': { // For alpha-equivalence, extend context without definition
            const lam2 = rt2 as Term & {tag:'Lam'};
            if (rt1._isAnnotated !== lam2._isAnnotated) return false;
            let paramTypeOk = true;
            if (rt1._isAnnotated) { 
                if (!rt1.paramType || !lam2.paramType || !areEqual(rt1.paramType, lam2.paramType, ctx, depth + 1)) {
                    paramTypeOk = false;
                }
            }
            if(!paramTypeOk) return false;

            const freshVName = rt1.paramName; 
            const freshV = Var(freshVName, true);
            const paramTypeForCtx = (rt1._isAnnotated && rt1.paramType) ? getTermRef(rt1.paramType) : Hole(freshHoleName()+"_areEqual_unannot_lam_param");
            const extendedCtx = extendCtx(ctx, freshVName, paramTypeForCtx, rt1.icit); // No definition for freshV
            return areEqual(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': { // For alpha-equivalence, extend context without definition
            const pi2 = rt2 as Term & {tag:'Pi'};
            if (!areEqual(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            const freshVName = rt1.paramName; 
            const freshV = Var(freshVName, true);
            const extendedCtx = extendCtx(ctx, freshVName, getTermRef(rt1.paramType), rt1.icit); // No definition for freshV
            return areEqual(rt1.bodyType(freshV), pi2.bodyType(freshV), extendedCtx, depth + 1);
        }
        case 'ObjTerm': return areEqual(rt1.cat, (rt2 as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
        case 'HomTerm': {
            const hom2 = rt2 as Term & {tag:'HomTerm'};
            return areEqual(rt1.cat, hom2.cat, ctx, depth + 1) &&
                   areEqual(rt1.dom, hom2.dom, ctx, depth + 1) &&
                   areEqual(rt1.cod, hom2.cod, ctx, depth + 1);
        }
        case 'FunctorCategoryTerm': {
            const fc2 = rt2 as Term & {tag:'FunctorCategoryTerm'};
            return areEqual(rt1.domainCat, fc2.domainCat, ctx, depth + 1) &&
                   areEqual(rt1.codomainCat, fc2.codomainCat, ctx, depth + 1);
        }
        case 'FMap0Term': {
            const fm0_2 = rt2 as Term & {tag:'FMap0Term'};
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areEqual(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2;
            };
            if (!implicitsMatch(rt1.catA_IMPLICIT, fm0_2.catA_IMPLICIT) ||
                !implicitsMatch(rt1.catB_IMPLICIT, fm0_2.catB_IMPLICIT)) {
                return false;
            }
            return areEqual(rt1.functor, fm0_2.functor, ctx, depth + 1) &&
                   areEqual(rt1.objectX, fm0_2.objectX, ctx, depth + 1);
        }
        case 'FMap1Term': {
            const fm1_2 = rt2 as Term & {tag:'FMap1Term'};
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areEqual(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2;
            };
            if (!implicitsMatch(rt1.catA_IMPLICIT, fm1_2.catA_IMPLICIT) ||
                !implicitsMatch(rt1.catB_IMPLICIT, fm1_2.catB_IMPLICIT) ||
                !implicitsMatch(rt1.objX_A_IMPLICIT, fm1_2.objX_A_IMPLICIT) ||
                !implicitsMatch(rt1.objY_A_IMPLICIT, fm1_2.objY_A_IMPLICIT)) {
                return false;
            }
            return areEqual(rt1.functor, fm1_2.functor, ctx, depth + 1) &&
                   areEqual(rt1.morphism_a, fm1_2.morphism_a, ctx, depth + 1);
        }
        case 'NatTransTypeTerm': {
            const nt2 = rt2 as Term & {tag:'NatTransTypeTerm'};
            return areEqual(rt1.catA, nt2.catA, ctx, depth + 1) &&
                   areEqual(rt1.catB, nt2.catB, ctx, depth + 1) &&
                   areEqual(rt1.functorF, nt2.functorF, ctx, depth + 1) &&
                   areEqual(rt1.functorG, nt2.functorG, ctx, depth + 1);
        }
        case 'NatTransComponentTerm': {
            const nc2 = rt2 as Term & {tag:'NatTransComponentTerm'};
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areEqual(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2;
            };
            if (!implicitsMatch(rt1.catA_IMPLICIT, nc2.catA_IMPLICIT) ||
                !implicitsMatch(rt1.catB_IMPLICIT, nc2.catB_IMPLICIT) ||
                !implicitsMatch(rt1.functorF_IMPLICIT, nc2.functorF_IMPLICIT) ||
                !implicitsMatch(rt1.functorG_IMPLICIT, nc2.functorG_IMPLICIT)) {
                return false;
            }
            return areEqual(rt1.transformation, nc2.transformation, ctx, depth + 1) &&
                   areEqual(rt1.objectX, nc2.objectX, ctx, depth + 1);
        }
        case 'HomCovFunctorIdentity': {
            const hc2 = rt2 as Term & {tag:'HomCovFunctorIdentity'};
            return areEqual(rt1.domainCat, hc2.domainCat, ctx, depth + 1) &&
                   areEqual(rt1.objW_InDomainCat, hc2.objW_InDomainCat, ctx, depth + 1);
        }
        case 'SetTerm': return true;
        default: const exhaustiveCheck: never = rt1; return false;
    }
}

export function termContainsHole(term: Term, holeId: string, visited: Set<string> = new Set(), depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH * 2) { 
        console.warn(`termContainsHole depth exceeded for hole ${holeId} in ${printTerm(term)}`);
        return true; 
    }
    
    const current = getTermRef(term); 

    const termKey = current.tag === 'Hole' ? `Hole:${current.id}` : 
                    current.tag === 'Var' ? `Var:${current.name}` :
                    printTerm(current); 

    if (visited.has(termKey) && current.tag !== 'Hole' && current.tag !== 'Var' ) {
         return false; 
    }
    visited.add(termKey);


    switch (current.tag) {
        case 'Hole': return current.id === holeId;
        case 'Type': case 'Var': case 'CatTerm': return false;
        case 'App':
            return termContainsHole(current.func, holeId, visited, depth + 1) ||
                   termContainsHole(current.arg, holeId, visited, depth + 1);
        case 'Lam':
            if (current.paramType && termContainsHole(current.paramType, holeId, visited, depth + 1)) return true;
            const freshVLam = Var(freshVarName("_occ_check_lam"), true); 
            return termContainsHole(current.body(freshVLam), holeId, new Set(visited) , depth + 1);
        case 'Pi':
            if (termContainsHole(current.paramType, holeId, visited, depth + 1)) return true;
            const freshVPi = Var(freshVarName("_occ_check_pi"), true); 
            return termContainsHole(current.bodyType(freshVPi), holeId, new Set(visited) , depth + 1);
        case 'ObjTerm': return termContainsHole(current.cat, holeId, visited, depth + 1);
        case 'HomTerm':
            return termContainsHole(current.cat, holeId, visited, depth + 1) ||
                   termContainsHole(current.dom, holeId, visited, depth + 1) ||
                   termContainsHole(current.cod, holeId, visited, depth + 1);
        case 'FunctorCategoryTerm':
            return termContainsHole(current.domainCat, holeId, visited, depth + 1) ||
                   termContainsHole(current.codomainCat, holeId, visited, depth + 1);
        case 'FMap0Term':
            return termContainsHole(current.functor, holeId, visited, depth + 1) ||
                   termContainsHole(current.objectX, holeId, visited, depth + 1) ||
                   (current.catA_IMPLICIT && termContainsHole(current.catA_IMPLICIT, holeId, visited, depth + 1)) ||
                   (current.catB_IMPLICIT && termContainsHole(current.catB_IMPLICIT, holeId, visited, depth + 1));
        case 'FMap1Term':
            return termContainsHole(current.functor, holeId, visited, depth + 1) ||
                   termContainsHole(current.morphism_a, holeId, visited, depth + 1) ||
                   (current.catA_IMPLICIT && termContainsHole(current.catA_IMPLICIT, holeId, visited, depth + 1)) ||
                   (current.catB_IMPLICIT && termContainsHole(current.catB_IMPLICIT, holeId, visited, depth + 1)) ||
                   (current.objX_A_IMPLICIT && termContainsHole(current.objX_A_IMPLICIT, holeId, visited, depth + 1)) ||
                   (current.objY_A_IMPLICIT && termContainsHole(current.objY_A_IMPLICIT, holeId, visited, depth + 1));
        case 'NatTransTypeTerm':
            return termContainsHole(current.catA, holeId, visited, depth + 1) ||
                   termContainsHole(current.catB, holeId, visited, depth + 1) ||
                   termContainsHole(current.functorF, holeId, visited, depth + 1) ||
                   termContainsHole(current.functorG, holeId, visited, depth + 1);
        case 'NatTransComponentTerm':
            return termContainsHole(current.transformation, holeId, visited, depth + 1) ||
                   termContainsHole(current.objectX, holeId, visited, depth + 1) ||
                   (current.catA_IMPLICIT && termContainsHole(current.catA_IMPLICIT, holeId, visited, depth + 1)) ||
                   (current.catB_IMPLICIT && termContainsHole(current.catB_IMPLICIT, holeId, visited, depth + 1)) ||
                   (current.functorF_IMPLICIT && termContainsHole(current.functorF_IMPLICIT, holeId, visited, depth + 1)) ||
                   (current.functorG_IMPLICIT && termContainsHole(current.functorG_IMPLICIT, holeId, visited, depth + 1));
        case 'HomCovFunctorIdentity':
            return termContainsHole(current.domainCat, holeId, visited, depth + 1) ||
                   termContainsHole(current.objW_InDomainCat, holeId, visited, depth + 1);
        case 'SetTerm': return false;
        default: const exhaustiveCheck: never = current; return false;
    }
}

export function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
    const normTerm = getTermRef(whnf(term, ctx, depth + 1)); 
    if (normTerm.tag === 'Hole') {
        if (hole.id === normTerm.id) return true; 
        if (hole.id < normTerm.id) { 
             (normTerm as Term & {tag:'Hole'}).ref = hole;
        } else {
             hole.ref = normTerm;
        }
        consoleLog(`[UnifyHole] ${hole.id} now points to ${normTerm.id} (or vice versa) (depth ${depth})`);
        return true;
    }

    if (termContainsHole(normTerm, hole.id, new Set(), depth + 1)) { // Occurs check
        console.error(`[UnifyHole CRITICAL] Occurs check FAILED for hole ${hole.id} in term ${printTerm(normTerm)}. Depth: ${depth}. This means unification cannot proceed for this hole.`);
        return false; 
    }
    consoleLog(`[UnifyHole] Setting ${hole.id}.ref = ${printTerm(normTerm)} (depth ${depth}). Current hole.ref before: ${hole.ref ? printTerm(hole.ref) : 'undefined'}`);
    hole.ref = normTerm; 
    // Check right after setting if getTermRef sees it
    const currentValOfHole = getTermRef(hole);
    consoleLog(`[UnifyHole] ${hole.id} now points to (via getTermRef): ${printTerm(currentValOfHole)}. Direct hole.ref: ${printTerm(hole.ref!)}. (depth ${depth})`);
    return true;
}

export function unifyArgs(args1: (Term | undefined)[], args2: (Term | undefined)[], ctx: Context, depth: number): UnifyResult {
    if (args1.length !== args2.length) return UnifyResult.Failed; 
    let madeProgressOverall = false; 
    let allSubSolved = true; 

    for (let i = 0; i < args1.length; i++) {
        const t1_arg = args1[i];
        const t2_arg = args2[i];

        if (t1_arg === undefined && t2_arg === undefined) continue; 

        const arg1ToUnify = t1_arg === undefined ? Hole(freshHoleName() + "_undef_arg_lhs_" + i) : t1_arg;
        const arg2ToUnify = t2_arg === undefined ? Hole(freshHoleName() + "_undef_arg_rhs_" + i) : t2_arg;
        
        const argStatus = unify(arg1ToUnify, arg2ToUnify, ctx, depth + 1); 

        if (argStatus === UnifyResult.Failed) return UnifyResult.Failed; 

        if (argStatus === UnifyResult.RewrittenByRule || argStatus === UnifyResult.Progress) {
            madeProgressOverall = true; 
        }
        if (argStatus !== UnifyResult.Solved) {
            allSubSolved = false; 
        }
    }

    if (allSubSolved) return UnifyResult.Solved;
    return madeProgressOverall ? UnifyResult.Progress : UnifyResult.Progress; 
}


export function unify(t1: Term, t2: Term, ctx: Context, depth = 0): UnifyResult {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Unification stack depth exceeded (Unify depth: ${depth}, ${printTerm(t1)} vs ${printTerm(t2)})`);

    let current_t1 = getTermRef(t1);
    let current_t2 = getTermRef(t2);
    if (current_t1 === current_t2 && current_t1.tag !== 'Hole') return UnifyResult.Solved;

    if (current_t1.tag === 'Hole') {
        return unifyHole(current_t1, current_t2, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(current_t1, current_t2, ctx, depth +1);
    }
    if (current_t2.tag === 'Hole') {
        return unifyHole(current_t2, current_t1, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(current_t1, current_t2, ctx, depth +1);
    }

    // Phase 1: Structural unification for known injective constructors (before full WHNF)
    if (current_t1.tag === current_t2.tag) {
        const commonTag = current_t1.tag;
        let structuralResult: UnifyResult | undefined = undefined;

        // Check for global injectivity of the common constructor tag itself if it's a known one.
        // This is different from isInjective on a global Var like `f_inj`.
        if (isEmdashUnificationInjectiveStructurally(commonTag)) {
            switch (commonTag) {
                case 'Type': case 'CatTerm': // These are just equal if tags match.
                    structuralResult = UnifyResult.Solved;
                    break;
                case 'Var': // Vars are compared by name.
                    structuralResult = (current_t1 as Term & {tag:'Var'}).name === (current_t2 as Term & {tag:'Var'}).name ? UnifyResult.Solved : UnifyResult.Failed;
                    break;
                case 'ObjTerm':
                    structuralResult = unify((current_t1 as Term & {tag:'ObjTerm'}).cat, (current_t2 as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
                    break;
                case 'HomTerm': {
                    const hom1 = current_t1 as Term & {tag:'HomTerm'};
                    const hom2 = current_t2 as Term & {tag:'HomTerm'};
                    structuralResult = unifyArgs([hom1.cat, hom1.dom, hom1.cod], [hom2.cat, hom2.dom, hom2.cod], ctx, depth + 1);
                    break;
                }
                case 'FMap0Term': {
                    const fm0_1 = current_t1 as Term & {tag:'FMap0Term'};
                    const fm0_2 = current_t2 as Term & {tag:'FMap0Term'};
                    const catA1_imp = fm0_1.catA_IMPLICIT || Hole(freshHoleName() + "_fm0_catA1_struct");
                    const catA2_imp = fm0_2.catA_IMPLICIT || Hole(freshHoleName() + "_fm0_catA2_struct");
                    const catB1_imp = fm0_1.catB_IMPLICIT || Hole(freshHoleName() + "_fm0_catB1_struct");
                    const catB2_imp = fm0_2.catB_IMPLICIT || Hole(freshHoleName() + "_fm0_catB2_struct");
                    structuralResult = unifyArgs(
                        [fm0_1.functor, fm0_1.objectX, catA1_imp, catB1_imp],
                        [fm0_2.functor, fm0_2.objectX, catA2_imp, catB2_imp],
                        ctx, depth + 1
                    );
                    break;
                }
                case 'FMap1Term': {
                    const fm1_1 = current_t1 as Term & {tag:'FMap1Term'};
                    const fm1_2 = current_t2 as Term & {tag:'FMap1Term'};
                    const catA1_imp = fm1_1.catA_IMPLICIT || Hole(freshHoleName() + "_fm1_catA1_struct");
                    const catA2_imp = fm1_2.catA_IMPLICIT || Hole(freshHoleName() + "_fm1_catA2_struct");
                    const catB1_imp = fm1_1.catB_IMPLICIT || Hole(freshHoleName() + "_fm1_catB1_struct");
                    const catB2_imp = fm1_2.catB_IMPLICIT || Hole(freshHoleName() + "_fm1_catB2_struct");
                    const objX1_imp = fm1_1.objX_A_IMPLICIT || Hole(freshHoleName() + "_fm1_objX1_struct");
                    const objX2_imp = fm1_2.objX_A_IMPLICIT || Hole(freshHoleName() + "_fm1_objX2_struct");
                    const objY1_imp = fm1_1.objY_A_IMPLICIT || Hole(freshHoleName() + "_fm1_objY1_struct");
                    const objY2_imp = fm1_2.objY_A_IMPLICIT || Hole(freshHoleName() + "_fm1_objY2_struct");
                    structuralResult = unifyArgs(
                        [fm1_1.functor, fm1_1.morphism_a, catA1_imp, catB1_imp, objX1_imp, objY1_imp],
                        [fm1_2.functor, fm1_2.morphism_a, catA2_imp, catB2_imp, objX2_imp, objY2_imp],
                        ctx, depth + 1
                    );
                    break;
                }
                case 'NatTransTypeTerm': {
                    const nt1 = current_t1 as Term & {tag:'NatTransTypeTerm'};
                    const nt2 = current_t2 as Term & {tag:'NatTransTypeTerm'};
                    structuralResult = unifyArgs(
                        [nt1.catA, nt1.catB, nt1.functorF, nt1.functorG],
                        [nt2.catA, nt2.catB, nt2.functorF, nt2.functorG],
                        ctx, depth + 1
                    );
                    break;
                }
                case 'NatTransComponentTerm': {
                    const nc1 = current_t1 as Term & {tag:'NatTransComponentTerm'};
                    const nc2 = current_t2 as Term & {tag:'NatTransComponentTerm'};
                    const catA1_imp = nc1.catA_IMPLICIT || Hole(freshHoleName() + "_nc_catA1_struct");
                    const catA2_imp = nc2.catA_IMPLICIT || Hole(freshHoleName() + "_nc_catA2_struct");
                    const catB1_imp = nc1.catB_IMPLICIT || Hole(freshHoleName() + "_nc_catB1_struct");
                    const catB2_imp = nc2.catB_IMPLICIT || Hole(freshHoleName() + "_nc_catB2_struct");
                    const funF1_imp = nc1.functorF_IMPLICIT || Hole(freshHoleName() + "_nc_funF1_struct");
                    const funF2_imp = nc2.functorF_IMPLICIT || Hole(freshHoleName() + "_nc_funF2_struct");
                    const funG1_imp = nc1.functorG_IMPLICIT || Hole(freshHoleName() + "_nc_funG1_struct");
                    const funG2_imp = nc2.functorG_IMPLICIT || Hole(freshHoleName() + "_nc_funG2_struct");
                    structuralResult = unifyArgs(
                        [nc1.transformation, nc1.objectX, catA1_imp, catB1_imp, funF1_imp, funG1_imp],
                        [nc2.transformation, nc2.objectX, catA2_imp, catB2_imp, funF2_imp, funG2_imp],
                        ctx, depth + 1
                    );
                    break;
                }
                 // Note: ComposeMorph is not typically considered injective in this structural way
                 // because its arguments (g, f, and other implicits) define its structure.
                 // App is handled after WHNF for global injectivity.
            }
        }


        if (structuralResult !== undefined) {
            // If structural unification succeeded or failed decisively, return that.
            // If it made progress, it might still need WHNF, so we don't return early.
            if (structuralResult === UnifyResult.Solved || structuralResult === UnifyResult.Failed) {
                 return (structuralResult === UnifyResult.Failed) ? tryUnificationRules(current_t1, current_t2, ctx, depth + 1) : structuralResult;
            }
        }
    }

    const rt1_whnf = whnf(current_t1, ctx, depth + 1);
    const rt2_whnf = whnf(current_t2, ctx, depth + 1);

    const rt1_final = getTermRef(rt1_whnf);
    const rt2_final = getTermRef(rt2_whnf);

    if (rt1_final === rt2_final && rt1_final.tag !== 'Hole') return UnifyResult.Solved;

    if (rt1_final.tag === 'Hole') {
        return unifyHole(rt1_final, rt2_final, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
    }
    if (rt2_final.tag === 'Hole') {
        return unifyHole(rt2_final, rt1_final, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
    }

    if (rt1_final.tag !== rt2_final.tag) {
        if ((rt1_final.tag === 'ObjTerm' && rt2_final.tag === 'Type') || (rt2_final.tag === 'ObjTerm' && rt1_final.tag === 'Type')) {
            const objTermNode = (rt1_final.tag === 'ObjTerm' ? rt1_final : rt2_final) as Term & {tag: 'ObjTerm'};
            const setGlobalDef = globalDefs.get("Set");
            if (setGlobalDef?.value) {
                const setTermConstant = getTermRef(setGlobalDef.value);
                addConstraint(objTermNode.cat, setTermConstant, `UnifRule: Obj A === Type => A === Set`);
                consoleLog(`[Unify] Applied kernel rule: Obj A === Type => A === Set for ${printTerm(objTermNode)}`);
                return UnifyResult.RewrittenByRule;
            }
        }
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }
    
    if ((rt1_final.tag === 'App' || rt1_final.tag === 'Lam' || rt1_final.tag === 'Pi') &&
        (rt1_final.icit !== (rt2_final as typeof rt1_final).icit)) { 
         return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1); 
    }

    // Helper to find the ultimate head of an application chain
    const getUltimateHead = (term: Term): Term => {
        let current = getTermRef(term);
        while (current.tag === 'App') {
            current = getTermRef(current.func);
        }
        return current;
    };

    switch (rt1_final.tag) {
        case 'Type': case 'CatTerm': return UnifyResult.Solved; 
        case 'Var': { // Comparing two Vars after WHNF
            const var1 = rt1_final; const var2 = rt2_final as Term & {tag:'Var'};
            if (var1.name === var2.name) return UnifyResult.Solved;

            // New: Check for different constants
            const gdef1 = globalDefs.get(var1.name);
            const gdef2 = globalDefs.get(var2.name);
            if (gdef1 && gdef1.isConstantSymbol && gdef2 && gdef2.isConstantSymbol) {
                // Different names, both are constants, so fail.
                consoleLog(`[Unify Var CONSTANT MISMATCH] ${var1.name} vs ${var2.name}`);
                return UnifyResult.Failed; 
            }
            return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        }
        case 'App': {
            const app1 = rt1_final; const app2 = rt2_final as Term & {tag:'App'};
            
            const ultimateHead1 = getUltimateHead(app1);
            const ultimateHead2 = getUltimateHead(app2);

            // New: Check for different constant heads
            if (ultimateHead1.tag === 'Var' && ultimateHead2.tag === 'Var' && ultimateHead1.name !== ultimateHead2.name) {
                const gdefHead1 = globalDefs.get(ultimateHead1.name);
                const gdefHead2 = globalDefs.get(ultimateHead2.name);
                if (gdefHead1 && gdefHead1.isConstantSymbol && gdefHead2 && gdefHead2.isConstantSymbol) {
                    consoleLog(`[Unify App CONSTANT HEAD MISMATCH] ${ultimateHead1.name} vs ${ultimateHead2.name}`);
                    return UnifyResult.Failed;
                }
            }

            if (ultimateHead1.tag === 'Var' && ultimateHead2.tag === 'Var' && ultimateHead1.name === ultimateHead2.name) {
                const gdef = globalDefs.get(ultimateHead1.name);
                if (gdef && gdef.isInjective) {
                    consoleLog(`[Unify App INJ] Head: ${ultimateHead1.name}. Unifying funcs: ${printTerm(app1.func)} vs ${printTerm(app2.func)} (depth ${depth})`);
                    const funcStatus = unify(app1.func, app2.func, ctx, depth + 1);
                    consoleLog(`[Unify App INJ] Head: ${ultimateHead1.name}. Func status: ${UnifyResult[funcStatus]} (depth ${depth})`);
                    if (funcStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
                    
                    consoleLog(`[Unify App INJ] Head: ${ultimateHead1.name}. Unifying args: ${printTerm(app1.arg)} vs ${printTerm(app2.arg)} (depth ${depth})`);
                    const argStatus = unify(app1.arg, app2.arg, ctx, depth + 1);
                    consoleLog(`[Unify App INJ] Head: ${ultimateHead1.name}. Arg status: ${UnifyResult[argStatus]} (depth ${depth})`);
                    if (argStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

                    if (funcStatus === UnifyResult.Solved && argStatus === UnifyResult.Solved) {
                        consoleLog(`[Unify App INJ] Head: ${ultimateHead1.name}. Both func/arg Solved. Returning Solved. (depth ${depth})`);
                        return UnifyResult.Solved;
                    } else {
                        consoleLog(`[Unify App INJ] Head: ${ultimateHead1.name}. Func/arg status (F:${UnifyResult[funcStatus]}, A:${UnifyResult[argStatus]}). Returning Progress. (depth ${depth})`);
                        return UnifyResult.Progress; // If any failed, it's caught. Else, it's Progress or Solved (already handled).
                    }
                }
            }
            // Default App unification (non-injective head or different heads)
            consoleLog(`[Unify App DEF] Unifying funcs: ${printTerm(app1.func)} vs ${printTerm(app2.func)} (depth ${depth})`);
            const funcUnifyStatus = unify(app1.func, app2.func, ctx, depth + 1);
            consoleLog(`[Unify App DEF] Func status: ${UnifyResult[funcUnifyStatus]} (depth ${depth})`);
            if (funcUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            
            consoleLog(`[Unify App DEF] Unifying args: ${printTerm(app1.arg)} vs ${printTerm(app2.arg)} (depth ${depth})`);
            const argUnifyStatus = unify(app1.arg, app2.arg, ctx, depth + 1);
            consoleLog(`[Unify App DEF] Arg status: ${UnifyResult[argUnifyStatus]} (depth ${depth})`);
            if (argUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            
            if (funcUnifyStatus === UnifyResult.Solved && argUnifyStatus === UnifyResult.Solved) {
                 // If func and args solved, the Apps are considered unified.
                 // The areEqual check here is more of a consistency check after the fact.
                 // If this fundamental unification strategy is sound, they should be equal.
                 // For now, let's assume if components solve, the App itself is Solved.
                 return UnifyResult.Solved; 
            }
            // If one was Progress and the other Solved, it's overall Progress.
            // If both were Progress, it's Progress.
            // Failed cases are handled above.
            return UnifyResult.Progress;
        }
        case 'Lam': { 
            const lam1 = rt1_final; const lam2 = rt2_final as Term & {tag:'Lam'};
            if (lam1._isAnnotated !== lam2._isAnnotated) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            
            let paramTypeStatus = UnifyResult.Solved;
            if (lam1._isAnnotated) { 
                if(!lam1.paramType || !lam2.paramType) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1); 
                paramTypeStatus = unify(lam1.paramType, lam2.paramType, ctx, depth + 1);
                if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            }
            
            const freshV = Var(freshVarName(lam1.paramName), true); 
            const CtxParamType = (lam1._isAnnotated && lam1.paramType) ? getTermRef(lam1.paramType) : Hole(freshHoleName() + "_unif_lam_ctx");
            const extendedCtx = extendCtx(ctx, freshV.name, CtxParamType, lam1.icit); 
            const bodyStatus = unify(lam1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
            
            if(bodyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            
            if(paramTypeStatus === UnifyResult.Solved && bodyStatus === UnifyResult.Solved) {
                return UnifyResult.Solved; // If components solve, Lam is solved
            }
            return UnifyResult.Progress;
        }
        case 'Pi': { 
            const pi1 = rt1_final; const pi2 = rt2_final as Term & {tag:'Pi'};
            const paramTypeStatus = unify(pi1.paramType, pi2.paramType, ctx, depth + 1);
            if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            
            const freshV = Var(freshVarName(pi1.paramName), true); 
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(pi1.paramType), pi1.icit); 
            const bodyTypeStatus = unify(pi1.bodyType(freshV), pi2.bodyType(freshV), extendedCtx, depth + 1);
            
            if(bodyTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            
            if(paramTypeStatus === UnifyResult.Solved && bodyTypeStatus === UnifyResult.Solved) {
                 return UnifyResult.Solved; // If components solve, Pi is solved
            }
            return UnifyResult.Progress;
        }
         case 'ObjTerm': { 
            const argStatus = unify((rt1_final as Term & {tag:'ObjTerm'}).cat, (rt2_final as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
            return (argStatus === UnifyResult.Failed) ? tryUnificationRules(rt1_final, rt2_final, ctx, depth +1) : argStatus;
        }
        case 'HomTerm': {
            const hom1 = rt1_final as Term & {tag:'HomTerm'}; const hom2 = rt2_final as Term & {tag:'HomTerm'};
            const catStatus = unify(hom1.cat, hom2.cat, ctx, depth + 1);
            if(catStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const domStatus = unify(hom1.dom, hom2.dom, ctx, depth + 1);
            if(domStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const codStatus = unify(hom1.cod, hom2.cod, ctx, depth + 1);
            if(codStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            
            if(catStatus === UnifyResult.Solved && domStatus === UnifyResult.Solved && codStatus === UnifyResult.Solved) {
                return UnifyResult.Solved; // If components solve, HomTerm is solved
            }
            return UnifyResult.Progress;
        }
        case 'FunctorCategoryTerm': {
            const fc1 = rt1_final as Term & {tag:'FunctorCategoryTerm'}; const fc2 = rt2_final as Term & {tag:'FunctorCategoryTerm'};
            const domStatus = unify(fc1.domainCat, fc2.domainCat, ctx, depth + 1);
            if (domStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const codStatus = unify(fc1.codomainCat, fc2.codomainCat, ctx, depth + 1);
            if (codStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            if (domStatus === UnifyResult.Solved && codStatus === UnifyResult.Solved) return UnifyResult.Solved;
            return UnifyResult.Progress;
        }
        case 'FMap0Term': {
            const fm0_1 = rt1_final as Term & {tag:'FMap0Term'}; const fm0_2 = rt2_final as Term & {tag:'FMap0Term'};
            const implicitsStatus = unifyArgs(
                [fm0_1.catA_IMPLICIT, fm0_1.catB_IMPLICIT],
                [fm0_2.catA_IMPLICIT, fm0_2.catB_IMPLICIT],
                ctx, depth + 1
            );
            if (implicitsStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const funcStatus = unify(fm0_1.functor, fm0_2.functor, ctx, depth + 1);
            if (funcStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const objStatus = unify(fm0_1.objectX, fm0_2.objectX, ctx, depth + 1);
            if (objStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            if (implicitsStatus === UnifyResult.Solved && funcStatus === UnifyResult.Solved && objStatus === UnifyResult.Solved) return UnifyResult.Solved;
            return UnifyResult.Progress;
        }
        case 'FMap1Term': {
            const fm1_1 = rt1_final as Term & {tag:'FMap1Term'}; const fm1_2 = rt2_final as Term & {tag:'FMap1Term'};
            const implicitsStatus = unifyArgs(
                [fm1_1.catA_IMPLICIT, fm1_1.catB_IMPLICIT, fm1_1.objX_A_IMPLICIT, fm1_1.objY_A_IMPLICIT],
                [fm1_2.catA_IMPLICIT, fm1_2.catB_IMPLICIT, fm1_2.objX_A_IMPLICIT, fm1_2.objY_A_IMPLICIT],
                ctx, depth + 1
            );
            if (implicitsStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const funcStatus = unify(fm1_1.functor, fm1_2.functor, ctx, depth + 1);
            if (funcStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const morphStatus = unify(fm1_1.morphism_a, fm1_2.morphism_a, ctx, depth + 1);
            if (morphStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            if (implicitsStatus === UnifyResult.Solved && funcStatus === UnifyResult.Solved && morphStatus === UnifyResult.Solved) return UnifyResult.Solved;
            return UnifyResult.Progress;
        }
        case 'NatTransTypeTerm': {
            const nt1 = rt1_final as Term & {tag:'NatTransTypeTerm'}; const nt2 = rt2_final as Term & {tag:'NatTransTypeTerm'};
            const catAStatus = unify(nt1.catA, nt2.catA, ctx, depth + 1);
            if (catAStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const catBStatus = unify(nt1.catB, nt2.catB, ctx, depth + 1);
            if (catBStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const funFStatus = unify(nt1.functorF, nt2.functorF, ctx, depth + 1);
            if (funFStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const funGStatus = unify(nt1.functorG, nt2.functorG, ctx, depth + 1);
            if (funGStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            if (catAStatus === UnifyResult.Solved && catBStatus === UnifyResult.Solved && funFStatus === UnifyResult.Solved && funGStatus === UnifyResult.Solved) return UnifyResult.Solved;
            return UnifyResult.Progress;
        }
        case 'NatTransComponentTerm': {
            const nc1 = rt1_final as Term & {tag:'NatTransComponentTerm'}; const nc2 = rt2_final as Term & {tag:'NatTransComponentTerm'};
            const implicitsStatus = unifyArgs(
                [nc1.catA_IMPLICIT, nc1.catB_IMPLICIT, nc1.functorF_IMPLICIT, nc1.functorG_IMPLICIT],
                [nc2.catA_IMPLICIT, nc2.catB_IMPLICIT, nc2.functorF_IMPLICIT, nc2.functorG_IMPLICIT],
                ctx, depth + 1
            );
            if (implicitsStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const transStatus = unify(nc1.transformation, nc2.transformation, ctx, depth + 1);
            if (transStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const objStatus = unify(nc1.objectX, nc2.objectX, ctx, depth + 1);
            if (objStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            if (implicitsStatus === UnifyResult.Solved && transStatus === UnifyResult.Solved && objStatus === UnifyResult.Solved) return UnifyResult.Solved;
            return UnifyResult.Progress;
        }
        case 'HomCovFunctorIdentity': {
            const hc1 = rt1_final as Term & {tag:'HomCovFunctorIdentity'};
            const hc2 = rt2_final as Term & {tag:'HomCovFunctorIdentity'};
            const domainStatus = unify(hc1.domainCat, hc2.domainCat, ctx, depth + 1);
            if (domainStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const objWStatus = unify(hc1.objW_InDomainCat, hc2.objW_InDomainCat, ctx, depth + 1);
            if (objWStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            if (domainStatus === UnifyResult.Solved && objWStatus === UnifyResult.Solved) return UnifyResult.Solved;
            return UnifyResult.Progress;
        }
        case 'SetTerm': return UnifyResult.Solved;
        default:
            // This case should ideally not be reached if tags are identical and handled above.
            // If it is, it implies a missing specific handler for a tag.
            const unhandledTag = (rt1_final as any)?.tag || 'unknown_tag';
            console.warn(`Unify: Unhandled identical tag in switch (after WHNF): ${unhandledTag}`);
            return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }
}

export function collectPatternVars(term: Term, patternVarDecls: PatternVarDecl[], collectedVars: Set<string>, visited: Set<Term> = new Set()): void {
    const current = getTermRef(term);
    if (visited.has(current) && current.tag !== 'Var' && current.tag !== 'Hole') return; 
    visited.add(current);

    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        collectedVars.add(current.name);
    } else if (current.tag === 'Hole' && isPatternVarName(current.id, patternVarDecls)) {
        collectedVars.add(current.id);
    }

    switch (current.tag) {
        case 'App':
            collectPatternVars(current.func, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.arg, patternVarDecls, collectedVars, visited);
            break;
        case 'Lam':
            if (current.paramType) collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            // Note: Lam body is a function, can't easily traverse its structure for pattern vars here.
            // Pattern matching on Lam bodies typically involves instantiating with a fresh var and matching the result.
            break;
        case 'Pi':
            collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            // Similar to Lam, Pi bodyType is a function.
            break;
        case 'ObjTerm': collectPatternVars(current.cat, patternVarDecls, collectedVars, visited); break;
        case 'HomTerm':
            collectPatternVars(current.cat, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.dom, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.cod, patternVarDecls, collectedVars, visited);
            break;
        case 'FunctorCategoryTerm':
            collectPatternVars(current.domainCat, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.codomainCat, patternVarDecls, collectedVars, visited);
            break;
        case 'FMap0Term':
            collectPatternVars(current.functor, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.objectX, patternVarDecls, collectedVars, visited);
            if(current.catA_IMPLICIT) collectPatternVars(current.catA_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.catB_IMPLICIT) collectPatternVars(current.catB_IMPLICIT, patternVarDecls, collectedVars, visited);
            break;
        case 'FMap1Term':
            collectPatternVars(current.functor, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.morphism_a, patternVarDecls, collectedVars, visited);
            if(current.catA_IMPLICIT) collectPatternVars(current.catA_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.catB_IMPLICIT) collectPatternVars(current.catB_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.objX_A_IMPLICIT) collectPatternVars(current.objX_A_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.objY_A_IMPLICIT) collectPatternVars(current.objY_A_IMPLICIT, patternVarDecls, collectedVars, visited);
            break;
        case 'NatTransTypeTerm':
            collectPatternVars(current.catA, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.catB, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.functorF, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.functorG, patternVarDecls, collectedVars, visited);
            break;
        case 'NatTransComponentTerm':
            collectPatternVars(current.transformation, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.objectX, patternVarDecls, collectedVars, visited);
            if(current.catA_IMPLICIT) collectPatternVars(current.catA_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.catB_IMPLICIT) collectPatternVars(current.catB_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.functorF_IMPLICIT) collectPatternVars(current.functorF_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.functorG_IMPLICIT) collectPatternVars(current.functorG_IMPLICIT, patternVarDecls, collectedVars, visited);
            break;
        case 'HomCovFunctorIdentity':
            collectPatternVars(current.domainCat, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.objW_InDomainCat, patternVarDecls, collectedVars, visited);
            break;
        case 'SetTerm': break; // No subterms with pattern variables
    }
}

export function applyAndAddRuleConstraints(rule: {lhsPattern1: Term, lhsPattern2: Term, patternVars: PatternVarDecl[], rhsNewConstraints: Array<{t1:Term, t2:Term}>, name: string}, subst: Substitution, ctx: Context): void {
    const lhsVars = new Set<string>(); 
    collectPatternVars(rule.lhsPattern1, rule.patternVars, lhsVars);
    collectPatternVars(rule.lhsPattern2, rule.patternVars, lhsVars);

    const finalSubst = new Map(subst); 

    for (const pVarDecl of rule.patternVars) {
        const pVarName = pVarDecl; 
        if (pVarName === '_') continue; 

        let usedInRhsConstraints = false;
        for(const {t1: rhs_t1, t2: rhs_t2} of rule.rhsNewConstraints) {
            const rhsConstraintVars = new Set<string>();
            collectPatternVars(rhs_t1, rule.patternVars, rhsConstraintVars);
            collectPatternVars(rhs_t2, rule.patternVars, rhsConstraintVars);
            if (rhsConstraintVars.has(pVarName)) {
                usedInRhsConstraints = true;
                break;
            }
        }
        if (usedInRhsConstraints && !lhsVars.has(pVarName) && !finalSubst.has(pVarName)) {
             finalSubst.set(pVarName, Hole(freshHoleName() + "_unifRuleRHS_" + pVarName.substring(1)));
        }
    }

    for (const constrPair of rule.rhsNewConstraints) {
        const newT1 = applySubst(constrPair.t1, finalSubst, rule.patternVars);
        const newT2 = applySubst(constrPair.t2, finalSubst, rule.patternVars);
        addConstraint(newT1, newT2, `UnifRule ${rule.name}`);
    }
}

export function tryUnificationRules(t1: Term, t2: Term, ctx: Context, depth: number): UnifyResult {
    for (const rule of userUnificationRules) {
        let subst1 = matchPattern(rule.lhsPattern1, t1, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t2, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) { 
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }
        subst1 = matchPattern(rule.lhsPattern1, t2, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t1, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) { 
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }
    }
    return UnifyResult.Failed; 
}

export function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > MAX_STACK_DEPTH * 2) throw new Error("solveConstraints stack depth exceeded");

    if (solveConstraintsControl.depth > 0 && stackDepth > 0) { 
        // consoleLog(`[solveConstraints SKIPPING RE-ENTRANT CALL] depth: ${solveConstraintsControl.depth}, stack: ${stackDepth}`);
        return true; 
    }

    solveConstraintsControl.depth++;
    let changedInOuterLoop = true;
    let iterations = 0;
    const maxIterations = (constraints.length * constraints.length + userUnificationRules.length * constraints.length + 100) * 2 + 200;

    while (changedInOuterLoop && iterations < maxIterations) {
        changedInOuterLoop = false;
        iterations++;
        let currentConstraintIdx = 0;
        while(currentConstraintIdx < constraints.length) { 
            const constraint = constraints[currentConstraintIdx];
            const c_t1_current_ref = getTermRef(constraint.t1);
            const c_t2_current_ref = getTermRef(constraint.t2);

            if (areEqual(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1)) {
                constraints.splice(currentConstraintIdx, 1); 
                changedInOuterLoop = true; 
                continue;
            }
            
            try {
                const unifyResult = unify(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1);

                if (unifyResult === UnifyResult.Solved) {
                    if (areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
                        constraints.splice(currentConstraintIdx, 1); 
                    } else {
                        currentConstraintIdx++;
                    }
                    changedInOuterLoop = true;
                } else if (unifyResult === UnifyResult.RewrittenByRule) {
                    constraints.splice(currentConstraintIdx, 1);
                    changedInOuterLoop = true;
                } else if (unifyResult === UnifyResult.Progress) {
                    changedInOuterLoop = true; 
                    currentConstraintIdx++;
                } else { 
                    console.log(`[solveConstraints DEBUG] UnifyResult.Failed for constraint: ${printTerm(c_t1_current_ref)} vs ${printTerm(c_t2_current_ref)} (orig: ${constraint.origin || 'unknown'})`);
                    console.warn(`Unification failed permanently for constraint: ${printTerm(c_t1_current_ref)} === ${printTerm(c_t2_current_ref)} (orig: ${constraint.origin || 'unknown'})`);
                    return false; 
                }
            } catch (e) {
                console.error(`Error during unification of ${printTerm(c_t1_current_ref)} and ${printTerm(c_t2_current_ref)} (origin: ${constraint.origin || 'unknown'}): ${(e as Error).message}`);
                console.error((e as Error).stack);
                return false; 
            }
        } 
    } 

    if (iterations >= maxIterations && changedInOuterLoop && constraints.length > 0) {
        console.log({constraints}, printTerm(constraints[0].t1), printTerm(constraints[0].t2));
        console.warn("Constraint solving reached max iterations and was still making changes. Constraints left: " + constraints.length);
    }

    const allSolved = constraints.length === 0 || constraints.every(c => areEqual(getTermRef(c.t1), getTermRef(c.t2), ctx, stackDepth + 1));
    if(allSolved && constraints.length > 0) constraints.length = 0; 

    solveConstraintsControl.depth--;
    return allSolved; 
}