/**
 * @file logic.ts
 * @description Implements the core logical operations of the type theory,
 * including Weak Head Normal Form (WHNF) reduction, normalization,
 * equality checking (convertibility), unification, pattern matching, and substitution.
 */

import {
    Term, Context, PatternVarDecl, Substitution, UnifyResult, Icit, Hole, App, Lam, Pi, Var,
    ObjTerm, HomTerm, Type, CatTerm, FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm,
    NatTransComponentTerm, HomCovFunctorIdentity, SetTerm, FunctorTypeTerm
} from './types';
import {
    getTermRef, consoleLog, globalDefs, userRewriteRules, addConstraint, constraints, emptyCtx,
    extendCtx, lookupCtx, isKernelConstantSymbolStructurally, isEmdashUnificationInjectiveStructurally,
    userUnificationRules, freshVarName, freshHoleName, solveConstraintsControl, printTerm
} from './state';

export const MAX_WHNF_ITERATIONS = 10000; // Max steps for WHNF reduction to prevent infinite loops.
export const MAX_STACK_DEPTH = 20000;   // Max recursion depth for various logical operations.

/**
 * Checks if two terms are structurally equal without performing WHNF reduction.
 * This is a stricter form of equality, comparing the raw structure of terms.
 * @param t1 The first term.
 * @param t2 The second term.
 * @param ctx The current context.
 * @param depth Recursion depth.
 * @returns True if structurally equal, false otherwise.
 */
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
            const extendedCtx = extendCtx(ctx, freshVName, paramTypeForCtx, rt1.icit);
            return areStructurallyEqualNoWhnf(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            if (!areStructurallyEqualNoWhnf(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            const freshVName = rt1.paramName;
            const freshV = Var(freshVName, true);
            const extendedCtx = extendCtx(ctx, freshVName, getTermRef(rt1.paramType), rt1.icit);
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
        case 'FunctorTypeTerm': {
            const ftt2 = rt2 as Term & {tag:'FunctorTypeTerm'};
            return areStructurallyEqualNoWhnf(rt1.domainCat, ftt2.domainCat, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.codomainCat, ftt2.codomainCat, ctx, depth + 1);
        }
        case 'FMap0Term': {
            const fm0_2 = rt2 as Term & {tag:'FMap0Term'};
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areStructurallyEqualNoWhnf(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2; // Both must be undefined or both defined and equal
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
            const exhaustiveCheck: never = rt1; return false; // Should be unreachable
    }
}

/**
 * Reduces a term to its Weak Head Normal Form (WHNF).
 * This involves performing beta-reductions at the head of the term,
 * unfolding global definitions, and applying rewrite rules.
 * @param term The term to reduce.
 * @param ctx The current context.
 * @param stackDepth Recursion depth.
 * @returns The term in WHNF.
 */
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

        // Check for local definitions first
        if (current.tag === 'Var') {
            const binding = lookupCtx(ctx, current.name);
            if (binding && binding.definition) {
                current = binding.definition; // Substitute with the definition
                changedInThisPass = true;
                continue; // Restart the whnf loop with the new term
            }
        }

        // Apply user rewrite rules (if not a kernel constant symbol)
        if (!isKernelConstantSymbolStructurally(current)) {
            for (const rule of userRewriteRules) {
                const subst = matchPattern(rule.elaboratedLhs, termBeforeInnerReductions, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    const rhsApplied = getTermRef(applySubst(rule.elaboratedRhs, subst, rule.patternVars));
                    // Check for actual change to prevent non-terminating rule applications like X -> X
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
                    // Beta reduction
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
                    // Hom in functor category is NatTransType
                    current = NatTransTypeTerm(cat_whnf_ref.domainCat, cat_whnf_ref.codomainCat, current.dom, current.cod);
                    reducedInKernelBlock = true;
                } else if (getTermRef(current.cat) !== cat_whnf_ref) {
                    current = HomTerm(cat_whnf_ref, current.dom, current.cod);
                    reducedInKernelBlock = true;
                } else {
                    // Hom in Set is Pi type
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
            case 'Var': { // Global definition unfolding (if no local definition was found)
                const gdef = globalDefs.get(current.name);
                if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol && !gdef.isTypeNameLike) {
                    current = gdef.value;
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'FMap0Term': {
                const functor_whnf = getTermRef(whnf(current.functor, ctx, stackDepth + 1));
                if (functor_whnf.tag === 'HomCovFunctorIdentity') {
                    // Rule: fapp0 (hom_cov A W) Y  ↪  Hom A W Y
                    current = HomTerm(functor_whnf.domainCat, functor_whnf.objW_InDomainCat, current.objectX);
                    reducedInKernelBlock = true;
                } else {
                    const objectX_whnf = getTermRef(whnf(current.objectX, ctx, stackDepth + 1));
                    const catA_IMPLICIT_whnf = current.catA_IMPLICIT ? getTermRef(whnf(current.catA_IMPLICIT, ctx, stackDepth + 1)) : undefined;
                    const catB_IMPLICIT_whnf = current.catB_IMPLICIT ? getTermRef(whnf(current.catB_IMPLICIT, ctx, stackDepth + 1)) : undefined;

                    if (getTermRef(current.functor) !== functor_whnf ||
                        getTermRef(current.objectX) !== objectX_whnf ||
                        (current.catA_IMPLICIT && getTermRef(current.catA_IMPLICIT) !== catA_IMPLICIT_whnf) ||
                        (current.catB_IMPLICIT && getTermRef(current.catB_IMPLICIT) !== catB_IMPLICIT_whnf)
                    ) {
                        current = FMap0Term(functor_whnf, objectX_whnf, catA_IMPLICIT_whnf, catB_IMPLICIT_whnf);
                        reducedInKernelBlock = true;
                    }
                }
                break;
            }
            case 'FunctorTypeTerm': {
                const domainCat_whnf = getTermRef(whnf(current.domainCat, ctx, stackDepth + 1));
                const codomainCat_whnf = getTermRef(whnf(current.codomainCat, ctx, stackDepth + 1));
                if (getTermRef(current.domainCat) !== domainCat_whnf || getTermRef(current.codomainCat) !== codomainCat_whnf) {
                    current = FunctorTypeTerm(domainCat_whnf, codomainCat_whnf);
                    reducedInKernelBlock = true;
                }
                break;
            }
        }

        if (reducedInKernelBlock) {
             changedInThisPass = true;
             continue; // Restart WHNF with the kernel-reduced term
        }

        // If only getTermRef changed the term, update and mark progress
        const currentAfterPossibleKernelOrRefChange = getTermRef(current);
        if (currentAfterPossibleKernelOrRefChange !== termBeforeInnerReductions && !changedInThisPass) {
            current = currentAfterPossibleKernelOrRefChange;
            changedInThisPass = true;
        }

        if (!changedInThisPass) break; // No change in this pass, term is in WHNF

        // Check for non-productive loops (term reduces to itself structurally)
        if (current === termAtStartOfOuterPass && !changedInThisPass && i > 0) break;


        if (i === MAX_WHNF_ITERATIONS - 1) {
             if (changedInThisPass || current !== termAtStartOfOuterPass) { // Check if it was still changing
                console.warn(`[TRACE whnf (${stackDepth})] WHNF reached max iterations for: ${printTerm(term)} -> ${printTerm(current)}`);
             }
        }
    }
    return current;
}

/**
 * Normalizes a term by reducing it to WHNF and then recursively normalizing its subterms.
 * @param term The term to normalize.
 * @param ctx The current context.
 * @param stackDepth Recursion depth.
 * @returns The normalized term.
 */
export function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Normalize stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    const headReduced = whnf(term, ctx, stackDepth + 1);
    const current = getTermRef(headReduced);
    switch (current.tag) {
        case 'Type': case 'Var' : case 'Hole': case 'CatTerm': case 'SetTerm': return current;
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
        case 'FunctorTypeTerm':
            return FunctorTypeTerm(
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
                const paramTypeForBodyCtx = normLamParamType ||
                                            (currentLam.paramType ? getTermRef(currentLam.paramType) : Hole(freshHoleName()+"_norm_lam_body_ctx"));
                const bodyCtx = extendCtx(ctx, currentLam.paramName, paramTypeForBodyCtx, currentLam.icit);
                return normalize(currentLam.body(v_arg_placeholder), bodyCtx, stackDepth + 1);
            };
            const normLam = Lam(currentLam.paramName, currentLam.icit, normLamParamType, newBodyFn) as Term & {tag: 'Lam'};
            normLam._isAnnotated = currentLam._isAnnotated && normLamParamType !== undefined;
            return normLam;
        }
        case 'App': {
            const normFunc = normalize(current.func, ctx, stackDepth + 1);
            const normArg = normalize(current.arg, ctx, stackDepth + 1);
            const finalNormFunc = getTermRef(normFunc);

            if (finalNormFunc.tag === 'Lam' && finalNormFunc.icit === current.icit) {
                // Beta reduction during normalization
                const bodyParamType = finalNormFunc.paramType ?
                                      getTermRef(finalNormFunc.paramType) :
                                      Hole(freshHoleName() + "_beta_param_type_");
                const extendedCtxForBody = extendCtx(
                    ctx,
                    finalNormFunc.paramName,
                    bodyParamType,
                    finalNormFunc.icit,
                    normArg // Definition for the parameter
                );
                // The body needs to be instantiated with Var(paramName) which will be substituted by whnf
                return normalize(finalNormFunc.body(Var(finalNormFunc.paramName, true)), extendedCtxForBody, stackDepth + 1);
            }
            return App(normFunc, normArg, current.icit);
        }
        case 'Pi': {
            const currentPi = current;
            const normPiParamType = normalize(currentPi.paramType, ctx, stackDepth + 1);
            const newBodyTypeFn = (v_arg_placeholder: Term): Term => {
                const bodyTypeCtx = extendCtx(ctx, currentPi.paramName, normPiParamType, currentPi.icit);
                return normalize(currentPi.bodyType(v_arg_placeholder), bodyTypeCtx, stackDepth + 1);
            };
            return Pi(currentPi.paramName, currentPi.icit, normPiParamType, newBodyTypeFn);
        }
        default: const exhaustiveCheck: never = current; throw new Error(`Normalize: Unhandled term: ${(exhaustiveCheck as any).tag }`);
    }
}

/**
 * Checks if two terms are equal (convertible) under the type theory.
 * This involves reducing both terms to WHNF and then comparing them structurally.
 * @param t1 The first term.
 * @param t2 The second term.
 * @param ctx The current context.
 * @param depth Recursion depth.
 * @returns True if the terms are equal, false otherwise.
 */
export function areEqual(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Equality check depth exceeded (areEqual depth: ${depth})`);
    const rt1 = getTermRef(whnf(t1, ctx, depth + 1));
    const rt2 = getTermRef(whnf(t2, ctx, depth + 1));

    // Structural comparison after WHNF
    return areStructurallyEqualNoWhnf(rt1, rt2, ctx, depth + 1);
}

/**
 * Checks if a term contains a specific hole.
 * Used for the occurs check in unification.
 * @param term The term to search within.
 * @param holeId The ID of the hole to find.
 * @param visited Set to track visited terms for cycle detection (especially within Hole refs).
 * @param depth Recursion depth.
 * @returns True if the hole is found, false otherwise.
 */
export function termContainsHole(term: Term, holeId: string, visited: Set<string> = new Set(), depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH * 2) { // Increased depth for occurs check
        console.warn(`termContainsHole depth exceeded for hole ${holeId} in ${printTerm(term)}`);
        return true; // Fail safe: assume it contains the hole to prevent unsound unification.
    }

    const current = getTermRef(term);

    // Create a unique key for the visited set. For Holes/Vars, use their ID/name. For others, use printTerm (could be slow but safer for complex structures).
    const termKey = current.tag === 'Hole' ? `Hole:${current.id}` :
                    current.tag === 'Var' ? `Var:${current.name}` :
                    printTerm(current); // Fallback for complex terms, might need optimization if performance becomes an issue.

    if (visited.has(termKey) && current.tag !== 'Hole' && current.tag !== 'Var' ) {
         // Avoid re-processing complex structures if already seen, unless it's a Hole/Var that could change.
         return false;
    }
    visited.add(termKey);


    switch (current.tag) {
        case 'Hole': return current.id === holeId;
        case 'Type': case 'Var': case 'CatTerm': case 'SetTerm': return false;
        case 'App':
            return termContainsHole(current.func, holeId, visited, depth + 1) ||
                   termContainsHole(current.arg, holeId, visited, depth + 1);
        case 'Lam': {
            const lam = current;
            if (lam.paramType && termContainsHole(lam.paramType, holeId, visited, depth + 1)) return true;
            // For Lam/Pi body, use a fresh Var to instantiate and check.
            // Create a new visited set for the body to avoid cross-scope false positives from the termKey of the placeholder.
            const freshVLam = Var(freshVarName("occ_check_lam_"), true, "occurs_check");
            return termContainsHole(lam.body(freshVLam), holeId, new Set(visited) , depth + 1);
        }
        case 'Pi': {
            const pi = current;
            if (termContainsHole(pi.paramType, holeId, visited, depth + 1)) return true;
            const freshVPi = Var(freshVarName("occ_check_pi_"), true, "occurs_check");
            return termContainsHole(pi.bodyType(freshVPi), holeId, new Set(visited) , depth + 1);
        }
        case 'ObjTerm': return termContainsHole(current.cat, holeId, visited, depth + 1);
        case 'HomTerm':
            return termContainsHole(current.cat, holeId, visited, depth + 1) ||
                   termContainsHole(current.dom, holeId, visited, depth + 1) ||
                   termContainsHole(current.cod, holeId, visited, depth + 1);
        case 'FunctorCategoryTerm':
        case 'FunctorTypeTerm':
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
        default: const exhaustiveCheck: never = current; return false; // Should be unreachable
    }
}

/**
 * Unifies a hole with a term. This involves an occurs check.
 * @param hole The hole term (must be tag: 'Hole').
 * @param term The term to unify the hole with.
 * @param ctx The current context.
 * @param depth Recursion depth.
 * @returns True if unification was successful, false otherwise (e.g., occurs check failed).
 */
export function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
    const normTerm = getTermRef(whnf(term, ctx, depth + 1));
    if (normTerm.tag === 'Hole') {
        if (hole.id === normTerm.id) return true; // Unifying a hole with itself
        // Prefer assigning the hole with the "larger" ID to the one with the "smaller" ID
        // to create shorter reference chains. This is a heuristic.
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
    // Sanity check right after setting if getTermRef sees it
    const currentValOfHole = getTermRef(hole);
    consoleLog(`[UnifyHole] ${hole.id} now points to (via getTermRef): ${printTerm(currentValOfHole)}. Direct hole.ref: ${printTerm(hole.ref!)}. (depth ${depth})`);
    return true;
}

/**
 * Unifies lists of arguments. Used for unifying components of structured terms.
 * @param args1 Array of first terms (or undefined for placeholders).
 * @param args2 Array of second terms (or undefined for placeholders).
 * @param ctx The current context.
 * @param depth Recursion depth.
 * @returns The result of the unification attempt.
 */
export function unifyArgs(args1: (Term | undefined)[], args2: (Term | undefined)[], ctx: Context, depth: number): UnifyResult {
    if (args1.length !== args2.length) return UnifyResult.Failed;
    let madeProgressOverall = false;
    let allSubSolved = true;

    for (let i = 0; i < args1.length; i++) {
        const t1_arg = args1[i];
        const t2_arg = args2[i];

        if (t1_arg === undefined && t2_arg === undefined) continue; // Both are wildcards, skip.

        // If one is undefined, create a fresh hole. This allows partial matching in structural unification.
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
    return madeProgressOverall ? UnifyResult.Progress : UnifyResult.Progress; // If not all solved but no failure, it's progress.
}


/**
 * Attempts to unify two terms, making them equal.
 * This is the core of the constraint solving mechanism.
 * @param t1 The first term.
 * @param t2 The second term.
 * @param ctx The current context.
 * @param depth Recursion depth.
 * @returns The result of the unification attempt.
 */
export function unify(t1: Term, t2: Term, ctx: Context, depth = 0): UnifyResult {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Unification stack depth exceeded (Unify depth: ${depth}, ${printTerm(t1)} vs ${printTerm(t2)})`);

    let current_t1 = getTermRef(t1);
    let current_t2 = getTermRef(t2);

    // If already structurally identical (and not holes), they are solved.
    if (current_t1 === current_t2 && current_t1.tag !== 'Hole') return UnifyResult.Solved;

    // Handle hole unification first.
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

        if (isEmdashUnificationInjectiveStructurally(commonTag)) {
            switch (commonTag) {
                case 'Type': case 'CatTerm': case 'SetTerm':
                    structuralResult = UnifyResult.Solved;
                    break;
                case 'Var':
                    structuralResult = (current_t1 as Term & {tag:'Var'}).name === (current_t2 as Term & {tag:'Var'}).name ? UnifyResult.Solved : UnifyResult.Failed;
                    break;
                case 'ObjTerm':
                    structuralResult = unify((current_t1 as Term & {tag:'ObjTerm'}).cat, (current_t2 as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
                    break;
                case 'HomTerm': {
                    const hom1 = current_t1 as Term & {tag:'HomTerm'}; const hom2 = current_t2 as Term & {tag:'HomTerm'};
                    structuralResult = unifyArgs([hom1.cat, hom1.dom, hom1.cod], [hom2.cat, hom2.dom, hom2.cod], ctx, depth + 1);
                    break;
                }
                case 'FunctorCategoryTerm':
                case 'FunctorTypeTerm': {
                    const fc1 = current_t1 as Term & {tag:'FunctorCategoryTerm'|'FunctorTypeTerm'}; const fc2 = current_t2 as Term & {tag:'FunctorCategoryTerm'|'FunctorTypeTerm'};
                    structuralResult = unifyArgs([fc1.domainCat, fc1.codomainCat], [fc2.domainCat, fc2.codomainCat], ctx, depth +1);
                    break;
                }
                // FMap0/1, NatTransComponent/Type are handled after WHNF usually or by specific unification rules if needed.
                // Here, we handle only the strictly structural ones marked by EMDASH_UNIFICATION_INJECTIVE_TAGS.
                // Other injective cases (like App with injective head) are handled after WHNF.
            }
        }

        if (structuralResult !== undefined) {
            if (structuralResult === UnifyResult.Solved || structuralResult === UnifyResult.Failed) {
                 return (structuralResult === UnifyResult.Failed) ? tryUnificationRules(current_t1, current_t2, ctx, depth + 1) : structuralResult;
            }
            // If progress, continue to WHNF phase.
        }
    }

    // Phase 2: Reduce to WHNF and then unify.
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

    // After WHNF, if tags differ, try unification rules or fail.
    if (rt1_final.tag !== rt2_final.tag) {
        // Special kernel rule: Obj A === Type implies A === Set
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

    // Icit check for App, Lam, Pi
    if ((rt1_final.tag === 'App' || rt1_final.tag === 'Lam' || rt1_final.tag === 'Pi') &&
        (rt1_final.icit !== (rt2_final as typeof rt1_final).icit)) {
         return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }

    // Helper to find the ultimate head of an application chain
    const getUltimateHead = (term: Term): Term => {
        let currentHead = getTermRef(term);
        while (currentHead.tag === 'App') {
            currentHead = getTermRef(currentHead.func);
        }
        return currentHead;
    };

    switch (rt1_final.tag) {
        case 'Type': case 'CatTerm': case 'SetTerm': return UnifyResult.Solved;
        case 'Var': {
            const var1 = rt1_final; const var2 = rt2_final as Term & {tag:'Var'};
            if (var1.name === var2.name) return UnifyResult.Solved;

            const gdef1 = globalDefs.get(var1.name);
            const gdef2 = globalDefs.get(var2.name);
            if (gdef1 && gdef1.isConstantSymbol && gdef2 && gdef2.isConstantSymbol) {
                consoleLog(`[Unify Var CONSTANT MISMATCH] ${var1.name} vs ${var2.name}`);
                return UnifyResult.Failed;
            }
            return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        }
        case 'App': {
            const app1 = rt1_final; const app2 = rt2_final as Term & {tag:'App'};
            const ultimateHead1 = getUltimateHead(app1);
            const ultimateHead2 = getUltimateHead(app2);

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
                if (gdef && gdef.isInjective) { // Injective global function symbol
                    // Unify function parts then argument parts
                    const funcStatus = unify(app1.func, app2.func, ctx, depth + 1);
                    if (funcStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
                    const argStatus = unify(app1.arg, app2.arg, ctx, depth + 1);
                    if (argStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

                    if (funcStatus === UnifyResult.Solved && argStatus === UnifyResult.Solved) return UnifyResult.Solved;
                    return UnifyResult.Progress;
                }
            }
            // Default App unification (non-injective head or different heads)
            const funcUnifyStatus = unify(app1.func, app2.func, ctx, depth + 1);
            if (funcUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const argUnifyStatus = unify(app1.arg, app2.arg, ctx, depth + 1);
            if (argUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            if (funcUnifyStatus === UnifyResult.Solved && argUnifyStatus === UnifyResult.Solved) return UnifyResult.Solved;
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

            if(paramTypeStatus === UnifyResult.Solved && bodyStatus === UnifyResult.Solved) return UnifyResult.Solved;
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

            if(paramTypeStatus === UnifyResult.Solved && bodyTypeStatus === UnifyResult.Solved) return UnifyResult.Solved;
            return UnifyResult.Progress;
        }
        case 'ObjTerm': {
            const argStatus = unify((rt1_final as Term & {tag:'ObjTerm'}).cat, (rt2_final as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
            return (argStatus === UnifyResult.Failed) ? tryUnificationRules(rt1_final, rt2_final, ctx, depth +1) : argStatus;
        }
        case 'HomTerm': {
            const hom1 = rt1_final as Term & {tag:'HomTerm'}; const hom2 = rt2_final as Term & {tag:'HomTerm'};
            return unifyArgs(
                [hom1.cat, hom1.dom, hom1.cod],
                [hom2.cat, hom2.dom, hom2.cod],
                ctx, depth + 1
            );
        }
        case 'FunctorCategoryTerm':
        case 'FunctorTypeTerm': {
            const fc1 = rt1_final as Term & {tag:'FunctorCategoryTerm'|'FunctorTypeTerm'};
            const fc2 = rt2_final as Term & {tag:'FunctorCategoryTerm'|'FunctorTypeTerm'};
            return unifyArgs([fc1.domainCat, fc1.codomainCat], [fc2.domainCat, fc2.codomainCat], ctx, depth + 1);
        }
        case 'FMap0Term': {
            const fm0_1 = rt1_final as Term & {tag:'FMap0Term'}; const fm0_2 = rt2_final as Term & {tag:'FMap0Term'};
            return unifyArgs(
                [fm0_1.functor, fm0_1.objectX, fm0_1.catA_IMPLICIT, fm0_1.catB_IMPLICIT],
                [fm0_2.functor, fm0_2.objectX, fm0_2.catA_IMPLICIT, fm0_2.catB_IMPLICIT],
                ctx, depth + 1
            );
        }
        case 'FMap1Term': {
            const fm1_1 = rt1_final as Term & {tag:'FMap1Term'}; const fm1_2 = rt2_final as Term & {tag:'FMap1Term'};
            return unifyArgs(
                [fm1_1.functor, fm1_1.morphism_a, fm1_1.catA_IMPLICIT, fm1_1.catB_IMPLICIT, fm1_1.objX_A_IMPLICIT, fm1_1.objY_A_IMPLICIT],
                [fm1_2.functor, fm1_2.morphism_a, fm1_2.catA_IMPLICIT, fm1_2.catB_IMPLICIT, fm1_2.objX_A_IMPLICIT, fm1_2.objY_A_IMPLICIT],
                ctx, depth + 1
            );
        }
        case 'NatTransTypeTerm': {
            const nt1 = rt1_final as Term & {tag:'NatTransTypeTerm'}; const nt2 = rt2_final as Term & {tag:'NatTransTypeTerm'};
            return unifyArgs(
                [nt1.catA, nt1.catB, nt1.functorF, nt1.functorG],
                [nt2.catA, nt2.catB, nt2.functorF, nt2.functorG],
                ctx, depth + 1
            );
        }
        case 'NatTransComponentTerm': {
            const nc1 = rt1_final as Term & {tag:'NatTransComponentTerm'}; const nc2 = rt2_final as Term & {tag:'NatTransComponentTerm'};
            return unifyArgs(
                [nc1.transformation, nc1.objectX, nc1.catA_IMPLICIT, nc1.catB_IMPLICIT, nc1.functorF_IMPLICIT, nc1.functorG_IMPLICIT],
                [nc2.transformation, nc2.objectX, nc2.catA_IMPLICIT, nc2.catB_IMPLICIT, nc2.functorF_IMPLICIT, nc2.functorG_IMPLICIT],
                ctx, depth + 1
            );
        }
        case 'HomCovFunctorIdentity': {
            const hc1 = rt1_final as Term & {tag:'HomCovFunctorIdentity'};
            const hc2 = rt2_final as Term & {tag:'HomCovFunctorIdentity'};
            return unifyArgs([hc1.domainCat, hc1.objW_InDomainCat], [hc2.domainCat, hc2.objW_InDomainCat], ctx, depth + 1);
        }
        default:
            const unhandledTag = (rt1_final as any)?.tag || 'unknown_tag';
            console.warn(`Unify: Unhandled identical tag in switch (after WHNF): ${unhandledTag}`);
            return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }
}

/**
 * Checks if a string is a declared pattern variable.
 * @param name The string to check.
 * @param patternVarDecls Array of declared pattern variable names.
 * @returns True if the name is a pattern variable, false otherwise.
 */
export function isPatternVarName(name: string, patternVarDecls: PatternVarDecl[]): boolean {
    return name.startsWith('$') && patternVarDecls.includes(name);
}

/**
 * Matches a pattern term against a subject term.
 * @param pattern The pattern term.
 * @param termToMatch The subject term to match against.
 * @param ctx The current context.
 * @param patternVarDecls Declared pattern variables for this rule.
 * @param currentSubst Current substitution (for accumulating matches).
 * @param stackDepth Recursion depth.
 * @returns A substitution if matching succeeds, null otherwise.
 */
export function matchPattern(
    pattern: Term,
    termToMatch: Term,
    ctx: Context,
    patternVarDecls: PatternVarDecl[],
    currentSubst?: Substitution,
    stackDepth = 0
): Substitution | null {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`matchPattern stack depth exceeded for pattern ${printTerm(pattern)} vs term ${printTerm(termToMatch)}`);

    const rtPattern = getTermRef(pattern);
    const rtTermToMatch = getTermRef(termToMatch);

    const subst = currentSubst ? new Map(currentSubst) : new Map<string, Term>();

    // Pattern variable matching
    if (rtPattern.tag === 'Var' && isPatternVarName(rtPattern.name, patternVarDecls)) {
        const pvarName = rtPattern.name;
        if (pvarName === '_') return subst; // Wildcard matches anything without binding
        const existing = subst.get(pvarName);
        if (existing) { // If already bound, check for consistency
            return areEqual(rtTermToMatch, getTermRef(existing), ctx, stackDepth + 1) ? subst : null;
        }
        subst.set(pvarName, rtTermToMatch);
        return subst;
    }

    // Hole as pattern variable (e.g. in implicit args of kernel terms in rules)
    if (rtPattern.tag === 'Hole') {
        if (rtPattern.id === '_') return subst; // Wildcard hole
        if (isPatternVarName(rtPattern.id, patternVarDecls)) {
            const pvarId = rtPattern.id;
            const existing = subst.get(pvarId);
            if (existing) {
                return areEqual(rtTermToMatch, getTermRef(existing), ctx, stackDepth + 1) ? subst : null;
            }
            subst.set(pvarId, rtTermToMatch);
            return subst;
        }
        // If not a pattern var, then it's a specific hole, must match exactly.
        if (rtTermToMatch.tag === 'Hole' && rtPattern.id === rtTermToMatch.id) return subst;
        return null; // Specific hole in pattern didn't match term
    }

    // If termToMatch is a hole but pattern is not a var/hole pattern, no match.
    if (rtTermToMatch.tag === 'Hole') return null;
    if (rtPattern.tag !== rtTermToMatch.tag) return null;

    // Icit check
    if ((rtPattern.tag === 'App' || rtPattern.tag === 'Lam' || rtPattern.tag === 'Pi') &&
        (rtTermToMatch.tag === rtPattern.tag) && rtPattern.icit !== rtTermToMatch.icit) {
        return null;
    }

    // Structural matching
    switch (rtPattern.tag) {
        case 'Type': case 'CatTerm': case 'SetTerm': return subst;
        case 'Var': // Non-pattern variable
            return rtPattern.name === (rtTermToMatch as Term & {tag:'Var'}).name ? subst : null;
        case 'App': {
            const termApp = rtTermToMatch as Term & {tag:'App'};
            const s1 = matchPattern(rtPattern.func, termApp.func, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s1) return null;
            return matchPattern(rtPattern.arg, termApp.arg, ctx, patternVarDecls, s1, stackDepth + 1);
        }
        case 'Lam': {
            const lamP = rtPattern; const lamT = rtTermToMatch as Term & {tag:'Lam'};
            if (lamP._isAnnotated !== lamT._isAnnotated) return null;
            let tempSubst = subst;
            if (lamP._isAnnotated) {
                if (!lamP.paramType || !lamT.paramType) return null; // Should not happen if well-typed
                 const sType = matchPattern(lamP.paramType, lamT.paramType, ctx, patternVarDecls, tempSubst, stackDepth + 1);
                 if (!sType) return null;
                 tempSubst = sType;
            }
            // For Lam/Pi bodies, we need alpha-equivalence. Instantiating with a fresh var and checking equality is a common way.
            const freshV = Var(freshVarName(lamP.paramName), true, "pattern_var");
            const paramTypeForCtx = (lamP._isAnnotated && lamP.paramType) ? getTermRef(lamP.paramType) : Hole(freshHoleName() + "_match_lam_body_ctx");
            const extendedCtx = extendCtx(ctx, freshV.name, paramTypeForCtx, lamP.icit);
            // The bodies themselves are not matched for further pattern variables here; structural equality is sufficient.
            return areEqual(lamP.body(freshV), lamT.body(freshV), extendedCtx, stackDepth + 1) ? tempSubst : null;
        }
        case 'Pi': {
            const piP = rtPattern; const piT = rtTermToMatch as Term & {tag:'Pi'};
            const sType = matchPattern(piP.paramType, piT.paramType, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!sType) return null;
            const freshV = Var(freshVarName(piP.paramName), true, "pattern_var");
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(piP.paramType), piP.icit);
            return areEqual(piP.bodyType(freshV), piT.bodyType(freshV), extendedCtx, stackDepth + 1) ? sType : null;
        }
        case 'ObjTerm':
            return matchPattern(rtPattern.cat, (rtTermToMatch as Term & {tag:'ObjTerm'}).cat, ctx, patternVarDecls, subst, stackDepth + 1);
        case 'HomTerm': {
            const homP = rtPattern; const homT = rtTermToMatch as Term & {tag:'HomTerm'};
            let s: Substitution | null = subst;
            s = matchPattern(homP.cat, homT.cat, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            s = matchPattern(homP.dom, homT.dom, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            return matchPattern(homP.cod, homT.cod, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'FunctorCategoryTerm':
        case 'FunctorTypeTerm': {
            const fcP = rtPattern as Term & {tag:'FunctorCategoryTerm'|'FunctorTypeTerm'};
            const fcT = rtTermToMatch as Term & {tag:'FunctorCategoryTerm'|'FunctorTypeTerm'};
            let s: Substitution | null = subst;
            s = matchPattern(fcP.domainCat, fcT.domainCat, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            return matchPattern(fcP.codomainCat, fcT.codomainCat, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'FMap0Term': {
            const fm0P = rtPattern; const fm0T = rtTermToMatch as Term & {tag:'FMap0Term'};
            let s: Substitution | null = subst;
            if (fm0P.catA_IMPLICIT) { if (!fm0T.catA_IMPLICIT) return null; s = matchPattern(fm0P.catA_IMPLICIT, fm0T.catA_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null; }
            if (fm0P.catB_IMPLICIT) { if (!fm0T.catB_IMPLICIT) return null; s = matchPattern(fm0P.catB_IMPLICIT, fm0T.catB_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null; }
            s = matchPattern(fm0P.functor, fm0T.functor, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            return matchPattern(fm0P.objectX, fm0T.objectX, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'FMap1Term': {
            const fm1P = rtPattern; const fm1T = rtTermToMatch as Term & {tag:'FMap1Term'};
            let s: Substitution | null = subst;
            const implicitsP = [fm1P.catA_IMPLICIT, fm1P.catB_IMPLICIT, fm1P.objX_A_IMPLICIT, fm1P.objY_A_IMPLICIT];
            const implicitsT = [fm1T.catA_IMPLICIT, fm1T.catB_IMPLICIT, fm1T.objX_A_IMPLICIT, fm1T.objY_A_IMPLICIT];
            for(let i=0; i<implicitsP.length; i++) {
                if (implicitsP[i]) { if (!implicitsT[i]) return null; s = matchPattern(implicitsP[i]!, implicitsT[i]!, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null; }
            }
            s = matchPattern(fm1P.functor, fm1T.functor, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            return matchPattern(fm1P.morphism_a, fm1T.morphism_a, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'NatTransTypeTerm': {
            const ntP = rtPattern; const ntT = rtTermToMatch as Term & {tag:'NatTransTypeTerm'};
            let s: Substitution | null = subst;
            s = matchPattern(ntP.catA, ntT.catA, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            s = matchPattern(ntP.catB, ntT.catB, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            s = matchPattern(ntP.functorF, ntT.functorF, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            return matchPattern(ntP.functorG, ntT.functorG, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'NatTransComponentTerm': {
            const ncP = rtPattern; const ncT = rtTermToMatch as Term & {tag:'NatTransComponentTerm'};
            let s: Substitution | null = subst;
            const implicitsP = [ncP.catA_IMPLICIT, ncP.catB_IMPLICIT, ncP.functorF_IMPLICIT, ncP.functorG_IMPLICIT];
            const implicitsT = [ncT.catA_IMPLICIT, ncT.catB_IMPLICIT, ncT.functorF_IMPLICIT, ncT.functorG_IMPLICIT];
            for(let i=0; i<implicitsP.length; i++) {
                if (implicitsP[i]) { if (!implicitsT[i]) return null; s = matchPattern(implicitsP[i]!, implicitsT[i]!, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null; }
            }
            s = matchPattern(ncP.transformation, ncT.transformation, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            return matchPattern(ncP.objectX, ncT.objectX, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'HomCovFunctorIdentity': {
            const hcP = rtPattern as Term & {tag:'HomCovFunctorIdentity'};
            const hcT = rtTermToMatch as Term & {tag:'HomCovFunctorIdentity'};
            let s: Substitution | null = subst;
            s = matchPattern(hcP.domainCat, hcT.domainCat, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            return matchPattern(hcP.objW_InDomainCat, hcT.objW_InDomainCat, ctx, patternVarDecls, s, stackDepth + 1);
        }
        default:
             const exhaustiveCheck: never = rtPattern;
             console.warn(`matchPattern: Unhandled pattern tag: ${(exhaustiveCheck as any).tag}.`);
             return null;
    }
}

/**
 * Applies a substitution to a term.
 * @param term The term to apply substitution to.
 * @param subst The substitution map.
 * @param patternVarDecls Declared pattern variables (to identify which Vars/Holes are substitutable).
 * @returns The term with substitutions applied.
 */
export function applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[]): Term {
    const current = getTermRef(term);

    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        if (current.name === '_') return Hole('_'); // Wildcard var remains wildcard hole
        const replacement = subst.get(current.name);
        return replacement !== undefined ? replacement : current; // If var not in subst, return as is
    }
    if (current.tag === 'Hole' && isPatternVarName(current.id, patternVarDecls)) {
        if (current.id === '_') return Hole('_'); // Wildcard hole remains wildcard hole
        const replacement = subst.get(current.id);
        return replacement !== undefined ? replacement : current;
    }

    // Recursive application for structured terms
    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': case 'CatTerm': case 'SetTerm': return current; // Non-pattern Vars/Holes or primitives
        case 'App':
            return App(applySubst(current.func, subst, patternVarDecls), applySubst(current.arg, subst, patternVarDecls), current.icit);
        case 'Lam': {
            const lam = current;
            const appliedParamType = lam.paramType ? applySubst(lam.paramType, subst, patternVarDecls) : undefined;
            // For Lam/Pi, substitution must be careful not to capture free variables in the replacement terms
            // if they become bound by the Lam/Pi. However, pattern variables are typically closed or instantiated
            // in a way that this is handled by the substitution map containing already-instantiated terms.
            // The body function itself needs to be reconstructed.
            const newBodyFn = (v_arg: Term): Term => {
                // Here, v_arg is a placeholder for the lambda's parameter.
                // We apply subst to the *structure* of the body.
                // If a pattern variable inside the body was $x, and $x is bound to, say, (App global_f paramName),
                // then paramName must be correctly handled if it matches the Lam's paramName.
                // This is typically okay because substitution is structural.
                // If subst contains Var(lam.paramName), it means that pattern var was bound to the lambda's own parameter.
                const bodyStructure = lam.body(Var(lam.paramName, true)); // Get structure using a lambda-bound var
                return applySubst(bodyStructure, subst, patternVarDecls);
            };
            const newLam = Lam(lam.paramName, lam.icit, appliedParamType, newBodyFn) as Term & {tag: 'Lam'};
            newLam._isAnnotated = lam._isAnnotated && appliedParamType !== undefined;
            return newLam;
        }
        case 'Pi': {
            const pi = current;
            const newBodyTypeFn = (v_arg: Term) => {
                const bodyTypeStructure = pi.bodyType(Var(pi.paramName, true));
                return applySubst(bodyTypeStructure, subst, patternVarDecls);
            };
            return Pi(pi.paramName, pi.icit, applySubst(pi.paramType, subst, patternVarDecls), newBodyTypeFn);
        }
        case 'ObjTerm': return ObjTerm(applySubst(current.cat, subst, patternVarDecls));
        case 'HomTerm':
            return HomTerm(
                applySubst(current.cat, subst, patternVarDecls),
                applySubst(current.dom, subst, patternVarDecls),
                applySubst(current.cod, subst, patternVarDecls)
            );
        case 'FunctorCategoryTerm':
        case 'FunctorTypeTerm':
            return current.tag === 'FunctorCategoryTerm' ? FunctorCategoryTerm(
                applySubst(current.domainCat, subst, patternVarDecls),
                applySubst(current.codomainCat, subst, patternVarDecls)
            ) : FunctorTypeTerm(
                applySubst(current.domainCat, subst, patternVarDecls),
                applySubst(current.codomainCat, subst, patternVarDecls)
            );
        case 'FMap0Term':
            return FMap0Term(
                applySubst(current.functor, subst, patternVarDecls),
                applySubst(current.objectX, subst, patternVarDecls),
                current.catA_IMPLICIT ? applySubst(current.catA_IMPLICIT, subst, patternVarDecls) : undefined,
                current.catB_IMPLICIT ? applySubst(current.catB_IMPLICIT, subst, patternVarDecls) : undefined
            );
        case 'FMap1Term':
            return FMap1Term(
                applySubst(current.functor, subst, patternVarDecls),
                applySubst(current.morphism_a, subst, patternVarDecls),
                current.catA_IMPLICIT ? applySubst(current.catA_IMPLICIT, subst, patternVarDecls) : undefined,
                current.catB_IMPLICIT ? applySubst(current.catB_IMPLICIT, subst, patternVarDecls) : undefined,
                current.objX_A_IMPLICIT ? applySubst(current.objX_A_IMPLICIT, subst, patternVarDecls) : undefined,
                current.objY_A_IMPLICIT ? applySubst(current.objY_A_IMPLICIT, subst, patternVarDecls) : undefined
            );
        case 'NatTransTypeTerm':
            return NatTransTypeTerm(
                applySubst(current.catA, subst, patternVarDecls),
                applySubst(current.catB, subst, patternVarDecls),
                applySubst(current.functorF, subst, patternVarDecls),
                applySubst(current.functorG, subst, patternVarDecls)
            );
        case 'NatTransComponentTerm':
            return NatTransComponentTerm(
                applySubst(current.transformation, subst, patternVarDecls),
                applySubst(current.objectX, subst, patternVarDecls),
                current.catA_IMPLICIT ? applySubst(current.catA_IMPLICIT, subst, patternVarDecls) : undefined,
                current.catB_IMPLICIT ? applySubst(current.catB_IMPLICIT, subst, patternVarDecls) : undefined,
                current.functorF_IMPLICIT ? applySubst(current.functorF_IMPLICIT, subst, patternVarDecls) : undefined,
                current.functorG_IMPLICIT ? applySubst(current.functorG_IMPLICIT, subst, patternVarDecls) : undefined
            );
        case 'HomCovFunctorIdentity':
            return HomCovFunctorIdentity(
                applySubst(current.domainCat, subst, patternVarDecls),
                applySubst(current.objW_InDomainCat, subst, patternVarDecls)
            );
        default:
            const exhaustiveCheck: never = current;
            throw new Error(`applySubst: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
}


/**
 * Collects all pattern variables used in a term.
 * @param term The term to scan.
 * @param patternVarDecls All declared pattern variables for the rule.
 * @param collectedVars A Set to store the names of found pattern variables.
 * @param visited Set to prevent infinite loops with term references.
 */
export function collectPatternVars(term: Term, patternVarDecls: PatternVarDecl[], collectedVars: Set<string>, visited: Set<Term> = new Set()): void {
    const current = getTermRef(term);
    if (visited.has(current) && current.tag !== 'Var' && current.tag !== 'Hole') return; // Avoid re-processing structural parts
    visited.add(current);

    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        collectedVars.add(current.name);
    } else if (current.tag === 'Hole' && isPatternVarName(current.id, patternVarDecls)) {
        collectedVars.add(current.id);
    }

    // Recursively collect from subterms
    switch (current.tag) {
        case 'App':
            collectPatternVars(current.func, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.arg, patternVarDecls, collectedVars, visited);
            break;
        case 'Lam':
            if (current.paramType) collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            // Body is a function, so we can't easily traverse its structure for pattern vars here.
            // Pattern variables are usually not expected deep inside lambda bodies in simple rewrite rules.
            // If they are, the pattern itself would likely be a higher-order pattern variable for the lambda.
            break;
        case 'Pi':
            collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            // Similar to Lam for bodyType.
            break;
        case 'ObjTerm': collectPatternVars(current.cat, patternVarDecls, collectedVars, visited); break;
        case 'HomTerm':
            collectPatternVars(current.cat, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.dom, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.cod, patternVarDecls, collectedVars, visited);
            break;
        case 'FunctorCategoryTerm': case 'FunctorTypeTerm':
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
        // Terminals like Type, Var (non-pattern), Hole (non-pattern), CatTerm, SetTerm have no subterms or are handled.
    }
}

/**
 * Applies a unification rule's RHS constraints using the substitution from matching its LHS.
 * Ensures that pattern variables appearing in RHS constraints but not in LHS are instantiated with fresh holes.
 * @param rule The unification rule.
 * @param subst The substitution obtained from matching LHS patterns.
 * @param ctx The current context.
 */
export function applyAndAddRuleConstraints(
    rule: {lhsPattern1: Term, lhsPattern2: Term, patternVars: PatternVarDecl[], rhsNewConstraints: Array<{t1:Term, t2:Term}>, name: string},
    subst: Substitution,
    ctx: Context // ctx is not strictly used here but kept for consistency with similar functions
): void {
    const lhsVars = new Set<string>();
    collectPatternVars(rule.lhsPattern1, rule.patternVars, lhsVars);
    collectPatternVars(rule.lhsPattern2, rule.patternVars, lhsVars);

    // Create a mutable copy of the substitution to add fresh holes if needed.
    const finalSubst = new Map(subst);

    // Instantiate RHS-only pattern variables with fresh holes.
    for (const pVarDecl of rule.patternVars) {
        const pVarName = pVarDecl; // Assuming PatternVarDecl is string
        if (pVarName === '_') continue; // Wildcard, not substitutable by name

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
        // If a pattern variable is used in RHS constraints but not in LHS and not already in subst (e.g. from matching the other LHS pattern),
        // it needs to be instantiated with a fresh hole.
        if (usedInRhsConstraints && !lhsVars.has(pVarName) && !finalSubst.has(pVarName)) {
             finalSubst.set(pVarName, Hole(freshHoleName() + "_unifRuleRHS_" + pVarName.substring(1)));
        }
    }

    // Apply substitution to RHS constraints and add them.
    for (const constrPair of rule.rhsNewConstraints) {
        const newT1 = applySubst(constrPair.t1, finalSubst, rule.patternVars);
        const newT2 = applySubst(constrPair.t2, finalSubst, rule.patternVars);
        addConstraint(newT1, newT2, `UnifRule ${rule.name}`);
    }
}

/**
 * Tries to apply user-defined unification rules to two terms.
 * @param t1 The first term.
 * @param t2 The second term.
 * @param ctx The current context.
 * @param depth Recursion depth.
 * @returns UnifyResult.RewrittenByRule if a rule applied, UnifyResult.Failed otherwise.
 */
export function tryUnificationRules(t1: Term, t2: Term, ctx: Context, depth: number): UnifyResult {
    for (const rule of userUnificationRules) {
        // Try matching (lhsPattern1 with t1, lhsPattern2 with t2)
        let subst1 = matchPattern(rule.lhsPattern1, t1, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            // Pass subst1 to accumulate matches for common pattern variables
            let subst2 = matchPattern(rule.lhsPattern2, t2, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) { // Both patterns matched
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }
        // Try matching (lhsPattern1 with t2, lhsPattern2 with t1) - symmetric application
        subst1 = matchPattern(rule.lhsPattern1, t2, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t1, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) { // Both patterns matched (symmetrically)
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }
    }
    return UnifyResult.Failed; // No rule applied
}

/**
 * Solves the current set of constraints.
 * Iteratively attempts to unify pairs of terms in the constraints list.
 * @param ctx The current context.
 * @param stackDepth Recursion depth for controlling re-entrant calls.
 * @returns True if all constraints were solved, false otherwise.
 */
export function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > MAX_STACK_DEPTH * 2) throw new Error("solveConstraints stack depth exceeded"); // Higher limit for constraint solver

    // Prevent deep re-entrant calls to solveConstraints from within unify/whnf etc.
    // The main call to solveConstraints will have depth 0.
    if (solveConstraintsControl.depth > 0 && stackDepth > 0) {
        // consoleLog(`[solveConstraints SKIPPING RE-ENTRANT CALL] depth: ${solveConstraintsControl.depth}, stack: ${stackDepth}`);
        return true; // Assume outer call will handle it
    }

    solveConstraintsControl.depth++;
    let changedInOuterLoop = true;
    let iterations = 0;
    // Max iterations can be quite high, depends on number of constraints and rules.
    const maxIterations = (constraints.length * constraints.length + userUnificationRules.length * constraints.length + 100) * 2 + 200;


    while (changedInOuterLoop && iterations < maxIterations) {
        changedInOuterLoop = false;
        iterations++;
        let currentConstraintIdx = 0;

        while(currentConstraintIdx < constraints.length) {
            const constraint = constraints[currentConstraintIdx];
            // Dereference terms before unification attempt
            const c_t1_current_ref = getTermRef(constraint.t1);
            const c_t2_current_ref = getTermRef(constraint.t2);

            // If terms are already equal, remove constraint
            if (areEqual(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1)) {
                constraints.splice(currentConstraintIdx, 1); // Remove solved constraint
                changedInOuterLoop = true; // Progress was made
                continue; // currentConstraintIdx remains the same, processing the new constraint at this index
            }

            // Attempt to unify
            try {
                const unifyResult = unify(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1);

                if (unifyResult === UnifyResult.Solved) {
                    // Double check equality after unify reports Solved, as unify might solve sub-problems
                    // but the top-level check via areEqual is the ultimate decider.
                    if (areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
                        constraints.splice(currentConstraintIdx, 1);
                    } else {
                         // It reported solved, but they are not equal. This might mean holes were linked,
                         // but the structure with these links is not yet equal. Keep for next iteration.
                        currentConstraintIdx++;
                    }
                    changedInOuterLoop = true;
                } else if (unifyResult === UnifyResult.RewrittenByRule) {
                    // Rule applied, new constraints might have been added. Remove current one.
                    constraints.splice(currentConstraintIdx, 1);
                    changedInOuterLoop = true; // Restart the loop as new constraints are added
                } else if (unifyResult === UnifyResult.Progress) {
                    // Progress made (e.g., a hole was instantiated but terms not fully equal yet)
                    changedInOuterLoop = true; // Indicate progress to continue outer loop
                    currentConstraintIdx++; // Move to next constraint
                } else { // UnifyResult.Failed
                    console.log(`[solveConstraints DEBUG] UnifyResult.Failed for constraint: ${printTerm(c_t1_current_ref)} vs ${printTerm(c_t2_current_ref)} (orig: ${constraint.origin || 'unknown'})`);
                    console.warn(`Unification failed permanently for constraint: ${printTerm(c_t1_current_ref)} === ${printTerm(c_t2_current_ref)} (orig: ${constraint.origin || 'unknown'})`);
                    solveConstraintsControl.depth--;
                    return false; // Hard failure
                }
            } catch (e) {
                console.error(`Error during unification of ${printTerm(c_t1_current_ref)} and ${printTerm(c_t2_current_ref)} (origin: ${constraint.origin || 'unknown'}): ${(e as Error).message}`);
                console.error((e as Error).stack);
                solveConstraintsControl.depth--;
                return false; // Error during unification
            }
        } // End of inner while loop (processing current constraints)
    } // End of outer while loop (iterations)

    if (iterations >= maxIterations && changedInOuterLoop && constraints.length > 0) {
        console.log({constraints_debug: constraints.map(c => `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))}`)});
        console.warn("Constraint solving reached max iterations and was still making changes. Constraints left: " + constraints.length);
    }

    // Final check: are all remaining constraints actually solved?
    const allSolved = constraints.length === 0 || constraints.every(c => areEqual(getTermRef(c.t1), getTermRef(c.t2), ctx, stackDepth + 1));
    if(allSolved && constraints.length > 0) constraints.length = 0; // Clear if all are actually equal

    solveConstraintsControl.depth--;
    return allSolved;
}