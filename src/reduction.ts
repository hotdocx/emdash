/**
 * @file reduction.ts
 * @description Term reduction (WHNF and normalization).
 */

import {
    Term, Context, App, Lam, Var, ObjTerm, HomTerm, NatTransTypeTerm, FMap0Term, FunctorTypeTerm, Pi,
    Type, Hole, CatTerm, SetTerm, FunctorCategoryTerm, FMap1Term, NatTransComponentTerm, HomCovFunctorIdentity, Icit, MkFunctorTerm
} from './types';
import {
    getTermRef, globalDefs, userRewriteRules, lookupCtx, isKernelConstantSymbolStructurally, printTerm,
    freshVarName, freshHoleName, extendCtx, getFlag
} from './state';
import { MAX_STACK_DEPTH } from './constants';
import { matchPattern, applySubst, getFreeVariables } from './pattern';
import { areStructurallyEqualNoWhnf } from './structural';

export const MAX_WHNF_ITERATIONS = 10000; // Max steps for WHNF reduction to prevent infinite loops.

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
    if (stackDepth > 30) {
        console.log("whnf: stackDepth > 30", {stackDepth, term: printTerm(term)});
    }
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
        // Be careful of name shadowing with global definitions
        if (current.tag === 'Var' && current.isLambdaBound) {
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
                    if (stackDepth > 30) {
                        console.log("whnf matchPattern subst: stackDepth", {stackDepth}, {pattern: printTerm(rule.elaboratedLhs), termToMatch: printTerm(termBeforeInnerReductions)});
                    }
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
                } else if (!areStructurallyEqualNoWhnf(getTermRef(current.func), func_whnf_ref, ctx, stackDepth + 1)) {
                    if (stackDepth > 30) {
                        console.log("whnf App: stackDepth", {stackDepth}, {func: printTerm(current.func), func_whnf_ref: printTerm(func_whnf_ref)});
                    }
                    current = App(func_whnf_ref, current.arg, current.icit);
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'Lam': { // Eta-contraction
                if (getFlag('etaEquality')) {
                    const lam = current;
                    // Instantiate body to inspect it. The var must be marked as lambda-bound.
                    const body = getTermRef(lam.body(Var(lam.paramName, true))); 
                    if (body.tag === 'App' && body.icit === lam.icit) {
                        const appArg = getTermRef(body.arg);
                        if (appArg.tag === 'Var' && appArg.name === lam.paramName && appArg.isLambdaBound) {
                            const funcPart = getTermRef(body.func);
                            // Check that the lambda's parameter is not free in the function part.
                            const freeVarsInF = getFreeVariables(funcPart);
                            if (!freeVarsInF.has(lam.paramName)) {
                                // This is a valid eta-contraction: λx. F x  -->  F
                                current = funcPart;
                                reducedInKernelBlock = true;
                            }
                        }
                    }
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
                // here we know that current.isLambdaBound is false
                const gdef = globalDefs.get(current.name);
                if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol) {
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
                } else if (functor_whnf.tag === 'MkFunctorTerm') {
                    // Rule: fmap0 (mkFunctor fmap0 fmap1) X  ↪  fmap0 X
                    current = App(functor_whnf.fmap0, current.objectX, Icit.Expl);
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
            case 'FMap1Term': {
                const functor_whnf = getTermRef(whnf(current.functor, ctx, stackDepth + 1));
                if (functor_whnf.tag === 'MkFunctorTerm') {
                    // Rule: fmap1 (mkFunctor fmap0 fmap1) {X} {Y} a  ↪  fmap1 {X} {Y} a
                    const fmap1 = functor_whnf.fmap1;
                    const X = current.objX_A_IMPLICIT!;
                    const Y = current.objY_A_IMPLICIT!;
                    const a = current.morphism_a;
                    current = App(App(App(fmap1, X, Icit.Impl), Y, Icit.Impl), a, Icit.Expl);
                    reducedInKernelBlock = true;
                }
                // No further reduction for FMap1Term in this pass
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
             // Other cases (Lam, Pi, Type, CatTerm, SetTerm, etc.) are already in WHNF or do not reduce further at head.
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
        case 'MkFunctorTerm':
            return MkFunctorTerm(
                normalize(current.domainCat, ctx, stackDepth + 1),
                normalize(current.codomainCat, ctx, stackDepth + 1),
                normalize(current.fmap0, ctx, stackDepth + 1),
                normalize(current.fmap1, ctx, stackDepth + 1)
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