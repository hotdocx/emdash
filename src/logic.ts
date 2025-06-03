/**
 * @file logic.ts
 *
 * Implements the core logical operations of the Emdash type system.
 * This includes Weak Head Normal Form (WHNF) reduction, full normalization,
 * term equality checking (convertibility), unification, and constraint solving.
 */

import {
    Term, Context, PatternVarDecl, Substitution, UnifyResult, Icit, Hole, App, Lam, Pi, Var, ObjTerm, HomTerm, Type, CatTerm, FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm, NatTransComponentTerm, HomCovFunctorIdentity, SetTerm, FunctorTypeTerm
} from './types';
import {
    getTermRef, globalDefs, userRewriteRules, addConstraint, constraints, emptyCtx, extendCtx, lookupCtx,
    isKernelConstantSymbolStructurally, isEmdashUnificationInjectiveStructurally, userUnificationRules, freshVarName, freshHoleName,
    solveConstraintsControl, CORE_MAX_STACK_DEPTH
} from './state';
import { matchPattern, applySubst, isPatternVarName } from './elaboration'; // For WHNF userRewriteRules and Unification rules
import { printTerm, consoleLog } from './utils';

/**
 * Maximum iterations for WHNF reduction to prevent infinite loops in non-terminating reductions.
 */
export const MAX_WHNF_ITERATIONS = 10000;


/**
 * Checks for structural equality of two terms *without* performing WHNF reduction.
 * This is a purely syntactic check, sensitive to alpha-renaming for binders.
 * @param t1 First term.
 * @param t2 Second term.
 * @param ctx Context (used for binder handling).
 * @param depth Recursion depth.
 * @returns True if terms are structurally equal.
 */
export function areStructurallyEqualNoWhnf(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > CORE_MAX_STACK_DEPTH) throw new Error(`Structural Equality check depth exceeded (areStructurallyEqualNoWhnf depth: ${depth})`);
    const rt1 = getTermRef(t1);
    const rt2 = getTermRef(t2);

    if (rt1.tag === 'Hole' && rt2.tag === 'Hole') return rt1.id === rt2.id;
    if (rt1.tag === 'Hole' || rt2.tag === 'Hole') return false; // One is hole, other is not.
    if (rt1.tag !== rt2.tag) return false;

    // Icit check for relevant terms
    if ((rt1.tag === 'App' || rt1.tag === 'Lam' || rt1.tag === 'Pi') &&
        (rt2.tag === rt1.tag) && rt1.icit !== (rt2 as typeof rt1).icit) {
        return false;
    }

    switch (rt1.tag) {
        case 'Type': case 'CatTerm': case 'SetTerm': return true;
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
            if (rt1._isAnnotated) { // Both must be annotated
                if (!rt1.paramType || !lam2.paramType || !areStructurallyEqualNoWhnf(rt1.paramType, lam2.paramType, ctx, depth + 1)) {
                    paramTypeOk = false;
                }
            }
            if (!paramTypeOk) return false;

            // Alpha-equivalence for bodies
            const freshVName = rt1.paramName; // Use one of the names, or generate fresh if needed
            const freshV = Var(freshVName, true); // Mark as lambda-bound for this check
            const paramTypeForCtx = (rt1._isAnnotated && rt1.paramType) ? getTermRef(rt1.paramType) : Hole(freshHoleName()+"_structEq_unannot_lam_param");
            const extendedCtx = extendCtx(ctx, freshVName, paramTypeForCtx, rt1.icit); // No definition for structural check
            return areStructurallyEqualNoWhnf(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            if (!areStructurallyEqualNoWhnf(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            // Alpha-equivalence for body types
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
                return rImp1 === rImp2; // Both undefined or one is undefined
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
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => { /* as above */
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
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => { /* as above */
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
        default:
            // Ensures all tags are handled. If a new tag is added to BaseTerm and not here, TypeScript will complain.
            const exhaustiveCheck: never = rt1; return false;
    }
}


/**
 * Reduces a term to its Weak Head Normal Form (WHNF).
 * This involves beta-reduction, applying rewrite rules, and unfolding definitions
 * at the head of the term.
 * @param term The term to reduce.
 * @param ctx The context.
 * @param stackDepth Current recursion depth.
 * @returns The term in WHNF.
 */
export function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > CORE_MAX_STACK_DEPTH) throw new Error(`WHNF stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    let current = term; // Start with the given term.
    // Loop for iterative reduction steps (e.g., multiple rewrite rule applications or unfolding).
    for (let i = 0; i < MAX_WHNF_ITERATIONS; i++) {
        let changedInThisPass = false; // Track if any reduction happened in the current iteration.
        const termAtStartOfOuterPass = current; // For cycle detection/non-termination warning.

        // Step 1: Dereference holes.
        const dereffedCurrent = getTermRef(current);
        if (dereffedCurrent !== current) {
            current = dereffedCurrent;
            changedInThisPass = true;
        }

        const termBeforeInnerReductions = current; // Snapshot before trying local defs, rules, or kernel reductions.

        // Step 2: Substitute local definitions (from context).
        if (current.tag === 'Var') {
            const binding = lookupCtx(ctx, current.name);
            if (binding && binding.definition) {
                current = binding.definition; // Substitute with the definition.
                changedInThisPass = true;
                continue; // Restart the whnf loop with the new term.
            }
        }

        // Step 3: Try user-defined rewrite rules, unless it's a kernel constant.
        // Kernel constants (e.g., CatTerm, SetTerm) should not be rewritten by general user rules.
        if (!isKernelConstantSymbolStructurally(termBeforeInnerReductions)) {
            for (const rule of userRewriteRules) {
                // `matchPattern` tries to match `rule.elaboratedLhs` against `termBeforeInnerReductions`.
                const subst = matchPattern(rule.elaboratedLhs, termBeforeInnerReductions, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    const rhsApplied = getTermRef(applySubst(rule.elaboratedRhs, subst, rule.patternVars));
                    // Ensure actual change to prevent loops with identity rules.
                    if (!areStructurallyEqualNoWhnf(rhsApplied, termBeforeInnerReductions, ctx, stackDepth + 1)) {
                        current = rhsApplied;
                        changedInThisPass = true;
                        break; // Found a matching rule and applied it.
                    }
                }
            }
            if (changedInThisPass) continue; // Restart WHNF with the rewritten term.
        }

        // Step 4: Kernel reduction rules (beta-reduction, specific term constructor reductions).
        let reducedInKernelBlock = false;
        switch (current.tag) {
            case 'App': {
                const func_whnf_ref = getTermRef(whnf(current.func, ctx, stackDepth + 1));
                if (func_whnf_ref.tag === 'Lam' && func_whnf_ref.icit === current.icit) { // Beta-reduction
                    current = func_whnf_ref.body(current.arg); // Apply argument to lambda body.
                    reducedInKernelBlock = true;
                } else if (getTermRef(current.func) !== func_whnf_ref) { // Function part reduced.
                    current = App(func_whnf_ref, current.arg, current.icit);
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'ObjTerm': { // Obj C -> Obj (whnf C)
                const cat_whnf_ref = getTermRef(whnf(current.cat, ctx, stackDepth + 1));
                if (getTermRef(current.cat) !== cat_whnf_ref) {
                    current = ObjTerm(cat_whnf_ref);
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'HomTerm': { // Hom C X Y -> Hom (whnf C) X Y. Also, Hom (FunctorCat A B) F G -> Transf A B F G. Hom Set X Y -> Pi x:X. Y.
                const cat_whnf_ref = getTermRef(whnf(current.cat, ctx, stackDepth + 1));
                if (cat_whnf_ref.tag === 'FunctorCategoryTerm') { // Hom [A,B] F G  ~>  Transf A B F G
                    current = NatTransTypeTerm(cat_whnf_ref.domainCat, cat_whnf_ref.codomainCat, current.dom, current.cod);
                    reducedInKernelBlock = true;
                } else if (getTermRef(current.cat) !== cat_whnf_ref) { // Category part reduced
                    current = HomTerm(cat_whnf_ref, current.dom, current.cod);
                    reducedInKernelBlock = true;
                } else { // Check for Hom Set X Y
                    const setGlobal = globalDefs.get("Set");
                    // Ensure setGlobal and its value exist and are structurally SetTerm
                    if (setGlobal?.value && areStructurallyEqualNoWhnf(cat_whnf_ref, getTermRef(setGlobal.value), ctx)) {
                         const domWhnf = whnf(current.dom, ctx, stackDepth + 1); // dom should be a Type here
                         const codWhnf = whnf(current.cod, ctx, stackDepth + 1); // cod should be a Type here
                         current = Pi(freshVarName("_x_hom_set"), Icit.Expl, domWhnf, _ => codWhnf);
                         reducedInKernelBlock = true;
                    }
                }
                break;
            }
            case 'Var': { // Global definition unfolding (if not a constant/type-like symbol).
                // Local definitions are handled earlier.
                const gdef = globalDefs.get(current.name);
                if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol && !gdef.isTypeNameLike) {
                    current = gdef.value;
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'FMap0Term': { // fmap0 (hom_cov A W) Y  ↪  Hom A W Y
                const functor_whnf = getTermRef(whnf(current.functor, ctx, stackDepth + 1));
                if (functor_whnf.tag === 'HomCovFunctorIdentity') {
                    current = HomTerm(functor_whnf.domainCat, functor_whnf.objW_InDomainCat, current.objectX);
                    reducedInKernelBlock = true;
                } else { // Functor or arguments might have reduced. Reconstruct if changed.
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
            case 'FunctorTypeTerm': { // Reduce components of FunctorTypeTerm
                const domainCat_whnf = getTermRef(whnf(current.domainCat, ctx, stackDepth + 1));
                const codomainCat_whnf = getTermRef(whnf(current.codomainCat, ctx, stackDepth + 1));
                if (getTermRef(current.domainCat) !== domainCat_whnf || getTermRef(current.codomainCat) !== codomainCat_whnf) {
                    current = FunctorTypeTerm(domainCat_whnf, codomainCat_whnf);
                    reducedInKernelBlock = true;
                }
                break;
            }
            // Other terms (Type, Lam, Pi, other Cat terms) are in WHNF if their components are,
            // or their reduction is handled by App (for Lam) or definition unfolding (for Var).
            // Lam and Pi themselves are values in WHNF.
        }

        if (reducedInKernelBlock) {
             changedInThisPass = true;
             continue; // Restart WHNF with the kernel-reduced term.
        }

        // If `current` was changed only by `getTermRef` at the start of the pass, but not by rules/kernel.
        const currentAfterPossibleKernelOrRefChange = getTermRef(current);
        if (currentAfterPossibleKernelOrRefChange !== termBeforeInnerReductions && !changedInThisPass) {
            current = currentAfterPossibleKernelOrRefChange;
            changedInThisPass = true;
        }

        // If no change in this pass, the term is in WHNF relative to current strategy.
        if (!changedInThisPass) break;

        // Safety check for non-terminating loops if term reduces to itself without actual change.
        if (current === termAtStartOfOuterPass && !changedInThisPass && i > 0) {
             // This should ideally be caught by `areStructurallyEqualNoWhnf` in rewrite rule application.
             console.warn(`[WHNF Cycle detected or no progress] Term: ${printTerm(current)} at iteration ${i}. Stopping.`);
             break;
        }

        if (i === MAX_WHNF_ITERATIONS - 1) {
             if (changedInThisPass || current !== termAtStartOfOuterPass) { // Still making progress or different term
                console.warn(`[WHNF Max Iterations] Reached for: ${printTerm(term)} -> ${printTerm(current)}. May not be fully in WHNF.`);
             }
        }
    }
    return current; // Return the term after reduction attempts.
}


/**
 * Normalizes a term by reducing it to WHNF and then recursively normalizing its subterms.
 * @param term The term to normalize.
 * @param ctx The context.
 * @param stackDepth Current recursion depth.
 * @returns The fully normalized term.
 */
export function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > CORE_MAX_STACK_DEPTH) throw new Error(`Normalize stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);

    // First, reduce the head of the term to WHNF.
    const headReduced = whnf(term, ctx, stackDepth + 1);
    const current = getTermRef(headReduced); // Resolve any hole assignments from whnf.

    // Then, recursively normalize the subterms based on the tag of the WHNF term.
    switch (current.tag) {
        case 'Type': case 'Var' : case 'Hole': case 'CatTerm': case 'SetTerm': return current; // Already normal.
        case 'ObjTerm':
            return ObjTerm(normalize(current.cat, ctx, stackDepth + 1));
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
            // Normalize parameter type if annotated.
            const normLamParamType = (currentLam._isAnnotated && currentLam.paramType)
                                     ? normalize(currentLam.paramType, ctx, stackDepth + 1)
                                     : undefined;

            // Normalize body under extended context.
            // The body function takes a placeholder (Var of paramName) to instantiate its structure.
            const newBodyFn = (v_arg_placeholder: Term): Term => {
                // Context for normalizing body: param is a binder, not defined as v_arg_placeholder.
                const paramTypeForBodyCtx = normLamParamType ||
                                            (currentLam.paramType ? getTermRef(currentLam.paramType) : Hole(freshHoleName()+"_norm_lam_body_ctx"));
                const bodyCtx = extendCtx(ctx, currentLam.paramName, paramTypeForBodyCtx, currentLam.icit); // No definition for param
                return normalize(currentLam.body(v_arg_placeholder), bodyCtx, stackDepth + 1);
            };
            // Construct new Lam with normalized components.
            const normLam = Lam(currentLam.paramName, currentLam.icit, normLamParamType, newBodyFn);
            (normLam as Term & {tag: 'Lam'})._isAnnotated = currentLam._isAnnotated && normLamParamType !== undefined;
            return normLam;
        }
        case 'App': {
            // WHNF might have performed beta-reduction. If App(Lam, arg) becomes Body(arg),
            // `current` would be Body(arg), and this case wouldn't be hit for the App itself.
            // If it's still an App, normalize func and arg.
            // Then, try one more WHNF step in case normalization enables further head reduction (e.g., if func normalized to Lam).
            const normFunc = normalize(current.func, ctx, stackDepth + 1);
            const normArg = normalize(current.arg, ctx, stackDepth + 1);
            const potentiallyReducibleApp = App(normFunc, normArg, current.icit);
            // After normalizing func and arg, the App might be reducible again.
            // e.g. if `current.func` normalized to a lambda.
            // So, we WHNF the reconstructed App.
            return whnf(potentiallyReducibleApp, ctx, stackDepth + 1);
        }
        case 'Pi': {
            const currentPi = current;
            const normPiParamType = normalize(currentPi.paramType, ctx, stackDepth + 1);
            // Normalize body type under extended context.
            const newBodyTypeFn = (v_arg_placeholder: Term): Term => {
                const bodyTypeCtx = extendCtx(ctx, currentPi.paramName, normPiParamType, currentPi.icit); // No definition for param
                return normalize(currentPi.bodyType(v_arg_placeholder), bodyTypeCtx, stackDepth + 1);
            };
            return Pi(currentPi.paramName, currentPi.icit, normPiParamType, newBodyTypeFn);
        }
        default: const exhaustiveCheck: never = current; throw new Error(`Normalize: Unhandled term: ${(exhaustiveCheck as any).tag }`);
    }
}


/**
 * Checks if two terms are equal (convertible) under the theory.
 * This involves reducing both terms to WHNF and then comparing them structurally.
 * For functions (Lam, Pi), it involves alpha-equivalence and checking bodies under extended contexts.
 * @param t1 First term.
 * @param t2 Second term.
 * @param ctx Context.
 * @param depth Recursion depth.
 * @returns True if terms are equal.
 */
export function areEqual(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > CORE_MAX_STACK_DEPTH) throw new Error(`Equality check depth exceeded (areEqual depth: ${depth})`);

    // Reduce both terms to WHNF before comparison.
    const rt1 = getTermRef(whnf(t1, ctx, depth + 1));
    const rt2 = getTermRef(whnf(t2, ctx, depth + 1));

    // Basic checks: identical holes, one is hole, different tags.
    if (rt1.tag === 'Hole' && rt2.tag === 'Hole') return rt1.id === rt2.id;
    if (rt1.tag === 'Hole' || rt2.tag === 'Hole') return false; // One is hole, other isn't (or different holes).
    if (rt1.tag !== rt2.tag) return false;

    // Icit check for App, Lam, Pi.
    if ((rt1.tag === 'App' || rt1.tag === 'Lam' || rt1.tag === 'Pi') &&
        (rt2.tag === rt1.tag) && rt1.icit !== (rt2 as typeof rt1).icit) {
        return false;
    }

    // Structural comparison based on tag.
    switch (rt1.tag) {
        case 'Type': case 'CatTerm': case 'SetTerm': return true;
        case 'Var': return rt1.name === (rt2 as Term & {tag:'Var'}).name; // Assumes WHNF resolved defs.
        case 'App': {
            const app2 = rt2 as Term & {tag:'App'};
            return areEqual(rt1.func, app2.func, ctx, depth + 1) &&
                   areEqual(rt1.arg, app2.arg, ctx, depth + 1);
        }
        case 'Lam': { // Alpha-equivalence for lambdas.
            const lam2 = rt2 as Term & {tag:'Lam'};
            if (rt1._isAnnotated !== lam2._isAnnotated) return false;
            let paramTypeOk = true;
            if (rt1._isAnnotated) { // Both must be annotated and types equal.
                if (!rt1.paramType || !lam2.paramType || !areEqual(rt1.paramType, lam2.paramType, ctx, depth + 1)) {
                    paramTypeOk = false;
                }
            }
            if(!paramTypeOk) return false;

            // Compare bodies under a fresh variable.
            const freshVName = rt1.paramName; // Or generate a globally unique name.
            const freshV = Var(freshVName, true); // Represents the bound variable.
            const paramTypeForCtx = (rt1._isAnnotated && rt1.paramType) ? getTermRef(rt1.paramType) : Hole(freshHoleName()+"_areEqual_unannot_lam_param");
            const extendedCtx = extendCtx(ctx, freshVName, paramTypeForCtx, rt1.icit); // No definition for freshV.
            return areEqual(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': { // Alpha-equivalence for Pi types.
            const pi2 = rt2 as Term & {tag:'Pi'};
            if (!areEqual(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            // Compare body types under a fresh variable.
            const freshVName = rt1.paramName;
            const freshV = Var(freshVName, true);
            const extendedCtx = extendCtx(ctx, freshVName, getTermRef(rt1.paramType), rt1.icit); // No definition.
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
        case 'FunctorTypeTerm': {
            const ftt2 = rt2 as Term & {tag:'FunctorTypeTerm'};
            return areEqual(rt1.domainCat, ftt2.domainCat, ctx, depth + 1) &&
                   areEqual(rt1.codomainCat, ftt2.codomainCat, ctx, depth + 1);
        }
        case 'FMap0Term': { // Implicit args must also be equal.
            const fm0_2 = rt2 as Term & {tag:'FMap0Term'};
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areEqual(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2; // Both undefined, or one is undefined.
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
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => { /* as above */
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
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => { /* as above */
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
        default: const exhaustiveCheck: never = rt1; return false;
    }
}


/**
 * Performs an occurs check: determines if a hole `holeId` appears in `term`.
 * This is crucial for preventing cyclic unification `?h = f(?h)`.
 * @param term The term to check.
 * @param holeId The ID of the hole to look for.
 * @param visited Set to track visited subterms to handle cycles in term structure (not hole cycles).
 * @param depth Recursion depth.
 * @returns True if the hole occurs in the term.
 */
export function termContainsHole(term: Term, holeId: string, visited: Set<string> = new Set(), depth = 0): boolean {
    if (depth > CORE_MAX_STACK_DEPTH * 2) { // Increased depth for occurs check as it can be deep
        console.warn(`termContainsHole depth exceeded for hole ${holeId} in ${printTerm(term)}`);
        return true; // Fail safe: assume it occurs to prevent infinite loops.
    }

    const current = getTermRef(term); // Important: check against the resolved term.

    // Create a unique key for the visited set to handle term structure cycles.
    // For Holes/Vars, ID/name is key. For others, printed form (approximate but usually good enough for cycle break).
    const termKey = current.tag === 'Hole' ? `Hole:${current.id}` :
                    current.tag === 'Var' ? `Var:${current.name}` :
                    printTerm(current); // A more robust key might be needed for complex structural cycles.

    if (visited.has(termKey) && current.tag !== 'Hole' && current.tag !== 'Var' ) { // Don't mark Holes/Vars as visited in this way
         return false; // Already visited this non-Hole/Var branch, and hole not found there.
    }
    visited.add(termKey);


    switch (current.tag) {
        case 'Hole': return current.id === holeId;
        case 'Type': case 'Var': case 'CatTerm': case 'SetTerm': return false; // Vars are not holes.
        case 'App':
            return termContainsHole(current.func, holeId, visited, depth + 1) ||
                   termContainsHole(current.arg, holeId, visited, depth + 1);
        case 'Lam':
            // Check param type (if any) and body. Body needs new visited set for its scope.
            if (current.paramType && termContainsHole(current.paramType, holeId, visited, depth + 1)) return true;
            const freshVLam = Var(current.paramName, true, "occurs_check"); // Special var for occurs check
            return termContainsHole(current.body(freshVLam), holeId, new Set(visited) , depth + 1); // new Set for body's scope
        case 'Pi':
            if (termContainsHole(current.paramType, holeId, visited, depth + 1)) return true;
            const freshVPi = Var(current.paramName, true, "occurs_check");
            return termContainsHole(current.bodyType(freshVPi), holeId, new Set(visited) , depth + 1); // new Set for body type's scope
        case 'ObjTerm': return termContainsHole(current.cat, holeId, visited, depth + 1);
        case 'HomTerm':
            return termContainsHole(current.cat, holeId, visited, depth + 1) ||
                   termContainsHole(current.dom, holeId, visited, depth + 1) ||
                   termContainsHole(current.cod, holeId, visited, depth + 1);
        // Recursively check subterms for other category theory constructors...
        case 'FunctorCategoryTerm':
            return termContainsHole(current.domainCat, holeId, visited, depth + 1) ||
                   termContainsHole(current.codomainCat, holeId, visited, depth + 1);
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
        default: const exhaustiveCheck: never = current; return false;
    }
}

/**
 * Unifies a hole `hole` with a term `term`.
 * If `term` is also a hole, points one to the other (preferring lower ID).
 * Otherwise, assigns `term` to `hole.ref` if occurs check passes.
 * @param hole The hole term to unify (must be a Hole).
 * @param term The term to unify the hole with.
 * @param ctx Context.
 * @param depth Recursion depth.
 * @returns True if unification was successful (or deferred if term is also a hole).
 */
function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
    const normTerm = getTermRef(whnf(term, ctx, depth + 1)); // Unify with WHNF of term.

    if (normTerm.tag === 'Hole') {
        if (hole.id === normTerm.id) return true; // Unifying hole with itself.
        // Point one hole to another (e.g., ?h1 = ?h2). Prefer smaller ID as root.
        if (hole.id < normTerm.id) {
             (normTerm as Term & {tag:'Hole'}).ref = hole;
        } else {
             hole.ref = normTerm;
        }
        consoleLog(`[UnifyHole] ${hole.id} now points to ${normTerm.id} (or vice versa) (depth ${depth})`);
        return true; // Not strictly solved, but progress made by linking holes.
    }

    // Occurs check: ensure `hole` does not appear in `normTerm`.
    if (termContainsHole(normTerm, hole.id, new Set(), depth + 1)) {
        console.error(`[UnifyHole CRITICAL] Occurs check FAILED for hole ${hole.id} in term ${printTerm(normTerm)}. Depth: ${depth}. This means unification cannot proceed for this hole.`);
        return false; // Occurs check failed.
    }

    // Assign normTerm to hole.ref. This "solves" the hole.
    consoleLog(`[UnifyHole] Setting ${hole.id}.ref = ${printTerm(normTerm)} (depth ${depth}).`);
    hole.ref = normTerm;
    return true; // Hole successfully unified.
}

/**
 * Helper to unify lists of arguments (e.g., for App, HomTerm, etc.).
 * @param args1 Array of terms or undefined.
 * @param args2 Array of terms or undefined.
 * @param ctx Context.
 * @param depth Recursion depth.
 * @returns Unification status for the argument list.
 */
function unifyArgs(args1: (Term | undefined)[], args2: (Term | undefined)[], ctx: Context, depth: number): UnifyResult {
    if (args1.length !== args2.length) return UnifyResult.Failed; // Different number of args.

    let madeProgressOverall = false;
    let allSubSolved = true;

    for (let i = 0; i < args1.length; i++) {
        const t1_arg = args1[i];
        const t2_arg = args2[i];

        if (t1_arg === undefined && t2_arg === undefined) continue; // Both undefined, skip.
        // If one is undefined and other is not, this is a structural mismatch if not handled by holes.
        // For unification, treat undefined implicit args as fresh holes.
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
    // If not all solved, but no failure and some progress, return Progress.
    // If no failure and no progress (all were Progress/Deferred), still Progress.
    return madeProgressOverall ? UnifyResult.Progress : UnifyResult.Progress; // Or map Deferred to Progress
}


/**
 * Attempts to unify two terms `t1` and `t2`.
 * Unification may solve holes, decompose problems, or apply unification rules.
 * @param t1 First term.
 * @param t2 Second term.
 * @param ctx Context.
 * @param depth Recursion depth.
 * @returns The result of the unification attempt.
 */
export function unify(t1: Term, t2: Term, ctx: Context, depth = 0): UnifyResult {
    if (depth > CORE_MAX_STACK_DEPTH) throw new Error(`Unification stack depth exceeded (Unify depth: ${depth}, ${printTerm(t1)} vs ${printTerm(t2)})`);

    // Always work with dereferenced terms.
    let current_t1 = getTermRef(t1);
    let current_t2 = getTermRef(t2);

    // If already identical (and not holes), they are unified.
    if (current_t1 === current_t2 && current_t1.tag !== 'Hole') return UnifyResult.Solved;

    // Handle hole cases first.
    if (current_t1.tag === 'Hole') {
        return unifyHole(current_t1, current_t2, ctx, depth + 1)
            ? UnifyResult.Solved // unifyHole returning true means it assigned or linked.
            : tryUnificationRules(current_t1, current_t2, ctx, depth +1); // If unifyHole failed (occurs check)
    }
    if (current_t2.tag === 'Hole') {
        return unifyHole(current_t2, current_t1, ctx, depth + 1)
            ? UnifyResult.Solved
            : tryUnificationRules(current_t1, current_t2, ctx, depth +1);
    }

    // Structural unification for known injective constructors (before full WHNF if structure is stable)
    if (current_t1.tag === current_t2.tag) {
        const commonTag = current_t1.tag;
        let structuralResult: UnifyResult | undefined = undefined;

        if (isEmdashUnificationInjectiveStructurally(commonTag)) {
            switch (commonTag) {
                case 'Type': case 'CatTerm': case 'SetTerm':
                    structuralResult = UnifyResult.Solved;
                    break;
                case 'Var': // Vars are compared by name after ensuring they are not global defs that should unfold.
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
                // FMap0Term, FMap1Term, NatTransComponentTerm can be injective if their functor/transf is.
                // This is usually handled after WHNF or by specific unification rules for them.
                // Adding simple structural decomposition here if their main components are considered fixed.
                case 'FMap0Term': {
                    const fm0_1 = current_t1 as Term & {tag:'FMap0Term'}; const fm0_2 = current_t2 as Term & {tag:'FMap0Term'};
                    // For implicits, if one side has it, other must too, or be a hole.
                    // unifyArgs handles undefined by creating holes.
                    structuralResult = unifyArgs(
                        [fm0_1.functor, fm0_1.objectX, fm0_1.catA_IMPLICIT, fm0_1.catB_IMPLICIT],
                        [fm0_2.functor, fm0_2.objectX, fm0_2.catA_IMPLICIT, fm0_2.catB_IMPLICIT],
                        ctx, depth + 1
                    );
                    break;
                }
                // Add similar cases for FMap1Term, NatTransTypeTerm, NatTransComponentTerm, HomCovFunctorIdentity etc.
                // if they are in EMDASH_UNIFICATION_INJECTIVE_TAGS and direct structural decomp is desired pre-WHNF.
            }
        }
        if (structuralResult !== undefined) {
            if (structuralResult === UnifyResult.Solved || structuralResult === UnifyResult.Failed) {
                 return (structuralResult === UnifyResult.Failed)
                        ? tryUnificationRules(current_t1, current_t2, ctx, depth + 1) // Try rules if structural failed
                        : structuralResult;
            }
            // If Progress, continue to WHNF phase.
        }
    }

    // Reduce to WHNF for unification.
    const rt1_whnf = whnf(current_t1, ctx, depth + 1);
    const rt2_whnf = whnf(current_t2, ctx, depth + 1);

    const rt1_final = getTermRef(rt1_whnf); // Resolve again after WHNF.
    const rt2_final = getTermRef(rt2_whnf);

    // Re-check identity and hole cases after WHNF.
    if (rt1_final === rt2_final && rt1_final.tag !== 'Hole') return UnifyResult.Solved;
    if (rt1_final.tag === 'Hole') {
        return unifyHole(rt1_final, rt2_final, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
    }
    if (rt2_final.tag === 'Hole') {
        return unifyHole(rt2_final, rt1_final, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
    }

    // If tags differ after WHNF, unification generally fails, unless a rule applies.
    if (rt1_final.tag !== rt2_final.tag) {
        // Special kernel rule: Obj A === Type  implies  A === Set
        if ((rt1_final.tag === 'ObjTerm' && rt2_final.tag === 'Type') || (rt2_final.tag === 'ObjTerm' && rt1_final.tag === 'Type')) {
            const objTermNode = (rt1_final.tag === 'ObjTerm' ? rt1_final : rt2_final) as Term & {tag: 'ObjTerm'};
            const setGlobalDef = globalDefs.get("Set");
            if (setGlobalDef?.value) { // Assuming Set is defined and its value is SetTerm()
                const setTermConstant = getTermRef(setGlobalDef.value);
                addConstraint(objTermNode.cat, setTermConstant, `UnifRule: Obj A === Type => A === Set`);
                consoleLog(`[Unify] Applied kernel rule: Obj A === Type => A === Set for ${printTerm(objTermNode)}`);
                return UnifyResult.RewrittenByRule; // Constraint added, solver will handle.
            }
        }
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1); // Try rules for mismatched tags.
    }

    // Icit check for App, Lam, Pi after WHNF.
    if ((rt1_final.tag === 'App' || rt1_final.tag === 'Lam' || rt1_final.tag === 'Pi') &&
        (rt1_final.icit !== (rt2_final as typeof rt1_final).icit)) {
         return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }

    // Main switch for tag-specific unification after WHNF.
    // Helper to find the ultimate head of an application chain (e.g., f a b -> f)
    const getUltimateHead = (term: Term): Term => {
        let currentHead = getTermRef(term);
        while (currentHead.tag === 'App') {
            currentHead = getTermRef(currentHead.func);
        }
        return currentHead;
    };

    switch (rt1_final.tag) {
        case 'Type': case 'CatTerm': case 'SetTerm': return UnifyResult.Solved; // Tags match, solved.
        case 'Var': { // Vars with same name and not further reducible.
            const var1 = rt1_final; const var2 = rt2_final as Term & {tag:'Var'};
            if (var1.name === var2.name) return UnifyResult.Solved;

            // Different constant symbols fail.
            const gdef1 = globalDefs.get(var1.name);
            const gdef2 = globalDefs.get(var2.name);
            if (gdef1 && gdef1.isConstantSymbol && gdef2 && gdef2.isConstantSymbol) {
                consoleLog(`[Unify Var CONSTANT MISMATCH] ${var1.name} vs ${var2.name}`);
                return UnifyResult.Failed;
            }
            // Otherwise, different vars, try rules or fail.
            return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        }
        case 'App': {
            const app1 = rt1_final; const app2 = rt2_final as Term & {tag:'App'};
            const ultimateHead1 = getUltimateHead(app1);
            const ultimateHead2 = getUltimateHead(app2);

            // If heads are different constants, fail.
            if (ultimateHead1.tag === 'Var' && ultimateHead2.tag === 'Var' && ultimateHead1.name !== ultimateHead2.name) {
                const gdefHead1 = globalDefs.get(ultimateHead1.name);
                const gdefHead2 = globalDefs.get(ultimateHead2.name);
                if (gdefHead1 && gdefHead1.isConstantSymbol && gdefHead2 && gdefHead2.isConstantSymbol) {
                    consoleLog(`[Unify App CONSTANT HEAD MISMATCH] ${ultimateHead1.name} vs ${ultimateHead2.name}`);
                    return UnifyResult.Failed;
                }
            }

            // If heads are same and injective global, unify components.
            if (ultimateHead1.tag === 'Var' && ultimateHead2.tag === 'Var' && ultimateHead1.name === ultimateHead2.name) {
                const gdef = globalDefs.get(ultimateHead1.name);
                if (gdef && gdef.isInjective) { // Head is an injective symbol.
                    // Unify func parts, then arg parts. This recursively handles (f x y) = (f x' y').
                    const funcStatus = unify(app1.func, app2.func, ctx, depth + 1);
                    if (funcStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
                    const argStatus = unify(app1.arg, app2.arg, ctx, depth + 1);
                    if (argStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

                    if (funcStatus === UnifyResult.Solved && argStatus === UnifyResult.Solved) return UnifyResult.Solved;
                    return UnifyResult.Progress; // Some component made progress or is deferred.
                }
            }
            // Default App unification (non-injective head or different/non-Var heads):
            // Unify functions and arguments separately. If both solve, App is solved.
            const funcUnifyStatus = unify(app1.func, app2.func, ctx, depth + 1);
            if (funcUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const argUnifyStatus = unify(app1.arg, app2.arg, ctx, depth + 1);
            if (argUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            if (funcUnifyStatus === UnifyResult.Solved && argUnifyStatus === UnifyResult.Solved) return UnifyResult.Solved;
            return UnifyResult.Progress; // Progress if sub-problems made progress or are deferred.
        }
        case 'Lam': { // Unify lambda parameters and bodies.
            const lam1 = rt1_final; const lam2 = rt2_final as Term & {tag:'Lam'};
            if (lam1._isAnnotated !== lam2._isAnnotated) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);

            let paramTypeStatus = UnifyResult.Solved;
            if (lam1._isAnnotated) { // Both annotated.
                if(!lam1.paramType || !lam2.paramType) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1); // Should not happen if well-formed.
                paramTypeStatus = unify(lam1.paramType, lam2.paramType, ctx, depth + 1);
                if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            }

            const freshV = Var(freshVarName(lam1.paramName), true); // For alpha-equivalence.
            const CtxParamType = (lam1._isAnnotated && lam1.paramType) ? getTermRef(lam1.paramType) : Hole(freshHoleName() + "_unif_lam_ctx");
            const extendedCtx = extendCtx(ctx, freshV.name, CtxParamType, lam1.icit);
            const bodyStatus = unify(lam1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);

            if(bodyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            if(paramTypeStatus === UnifyResult.Solved && bodyStatus === UnifyResult.Solved) return UnifyResult.Solved;
            return UnifyResult.Progress;
        }
        case 'Pi': { // Unify Pi parameter types and body types.
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
        // Cases for injective category theory constructors (after WHNF ensures they are not further reducible at head)
        case 'ObjTerm': {
            const argStatus = unify((rt1_final as Term & {tag:'ObjTerm'}).cat, (rt2_final as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
            return (argStatus === UnifyResult.Failed) ? tryUnificationRules(rt1_final, rt2_final, ctx, depth +1) : argStatus;
        }
        case 'HomTerm': {
            const hom1 = rt1_final as Term & {tag:'HomTerm'}; const hom2 = rt2_final as Term & {tag:'HomTerm'};
            const res = unifyArgs([hom1.cat, hom1.dom, hom1.cod], [hom2.cat, hom2.dom, hom2.cod], ctx, depth + 1);
            return (res === UnifyResult.Failed) ? tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1) : res;
        }
        case 'FunctorCategoryTerm': {
            const fc1 = rt1_final as Term & {tag:'FunctorCategoryTerm'}; const fc2 = rt2_final as Term & {tag:'FunctorCategoryTerm'};
            const res = unifyArgs([fc1.domainCat, fc1.codomainCat], [fc2.domainCat, fc2.codomainCat], ctx, depth + 1);
            return (res === UnifyResult.Failed) ? tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1) : res;
        }
        case 'FunctorTypeTerm': {
            const ftt1 = rt1_final as Term & {tag:'FunctorTypeTerm'}; const ftt2 = rt2_final as Term & {tag:'FunctorTypeTerm'};
            const res = unifyArgs([ftt1.domainCat, ftt1.codomainCat], [ftt2.domainCat, ftt2.codomainCat], ctx, depth + 1);
            return (res === UnifyResult.Failed) ? tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1) : res;
        }
        case 'FMap0Term': {
            const fm0_1 = rt1_final as Term & {tag:'FMap0Term'}; const fm0_2 = rt2_final as Term & {tag:'FMap0Term'};
            const res = unifyArgs(
                [fm0_1.functor, fm0_1.objectX, fm0_1.catA_IMPLICIT, fm0_1.catB_IMPLICIT],
                [fm0_2.functor, fm0_2.objectX, fm0_2.catA_IMPLICIT, fm0_2.catB_IMPLICIT],
                ctx, depth + 1
            );
            return (res === UnifyResult.Failed) ? tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1) : res;
        }
        case 'FMap1Term': {
            const fm1_1 = rt1_final as Term & {tag:'FMap1Term'}; const fm1_2 = rt2_final as Term & {tag:'FMap1Term'};
            const res = unifyArgs(
                [fm1_1.functor, fm1_1.morphism_a, fm1_1.catA_IMPLICIT, fm1_1.catB_IMPLICIT, fm1_1.objX_A_IMPLICIT, fm1_1.objY_A_IMPLICIT],
                [fm1_2.functor, fm1_2.morphism_a, fm1_2.catA_IMPLICIT, fm1_2.catB_IMPLICIT, fm1_2.objX_A_IMPLICIT, fm1_2.objY_A_IMPLICIT],
                ctx, depth + 1
            );
            return (res === UnifyResult.Failed) ? tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1) : res;
        }
        case 'NatTransTypeTerm': {
            const nt1 = rt1_final as Term & {tag:'NatTransTypeTerm'}; const nt2 = rt2_final as Term & {tag:'NatTransTypeTerm'};
            const res = unifyArgs(
                [nt1.catA, nt1.catB, nt1.functorF, nt1.functorG],
                [nt2.catA, nt2.catB, nt2.functorF, nt2.functorG],
                ctx, depth + 1
            );
            return (res === UnifyResult.Failed) ? tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1) : res;
        }
        case 'NatTransComponentTerm': {
            const nc1 = rt1_final as Term & {tag:'NatTransComponentTerm'}; const nc2 = rt2_final as Term & {tag:'NatTransComponentTerm'};
            const res = unifyArgs(
                [nc1.transformation, nc1.objectX, nc1.catA_IMPLICIT, nc1.catB_IMPLICIT, nc1.functorF_IMPLICIT, nc1.functorG_IMPLICIT],
                [nc2.transformation, nc2.objectX, nc2.catA_IMPLICIT, nc2.catB_IMPLICIT, nc2.functorF_IMPLICIT, nc2.functorG_IMPLICIT],
                ctx, depth + 1
            );
            return (res === UnifyResult.Failed) ? tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1) : res;
        }
        case 'HomCovFunctorIdentity': {
            const hc1 = rt1_final as Term & {tag:'HomCovFunctorIdentity'};
            const hc2 = rt2_final as Term & {tag:'HomCovFunctorIdentity'};
            const res = unifyArgs(
                [hc1.domainCat, hc1.objW_InDomainCat],
                [hc2.domainCat, hc2.objW_InDomainCat],
                ctx, depth + 1
            );
            return (res === UnifyResult.Failed) ? tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1) : res;
        }
        default:
            // This case should ideally not be reached if tags are identical and handled above.
            // If it is, it implies a missing specific handler for a tag.
            const unhandledTag = (rt1_final as any)?.tag || 'unknown_tag';
            console.warn(`Unify: Unhandled identical tag in switch (after WHNF): ${unhandledTag}`);
            return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }
}


/**
 * Collects all pattern variables (e.g., $x, $A) present in a term.
 * @param term The term to scan.
 * @param patternVarDecls List of declared pattern variable names for the current rule.
 * @param collectedVars Set to accumulate found pattern variable names.
 * @param visited Set to handle cycles in term structure during traversal.
 */
export function collectPatternVars(term: Term, patternVarDecls: PatternVarDecl[], collectedVars: Set<string>, visited: Set<Term> = new Set()): void {
    const current = getTermRef(term);
    if (visited.has(current) && current.tag !== 'Var' && current.tag !== 'Hole') return; // Avoid re-processing shared structures.
    visited.add(current);

    // Check if current term itself is a pattern variable.
    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        collectedVars.add(current.name);
    } else if (current.tag === 'Hole' && isPatternVarName(current.id, patternVarDecls)) {
        collectedVars.add(current.id); // Holes can also be used as pattern vars, e.g. $_
    }

    // Recursively scan subterms.
    switch (current.tag) {
        case 'App':
            collectPatternVars(current.func, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.arg, patternVarDecls, collectedVars, visited);
            break;
        case 'Lam':
            if (current.paramType) collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            // Body is a function; pattern vars in body are typically handled by instantiation during matching.
            // For collecting vars from the *structure* of the RHS of a rule, this might need instantiation.
            // For now, assume pattern vars in Lam bodies are found if they are in `paramType`.
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
        // Add cases for all other term types with subterms...
        case 'FunctorCategoryTerm':
            collectPatternVars(current.domainCat, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.codomainCat, patternVarDecls, collectedVars, visited);
            break;
        case 'FunctorTypeTerm':
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
        // Tags with no subterms (Var, Hole, Type, CatTerm, SetTerm) are base cases.
    }
}

/**
 * Applies a substitution from a unification rule match and adds new constraints from RHS of the rule.
 * Ensures that pattern variables appearing in RHS constraints but not in LHS patterns are instantiated with fresh holes.
 * @param rule The unification rule that was matched.
 * @param subst The substitution derived from matching LHS patterns.
 * @param ctx Context.
 */
function applyAndAddRuleConstraints(
    rule: { name: string, patternVars: PatternVarDecl[], lhsPattern1: Term, lhsPattern2: Term, rhsNewConstraints: Array<{t1:Term, t2:Term}> },
    subst: Substitution,
    ctx: Context // Ctx might be needed if applySubst or addConstraint evolves.
): void {
    // Collect pattern variables actually present in the rule's LHS patterns.
    const lhsVars = new Set<string>();
    collectPatternVars(rule.lhsPattern1, rule.patternVars, lhsVars);
    collectPatternVars(rule.lhsPattern2, rule.patternVars, lhsVars);

    // Create a modifiable substitution map.
    const finalSubst = new Map(subst);

    // For any pattern variable declared in `rule.patternVars` that appears in an RHS constraint
    // but NOT in any LHS pattern (and thus not in `subst`), instantiate it with a fresh hole.
    // This handles "existential" variables on the RHS of unification rules.
    for (const pVarDecl of rule.patternVars) {
        const pVarName = pVarDecl; // Assuming PatternVarDecl is string.
        if (pVarName === '_') continue; // Wildcard, not a variable to substitute.

        // Check if this pVar is used in any RHS constraint.
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
        // If used in RHS but not bound by LHS match, create a hole for it.
        if (usedInRhsConstraints && !lhsVars.has(pVarName) && !finalSubst.has(pVarName)) {
             finalSubst.set(pVarName, Hole(freshHoleName() + "_unifRuleRHS_" + pVarName.substring(1))); // Assuming pVarName starts with '$'
        }
    }

    // Apply the (potentially augmented) substitution to the RHS constraints and add them.
    for (const constrPair of rule.rhsNewConstraints) {
        const newT1 = applySubst(constrPair.t1, finalSubst, rule.patternVars);
        const newT2 = applySubst(constrPair.t2, finalSubst, rule.patternVars);
        addConstraint(newT1, newT2, `UnifRule ${rule.name}`);
    }
}

/**
 * Tries to apply user-defined unification rules to two terms.
 * A rule `L1 === L2  ==>  R1 === R2, ...` matches if `t1` matches `L1` and `t2` matches `L2` (or vice-versa).
 * If a match occurs, new constraints from the RHS are added.
 * @param t1 First term.
 * @param t2 Second term.
 * @param ctx Context.
 * @param depth Recursion depth.
 * @returns `UnifyResult.RewrittenByRule` if a rule applied, `UnifyResult.Failed` otherwise.
 */
function tryUnificationRules(t1: Term, t2: Term, ctx: Context, depth: number): UnifyResult {
    for (const rule of userUnificationRules) {
        // Try matching (t1 with lhsPattern1, t2 with lhsPattern2)
        let subst1 = matchPattern(rule.lhsPattern1, t1, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            // Pass subst1 to continue matching with consistent variable bindings.
            let subst2 = matchPattern(rule.lhsPattern2, t2, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) { // Full match for the rule.
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule; // Rule applied, new constraints added.
            }
        }
        // Try matching symmetrically (t2 with lhsPattern1, t1 with lhsPattern2)
        subst1 = matchPattern(rule.lhsPattern1, t2, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t1, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) { // Full match for the rule (symmetric).
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }
    }
    return UnifyResult.Failed; // No unification rule applied.
}


/**
 * Solves the current set of constraints.
 * Iteratively attempts to unify constraints until no more progress can be made or all are solved.
 * @param ctx The context for unification.
 * @param stackDepth Current recursion depth (for re-entrancy control).
 * @returns True if all constraints were solved, false otherwise.
 */
export function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > CORE_MAX_STACK_DEPTH * 2) throw new Error("solveConstraints stack depth exceeded");

    // Basic re-entrancy guard.
    if (solveConstraintsControl.depth > 0 && stackDepth > 0) {
        // This typically means solveConstraints was called from within unify/whnf,
        // which itself was called by solveConstraints. Allow shallow re-entry for specific cases
        // but prevent deep unbounded recursion.
        // consoleLog(`[solveConstraints SKIPPING RE-ENTRANT CALL] depth: ${solveConstraintsControl.depth}, stack: ${stackDepth}`);
        return true; // Assume outer call will handle it, or constraints will be re-evaluated.
    }

    solveConstraintsControl.depth++;
    let changedInOuterLoop = true; // Tracks if any constraint was solved or rule applied in an iteration.
    let iterations = 0;
    // Max iterations: heuristic based on number of constraints and rules, to prevent infinite loops.
    const maxIterations = (constraints.length * constraints.length + userUnificationRules.length * constraints.length + 100) * 2 + 200;

    while (changedInOuterLoop && iterations < maxIterations) {
        changedInOuterLoop = false;
        iterations++;
        let currentConstraintIdx = 0;

        while(currentConstraintIdx < constraints.length) {
            const constraint = constraints[currentConstraintIdx];
            const c_t1_current_ref = getTermRef(constraint.t1); // Work with resolved terms.
            const c_t2_current_ref = getTermRef(constraint.t2);

            // If terms are already equal, remove constraint.
            if (areEqual(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1)) {
                constraints.splice(currentConstraintIdx, 1); // Remove solved constraint.
                changedInOuterLoop = true;
                continue; // Process next constraint from the (now shorter) list.
            }

            // Attempt to unify the constraint.
            try {
                const unifyResult = unify(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1);

                if (unifyResult === UnifyResult.Solved) {
                    // Unification reported Solved. Double check with areEqual before removing.
                    // This handles cases where unify solved a hole that makes terms equal.
                    if (areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
                        constraints.splice(currentConstraintIdx, 1);
                    } else {
                        // Unify said Solved but areEqual is false. This implies `unify` might have linked two holes
                        // (e.g. ?a = ?b) which it considers "solved" for that step but doesn't make them ground-equal.
                        // Keep the constraint for now, it might resolve later.
                        currentConstraintIdx++;
                    }
                    changedInOuterLoop = true;
                } else if (unifyResult === UnifyResult.RewrittenByRule) {
                    // A unification rule applied, replacing this constraint with new ones (or none).
                    constraints.splice(currentConstraintIdx, 1); // Original constraint consumed by rule.
                    changedInOuterLoop = true;
                    // New constraints are added by `applyAndAddRuleConstraints`, will be processed in this loop or next.
                } else if (unifyResult === UnifyResult.Progress) {
                    // Unification made progress (e.g., decomposed a problem) but not fully solved.
                    // Keep constraint, try again later.
                    changedInOuterLoop = true; // Progress was made overall.
                    currentConstraintIdx++;
                } else { // UnifyResult.Failed
                    console.log(`[solveConstraints DEBUG] UnifyResult.Failed for constraint: ${printTerm(c_t1_current_ref)} vs ${printTerm(c_t2_current_ref)} (orig: ${constraint.origin || 'unknown'})`);
                    console.warn(`Unification failed permanently for constraint: ${printTerm(c_t1_current_ref)} === ${printTerm(c_t2_current_ref)} (orig: ${constraint.origin || 'unknown'})`);
                    solveConstraintsControl.depth--;
                    return false; // Hard failure.
                }
            } catch (e) {
                // Catch errors during unification itself (e.g., stack overflow, internal errors).
                console.error(`Error during unification of ${printTerm(c_t1_current_ref)} and ${printTerm(c_t2_current_ref)} (origin: ${constraint.origin || 'unknown'}): ${(e as Error).message}`);
                console.error((e as Error).stack);
                solveConstraintsControl.depth--;
                return false; // Unification process itself failed.
            }
        } // End while currentConstraintIdx < constraints.length
    } // End while changedInOuterLoop

    if (iterations >= maxIterations && changedInOuterLoop && constraints.length > 0) {
        // Reached max iterations but was still making changes. Likely a complex scenario or non-termination.
        console.warn(`Constraint solving reached max iterations (${maxIterations}) and was still making changes. Constraints left: ${constraints.length}`);
        if (constraints.length > 0) {
            console.warn(`First remaining constraint: ${printTerm(getTermRef(constraints[0].t1))} vs ${printTerm(getTermRef(constraints[0].t2))}`);
        }
    }

    // Final check: are all remaining constraints actually solved?
    const allSolved = constraints.length === 0 || constraints.every(c => areEqual(getTermRef(c.t1), getTermRef(c.t2), ctx, stackDepth + 1));
    if(allSolved && constraints.length > 0) {
        consoleLog(`[solveConstraints] All remaining ${constraints.length} constraints verified as equal.`);
        constraints.length = 0; // Clear them if all are effectively solved.
    }

    solveConstraintsControl.depth--;
    return allSolved;
}