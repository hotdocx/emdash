import { Term, Context, PatternVarDecl, Substitution, UnifyResult, Icit, Hole, App, Lam, Pi, Var, ObjTerm, HomTerm, Type, CatTerm, MkCat_, IdentityMorph, ComposeMorph } from './core_types';
import { getTermRef, consoleLog, globalDefs, userRewriteRules, addConstraint, constraints, emptyCtx, extendCtx, isKernelConstantSymbolStructurally, isEmdashUnificationInjectiveStructurally, userUnificationRules, freshVarName, freshHoleName } from './core_context_globals';
import { printTerm, isPatternVarName, matchPattern, applySubst } from './core_elaboration';

export const MAX_WHNF_ITERATIONS = 1000;
export const MAX_STACK_DEPTH = 200;

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
            const freshVName = rt1.paramName; // Use original param name for HOAS instantiation
            const freshV = Var(freshVName);
            // Context for body comparison: Use the actual param type if annotated, otherwise a placeholder hole
            const paramTypeForCtx = (rt1._isAnnotated && rt1.paramType) ? getTermRef(rt1.paramType) : Hole(freshHoleName()+"_structEq_unannot_lam_param");
            const extendedCtx = extendCtx(ctx, freshVName, paramTypeForCtx, rt1.icit);
            return areStructurallyEqualNoWhnf(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            if (!areStructurallyEqualNoWhnf(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            const freshVName = rt1.paramName; // Use original param name
            const freshV = Var(freshVName);
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
        case 'MkCat_': {
            const mkcat2 = rt2 as Term & {tag:'MkCat_'};
            return areStructurallyEqualNoWhnf(rt1.objRepresentation, mkcat2.objRepresentation, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.homRepresentation, mkcat2.homRepresentation, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.composeImplementation, mkcat2.composeImplementation, ctx, depth + 1);
        }
        case 'IdentityMorph': {
            const id2 = rt2 as Term & {tag:'IdentityMorph'};
            const cat1_eq = rt1.cat_IMPLICIT ? getTermRef(rt1.cat_IMPLICIT) : undefined;
            const cat2_eq = id2.cat_IMPLICIT ? getTermRef(id2.cat_IMPLICIT) : undefined;
            let implicitsResult = true;
            if (cat1_eq && cat2_eq) {
                 if (!areStructurallyEqualNoWhnf(cat1_eq, cat2_eq, ctx, depth + 1)) implicitsResult = false;
            } else if (cat1_eq !== cat2_eq) { // One has it, the other doesn't
                implicitsResult = false;
            }
            return implicitsResult && areStructurallyEqualNoWhnf(rt1.obj, id2.obj, ctx, depth + 1);
        }
        case 'ComposeMorph': {
            const comp2 = rt2 as Term & {tag:'ComposeMorph'};
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areStructurallyEqualNoWhnf(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2; // Both must be undefined or both defined and equal
            };
            if (!implicitsMatch(rt1.cat_IMPLICIT, comp2.cat_IMPLICIT) ||
                !implicitsMatch(rt1.objX_IMPLICIT, comp2.objX_IMPLICIT) ||
                !implicitsMatch(rt1.objY_IMPLICIT, comp2.objY_IMPLICIT) ||
                !implicitsMatch(rt1.objZ_IMPLICIT, comp2.objZ_IMPLICIT)) {
                return false;
            }
            return areStructurallyEqualNoWhnf(rt1.g, comp2.g, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.f, comp2.f, ctx, depth + 1);
        }
        default:
            const exhaustiveCheck: never = rt1; return false;
    }
}

export function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`WHNF stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    let current = term;
    for (let i = 0; i < MAX_WHNF_ITERATIONS; i++) {
        let changedInThisPass = false;
        const termAtStartOfOuterPass = current; // For termination check on non-structural changes

        const dereffedCurrent = getTermRef(current);
        if (dereffedCurrent !== current) { // Check if getTermRef changed 'current' (e.g. Hole resolved)
            current = dereffedCurrent;
            changedInThisPass = true;
        }
        
        const termBeforeInnerReductions = current; // Capture state before trying any rule

        // Try user rewrite rules first, but only if not a kernel constant structure
        if (!isKernelConstantSymbolStructurally(current)) {
            for (const rule of userRewriteRules) { // userRewriteRules now StoredRewriteRule[]
                // Ensure termBeforeInnerReductions is WHNF enough for matching if rules expect it
                // However, matchPattern itself does not WHNF the termToMatch. WHNF is done at the start of this whnf call.
                const subst = matchPattern(rule.elaboratedLhs, termBeforeInnerReductions, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    const rhsApplied = getTermRef(applySubst(rule.elaboratedRhs, subst, rule.patternVars));
                    // Check if the rule application actually changed the term structurally to avoid infinite loops on non-reducing rules.
                    if (rhsApplied !== termBeforeInnerReductions && !areStructurallyEqualNoWhnf(rhsApplied, termBeforeInnerReductions, ctx, stackDepth + 1)) {
                        current = rhsApplied;
                        changedInThisPass = true;
                        break; // Restart WHNF from the top with the new term
                    }
                }
            }
            if (changedInThisPass) continue; // Restart WHNF if a rule applied and changed the term
        }

        // If no user rule applied or changed the term, try kernel reductions
        let reducedInKernelBlock = false;
        const termBeforeKernelReduction = current; // For comparison after kernel attempt

        switch (current.tag) {
            case 'App': {
                const func_whnf_ref = getTermRef(whnf(current.func, ctx, stackDepth + 1));
                if (func_whnf_ref.tag === 'Lam' && func_whnf_ref.icit === current.icit) { // Icit must match for beta-reduction
                    current = func_whnf_ref.body(current.arg);
                    reducedInKernelBlock = true;
                } else if (getTermRef(current.func) !== func_whnf_ref) { // func part was reduced by whnf
                    current = App(func_whnf_ref, current.arg, current.icit);
                    reducedInKernelBlock = true;
                }
                // Note: arg is not whnf'd here, that's for normalize
                break;
            }
            case 'ObjTerm': {
                const cat_whnf_ref = getTermRef(whnf(current.cat, ctx, stackDepth + 1));
                if (cat_whnf_ref.tag === 'MkCat_') {
                    current = cat_whnf_ref.objRepresentation;
                    reducedInKernelBlock = true;
                } else if (getTermRef(current.cat) !== cat_whnf_ref) {
                    current = ObjTerm(cat_whnf_ref);
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'HomTerm': {
                const cat_whnf_ref = getTermRef(whnf(current.cat, ctx, stackDepth + 1));
                if (cat_whnf_ref.tag === 'MkCat_') {
                    current = App(App(cat_whnf_ref.homRepresentation, current.dom, Icit.Expl), current.cod, Icit.Expl);
                    reducedInKernelBlock = true;
                } else if (getTermRef(current.cat) !== cat_whnf_ref) {
                    current = HomTerm(cat_whnf_ref, current.dom, current.cod);
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'ComposeMorph': {
                // Ensure implicits are present for reduction (they should be Holes if not yet known)
                if (current.cat_IMPLICIT && current.objX_IMPLICIT && current.objY_IMPLICIT && current.objZ_IMPLICIT) {
                    const cat_whnf_ref = getTermRef(whnf(current.cat_IMPLICIT, ctx, stackDepth + 1));
                    if (cat_whnf_ref.tag === 'MkCat_') {
                        // All objX/Y/Z implicits are used directly as they are object representations.
                        current = App(App(App(App(App(cat_whnf_ref.composeImplementation, current.objX_IMPLICIT, Icit.Expl), current.objY_IMPLICIT, Icit.Expl), current.objZ_IMPLICIT, Icit.Expl), current.g, Icit.Expl), current.f, Icit.Expl);
                        reducedInKernelBlock = true;
                    }
                }
                break;
            }
            case 'Var': {
                const gdef = globalDefs.get(current.name);
                if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol) {
                    current = gdef.value; // Substitute variable with its definition
                    reducedInKernelBlock = true;
                }
                break;
            }
        }

        if (reducedInKernelBlock) {
             changedInThisPass = true; // Mark change and continue WHNF loop
             continue;
        }
        
        // If getTermRef changed current (e.g. Hole resolved) without other reductions
        const currentAfterPossibleKernelOrRefChange = getTermRef(current);
        if (currentAfterPossibleKernelOrRefChange !== termBeforeInnerReductions && !changedInThisPass) {
             // This case covers if only getTermRef (at the start of the loop or implicitly) changed `current`
            current = currentAfterPossibleKernelOrRefChange;
            changedInThisPass = true;
        }
        
        // If no change in this entire pass (neither rewrite rule nor kernel reduction), then it's WHNF.
        if (!changedInThisPass) break;

        // Safety break for non-structural changes that might loop (e.g. hole pointing to itself, though getTermRef should handle this)
        if (current === termAtStartOfOuterPass && !changedInThisPass && i > 0) break; 

        if (i === MAX_WHNF_ITERATIONS - 1) { // Loop is about to exceed max iterations
             if (changedInThisPass || current !== termAtStartOfOuterPass) { // If it was still changing
                console.warn(`[TRACE whnf (${stackDepth})] WHNF reached max iterations for: ${printTerm(term)} -> ${printTerm(current)}`);
             } // If no change, it would have broken out earlier.
        }
    }
    return current;
}

export function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Normalize stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    const headReduced = whnf(term, ctx, stackDepth + 1);
    const current = getTermRef(headReduced); // Ensure we have the actual term after WHNF and dereferencing

    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': case 'CatTerm': return current;
        case 'ObjTerm': return ObjTerm(normalize(current.cat, ctx, stackDepth + 1));
        case 'HomTerm':
            return HomTerm(
                normalize(current.cat, ctx, stackDepth + 1),
                normalize(current.dom, ctx, stackDepth + 1),
                normalize(current.cod, ctx, stackDepth + 1)
            );
        case 'MkCat_':
            return MkCat_(
                normalize(current.objRepresentation, ctx, stackDepth + 1),
                normalize(current.homRepresentation, ctx, stackDepth + 1),
                normalize(current.composeImplementation, ctx, stackDepth + 1)
            );
        case 'IdentityMorph':
            return IdentityMorph(
                normalize(current.obj, ctx, stackDepth + 1),
                current.cat_IMPLICIT ? normalize(current.cat_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'ComposeMorph':
             return ComposeMorph(
                normalize(current.g, ctx, stackDepth + 1),
                normalize(current.f, ctx, stackDepth + 1),
                current.cat_IMPLICIT ? normalize(current.cat_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objX_IMPLICIT ? normalize(current.objX_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objY_IMPLICIT ? normalize(current.objY_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objZ_IMPLICIT ? normalize(current.objZ_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'Lam': {
            const currentLam = current;
            // Normalize paramType only if it's annotated and present
            const normLamParamType = (currentLam._isAnnotated && currentLam.paramType)
                                     ? normalize(currentLam.paramType, ctx, stackDepth + 1)
                                     : undefined;

            const newBodyFn = (v_arg: Term): Term => {
                // The context for normalizing the body needs the lambda's parameter binding.
                // The v_arg is the (fresh) variable representing the lambda parameter.
                const paramTypeForBodyCtx = normLamParamType || // Use normalized type if available
                                            (currentLam.paramType ? getTermRef(currentLam.paramType) : Hole(freshHoleName()+"_norm_lam_body_ctx"));

                // Extend the outer context (ctx) not a potentially modified inner context
                const bodyCtx = extendCtx(ctx, currentLam.paramName, paramTypeForBodyCtx, currentLam.icit);
                return normalize(currentLam.body(v_arg), bodyCtx, stackDepth + 1);
            };
            // Direct construction for robustness
            return {
                tag: 'Lam',
                paramName: currentLam.paramName,
                icit: currentLam.icit,
                paramType: normLamParamType, // Correctly undefined if not annotated originally
                _isAnnotated: currentLam._isAnnotated, // Preserve original annotation status
                body: newBodyFn
            };
        }
        case 'App':
            const normFunc = normalize(current.func, ctx, stackDepth + 1);
            const normArg = normalize(current.arg, ctx, stackDepth + 1);
            const finalNormFunc = getTermRef(normFunc); // Deref after normalize
            // Post-normalization beta-reduction attempt if func became a lambda
            if (finalNormFunc.tag === 'Lam' && finalNormFunc.icit === current.icit) {
                // Recursively normalize the result of beta-reduction
                return normalize(finalNormFunc.body(normArg), ctx, stackDepth + 1);
            }
            return App(normFunc, normArg, current.icit); // No reduction, return App with normalized parts
        case 'Pi': {
            const currentPi = current;
            const normPiParamType = normalize(currentPi.paramType, ctx, stackDepth + 1);
            return Pi(currentPi.paramName, currentPi.icit, normPiParamType, (v_arg: Term) => {
                const bodyTypeCtx = extendCtx(ctx, currentPi.paramName, normPiParamType, currentPi.icit);
                return normalize(currentPi.bodyType(v_arg), bodyTypeCtx, stackDepth + 1);
            });
        }
        default: const exhaustiveCheck: never = current; throw new Error(`Normalize: Unhandled term: ${exhaustiveCheck}`);
    }
}

export function areEqual(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Equality check depth exceeded (areEqual depth: ${depth})`);
    const rt1 = getTermRef(whnf(t1, ctx, depth + 1));
    const rt2 = getTermRef(whnf(t2, ctx, depth + 1));

    if (rt1.tag === 'Hole' && rt2.tag === 'Hole') return rt1.id === rt2.id;
    if (rt1.tag === 'Hole' || rt2.tag === 'Hole') return false; // One is hole, other isn't
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
            return areEqual(rt1.func, app2.func, ctx, depth + 1) &&
                   areEqual(rt1.arg, app2.arg, ctx, depth + 1);
        }
        case 'Lam': {
            const lam2 = rt2 as Term & {tag:'Lam'};
            if (rt1._isAnnotated !== lam2._isAnnotated) return false;
            let paramTypeOk = true;
            if (rt1._isAnnotated) { // If annotated, paramTypes must exist and be equal
                if (!rt1.paramType || !lam2.paramType || !areEqual(rt1.paramType, lam2.paramType, ctx, depth + 1)) {
                    paramTypeOk = false;
                }
            } // If not annotated, paramTypes are ignored (should be undefined)
            if(!paramTypeOk) return false;

            const freshVName = rt1.paramName; // Use original paramName for HOAS instantiation
            const freshV = Var(freshVName);
            // For context, use the actual param type if annotated, otherwise a placeholder
            const paramTypeForCtx = (rt1._isAnnotated && rt1.paramType) ? getTermRef(rt1.paramType) : Hole(freshHoleName()+"_areEqual_unannot_lam_param");
            const extendedCtx = extendCtx(ctx, freshVName, paramTypeForCtx, rt1.icit);
            return areEqual(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            if (!areEqual(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            const freshVName = rt1.paramName; // Use original paramName
            const freshV = Var(freshVName);
            const extendedCtx = extendCtx(ctx, freshVName, getTermRef(rt1.paramType), rt1.icit);
            return areEqual(rt1.bodyType(freshV), pi2.bodyType(freshV), extendedCtx, depth + 1);
        }
        case 'ObjTerm': return areEqual(rt1.cat, (rt2 as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
        case 'HomTerm': {
            const hom2 = rt2 as Term & {tag:'HomTerm'};
            return areEqual(rt1.cat, hom2.cat, ctx, depth + 1) &&
                   areEqual(rt1.dom, hom2.dom, ctx, depth + 1) &&
                   areEqual(rt1.cod, hom2.cod, ctx, depth + 1);
        }
        case 'MkCat_': {
            const mkcat2 = rt2 as Term & {tag:'MkCat_'};
            return areEqual(rt1.objRepresentation, mkcat2.objRepresentation, ctx, depth + 1) &&
                   areEqual(rt1.homRepresentation, mkcat2.homRepresentation, ctx, depth + 1) &&
                   areEqual(rt1.composeImplementation, mkcat2.composeImplementation, ctx, depth + 1);
        }
        case 'IdentityMorph': {
            const id2 = rt2 as Term & {tag:'IdentityMorph'};
            const cat1_eq = rt1.cat_IMPLICIT ? getTermRef(rt1.cat_IMPLICIT) : undefined;
            const cat2_eq = id2.cat_IMPLICIT ? getTermRef(id2.cat_IMPLICIT) : undefined;
            let implicitsResult = true;
            if (cat1_eq && cat2_eq) { // Both defined
                 if (!areEqual(cat1_eq, cat2_eq, ctx, depth + 1)) implicitsResult = false;
            } else if (cat1_eq !== cat2_eq) { // One defined, other not
                implicitsResult = false;
            }
            return implicitsResult && areEqual(rt1.obj, id2.obj, ctx, depth + 1);
        }
        case 'ComposeMorph': {
            const comp2 = rt2 as Term & {tag:'ComposeMorph'};
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areEqual(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2; // Both must be undefined, or both defined and equal
            };
             if (!implicitsMatch(rt1.cat_IMPLICIT, comp2.cat_IMPLICIT) ||
                !implicitsMatch(rt1.objX_IMPLICIT, comp2.objX_IMPLICIT) ||
                !implicitsMatch(rt1.objY_IMPLICIT, comp2.objY_IMPLICIT) ||
                !implicitsMatch(rt1.objZ_IMPLICIT, comp2.objZ_IMPLICIT)) {
                return false;
            }
            return areEqual(rt1.g, comp2.g, ctx, depth + 1) &&
                   areEqual(rt1.f, comp2.f, ctx, depth + 1);
        }
        default: const exhaustiveCheck: never = rt1; return false;
    }
}

export function termContainsHole(term: Term, holeId: string, visited: Set<string> = new Set(), depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH * 2) { // Increased depth for occurs check, can be complex
        console.warn(`termContainsHole depth exceeded for hole ${holeId} in ${printTerm(term)}`);
        return true; // Fail safe: assume it contains the hole to prevent unsound unification
    }
    
    const current = getTermRef(term); // Crucial: operate on the resolved term

    // Use a unique key for visited set to handle shared structures and simple cycles
    // For HOAS, new Set() for recursive calls on instantiated bodies prevents cross-body visited issues.
    const termKey = current.tag === 'Hole' ? `Hole:${current.id}` : 
                    current.tag === 'Var' ? `Var:${current.name}` :
                    printTerm(current); // printTerm can be expensive but provides some structural identity for non-Vars/Holes.

    if (visited.has(termKey) && current.tag !== 'Hole' && current.tag !== 'Var' /* Vars/Holes are fine to revisit if IDs are different */) {
         return false; // Already checked this non-Hole/non-Var branch if the structure is identical.
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
            const freshVLam = Var(freshVarName("_occ_check_lam")); // Fresh var for HOAS body
            return termContainsHole(current.body(freshVLam), holeId, new Set(visited) /* new Set for body */, depth + 1);
        case 'Pi':
            if (termContainsHole(current.paramType, holeId, visited, depth + 1)) return true;
            const freshVPi = Var(freshVarName("_occ_check_pi")); // Fresh var for HOAS body type
            return termContainsHole(current.bodyType(freshVPi), holeId, new Set(visited) /* new Set for body type */, depth + 1);
        case 'ObjTerm': return termContainsHole(current.cat, holeId, visited, depth + 1);
        case 'HomTerm':
            return termContainsHole(current.cat, holeId, visited, depth + 1) ||
                   termContainsHole(current.dom, holeId, visited, depth + 1) ||
                   termContainsHole(current.cod, holeId, visited, depth + 1);
        case 'MkCat_':
            return termContainsHole(current.objRepresentation, holeId, visited, depth + 1) ||
                   termContainsHole(current.homRepresentation, holeId, visited, depth + 1) ||
                   termContainsHole(current.composeImplementation, holeId, visited, depth + 1);
        case 'IdentityMorph':
            return (current.cat_IMPLICIT && termContainsHole(current.cat_IMPLICIT, holeId, visited, depth + 1)) ||
                   termContainsHole(current.obj, holeId, visited, depth + 1);
        case 'ComposeMorph':
            return termContainsHole(current.g, holeId, visited, depth + 1) ||
                   termContainsHole(current.f, holeId, visited, depth + 1) ||
                   (current.cat_IMPLICIT && termContainsHole(current.cat_IMPLICIT, holeId, visited, depth + 1)) ||
                   (current.objX_IMPLICIT && termContainsHole(current.objX_IMPLICIT, holeId, visited, depth + 1)) ||
                   (current.objY_IMPLICIT && termContainsHole(current.objY_IMPLICIT, holeId, visited, depth + 1)) ||
                   (current.objZ_IMPLICIT && termContainsHole(current.objZ_IMPLICIT, holeId, visited, depth + 1));
        default: const exhaustiveCheck: never = current; return false;
    }
}

export function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
    const normTerm = getTermRef(whnf(term, ctx, depth + 1)); // WHNF the term to unify with
    if (normTerm.tag === 'Hole') {
        if (hole.id === normTerm.id) return true; // Unifying a hole with itself
        // Consistent ordering for hole unification (e.g. by ID name, or creation order if IDs are sequential)
        // This naive ID string comparison might not be robust if IDs are not well-ordered.
        // A proper solution might involve a global map or ranking of holes.
        if (hole.id < normTerm.id) { // Arbitrary but consistent ordering
             (normTerm as Term & {tag:'Hole'}).ref = hole;
        } else {
             hole.ref = normTerm;
        }
        consoleLog(`UnifyHole: ${hole.id} now points to ${normTerm.id} (or vice versa)`);
        return true;
    }
    // Occurs check: does 'normTerm' contain 'hole'?
    if (termContainsHole(normTerm, hole.id, new Set(), depth + 1)) {
        consoleLog(`UnifyHole: Occurs check failed for ${hole.id} in ${printTerm(normTerm)}`);
        return false; // Occurs check failed
    }
    hole.ref = normTerm; // Point the hole to the (normalized) term
    consoleLog(`UnifyHole: ${hole.id} now points to ${printTerm(normTerm)}`);
    return true;
}

// Unify lists of optional arguments (e.g. for kernel implicits)
export function unifyArgs(args1: (Term | undefined)[], args2: (Term | undefined)[], ctx: Context, depth: number): UnifyResult {
    if (args1.length !== args2.length) return UnifyResult.Failed; // Should not happen if used for same constructor
    let madeProgressOverall = false; // Tracks if any sub-unification made progress or was rewritten
    let allSubSolved = true; // Tracks if all sub-problems are fully solved

    for (let i = 0; i < args1.length; i++) {
        const t1_arg = args1[i];
        const t2_arg = args2[i];

        if (t1_arg === undefined && t2_arg === undefined) continue; // Both undefined, trivially equal

        // If one is undefined and the other is a concrete term (not a hole), this is a mismatch.
        // If one is undefined and other is a hole, the undefined one effectively becomes a new hole.
        const arg1ToUnify = t1_arg === undefined ? Hole(freshHoleName() + "_undef_arg_lhs_" + i) : t1_arg;
        const arg2ToUnify = t2_arg === undefined ? Hole(freshHoleName() + "_undef_arg_rhs_" + i) : t2_arg;
        
        if ((t1_arg === undefined && getTermRef(arg2ToUnify).tag !== 'Hole') ||
            (t2_arg === undefined && getTermRef(arg1ToUnify).tag !== 'Hole')) {
             // This check means if one side is implicitly absent (becomes a fresh hole), the other side better be a hole or unify with a fresh hole.
             // If one side is 'undefined' (becomes a hole) and other is 'Var("X")', it's like ?new_hole = Var("X"), which is fine.
             // The issue is if t1_arg is undefined, and t2_arg is Var("X"), then arg1ToUnify is Hole, arg2ToUnify is Var("X").
             // The condition above seems too strict.
             // What we want is: if one is undefined, it's like a wildcard (a fresh hole).
        }


        const argStatus = unify(arg1ToUnify, arg2ToUnify, ctx, depth + 1); // depth + 1 for recursion

        if (argStatus === UnifyResult.Failed) return UnifyResult.Failed; // If any arg fails, the whole thing fails

        if (argStatus === UnifyResult.RewrittenByRule || argStatus === UnifyResult.Progress) {
            madeProgressOverall = true; // If any arg makes progress or rewrites, overall progress is made
        }
        if (argStatus !== UnifyResult.Solved) {
            allSubSolved = false; // If any arg isn't solved, not all are solved
        }
    }

    if (allSubSolved) return UnifyResult.Solved;
    // If not all solved, but some progress was made (or rule rewritten), return that status.
    // If no progress and not all solved, it's still 'Progress' because sub-problems might solve later.
    return madeProgressOverall ? UnifyResult.Progress : UnifyResult.Progress; // Or perhaps a more nuanced status if no madeProgressOverall
}


export function unify(t1: Term, t2: Term, ctx: Context, depth = 0): UnifyResult {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Unification stack depth exceeded (Unify depth: ${depth}, ${printTerm(t1)} vs ${printTerm(t2)})`);

    const rt1_orig_ref = getTermRef(t1);
    const rt2_orig_ref = getTermRef(t2);

    if (rt1_orig_ref === rt2_orig_ref && rt1_orig_ref.tag !== 'Hole') return UnifyResult.Solved; // Same non-hole object after deref

    // Handle Hole on either side first (before WHNFing the other side if it's not a hole)
    if (rt1_orig_ref.tag === 'Hole') {
        return unifyHole(rt1_orig_ref, rt2_orig_ref, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(rt1_orig_ref, rt2_orig_ref, ctx, depth +1);
    }
    if (rt2_orig_ref.tag === 'Hole') {
        return unifyHole(rt2_orig_ref, rt1_orig_ref, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(rt1_orig_ref, rt2_orig_ref, ctx, depth +1);
    }

    // Now, neither is a Hole at the top level after initial getTermRef. WHNF both.
    const rt1_whnf = whnf(rt1_orig_ref, ctx, depth + 1);
    const rt2_whnf = whnf(rt2_orig_ref, ctx, depth + 1);

    // Dereference again after whnf, as whnf might return a hole or a ref to another term
    const rt1_final = getTermRef(rt1_whnf);
    const rt2_final = getTermRef(rt2_whnf);

    // Check for direct equality again if WHNF changed things or resolved to same term
    if (rt1_final === rt2_final && rt1_final.tag !== 'Hole') return UnifyResult.Solved;

    // Handle Hole again if WHNF exposed one
    if (rt1_final.tag === 'Hole') {
        return unifyHole(rt1_final, rt2_final, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
    }
    if (rt2_final.tag === 'Hole') {
        return unifyHole(rt2_final, rt1_final, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
    }

    // Structural comparison if tags differ after WHNF and dereferencing
    if (rt1_final.tag !== rt2_final.tag) {
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }
    
    // Icit check for App, Lam, Pi (tags are guaranteed to be the same here)
    if ((rt1_final.tag === 'App' || rt1_final.tag === 'Lam' || rt1_final.tag === 'Pi') &&
        (rt1_final.icit !== (rt2_final as typeof rt1_final).icit)) { // rt2_final has same tag as rt1_final
         return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1); // Different icitness, try rules
    }


    switch (rt1_final.tag) {
        case 'Type': case 'CatTerm': return UnifyResult.Solved; // Tags already matched, no further structure
        case 'Var': // Tags are 'Var' and names differ (checked by rt1_final === rt2_final earlier if names were same)
            return rt1_final.name === (rt2_final as Term & {tag:'Var'}).name ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        case 'App': {
            const app1 = rt1_final; const app2 = rt2_final as Term & {tag:'App'};
            // Injectivity for Var as function head
            const f1_head_whnf = getTermRef(whnf(app1.func, ctx, depth + 1));
            const f2_head_whnf = getTermRef(whnf(app2.func, ctx, depth + 1));

            if (f1_head_whnf.tag === 'Var' && f2_head_whnf.tag === 'Var' && f1_head_whnf.name === f2_head_whnf.name) {
                const gdef = globalDefs.get(f1_head_whnf.name);
                if (gdef && gdef.isInjective) { // If common Var head is injective
                    return unify(app1.arg, app2.arg, ctx, depth + 1); // Unify only args
                }
            }
            // Default: unify func and arg parts if not injective or different heads
            const funcUnifyStatus = unify(app1.func, app2.func, ctx, depth + 1);
            if (funcUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            
            const argUnifyStatus = unify(app1.arg, app2.arg, ctx, depth + 1);
            if (argUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            
            if (funcUnifyStatus === UnifyResult.Solved && argUnifyStatus === UnifyResult.Solved) {
                 // After sub-problems "solved", check if the whole App terms are now equal.
                 // Holes might have been filled making them equal.
                 return areEqual(rt1_final, rt2_final, ctx, depth+1) ? UnifyResult.Solved : UnifyResult.Progress;
            }
            return UnifyResult.Progress; // If sub-problems made progress but not fully solved, overall is progress
        }
        case 'Lam': {
            const lam1 = rt1_final; const lam2 = rt2_final as Term & {tag:'Lam'};
            if (lam1._isAnnotated !== lam2._isAnnotated) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            
            let paramTypeStatus = UnifyResult.Solved;
            if (lam1._isAnnotated) { // If annotated, types must be present and unify
                if(!lam1.paramType || !lam2.paramType) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1); // Should not happen if _isAnnotated
                paramTypeStatus = unify(lam1.paramType, lam2.paramType, ctx, depth + 1);
                if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }
            
            const freshV = Var(freshVarName(lam1.paramName)); // Use original param name for HOAS
            const CtxParamType = (lam1._isAnnotated && lam1.paramType) ? getTermRef(lam1.paramType) : Hole(freshHoleName() + "_unif_lam_ctx");
            const extendedCtx = extendCtx(ctx, freshV.name, CtxParamType, lam1.icit);
            const bodyStatus = unify(lam1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
            
            if(bodyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            
            if(paramTypeStatus === UnifyResult.Solved && bodyStatus === UnifyResult.Solved) {
                return areEqual(rt1_final, rt2_final, ctx, depth+1) ? UnifyResult.Solved : UnifyResult.Progress;
            }
            return UnifyResult.Progress;
        }
        case 'Pi': {
            const pi1 = rt1_final; const pi2 = rt2_final as Term & {tag:'Pi'};
            const paramTypeStatus = unify(pi1.paramType, pi2.paramType, ctx, depth + 1);
            if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            
            const freshV = Var(freshVarName(pi1.paramName)); // Use original param name
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(pi1.paramType), pi1.icit);
            const bodyTypeStatus = unify(pi1.bodyType(freshV), pi2.bodyType(freshV), extendedCtx, depth + 1);
            
            if(bodyTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            
            if(paramTypeStatus === UnifyResult.Solved && bodyTypeStatus === UnifyResult.Solved) {
                 return areEqual(rt1_final, rt2_final, ctx, depth+1) ? UnifyResult.Solved : UnifyResult.Progress;
            }
            return UnifyResult.Progress;
        }
         case 'ObjTerm': {
            const argStatus = unify(rt1_final.cat, (rt2_final as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
            return (argStatus === UnifyResult.Failed) ? tryUnificationRules(rt1_final, rt2_final, ctx, depth +1) : argStatus;
        }
        case 'HomTerm': {
            const hom1 = rt1_final; const hom2 = rt2_final as Term & {tag:'HomTerm'};
            const catStatus = unify(hom1.cat, hom2.cat, ctx, depth + 1);
            if(catStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const domStatus = unify(hom1.dom, hom2.dom, ctx, depth + 1);
            if(domStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const codStatus = unify(hom1.cod, hom2.cod, ctx, depth + 1);
            if(codStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            
            if(catStatus === UnifyResult.Solved && domStatus === UnifyResult.Solved && codStatus === UnifyResult.Solved) {
                return areEqual(rt1_final, rt2_final, ctx, depth+1) ? UnifyResult.Solved : UnifyResult.Progress;
            }
            return UnifyResult.Progress;
        }
        case 'MkCat_': {
            const mk1 = rt1_final; const mk2 = rt2_final as Term & {tag:'MkCat_'};
            const objRStatus = unify(mk1.objRepresentation, mk2.objRepresentation, ctx, depth + 1);
            if(objRStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            const homRStatus = unify(mk1.homRepresentation, mk2.homRepresentation, ctx, depth + 1);
            if(homRStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            const compIStatus = unify(mk1.composeImplementation, mk2.composeImplementation, ctx, depth + 1);
            if(compIStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            
            if(objRStatus === UnifyResult.Solved && homRStatus === UnifyResult.Solved && compIStatus === UnifyResult.Solved) {
                 return areEqual(rt1_final, rt2_final, ctx, depth+1) ? UnifyResult.Solved : UnifyResult.Progress;
            }
            return UnifyResult.Progress;
        }
        case 'IdentityMorph': {
            const id1 = rt1_final; const id2 = rt2_final as Term & {tag:'IdentityMorph'};
            // unifyArgs handles undefined implicits by treating them as fresh holes
            const catStatus = unifyArgs([id1.cat_IMPLICIT], [id2.cat_IMPLICIT], ctx, depth + 1);
            if(catStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            
            const objStatus = unify(id1.obj, id2.obj, ctx, depth + 1);
            if(objStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            
            if(catStatus === UnifyResult.Solved && objStatus === UnifyResult.Solved){
                 return areEqual(rt1_final, rt2_final, ctx, depth+1) ? UnifyResult.Solved : UnifyResult.Progress;
            }
            return UnifyResult.Progress;
        }
        case 'ComposeMorph': {
            const cm1 = rt1_final; const cm2 = rt2_final as Term & {tag:'ComposeMorph'};
            const implicitsStatus = unifyArgs(
                [cm1.cat_IMPLICIT, cm1.objX_IMPLICIT, cm1.objY_IMPLICIT, cm1.objZ_IMPLICIT],
                [cm2.cat_IMPLICIT, cm2.objX_IMPLICIT, cm2.objY_IMPLICIT, cm2.objZ_IMPLICIT],
                ctx, depth + 1 
            );
            if (implicitsStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            
            const gStatus = unify(cm1.g, cm2.g, ctx, depth + 1);
            if (gStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            
            const fStatus = unify(cm1.f, cm2.f, ctx, depth + 1);
            if (fStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            
            if (implicitsStatus === UnifyResult.Solved && gStatus === UnifyResult.Solved && fStatus === UnifyResult.Solved) {
                return areEqual(rt1_final, rt2_final, ctx, depth+1) ? UnifyResult.Solved : UnifyResult.Progress;
            }
            return UnifyResult.Progress;
        }
        default:
            console.warn(`Unify: Unhandled same-tag case: ${rt1_final.tag}`);
            return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }
}

export function collectPatternVars(term: Term, patternVarDecls: PatternVarDecl[], collectedVars: Set<string>, visited: Set<Term> = new Set()): void {
    const current = getTermRef(term);
    if (visited.has(current) && current.tag !== 'Var' && current.tag !== 'Hole') return; // Avoid re-processing same structure
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
            // For HOAS body, we cannot inspect without instantiation.
            // This function is for collecting $vars in the *structure* of the pattern,
            // not variables bound *by* the pattern that might appear in a HOAS body.
            // If $vars are intended inside HOAS body, this simple traversal won't find them.
            // Assume pattern vars are in structural positions or param types for now.
            break;
        case 'Pi':
            collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            // Similar to Lam body for bodyType.
            break;
        case 'ObjTerm': collectPatternVars(current.cat, patternVarDecls, collectedVars, visited); break;
        case 'HomTerm':
            collectPatternVars(current.cat, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.dom, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.cod, patternVarDecls, collectedVars, visited);
            break;
        case 'MkCat_':
            collectPatternVars(current.objRepresentation, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.homRepresentation, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.composeImplementation, patternVarDecls, collectedVars, visited);
            break;
        case 'IdentityMorph':
            if(current.cat_IMPLICIT) collectPatternVars(current.cat_IMPLICIT, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.obj, patternVarDecls, collectedVars, visited);
            break;
        case 'ComposeMorph':
            collectPatternVars(current.g, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.f, patternVarDecls, collectedVars, visited);
            if(current.cat_IMPLICIT) collectPatternVars(current.cat_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.objX_IMPLICIT) collectPatternVars(current.objX_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.objY_IMPLICIT) collectPatternVars(current.objY_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.objZ_IMPLICIT) collectPatternVars(current.objZ_IMPLICIT, patternVarDecls, collectedVars, visited);
            break;
        // No default needed as we only recurse on specific structures. Other tags are leaves for this function.
    }
}

export function applyAndAddRuleConstraints(rule: {lhsPattern1: Term, lhsPattern2: Term, patternVars: PatternVarDecl[], rhsNewConstraints: Array<{t1:Term, t2:Term}>, name: string}, subst: Substitution, ctx: Context): void {
    const lhsVars = new Set<string>(); // Vars appearing in LHS of the unification rule
    collectPatternVars(rule.lhsPattern1, rule.patternVars, lhsVars);
    collectPatternVars(rule.lhsPattern2, rule.patternVars, lhsVars);

    const finalSubst = new Map(subst); // Copy original substitution

    // For pattern variables used in RHS constraints but not in LHS patterns,
    // substitute them with fresh holes if not already in `subst`.
    for (const pVarDecl of rule.patternVars) {
        const pVarName = pVarDecl; // pVarDecl is now string (e.g., "$x")
        if (pVarName === '_') continue; // Wildcard

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
        // If a pVar is in RHS constraints, not in LHS patterns, and not already in subst, make it a fresh hole.
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

export function tryUnificationRules(t1: Term, t2: Term, ctx: Context, depth: number): UnifyResult {
    for (const rule of userUnificationRules) {
        // Try matching (LHS1, LHS2) with (t1, t2)
        let subst1 = matchPattern(rule.lhsPattern1, t1, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t2, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) { // Matched t1 with LHS1, t2 with LHS2
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }
        // Try matching (LHS1, LHS2) with (t2, t1) - symmetric application
        subst1 = matchPattern(rule.lhsPattern1, t2, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t1, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) { // Matched t2 with LHS1, t1 with LHS2
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }
    }
    return UnifyResult.Failed; // No rule applied
}

export function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > MAX_STACK_DEPTH * 2) throw new Error("solveConstraints stack depth exceeded");
    let changedInOuterLoop = true;
    let iterations = 0;
    // Max iterations: roughly (num_constraints^2) for pairwise interactions, plus rule applications,
    // plus a buffer. Multiplied by 2 for good measure.
    const maxIterations = (constraints.length * constraints.length + userUnificationRules.length * constraints.length + 100) * 2 + 200;

    while (changedInOuterLoop && iterations < maxIterations) {
        changedInOuterLoop = false;
        iterations++;
        let currentConstraintIdx = 0;
        while(currentConstraintIdx < constraints.length) { // Iterate through current constraints
            const constraint = constraints[currentConstraintIdx];
            const c_t1_current_ref = getTermRef(constraint.t1);
            const c_t2_current_ref = getTermRef(constraint.t2);

            // Check if constraint is already satisfied
            if (areEqual(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1)) {
                constraints.splice(currentConstraintIdx, 1); // Remove solved constraint
                changedInOuterLoop = true; // Progress made
                // Do not increment currentConstraintIdx, as the list shifted
                continue;
            }
            
            // Try to unify the current constraint
            try {
                const unifyResult = unify(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1);

                if (unifyResult === UnifyResult.Solved) {
                    // Unification claims solved. Verify by checking equality again.
                    // This is important if `unify` filled holes.
                    if (areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
                        constraints.splice(currentConstraintIdx, 1); // Remove if truly solved
                    } else {
                        // Claimed solved by unify, but not equal. This might mean holes were filled
                        // but the terms are not yet structurally identical (e.g. ?X=Y, ?X=Z becoming Y=Z).
                        // Keep the constraint for now, it might simplify further or other constraints might help.
                        currentConstraintIdx++;
                    }
                    changedInOuterLoop = true;
                } else if (unifyResult === UnifyResult.RewrittenByRule) {
                    // Rule applied, original constraint is removed, new ones are added by the rule.
                    constraints.splice(currentConstraintIdx, 1);
                    changedInOuterLoop = true;
                    // Restart constraint solving from the beginning as new constraints were added.
                    // This is implicit by not incrementing currentConstraintIdx and continuing the outer loop.
                } else if (unifyResult === UnifyResult.Progress) {
                    // Unification made some progress (e.g., decomposed a problem or filled a hole partially)
                    // but not fully solved. Keep constraint and move to next.
                    changedInOuterLoop = true; // Progress was made
                    currentConstraintIdx++;
                } else { // UnifyResult.Failed
                    console.warn(`Unification failed permanently for constraint: ${printTerm(c_t1_current_ref)} === ${printTerm(c_t2_current_ref)} (orig: ${constraint.origin || 'unknown'})`);
                    // This constraint cannot be solved with current rules/logic.
                    return false; // Overall solving fails
                }
            } catch (e) {
                console.error(`Error during unification of ${printTerm(c_t1_current_ref)} and ${printTerm(c_t2_current_ref)} (origin: ${constraint.origin || 'unknown'}): ${(e as Error).message}`);
                console.error((e as Error).stack);
                return false; // Error means failure to solve
            }
        } // End of inner while loop (iterating through constraints)
    } // End of outer while loop (looping as long as changes are made)

    if (iterations >= maxIterations && changedInOuterLoop && constraints.length > 0) {
        console.warn("Constraint solving reached max iterations and was still making changes. Constraints left: " + constraints.length);
        // It's possible it's a very complex set or a non-terminating but productive loop.
        // For now, consider this a failure if constraints remain.
    }

    // Final check: are all remaining constraints truly satisfied?
    if (constraints.length > 0) {
        for (const constraint of constraints) { // Check all that are left
            if (!areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
                console.warn(`Final check failed for UNRESOLVED constraint: ${printTerm(getTermRef(constraint.t1))} === ${printTerm(getTermRef(constraint.t2))} (orig: ${constraint.origin || 'unknown'})`);
                if (DEBUG_VERBOSE || iterations >= maxIterations) { // Print all remaining if stuck or verbose
                    console.warn("All remaining constraints after solve attempt:");
                    constraints.forEach(c => console.warn(`  ${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (origin: ${c.origin})`));
                }
                return false; // Not all constraints solved
            }
        }
        // If loop finished and all remaining constraints are equal, they can be cleared.
        // This might happen if the loop terminates due to maxIterations but remaining ones were actually solved.
        if (constraints.every(c => areEqual(getTermRef(c.t1), getTermRef(c.t2), ctx, stackDepth + 1))) {
            constraints.length = 0;
        }
    }
    return constraints.length === 0; // Success if no constraints are left
}