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
            const freshVName = rt1.paramName;
            const freshV = Var(freshVName);
            const paramTypeForCtx = rt1.paramType ? getTermRef(rt1.paramType) : Hole(freshHoleName()+"_structEq_unannot_lam_param");
            const extendedCtx = extendCtx(ctx, freshVName, paramTypeForCtx, rt1.icit);
            return areStructurallyEqualNoWhnf(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            if (!areStructurallyEqualNoWhnf(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            const freshVName = rt1.paramName;
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
            } else if (cat1_eq !== cat2_eq) { implicitsResult = false; }
            return implicitsResult && areStructurallyEqualNoWhnf(rt1.obj, id2.obj, ctx, depth + 1);
        }
        case 'ComposeMorph': {
            const comp2 = rt2 as Term & {tag:'ComposeMorph'};
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areStructurallyEqualNoWhnf(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2;
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
        const termAtStartOfOuterPass = current;

        const dereffedCurrent = getTermRef(current);
        if (dereffedCurrent !== current) {
            current = dereffedCurrent;
            changedInThisPass = true;
        }
        
        const termBeforeInnerReductions = current;

        if (!isKernelConstantSymbolStructurally(current)) {
            for (const rule of userRewriteRules) { // userRewriteRules now StoredRewriteRule[]
                const subst = matchPattern(rule.elaboratedLhs, termBeforeInnerReductions, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    const rhsApplied = getTermRef(applySubst(rule.elaboratedRhs, subst, rule.patternVars));
                    if (areStructurallyEqualNoWhnf(rhsApplied, termBeforeInnerReductions, ctx, stackDepth + 1)) {
                        // No change
                    } else {
                        current = rhsApplied;
                        changedInThisPass = true;
                        break;
                    }
                }
            }
            if (changedInThisPass) continue;
        }

        let reducedInThisBlock = false;
        switch (current.tag) {
            case 'App': {
                const func_whnf_ref = getTermRef(whnf(current.func, ctx, stackDepth + 1));
                if (func_whnf_ref.tag === 'Lam' && func_whnf_ref.icit === current.icit) { // Icit must match for beta-reduction
                    current = func_whnf_ref.body(current.arg);
                    reducedInThisBlock = true;
                } else if (getTermRef(current.func) !== func_whnf_ref) { // func part changed
                    current = App(func_whnf_ref, current.arg, current.icit);
                    reducedInThisBlock = true;
                }
                break;
            }
            case 'ObjTerm': {
                const cat_whnf_ref = getTermRef(whnf(current.cat, ctx, stackDepth + 1));
                if (cat_whnf_ref.tag === 'MkCat_') {
                    current = cat_whnf_ref.objRepresentation;
                    reducedInThisBlock = true;
                } else if (getTermRef(current.cat) !== cat_whnf_ref) {
                    current = ObjTerm(cat_whnf_ref);
                    reducedInThisBlock = true;
                }
                break;
            }
            case 'HomTerm': {
                const cat_whnf_ref = getTermRef(whnf(current.cat, ctx, stackDepth + 1));
                if (cat_whnf_ref.tag === 'MkCat_') {
                    current = App(App(cat_whnf_ref.homRepresentation, current.dom, Icit.Expl), current.cod, Icit.Expl);
                    reducedInThisBlock = true;
                } else if (getTermRef(current.cat) !== cat_whnf_ref) {
                    current = HomTerm(cat_whnf_ref, current.dom, current.cod);
                    reducedInThisBlock = true;
                }
                break;
            }
            case 'ComposeMorph': {
                if (current.cat_IMPLICIT && current.objX_IMPLICIT && current.objY_IMPLICIT && current.objZ_IMPLICIT) {
                    const cat_whnf_ref = getTermRef(whnf(current.cat_IMPLICIT, ctx, stackDepth + 1));
                    if (cat_whnf_ref.tag === 'MkCat_') {
                        current = App(App(App(App(App(cat_whnf_ref.composeImplementation, current.objX_IMPLICIT, Icit.Expl), current.objY_IMPLICIT, Icit.Expl), current.objZ_IMPLICIT, Icit.Expl), current.g, Icit.Expl), current.f, Icit.Expl);
                        reducedInThisBlock = true;
                    }
                }
                break;
            }
            case 'Var': {
                const gdef = globalDefs.get(current.name);
                if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol) {
                    current = gdef.value;
                    reducedInThisBlock = true;
                }
                break;
            }
        }
        if (reducedInThisBlock) {
             changedInThisPass = true;
             continue;
        }
        
        const currentAfterSubPartsReduced = getTermRef(current);
        if (currentAfterSubPartsReduced !== termBeforeInnerReductions) {
            current = currentAfterSubPartsReduced;
            changedInThisPass = true;
        }
        
        if (!changedInThisPass) break;
        if (current === termAtStartOfOuterPass && !changedInThisPass && i > 0) break;
        if (i === MAX_WHNF_ITERATIONS - 1 && (changedInThisPass || current !== termAtStartOfOuterPass)) {
            console.warn(`[TRACE whnf (${stackDepth})] WHNF reached max iterations for: ${printTerm(term)} -> ${printTerm(current)}`);
        }
    }
    return current;
}

export function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Normalize stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    const headReduced = whnf(term, ctx, stackDepth + 1);
    const current = getTermRef(headReduced);

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
            const normLamParamType = (currentLam._isAnnotated && currentLam.paramType)
                                     ? normalize(currentLam.paramType, ctx, stackDepth + 1)
                                     : undefined;
            const newLam = Lam(currentLam.paramName, currentLam.icit, normLamParamType,
                (v_arg: Term) => {
                    const paramTypeForBodyCtx = normLamParamType ||
                                                (currentLam.paramType ? getTermRef(currentLam.paramType) : Hole(freshHoleName()+"_norm_lam_body"));
                    let bodyCtx = ctx;
                    if (v_arg.tag === 'Var') { bodyCtx = extendCtx(ctx, v_arg.name, paramTypeForBodyCtx, currentLam.icit); }
                    return normalize(currentLam.body(v_arg), bodyCtx, stackDepth + 1);
                });
            (newLam as Term & {tag:'Lam'})._isAnnotated = currentLam._isAnnotated;
            if(normLamParamType) (newLam as Term & {tag:'Lam'}).paramType = normLamParamType;
            return newLam;
        }
        case 'App':
            const normFunc = normalize(current.func, ctx, stackDepth + 1);
            const normArg = normalize(current.arg, ctx, stackDepth + 1);
            const finalNormFunc = getTermRef(normFunc);
            if (finalNormFunc.tag === 'Lam' && finalNormFunc.icit === current.icit) {
                return normalize(finalNormFunc.body(normArg), ctx, stackDepth + 1);
            }
            return App(normFunc, normArg, current.icit);
        case 'Pi': {
            const currentPi = current;
            const normPiParamType = normalize(currentPi.paramType, ctx, stackDepth + 1);
            return Pi(currentPi.paramName, currentPi.icit, normPiParamType, (v_arg: Term) => {
                let bodyTypeCtx = ctx;
                if (v_arg.tag === 'Var') { bodyTypeCtx = extendCtx(ctx, v_arg.name, normPiParamType, currentPi.icit); }
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
        case 'Lam': {
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
            const freshV = Var(freshVName);
            const paramTypeForCtx = rt1.paramType ? getTermRef(rt1.paramType) : Hole(freshHoleName()+"_areEqual_unannot_lam_param");
            const extendedCtx = extendCtx(ctx, freshVName, paramTypeForCtx, rt1.icit);
            return areEqual(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            if (!areEqual(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            const freshVName = rt1.paramName;
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
            if (cat1_eq && cat2_eq) {
                 if (!areEqual(cat1_eq, cat2_eq, ctx, depth + 1)) implicitsResult = false;
            } else if (cat1_eq !== cat2_eq) { implicitsResult = false; }
            return implicitsResult && areEqual(rt1.obj, id2.obj, ctx, depth + 1);
        }
        case 'ComposeMorph': {
            const comp2 = rt2 as Term & {tag:'ComposeMorph'};
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areEqual(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2;
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
    if (depth > MAX_STACK_DEPTH * 2) {
        console.warn(`termContainsHole depth exceeded for hole ${holeId} in ${printTerm(term)}`);
        return true;
    }
    // Mark visited to handle cycles through non-Hole term structures (though less likely without general recursion)
    // For Holes, getTermRef handles cycles.
    const termKey = term.tag === 'Hole' ? term.id : printTerm(term); // A more robust key might be needed
    if (visited.has(termKey) && term.tag !== 'Hole') return false; // Already checked this non-Hole branch
    visited.add(termKey);

    const current = getTermRef(term); // Crucial: operate on the resolved term

    switch (current.tag) {
        case 'Hole': return current.id === holeId;
        case 'Type': case 'Var': case 'CatTerm': return false;
        case 'App':
            return termContainsHole(current.func, holeId, visited, depth + 1) ||
                   termContainsHole(current.arg, holeId, visited, depth + 1);
        case 'Lam':
            if (current.paramType && termContainsHole(current.paramType, holeId, visited, depth + 1)) return true;
            // For HOAS body, must instantiate to check. This creates a temporary structure.
            // This visited set is for the current path; new set for body check is okay.
            const freshVLam = Var(freshVarName("_occ_check_lam"));
            return termContainsHole(current.body(freshVLam), holeId, new Set(visited), depth + 1);
        case 'Pi':
            if (termContainsHole(current.paramType, holeId, visited, depth + 1)) return true;
            const freshVPi = Var(freshVarName("_occ_check_pi"));
            return termContainsHole(current.bodyType(freshVPi), holeId, new Set(visited), depth + 1);
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
        if (hole.id === normTerm.id) return true;
        // Consistent ordering for hole unification (e.g. by ID name, or creation order if IDs are sequential)
        // This naive ID string comparison might not be robust if IDs are not well-ordered.
        // A proper solution might involve a global map or ranking of holes.
        if (hole.id < normTerm.id) {
             (normTerm as Term & {tag:'Hole'}).ref = hole;
        } else {
             hole.ref = normTerm;
        }
        consoleLog(`UnifyHole: ${hole.id} now points to ${normTerm.id} (or vice versa)`);
        return true;
    }
    if (termContainsHole(normTerm, hole.id, new Set(), depth + 1)) {
        consoleLog(`UnifyHole: Occurs check failed for ${hole.id} in ${printTerm(normTerm)}`);
        return false;
    }
    hole.ref = normTerm;
    consoleLog(`UnifyHole: ${hole.id} now points to ${printTerm(normTerm)}`);
    return true;
}

export function unifyArgs(args1: (Term | undefined)[], args2: (Term | undefined)[], ctx: Context, depth: number): UnifyResult {
    if (args1.length !== args2.length) return UnifyResult.Failed;
    let madeProgress = false;
    let allSubSolved = true;
    for (let i = 0; i < args1.length; i++) {
        const t1_arg = args1[i]; const t2_arg = args2[i];
        if (t1_arg === undefined && t2_arg === undefined) continue;
        if ((t1_arg === undefined && t2_arg && getTermRef(t2_arg).tag !== 'Hole') ||
            (t2_arg === undefined && t1_arg && getTermRef(t1_arg).tag !== 'Hole')) {
            return UnifyResult.Failed;
        }
        const arg1ToUnify = t1_arg === undefined ? Hole(freshHoleName() + "_undef_arg_lhs_" + i) : t1_arg;
        const arg2ToUnify = t2_arg === undefined ? Hole(freshHoleName() + "_undef_arg_rhs_" + i) : t2_arg;
        const argStatus = unify(arg1ToUnify, arg2ToUnify, ctx, depth + 1);
        if (argStatus === UnifyResult.Failed) return UnifyResult.Failed;
        if (argStatus === UnifyResult.RewrittenByRule || argStatus === UnifyResult.Progress) madeProgress = true;
        if (argStatus !== UnifyResult.Solved) allSubSolved = false;
    }
    if (allSubSolved) return UnifyResult.Solved;
    return madeProgress ? UnifyResult.Progress : UnifyResult.Progress; // Progress if not all solved
}


export function unify(t1: Term, t2: Term, ctx: Context, depth = 0): UnifyResult {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Unification stack depth exceeded (Unify depth: ${depth}, ${printTerm(t1)} vs ${printTerm(t2)})`);

    const rt1_orig_ref = getTermRef(t1);
    const rt2_orig_ref = getTermRef(t2);

    if (rt1_orig_ref === rt2_orig_ref && rt1_orig_ref.tag !== 'Hole') return UnifyResult.Solved; // Same non-hole object

    // Handle Hole on either side first
    if (rt1_orig_ref.tag === 'Hole') {
        return unifyHole(rt1_orig_ref, rt2_orig_ref, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(rt1_orig_ref, rt2_orig_ref, ctx, depth +1);
    }
    if (rt2_orig_ref.tag === 'Hole') {
        return unifyHole(rt2_orig_ref, rt1_orig_ref, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(rt1_orig_ref, rt2_orig_ref, ctx, depth +1);
    }

    // Now, neither is a Hole at the top level. WHNF both.
    const rt1_whnf = whnf(rt1_orig_ref, ctx, depth + 1);
    const rt2_whnf = whnf(rt2_orig_ref, ctx, depth + 1);

    const rt1_final = getTermRef(rt1_whnf); // Dereference again after whnf
    const rt2_final = getTermRef(rt2_whnf);

    if (rt1_final === rt2_final && rt1_final.tag !== 'Hole') return UnifyResult.Solved;

    // Handle Hole again if WHNF exposed one
    if (rt1_final.tag === 'Hole') {
        return unifyHole(rt1_final, rt2_final, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
    }
    if (rt2_final.tag === 'Hole') {
        return unifyHole(rt2_final, rt1_final, ctx, depth + 1) ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
    }

    // Structural comparison if tags differ after WHNF
    if (rt1_final.tag !== rt2_final.tag) {
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }
    
    // Icit check for App, Lam, Pi
    if ((rt1_final.tag === 'App' || rt1_final.tag === 'Lam' || rt1_final.tag === 'Pi') &&
        (rt2_final.tag === rt1_final.tag) && rt1_final.icit !== (rt2_final as typeof rt1_final).icit) {
         return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }


    switch (rt1_final.tag) {
        case 'Type': case 'CatTerm': return UnifyResult.Solved; // Tags already matched
        case 'Var':
            return rt1_final.name === (rt2_final as Term & {tag:'Var'}).name ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        case 'App': {
            const app1 = rt1_final; const app2 = rt2_final as Term & {tag:'App'};
            // Injectivity for Var
            const f1_whnf = whnf(app1.func, ctx, depth + 1);
            const f2_whnf = whnf(app2.func, ctx, depth + 1);
            if (f1_whnf.tag === 'Var' && f2_whnf.tag === 'Var' && f1_whnf.name === f2_whnf.name) {
                const gdef = globalDefs.get(f1_whnf.name);
                if (gdef && gdef.isInjective) {
                    return unify(app1.arg, app2.arg, ctx, depth + 1);
                }
            }
            // Default: unify func and arg parts
            const funcUnifyStatus = unify(app1.func, app2.func, ctx, depth + 1);
            if (funcUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const argUnifyStatus = unify(app1.arg, app2.arg, ctx, depth + 1);
            if (argUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            if (funcUnifyStatus === UnifyResult.Solved && argUnifyStatus === UnifyResult.Solved) {
                 return areEqual(rt1_final, rt2_final, ctx, depth+1) ? UnifyResult.Solved : UnifyResult.Progress; // Solved if structurally equal after component solve
            }
            return UnifyResult.Progress;
        }
        case 'Lam': {
            const lam1 = rt1_final; const lam2 = rt2_final as Term & {tag:'Lam'};
            if (lam1._isAnnotated !== lam2._isAnnotated) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            let paramTypeStatus = UnifyResult.Solved;
            if (lam1._isAnnotated) {
                if(!lam1.paramType || !lam2.paramType) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
                paramTypeStatus = unify(lam1.paramType, lam2.paramType, ctx, depth + 1);
                if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }
            const freshV = Var(freshVarName(lam1.paramName));
            const CtxParamType = lam1.paramType ? getTermRef(lam1.paramType) : Hole(freshHoleName() + "_unif_lam_ctx");
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
            const freshV = Var(freshVarName(pi1.paramName));
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
            const catStatus = unifyArgs([id1.cat_IMPLICIT], [id2.cat_IMPLICIT], ctx, depth, rt1_final, rt2_final); // unifyArgs handles undefined
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
                ctx, depth, rt1_final, rt2_final
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
            // HOAS body: cannot inspect without instantiation. Assume pvars not inside body func for now.
            break;
        case 'Pi':
            collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            // HOAS body type: similar to Lam body.
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
    }
}

export function applyAndAddRuleConstraints(rule: {lhsPattern1: Term, lhsPattern2: Term, patternVars: PatternVarDecl[], rhsNewConstraints: Array<{t1:Term, t2:Term}>, name: string}, subst: Substitution, ctx: Context): void {
    const lhsVars = new Set<string>();
    collectPatternVars(rule.lhsPattern1, rule.patternVars, lhsVars);
    collectPatternVars(rule.lhsPattern2, rule.patternVars, lhsVars);

    const finalSubst = new Map(subst);
    for (const pVarDecl of rule.patternVars) {
        const pVarName = pVarDecl; // pVarDecl is now string
        if (pVarName === '_') continue;
        let usedInRhs = false;
        for(const {t1: rhs_t1, t2: rhs_t2} of rule.rhsNewConstraints) {
            const rhsConstraintVars = new Set<string>();
            collectPatternVars(rhs_t1, rule.patternVars, rhsConstraintVars);
            collectPatternVars(rhs_t2, rule.patternVars, rhsConstraintVars);
            if (rhsConstraintVars.has(pVarName)) { usedInRhs = true; break; }
        }
        if (usedInRhs && !lhsVars.has(pVarName) && !finalSubst.has(pVarName)) {
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
    if (stackDepth > MAX_STACK_DEPTH * 2) throw new Error("solveConstraints stack depth exceeded"); // Increased limit
    let changedInOuterLoop = true;
    let iterations = 0;
    const maxIterations = (constraints.length * constraints.length + userUnificationRules.length * 2 + 100) * 2 + 200;

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
                    // Check again after unification attempt which might fill holes
                    if (areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
                        constraints.splice(currentConstraintIdx, 1);
                    } else {
                         // It claimed solved, but not equal. Could be progress still needed.
                        currentConstraintIdx++;
                    }
                    changedInOuterLoop = true;
                } else if (unifyResult === UnifyResult.RewrittenByRule) {
                    constraints.splice(currentConstraintIdx, 1);
                    changedInOuterLoop = true;
                } else if (unifyResult === UnifyResult.Progress) {
                    changedInOuterLoop = true;
                    currentConstraintIdx++;
                } else { // Failed
                    console.warn(`Unification failed permanently for: ${printTerm(c_t1_current_ref)} === ${printTerm(c_t2_current_ref)} (orig: ${constraint.origin || 'unknown'})`);
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
        console.warn("Constraint solving reached max iterations and was still making changes. Constraints left: " + constraints.length);
    }
    if (constraints.length > 0) {
        for (const constraint of constraints) {
            if (!areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
                console.warn(`Final check failed for constraint: ${printTerm(getTermRef(constraint.t1))} === ${printTerm(getTermRef(constraint.t2))} (orig: ${constraint.origin || 'unknown'})`);
                 // For debugging, print all remaining constraints
                console.warn("All remaining constraints after solve failure:");
                constraints.forEach(c => console.warn(`  ${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`));
                return false;
            }
        }
    }
    return constraints.length === 0;
}