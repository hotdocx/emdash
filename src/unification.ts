/**
 * @file unification.ts
 * @description Term unification, constraint solving, and unification rule application.
 */

import {
    Term, Context, UnifyResult, Hole, Var, App, Lam, Pi, Type, CatTerm, ObjTerm, HomTerm,
    FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm, NatTransComponentTerm,
    HomCovFunctorIdentity, SetTerm, FunctorTypeTerm, Icit, Substitution, PatternVarDecl, UnificationRule
} from './types';
import {
    getTermRef, consoleLog, globalDefs, addConstraint, constraints, extendCtx, isEmdashUnificationInjectiveStructurally,
    userUnificationRules, freshVarName, freshHoleName, solveConstraintsControl, printTerm
} from './state';
import { MAX_STACK_DEPTH } from './constants';
import { whnf } from './reduction';
import { areEqual, areAllArgsConvertible } from './equality';
import { matchPattern, applySubst, collectPatternVars, getHeadAndSpine, abstractTermOverSpine, getFreeVariables } from './pattern';

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
            const freshVLam = Var(lam.paramName, true, "occurs_check");
            return termContainsHole(lam.body(freshVLam), holeId, new Set(visited) , depth + 1);
        }
        case 'Pi': {
            const pi = current;
            if (termContainsHole(pi.paramType, holeId, visited, depth + 1)) return true;
            const freshVPi = Var(pi.paramName, true, "occurs_check");
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
        case 'MkFunctorTerm':
            return termContainsHole(current.domainCat, holeId, visited, depth + 1) ||
                    termContainsHole(current.codomainCat, holeId, visited, depth + 1) ||
                    termContainsHole(current.fmap0, holeId, visited, depth + 1) ||
                    termContainsHole(current.fmap1, holeId, visited, depth + 1);
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
    if (depth > 30) console.log("unify: depth > 30", {depth}, {t1: printTerm(t1)}, {t2: printTerm(t2)});
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

    // --- Higher-Order Unification (Flex-Rigid for Miller Fragment) ---
    const hs1 = getHeadAndSpine(current_t1);
    const hs2 = getHeadAndSpine(current_t2);

    if (hs1.head.tag === 'Hole') {
        if (hs2.head.tag !== 'Hole') { // Flex-Rigid: ?M s1...sn = RHS
            const flexRigidResult = solveHoFlexRigid(hs1.head as Term & {tag: 'Hole'}, hs1.spine, current_t2, ctx, depth + 1);
            if (flexRigidResult !== UnifyResult.Failed) return flexRigidResult; // Solved or Progress
            // if Failed, fall through to other unification methods / rules
        } else { // Flex-Flex: ?M s1...sn = ?N t1...tm
            // TODO: Handle Flex-Flex, e.g. if M=N, unify spines. For now, fall through.
        }
    } else if (hs2.head.tag === 'Hole') { // Rigid-Flex: LHS = ?N t1...tm
        const rigidFlexResult = solveHoFlexRigid(hs2.head as Term & {tag: 'Hole'}, hs2.spine, current_t1, ctx, depth + 1);
        if (rigidFlexResult !== UnifyResult.Failed) return rigidFlexResult;
        // if Failed, fall through
    }
    // --- End Higher-Order Unification Attempt ---

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
                if (gdef && gdef.isInjective) { 
                    const funcStatus = unify(app1.func, app2.func, ctx, depth + 1);
                    if (funcStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
                    const argStatus = unify(app1.arg, app2.arg, ctx, depth + 1);
                    if (argStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

                    if (funcStatus === UnifyResult.Solved && argStatus === UnifyResult.Solved) return UnifyResult.Solved;
                    return UnifyResult.Progress;
                }
            }
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
        case 'ObjTerm': { // INJECTIVE
            const obj1 = rt1_final as Term & {tag:'ObjTerm'};
            const obj2 = rt2_final as Term & {tag:'ObjTerm'};
            let unifRuleResult = tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            if (unifRuleResult === UnifyResult.RewrittenByRule) {
                return unifRuleResult;
            }
            return unifyArgs([obj1.cat], [obj2.cat], ctx, depth + 1);
        }
        case 'HomTerm': { // INJECTIVE
            const hom1 = rt1_final as Term & {tag:'HomTerm'}; 
            const hom2 = rt2_final as Term & {tag:'HomTerm'};
            let unifRuleResult = tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            if (unifRuleResult === UnifyResult.RewrittenByRule) {
                return unifRuleResult;
            }
            return unifyArgs(
                [hom1.cat, hom1.dom, hom1.cod],
                [hom2.cat, hom2.dom, hom2.cod],
                ctx, depth + 1
            );
        }
        case 'FunctorCategoryTerm': // INJECTIVE
        case 'FunctorTypeTerm': { // INJECTIVE
            const fc1 = rt1_final as Term & {tag:'FunctorCategoryTerm'|'FunctorTypeTerm'};
            const fc2 = rt2_final as Term & {tag:'FunctorCategoryTerm'|'FunctorTypeTerm'};
            let unifRuleResult = tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            if (unifRuleResult === UnifyResult.RewrittenByRule) {
                return unifRuleResult;
            }
            return unifyArgs([fc1.domainCat, fc1.codomainCat], [fc2.domainCat, fc2.codomainCat], ctx, depth + 1);
        }
        case 'FMap0Term': { // NON-INJECTIVE
            const fm0_1 = rt1_final as Term & {tag:'FMap0Term'}; 
            const fm0_2 = rt2_final as Term & {tag:'FMap0Term'};
            const args1_fm0 = [fm0_1.functor, fm0_1.objectX, fm0_1.catA_IMPLICIT, fm0_1.catB_IMPLICIT];
            const args2_fm0 = [fm0_2.functor, fm0_2.objectX, fm0_2.catA_IMPLICIT, fm0_2.catB_IMPLICIT];
            if (areAllArgsConvertible(args1_fm0, args2_fm0, ctx, depth + 1)) {
                return UnifyResult.Solved;
            } else {
                return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }
        }
        case 'FMap1Term': { // NON-INJECTIVE
            const fm1_1 = rt1_final as Term & {tag:'FMap1Term'}; 
            const fm1_2 = rt2_final as Term & {tag:'FMap1Term'};
            const args1_fm1 = [fm1_1.functor, fm1_1.morphism_a, fm1_1.catA_IMPLICIT, fm1_1.catB_IMPLICIT, fm1_1.objX_A_IMPLICIT, fm1_1.objY_A_IMPLICIT];
            const args2_fm1 = [fm1_2.functor, fm1_2.morphism_a, fm1_2.catA_IMPLICIT, fm1_2.catB_IMPLICIT, fm1_2.objX_A_IMPLICIT, fm1_2.objY_A_IMPLICIT];
            if (areAllArgsConvertible(args1_fm1, args2_fm1, ctx, depth + 1)) {
                return UnifyResult.Solved;
            } else {
                return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }
        }
        case 'NatTransTypeTerm': { // INJECTIVE
            const nt1 = rt1_final as Term & {tag:'NatTransTypeTerm'}; 
            const nt2 = rt2_final as Term & {tag:'NatTransTypeTerm'};
            let unifRuleResult = tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            if (unifRuleResult === UnifyResult.RewrittenByRule) {
                return unifRuleResult;
            }
            return unifyArgs(
                [nt1.catA, nt1.catB, nt1.functorF, nt1.functorG],
                [nt2.catA, nt2.catB, nt2.functorF, nt2.functorG],
                ctx, depth + 1
            );
        }
        case 'NatTransComponentTerm': { // NON-INJECTIVE
            const nc1 = rt1_final as Term & {tag:'NatTransComponentTerm'}; 
            const nc2 = rt2_final as Term & {tag:'NatTransComponentTerm'};
            const args1_nc = [nc1.transformation, nc1.objectX, nc1.catA_IMPLICIT, nc1.catB_IMPLICIT, nc1.functorF_IMPLICIT, nc1.functorG_IMPLICIT];
            const args2_nc = [nc2.transformation, nc2.objectX, nc2.catA_IMPLICIT, nc2.catB_IMPLICIT, nc2.functorF_IMPLICIT, nc2.functorG_IMPLICIT];
            if (areAllArgsConvertible(args1_nc, args2_nc, ctx, depth + 1)) {
                return UnifyResult.Solved;
            } else {
                return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }
        }
        case 'HomCovFunctorIdentity': { // NON-INJECTIVE
            const hc1 = rt1_final as Term & {tag:'HomCovFunctorIdentity'};
            const hc2 = rt2_final as Term & {tag:'HomCovFunctorIdentity'};
            const args1_hc = [hc1.domainCat, hc1.objW_InDomainCat];
            const args2_hc = [hc2.domainCat, hc2.objW_InDomainCat];
            if (areAllArgsConvertible(args1_hc, args2_hc, ctx, depth + 1)) {
                return UnifyResult.Solved;
            } else {
                return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }
        }
        case 'MkFunctorTerm': { // INJECTIVE
            const mft1 = rt1_final as Term & {tag:'MkFunctorTerm'};
            const mft2 = rt2_final as Term & {tag:'MkFunctorTerm'};
            let unifRuleResult = tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            if (unifRuleResult === UnifyResult.RewrittenByRule) {
                return unifRuleResult;
            }
            return unifyArgs(
                [mft1.domainCat, mft1.codomainCat, mft1.fmap0, mft1.fmap1],
                [mft2.domainCat, mft2.codomainCat, mft2.fmap0, mft2.fmap1],
                ctx, depth + 1
            );
        }
        default:
            const unhandledTag = (rt1_final as any)?.tag || 'unknown_tag';
            console.warn(`Unify: Unhandled identical tag in switch (after WHNF): ${unhandledTag}`);
            return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
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

/**
 * Solves a higher-order unification problem of the form `?Hole spineArgs = rhsTerm` (flex-rigid)
 * for the Miller fragment (spineArgs are distinct bound variables).
 * @param hole The Hole term at the head of the flexible term.
 * @param spineArgs The arguments applied to the hole.
 * @param rhsTerm The rigid term on the other side of the equation.
 * @param ctx The current context.
 * @param depth Recursion depth.
 * @returns UnifyResult indicating success, progress, or failure.
 */
export function solveHoFlexRigid(
    hole: Term & { tag: 'Hole' },
    spineArgs: Term[],
    rhsTerm: Term,
    ctx: Context,
    depth: number
): UnifyResult {
    if (depth > MAX_STACK_DEPTH) throw new Error(`solveHoFlexRigid stack depth exceeded`);

    // 1. Validate Spine (Miller Fragment)
    const spineVars: (Term & { tag: 'Var' })[] = [];
    const distinctVarNames = new Set<string>();
    for (const arg of spineArgs) {
        const argRef = getTermRef(arg);
        if (argRef.tag !== 'Var' || !argRef.isLambdaBound) {
            consoleLog(`[solveHoFlexRigid] Spine validation failed: arg ${printTerm(argRef)} is not a lambda-bound variable.`);
            return UnifyResult.Failed; // Not a valid Miller fragment spine arg
        }
        if (distinctVarNames.has(argRef.name)) {
            consoleLog(`[solveHoFlexRigid] Spine validation failed: variable ${argRef.name} is not distinct in spine.`);
            return UnifyResult.Failed; // Variables in spine must be distinct
        }
        distinctVarNames.add(argRef.name);
        spineVars.push(argRef);
    }

    // 2. Occurs Check
    // Ensure WHNF of rhsTerm is used for occurs check, as hole.ref assignment uses WHNF.
    const whnfRhs = whnf(rhsTerm, ctx, depth + 1);
    if (termContainsHole(whnfRhs, hole.id, new Set(), depth + 1)) {
        consoleLog(`[solveHoFlexRigid] Occurs check failed for hole ${hole.id} in RHS ${printTerm(whnfRhs)}.`);
        return UnifyResult.Failed;
    }

    // 2.5. Scope Check
    if (hole.patternAllowedLocalBinders) {
        // This hole has scope restrictions. The free variables of the solution must be allowed.
        // Free variables of solution = FV(rhsTerm) \ {spineVars}
        const freeVarsRhs = getFreeVariables(whnfRhs);
        const spineVarNames = new Set(spineVars.map(v => v.name));
        
        for (const freeVarName of freeVarsRhs) {
            if (!spineVarNames.has(freeVarName)) {
                // This variable will be free in the solution. Check if it's allowed.
                // NOTE: This assumes binder names in the pattern and subject match, which is true
                // for general unification but requires binderNameMapping in pattern matching (which is handled there).
                if (!hole.patternAllowedLocalBinders.includes(freeVarName)) {
                    consoleLog(`[solveHoFlexRigid] Scope check failed for hole ${hole.id}. Solution would contain free variable '${freeVarName}' which is not in the allowed list [${hole.patternAllowedLocalBinders.join(', ')}].`);
                    return UnifyResult.Failed;
                }
            }
        }
    }

    // 3. Construct Solution
    try {
        consoleLog(`[solveHoFlexRigid] Attempting to solve ${hole.id} with spine [${spineVars.map(v => printTerm(v)).join(', ')}] = ${printTerm(rhsTerm)}`);
        const solution = abstractTermOverSpine(whnfRhs, spineVars, ctx);
        // Before assigning, ensure the solution itself doesn't immediately make the occurs check fail again if it were re-checked
        // This is mostly covered by the initial occurs check on whnfRhs, as abstractTermOverSpine shouldn't reintroduce the hole.
        consoleLog(`[solveHoFlexRigid] Solution for ${hole.id}: ${printTerm(solution)}`);
        
        // The unifyHole function handles assigning to hole.ref and further checks/dereferencing.
        // We directly assign here and expect the broader unification loop to continue/re-check.
        // This is because unifyHole might try to unify hole with another hole, which is not what we are doing here.
        // We are *defining* the hole.
        hole.ref = solution; 
        // After setting the ref, the original constraint might now be solvable or lead to new ones.
        // Returning Progress indicates that the constraint processor should re-evaluate.
        return UnifyResult.Progress; // Indicates a change was made, constraints should be re-evaluated.
    } catch (e) {
        console.error(`[solveHoFlexRigid] Error constructing solution for ${hole.id}: ${(e as Error).message}. Stack: ${(e as Error).stack}`);
        return UnifyResult.Failed;
    }
} 