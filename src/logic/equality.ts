/**
 * @file equality.ts
 * @description Term equality (convertibility) checking.
 */

import {
    Term, Context, Hole, Var, App, Lam, Pi, Type, CatTerm, ObjTerm, HomTerm,
    FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm,
    NatTransComponentTerm, HomCovFunctorIdentity, SetTerm, FunctorTypeTerm, Icit
} from '../types';
import { getTermRef, freshHoleName, extendCtx } from '../state';
import { MAX_STACK_DEPTH } from './constants';
import { whnf } from './reduction';

/**
 * Checks if all corresponding arguments in two lists are equal by convertibility (areEqual).
 * Handles undefined arguments by treating them as distinct unless both are undefined.
 * @param args1 First list of terms (or undefined).
 * @param args2 Second list of terms (or undefined).
 * @param ctx The current context.
 * @param depth Recursion depth.
 * @returns True if all defined argument pairs are convertible and undefined positions match, false otherwise.
 */
export function areAllArgsConvertible(args1: (Term | undefined)[], args2: (Term | undefined)[], ctx: Context, depth: number): boolean {
    if (args1.length !== args2.length) return false;
    for (let i = 0; i < args1.length; i++) {
        const t1_arg = args1[i];
        const t2_arg = args2[i];

        if (t1_arg === undefined && t2_arg === undefined) {
            continue; // Both undefined, this pair is considered matching.
        }
        if (t1_arg === undefined || t2_arg === undefined) {
            return false; // One is undefined and the other is not, so they are not equal.
        }
        // Both args are defined Terms, check them with areEqual.
        if (!areEqual(t1_arg, t2_arg, ctx, depth + 1)) {
            return false;
        }
    }
    return true;
}

/**
 * Checks if two terms are equal (convertible) under the type theory.
 * This involves reducing both terms to WHNF and then recursively test convertibility of the subterms.
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
        case 'FunctorTypeTerm': {
            const ftt2 = rt2 as Term & {tag:'FunctorTypeTerm'};
            return areEqual(rt1.domainCat, ftt2.domainCat, ctx, depth + 1) &&
                   areEqual(rt1.codomainCat, ftt2.codomainCat, ctx, depth + 1);
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