/**
 * @file pattern.ts
 * @description Pattern matching, substitution, and related utilities for terms.
 */

import {
    Term, Context, PatternVarDecl, Substitution, Hole, Var, App, Lam, Pi, Type, CatTerm, SetTerm,
    ObjTerm, HomTerm, FunctorCategoryTerm, FunctorTypeTerm, FMap0Term, FMap1Term,
    NatTransTypeTerm, NatTransComponentTerm, HomCovFunctorIdentity, Icit, UnificationRule
} from '../types';
import {
    getTermRef, freshVarName, freshHoleName, extendCtx, printTerm,
    addConstraint, userUnificationRules, consoleLog
} from '../state';
import { areEqual } from './equality';
import { MAX_STACK_DEPTH } from './constants';

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
            const newBodyFn = (v_arg: Term): Term => {
                const bodyCtxSubst = new Map(subst);  // is such cloning of substnecessary?
                return applySubst(lam.body(v_arg), bodyCtxSubst, patternVarDecls);
            };

            const newLam = Lam(lam.paramName, lam.icit, appliedParamType, newBodyFn);
            (newLam as Term & {tag: 'Lam'})._isAnnotated = lam._isAnnotated && appliedParamType !== undefined;
            return newLam;
        }
        case 'Pi': {
            const pi = current;
            const newBodyTypeFn = (v_arg: Term) => {
                const bodyCtxSubst = new Map(subst);  // is such cloning of subst necessary?
                return applySubst(pi.bodyType(v_arg), bodyCtxSubst, patternVarDecls);
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
            return FunctorCategoryTerm(
                applySubst(current.domainCat, subst, patternVarDecls),
                applySubst(current.codomainCat, subst, patternVarDecls)
            );
        case 'FunctorTypeTerm':
            return FunctorTypeTerm(
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