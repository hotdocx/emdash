/**
 * @file pattern.ts
 * @description Pattern matching, substitution, and related utilities for terms.
 */

import {
    Term, Context, PatternVarDecl, Substitution, Hole, Var, App, Lam, Pi, Type, CatTerm, SetTerm,
    ObjTerm, HomTerm, FunctorCategoryTerm, FunctorTypeTerm, FMap0Term, FMap1Term,
    NatTransTypeTerm, NatTransComponentTerm, HomCovFunctorIdentity, Icit, UnificationRule, MkFunctorTerm
} from './types';
import {
    getTermRef, freshVarName, freshHoleName, extendCtx, printTerm,
    addConstraint, userUnificationRules, consoleLog, lookupCtx
} from './state';
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
 * @param patternLocalBinders Names of variables bound by Lam/Pi in the pattern structure itself.
 * @param binderNameMapping A map to track binder name mappings.
 * @returns A substitution if matching succeeds, null otherwise.
 */
export function matchPattern(
    pattern: Term,
    termToMatch: Term,
    ctx: Context,
    patternVarDecls: PatternVarDecl[],
    currentSubst?: Substitution,
    stackDepth = 0,
    patternLocalBinders: Set<string> = new Set<string>(),
    binderNameMapping: Map<string, string> = new Map()
): Substitution | null {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`matchPattern stack depth exceeded for pattern ${printTerm(pattern)} vs term ${printTerm(termToMatch)}`);
    // if (stackDepth > 30) console.log("matchPattern: stackDepth", {stackDepth}, {pattern: printTerm(pattern), termToMatch: printTerm(termToMatch)});
    const rtPattern = getTermRef(pattern);
    const rtTermToMatch = getTermRef(termToMatch);

    const subst = currentSubst ? new Map(currentSubst) : new Map<string, Term>();

    // Pattern variable matching (Var)
    if (rtPattern.tag === 'Var' && isPatternVarName(rtPattern.name, patternVarDecls)) {
        const pvarName = rtPattern.name;
        if (pvarName === '_') return subst; // Wildcard matches anything without binding
        const existing = subst.get(pvarName);
        if (existing) { // If already bound, check for consistency
            return areEqual(rtTermToMatch, getTermRef(existing), ctx, stackDepth + 1) ? subst : null;
        }
        // NOTE: Scope check for Var pattern variables is typically not done with patternAllowedLocalBinders.
        // If needed, it would be similar to Hole, but Var doesn't carry patternAllowedLocalBinders.
        subst.set(pvarName, rtTermToMatch);
        return subst;
    }

    // Hole as pattern variable (e.g. $F)
    if (rtPattern.tag === 'Hole' && isPatternVarName(rtPattern.id, patternVarDecls)) {
        const pVarHole = rtPattern as Term & { tag: 'Hole' };
        const pvarId = pVarHole.id;
        if (pvarId === '_') return subst; // Wildcard hole

        const existing = subst.get(pvarId);
        if (existing) {
            return areEqual(rtTermToMatch, getTermRef(existing), ctx, stackDepth + 1) ? subst : null;
        }

        // Scope Check for Hole pattern variables
        if (pVarHole.patternAllowedLocalBinders !== undefined) {
            const actualMatchedTerm = rtTermToMatch;
            const freeVarsInActualMatchedTerm = getFreeVariables(actualMatchedTerm, new Set());

            let scopeCheckFailed = false;
            for (const patternBinderName of patternLocalBinders) {
                if (!pVarHole.patternAllowedLocalBinders.includes(patternBinderName)) {
                    // This patternBinderName is bound in the pattern context but NOT allowed for this $Hole.
                    // So, the actualMatchedTerm must NOT contain it as free.
                    const termBinderName = binderNameMapping.get(patternBinderName);
                    if (termBinderName && freeVarsInActualMatchedTerm.has(termBinderName)) {
                        consoleLog(`[matchPattern SCOPE FAIL] Pattern variable ${pvarId} matched term '${printTerm(actualMatchedTerm)}' which freely contains '${termBinderName}'. '${patternBinderName}' (as '${termBinderName}') is bound in pattern but not in ${pvarId}.patternAllowedLocalBinders = [${pVarHole.patternAllowedLocalBinders.join(', ')}]. Pattern local binders: [${Array.from(patternLocalBinders).join(', ')}]`);
                        scopeCheckFailed = true;
                        break;
                    }
                }
            }
            if (scopeCheckFailed) return null;
        }

        subst.set(pvarId, rtTermToMatch);
        return subst;
    }

    // If rtPattern is a specific Hole (not a pattern var), it must match an identical hole.
    if (rtPattern.tag === 'Hole') { // Not a pattern variable, because isPatternVarName was false
        if (rtTermToMatch.tag === 'Hole' && rtPattern.id === rtTermToMatch.id) return subst;
        return null; // Specific hole in pattern didn't match term
    }

    // If termToMatch is a hole but pattern is not a var/hole pattern, no match.
    // (Unless the hole in termToMatch is bound to something that matches the pattern)
    if (rtTermToMatch.tag === 'Hole') return null;
    if (rtPattern.tag !== rtTermToMatch.tag) {
        // If tags don't match, the only hope is a higher-order match for an App pattern
        if(rtPattern.tag === 'App') {
            const { head: patternHead } = getHeadAndSpine(rtPattern);
            if(patternHead.tag === 'Hole' && isPatternVarName(patternHead.id, patternVarDecls)) {
                // Fall through to App's HO logic
            } else {
                return null;
            }
        } else {
            return null;
        }
    }

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
            const { head: patternHead, spine: patternSpine } = getHeadAndSpine(rtPattern);

            const pvarName = (patternHead.tag === 'Hole' && isPatternVarName(patternHead.id, patternVarDecls)) ? patternHead.id : null;

            // If head is a pattern var, attempt higher-order matching.
            if (pvarName) {
                // Perform scope check on the term being matched BEFORE abstracting it.
                if (patternHead.tag === 'Hole' && patternHead.patternAllowedLocalBinders !== undefined) {
                    const freeVarsInTerm = getFreeVariables(rtTermToMatch, new Set(Array.from(binderNameMapping.values())));
                    
                    for (const patternBinderName of patternLocalBinders) {
                        if (!patternHead.patternAllowedLocalBinders.includes(patternBinderName)) {
                            const termBinderName = binderNameMapping.get(patternBinderName);
                            if (termBinderName && freeVarsInTerm.has(termBinderName)) {
                                consoleLog(`[matchPattern SCOPE FAIL] HO-match for ${pvarName}: term '${printTerm(rtTermToMatch)}' has free var '${termBinderName}' corresponding to disallowed pattern binder '${patternBinderName}'`);
                                return null;
                            }
                        }
                    }
                }

                // All args in patternSpine must be distinct variables bound in the pattern.
                const spineVarNames = new Set<string>();
                const spineVars: (Term & { tag: 'Var' })[] = [];
                for (const p of patternSpine) {
                    const rp = getTermRef(p);
                     if (rp.tag === 'Var') {
                        const mappedPatternBinderName = Array.from(binderNameMapping.entries()).find(([_, tName]) => tName === rp.name)?.[0];
                        if (mappedPatternBinderName && patternLocalBinders.has(mappedPatternBinderName) && !spineVarNames.has(rp.name)) {
                             spineVarNames.add(rp.name);
                             spineVars.push(rp as Term & {tag: 'Var'});
                             continue;
                        }
                    }
                    // This path is for when the pattern is like $F(G(x)) or $F(c), which is not simple Miller.
                    // We fall back to structural matching in this case.
                    return matchPatternStructural(rtPattern, rtTermToMatch, ctx, patternVarDecls, subst, stackDepth, patternLocalBinders, binderNameMapping);
                }

                const solution = abstractTermOverSpine(rtTermToMatch, spineVars, ctx);
                
                const existing = subst.get(pvarName);
                if (existing) {
                    return areEqual(solution, getTermRef(existing), ctx, stackDepth + 1) ? subst : null;
                }
                subst.set(pvarName, solution);
                return subst;
            }
            
            // Default to structural matching if head is not a pattern variable.
            return matchPatternStructural(rtPattern, rtTermToMatch, ctx, patternVarDecls, subst, stackDepth, patternLocalBinders, binderNameMapping);
        }
        case 'Lam': {
            const lamP = rtPattern; const lamT = rtTermToMatch as Term & {tag:'Lam'};
            if (lamP._isAnnotated !== lamT._isAnnotated) return null;
            // Icit already checked above for Lam/Pi/App

            let s: Substitution | null = subst;
            if (lamP._isAnnotated) {
                if (!lamP.paramType || !lamT.paramType) return null; 
                 const sType = matchPattern(lamP.paramType, lamT.paramType, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping);
                 if (!sType) return null;
                 s = sType;
            }
            
            const commonVarName = lamT.paramName; // Use term's param name
            const commonVar = Var(commonVarName, true);

            const patternBodyInst = lamP.body(commonVar);
            const termBodyInst = lamT.body(commonVar); 

            const newPatternLocalBinders = new Set(patternLocalBinders);
            newPatternLocalBinders.add(lamP.paramName);

            const newBinderNameMapping = new Map(binderNameMapping);
            newBinderNameMapping.set(lamP.paramName, lamT.paramName);

            const newCtx = lamT.paramType ? extendCtx(ctx, lamT.paramName, lamT.paramType, lamT.icit) : ctx;

            return matchPattern(patternBodyInst, termBodyInst, newCtx, patternVarDecls, s, stackDepth + 1, newPatternLocalBinders, newBinderNameMapping);
        }
        case 'Pi': {
            const piP = rtPattern; const piT = rtTermToMatch as Term & {tag:'Pi'};
            // Icit already checked above for Lam/Pi/App
            const sType = matchPattern(piP.paramType, piT.paramType, ctx, patternVarDecls, subst, stackDepth + 1, patternLocalBinders, binderNameMapping);
            if (!sType) return null;

            const commonVarName = piT.paramName; // Use term's param name
            const commonVar = Var(commonVarName, true);

            const patternBodyTypeInst = piP.bodyType(commonVar);
            const termBodyTypeInst = piT.bodyType(commonVar);

            const newPatternLocalBinders = new Set(patternLocalBinders);
            newPatternLocalBinders.add(piP.paramName);
            
            const newBinderNameMapping = new Map(binderNameMapping);
            newBinderNameMapping.set(piP.paramName, piT.paramName);

            const newCtx = extendCtx(ctx, piT.paramName, piT.paramType, piT.icit);

            return matchPattern(patternBodyTypeInst, termBodyTypeInst, newCtx, patternVarDecls, sType, stackDepth + 1, newPatternLocalBinders, newBinderNameMapping);
        }
        case 'ObjTerm':
            return matchPattern(rtPattern.cat, (rtTermToMatch as Term & {tag:'ObjTerm'}).cat, ctx, patternVarDecls, subst, stackDepth + 1, patternLocalBinders, binderNameMapping);
        case 'HomTerm': {
            const homP = rtPattern; const homT = rtTermToMatch as Term & {tag:'HomTerm'};
            let s: Substitution | null = subst;
            s = matchPattern(homP.cat, homT.cat, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            s = matchPattern(homP.dom, homT.dom, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            return matchPattern(homP.cod, homT.cod, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping);
        }
        case 'FunctorCategoryTerm':
        case 'FunctorTypeTerm': {
            const fcP = rtPattern as Term & {tag:'FunctorCategoryTerm'|'FunctorTypeTerm'};
            const fcT = rtTermToMatch as Term & {tag:'FunctorCategoryTerm'|'FunctorTypeTerm'};
            let s: Substitution | null = subst;
            s = matchPattern(fcP.domainCat, fcT.domainCat, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            return matchPattern(fcP.codomainCat, fcT.codomainCat, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping);
        }
        case 'FMap0Term': {
            const fm0P = rtPattern; const fm0T = rtTermToMatch as Term & {tag:'FMap0Term'};
            let s: Substitution | null = subst;
            if (fm0P.catA_IMPLICIT) { if (!fm0T.catA_IMPLICIT) return null; s = matchPattern(fm0P.catA_IMPLICIT, fm0T.catA_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null; }
            if (fm0P.catB_IMPLICIT) { if (!fm0T.catB_IMPLICIT) return null; s = matchPattern(fm0P.catB_IMPLICIT, fm0T.catB_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null; }
            s = matchPattern(fm0P.functor, fm0T.functor, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            return matchPattern(fm0P.objectX, fm0T.objectX, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping);
        }
        case 'FMap1Term': {
            const fm1P = rtPattern; const fm1T = rtTermToMatch as Term & {tag:'FMap1Term'};
            let s: Substitution | null = subst;
            const implicitsP = [fm1P.catA_IMPLICIT, fm1P.catB_IMPLICIT, fm1P.objX_A_IMPLICIT, fm1P.objY_A_IMPLICIT];
            const implicitsT = [fm1T.catA_IMPLICIT, fm1T.catB_IMPLICIT, fm1T.objX_A_IMPLICIT, fm1T.objY_A_IMPLICIT];
            for(let i=0; i<implicitsP.length; i++) {
                if (implicitsP[i]) { if (!implicitsT[i]) return null; s = matchPattern(implicitsP[i]!, implicitsT[i]!, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null; }
            }
            s = matchPattern(fm1P.functor, fm1T.functor, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            return matchPattern(fm1P.morphism_a, fm1T.morphism_a, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping);
        }
        case 'NatTransTypeTerm': {
            const ntP = rtPattern; const ntT = rtTermToMatch as Term & {tag:'NatTransTypeTerm'};
            let s: Substitution | null = subst;
            s = matchPattern(ntP.catA, ntT.catA, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            s = matchPattern(ntP.catB, ntT.catB, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            s = matchPattern(ntP.functorF, ntT.functorF, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            return matchPattern(ntP.functorG, ntT.functorG, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping);
        }
        case 'NatTransComponentTerm': {
            const ncP = rtPattern; const ncT = rtTermToMatch as Term & {tag:'NatTransComponentTerm'};
            let s: Substitution | null = subst;
            const implicitsP = [ncP.catA_IMPLICIT, ncP.catB_IMPLICIT, ncP.functorF_IMPLICIT, ncP.functorG_IMPLICIT];
            const implicitsT = [ncT.catA_IMPLICIT, ncT.catB_IMPLICIT, ncT.functorF_IMPLICIT, ncT.functorG_IMPLICIT];
            for(let i=0; i<implicitsP.length; i++) {
                if (implicitsP[i]) { if (!implicitsT[i]) return null; s = matchPattern(implicitsP[i]!, implicitsT[i]!, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null; }
            }
            s = matchPattern(ncP.transformation, ncT.transformation, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            return matchPattern(ncP.objectX, ncT.objectX, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping);
        }
        case 'HomCovFunctorIdentity': {
            const hcP = rtPattern as Term & {tag:'HomCovFunctorIdentity'};
            const hcT = rtTermToMatch as Term & {tag:'HomCovFunctorIdentity'};
            let s: Substitution | null = subst;
            s = matchPattern(hcP.domainCat, hcT.domainCat, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            return matchPattern(hcP.objW_InDomainCat, hcT.objW_InDomainCat, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping);
        }
        case 'MkFunctorTerm': {
            const mftP = rtPattern as Term & {tag:'MkFunctorTerm'};
            const mftT = rtTermToMatch as Term & {tag:'MkFunctorTerm'};
            let s: Substitution | null = subst;
            s = matchPattern(mftP.domainCat, mftT.domainCat, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            s = matchPattern(mftP.codomainCat, mftT.codomainCat, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            s = matchPattern(mftP.fmap0, mftT.fmap0, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            s = matchPattern(mftP.fmap1, mftT.fmap1, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping); if (!s) return null;
            
            if (mftP.proof) {
                if (!mftT.proof) return null; // Mismatch if one has a proof and the other doesn't
                s = matchPattern(mftP.proof, mftT.proof, ctx, patternVarDecls, s, stackDepth + 1, patternLocalBinders, binderNameMapping);
                if (!s) return null;
            } else if (mftT.proof) {
                return null; // Mismatch
            }
            return s;
        }
        default:
             const exhaustiveCheck: never = rtPattern;
             console.warn(`matchPattern: Unhandled pattern tag: ${(exhaustiveCheck as any).tag}.`);
             return null;
    }
}

/**
 * A helper for purely structural matching of App terms.
 */
function matchPatternStructural(
    rtPattern: Term & { tag: 'App' },
    rtTermToMatch: Term,
    ctx: Context,
    patternVarDecls: PatternVarDecl[],
    subst: Substitution,
    stackDepth: number,
    patternLocalBinders: Set<string>,
    binderNameMapping: Map<string, string>
): Substitution | null {
    if (rtTermToMatch.tag !== 'App' || rtPattern.icit !== rtTermToMatch.icit) return null;

    const s1 = matchPattern(rtPattern.func, rtTermToMatch.func, ctx, patternVarDecls, subst, stackDepth + 1, patternLocalBinders, binderNameMapping);
    if (!s1) return null;
    return matchPattern(rtPattern.arg, rtTermToMatch.arg, ctx, patternVarDecls, s1, stackDepth + 1, patternLocalBinders, binderNameMapping);
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

            // Instantiate the body with a placeholder
            const placeholderVar = Var(lam.paramName, true);
            const bodyInstance = lam.body(placeholderVar);

            // Apply the substitution to the body structure ONCE.
            const appliedBodyInstance = applySubst(bodyInstance, subst, patternVarDecls);

            // Create the new lambda with a simple substitution body to re-abstract the placeholder
            const newBodyFn = (v_arg: Term): Term => {
                return replaceFreeVar(appliedBodyInstance, placeholderVar.name, v_arg);
            };

            const newLam = Lam(lam.paramName, lam.icit, appliedParamType, newBodyFn);
            (newLam as Term & {tag: 'Lam'})._isAnnotated = lam._isAnnotated && appliedParamType !== undefined;
            return newLam;
        }
        case 'Pi': {
            const pi = current;
            const appliedParamType = applySubst(pi.paramType, subst, patternVarDecls);
            
            // Instantiate the body with a placeholder
            const placeholderVar = Var(pi.paramName, true);
            const bodyTypeInstance = pi.bodyType(placeholderVar);
            
            // Apply substitution to the body structure ONCE
            const appliedBodyTypeInstance = applySubst(bodyTypeInstance, subst, patternVarDecls);

            const newBodyTypeFn = (v_arg: Term) => {
                return replaceFreeVar(appliedBodyTypeInstance, placeholderVar.name, v_arg);
            };
            return Pi(pi.paramName, pi.icit, appliedParamType, newBodyTypeFn);
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
        case 'MkFunctorTerm':
            return MkFunctorTerm(
                applySubst(current.domainCat, subst, patternVarDecls),
                applySubst(current.codomainCat, subst, patternVarDecls),
                applySubst(current.fmap0, subst, patternVarDecls),
                applySubst(current.fmap1, subst, patternVarDecls),
                current.proof ? applySubst(current.proof, subst, patternVarDecls) : undefined
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
        case 'MkFunctorTerm':
            collectPatternVars(current.domainCat, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.codomainCat, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.fmap0, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.fmap1, patternVarDecls, collectedVars, visited);
            if (current.proof) collectPatternVars(current.proof, patternVarDecls, collectedVars, visited);
            break;
        // Terminals like Type, Var (non-pattern), Hole (non-pattern), CatTerm, SetTerm have no subterms or are handled.
    }
}

/**
 * Deconstructs a term into its head and spine of arguments.
 * Example: App(App(f, x), y) -> { head: f, spine: [x, y] }
 * Example: f (not an App) -> { head: f, spine: [] }
 * The spine is ordered from outermost argument to innermost (f x y -> spine [x,y])
 * @param term The term to deconstruct.
 * @returns An object containing the head of the application chain and the spine of arguments.
 */
export function getHeadAndSpine(term: Term): { head: Term, spine: Term[] } {
    let currentTerm = getTermRef(term);
    const spine: Term[] = [];
    while (currentTerm.tag === 'App') {
        spine.push(currentTerm.arg);
        currentTerm = getTermRef(currentTerm.func);
    }
    return { head: currentTerm, spine: spine.reverse() }; // Reverse to get application order (f x y -> [x,y])
}

/**
 * Replaces all free occurrences of a variable with a given name in a term with a replacement term (usually another Var).
 * This function is capture-avoiding with respect to new binders introduced within `replacementVar` if it were complex,
 * but typically `replacementVar` is a simple Var (a lambda parameter).
 * @param term The term to perform substitution in.
 * @param freeVarName The name of the free variable to replace.
 * @param replacementVar The variable term to substitute with.
 * @param boundInScope Set of names currently bound by lambdas/pis in the traversal path.
 * @returns The term with free occurrences of the variable replaced.
 */
export function replaceFreeVar(term: Term, freeVarName: string, replacementVar: Term, boundInScope: Set<string> = new Set()): Term {
    const current = getTermRef(term);

    switch (current.tag) {
        case 'Var':
            // Replace if name matches AND it's not shadowed by an inner binder within the current term being processed.
            return (current.name === freeVarName && !boundInScope.has(freeVarName) && current.isLambdaBound) ? replacementVar : current;
        case 'Lam': {
            const lam = current;
            const paramTypeReplaced = lam.paramType ? replaceFreeVar(lam.paramType, freeVarName, replacementVar, boundInScope) : undefined;

            // If this lambda binds the variable we want to replace, substitution stops here for the body.
            if (lam.paramName === freeVarName) {
                return Lam(lam.paramName, lam.icit, paramTypeReplaced, lam.body);
            }

            // Check for variable capture.
            const freeVarsInReplacement = getFreeVariables(replacementVar);
            if (freeVarsInReplacement.has(lam.paramName)) {
                // CAPTURE DETECTED: Rename the binder.
                const freshName = freshVarName(lam.paramName);
                const freshVar = Var(freshName, true);
                const bodyWithFreshVar = lam.body(freshVar); // Instantiate old body with NEW fresh var

                const newBoundInScope = new Set(boundInScope);
                newBoundInScope.add(freshName);
                
                // Recurse into the renamed body.
                const newBody = replaceFreeVar(bodyWithFreshVar, freeVarName, replacementVar, newBoundInScope);

                const newLam = Lam(freshName, lam.icit, paramTypeReplaced, (v_arg) => {
                    return replaceFreeVar(newBody, freshName, v_arg);
                });
                (newLam as Term & {tag: 'Lam'})._isAnnotated = lam._isAnnotated && paramTypeReplaced !== undefined;
                return newLam;
            } else {
                // NO CAPTURE: Proceed with substitution in the body.
                const newBoundInScope = new Set(boundInScope);
                newBoundInScope.add(lam.paramName);

                const placeholder = Var(lam.paramName, true);
                const bodyInstance = lam.body(placeholder);
                const replacedBodyInstance = replaceFreeVar(bodyInstance, freeVarName, replacementVar, newBoundInScope);

                const newBodyFn = (v_arg: Term): Term => {
                    return replaceFreeVar(replacedBodyInstance, placeholder.name, v_arg);
                };
                const resLam = Lam(lam.paramName, lam.icit, paramTypeReplaced, newBodyFn);
                (resLam as Term & { tag: 'Lam' })._isAnnotated = lam._isAnnotated && paramTypeReplaced !== undefined;
                return resLam;
            }
        }
        case 'Pi': {
            const pi = current;
            const newParamType = replaceFreeVar(pi.paramType, freeVarName, replacementVar, boundInScope);

            // If this Pi binds the variable we want to replace, substitution stops here for the body.
            if (pi.paramName === freeVarName) {
                return Pi(pi.paramName, pi.icit, newParamType, pi.bodyType);
            }

            // Check for variable capture.
            const freeVarsInReplacement = getFreeVariables(replacementVar);
            if (freeVarsInReplacement.has(pi.paramName)) {
                // CAPTURE DETECTED: Rename the binder.
                const freshName = freshVarName(pi.paramName);
                const freshVar = Var(freshName, true);
                const bodyTypeWithFreshVar = pi.bodyType(freshVar);

                const newBoundInScope = new Set(boundInScope);
                newBoundInScope.add(freshName);

                const newBodyType = replaceFreeVar(bodyTypeWithFreshVar, freeVarName, replacementVar, newBoundInScope);

                return Pi(freshName, pi.icit, newParamType, (v_arg: Term) => {
                    return replaceFreeVar(newBodyType, freshName, v_arg);
                });
            } else {
                // NO CAPTURE: Proceed with substitution in the body.
                const newBoundInScope = new Set(boundInScope);
                newBoundInScope.add(pi.paramName);

                const placeholder = Var(pi.paramName, true);
                const bodyTypeInstance = pi.bodyType(placeholder);
                const replacedBodyTypeInstance = replaceFreeVar(bodyTypeInstance, freeVarName, replacementVar, newBoundInScope);
                
                const newBodyTypeFn = (v_arg: Term) => {
                    return replaceFreeVar(replacedBodyTypeInstance, placeholder.name, v_arg);
                };

                return Pi(pi.paramName, pi.icit, newParamType, newBodyTypeFn);
            }
        }
        case 'App':
            return App(
                replaceFreeVar(current.func, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.arg, freeVarName, replacementVar, boundInScope),
                current.icit
            );
        // Base cases that don't bind variables or have no subterms with variables relevant here
        case 'Type': case 'Hole': case 'CatTerm': case 'SetTerm': return current;
        // Cases that have subterms but don't bind variables themselves
        case 'ObjTerm': return ObjTerm(replaceFreeVar(current.cat, freeVarName, replacementVar, boundInScope));
        case 'HomTerm':
            return HomTerm(
                replaceFreeVar(current.cat, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.dom, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.cod, freeVarName, replacementVar, boundInScope)
            );
        case 'FunctorCategoryTerm': case 'FunctorTypeTerm':
            return current.tag === 'FunctorCategoryTerm' ? FunctorCategoryTerm(
                replaceFreeVar(current.domainCat, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.codomainCat, freeVarName, replacementVar, boundInScope)
            ) : FunctorTypeTerm(
                replaceFreeVar(current.domainCat, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.codomainCat, freeVarName, replacementVar, boundInScope)
            );
        case 'FMap0Term':
            return FMap0Term(
                replaceFreeVar(current.functor, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.objectX, freeVarName, replacementVar, boundInScope),
                current.catA_IMPLICIT ? replaceFreeVar(current.catA_IMPLICIT, freeVarName, replacementVar, boundInScope) : undefined,
                current.catB_IMPLICIT ? replaceFreeVar(current.catB_IMPLICIT, freeVarName, replacementVar, boundInScope) : undefined
            );
        case 'FMap1Term':
            return FMap1Term(
                replaceFreeVar(current.functor, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.morphism_a, freeVarName, replacementVar, boundInScope),
                current.catA_IMPLICIT ? replaceFreeVar(current.catA_IMPLICIT, freeVarName, replacementVar, boundInScope) : undefined,
                current.catB_IMPLICIT ? replaceFreeVar(current.catB_IMPLICIT, freeVarName, replacementVar, boundInScope) : undefined,
                current.objX_A_IMPLICIT ? replaceFreeVar(current.objX_A_IMPLICIT, freeVarName, replacementVar, boundInScope) : undefined,
                current.objY_A_IMPLICIT ? replaceFreeVar(current.objY_A_IMPLICIT, freeVarName, replacementVar, boundInScope) : undefined
            );
        case 'NatTransTypeTerm':
            return NatTransTypeTerm(
                replaceFreeVar(current.catA, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.catB, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.functorF, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.functorG, freeVarName, replacementVar, boundInScope)
            );
        case 'NatTransComponentTerm':
            return NatTransComponentTerm(
                replaceFreeVar(current.transformation, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.objectX, freeVarName, replacementVar, boundInScope),
                current.catA_IMPLICIT ? replaceFreeVar(current.catA_IMPLICIT, freeVarName, replacementVar, boundInScope) : undefined,
                current.catB_IMPLICIT ? replaceFreeVar(current.catB_IMPLICIT, freeVarName, replacementVar, boundInScope) : undefined,
                current.functorF_IMPLICIT ? replaceFreeVar(current.functorF_IMPLICIT, freeVarName, replacementVar, boundInScope) : undefined,
                current.functorG_IMPLICIT ? replaceFreeVar(current.functorG_IMPLICIT, freeVarName, replacementVar, boundInScope) : undefined
            );
        case 'HomCovFunctorIdentity':
            return HomCovFunctorIdentity(
                replaceFreeVar(current.domainCat, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.objW_InDomainCat, freeVarName, replacementVar, boundInScope)
            );
        case 'MkFunctorTerm':
            return MkFunctorTerm(
                replaceFreeVar(current.domainCat, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.codomainCat, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.fmap0, freeVarName, replacementVar, boundInScope),
                replaceFreeVar(current.fmap1, freeVarName, replacementVar, boundInScope),
                current.proof ? replaceFreeVar(current.proof, freeVarName, replacementVar, boundInScope) : undefined
            );
        default:
            const exhaustiveCheck: never = current;
            throw new Error(`replaceFreeVar: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
}

/**
 * Abstracts a term over a list of spine variables, creating nested Lambdas.
 * e.g., abstractTermOverSpine(Body, [v1, v2], ctx) -> Lam(v1.name, v1.type, LV1 => Lam(v2.name, v2.type, LV2 => Body') ) 
 * where Body' is Body with original v1 replaced by LV1 and v2 by LV2.
 * @param termToAbstract The term that will become the body of the innermost lambda.
 * @param spineVars An array of Var terms that were in the application spine. Order: outermost argument first.
 * @param ctx The context to look up types for spine variables.
 * @returns A new Term consisting of nested Lambdas.
 */
export function abstractTermOverSpine(termToAbstract: Term, spineVars: (Term & {tag:'Var'})[], ctx: Context): Term {
    let resultingLambda = termToAbstract;

    // Iterate from the last spine variable (innermost parameter in the spine) to the first,
    // so the last spine variable becomes the parameter of the innermost lambda created,
    // and the first spine variable (outermost argument in application) becomes the parameter of the outermost lambda.
    for (let i = spineVars.length - 1; i >= 0; i--) { // Iterate backwards
        const spineVar = spineVars[i];
        const spineVarName = spineVar.name;
        const binding = lookupCtx(ctx, spineVarName);
        // Ensure the variable from the spine is indeed the one bound in the current context as expected.
        // This check might need refinement if spineVar objects don't have perfect identity with context-bound vars.
        if (!binding || !binding.type || !spineVar.isLambdaBound /* Spine vars must be bound vars */) {
            throw new Error(`Spine variable ${spineVarName} is not a recognized bound variable in context or has no type.`);
        }
        const spineVarType = binding.type; // Use type from context for the lambda parameter
        const icitForLambda = binding.icit || Icit.Expl; // Default to Explicit if not specified in context binding

        const bodyToWrapInLambda = resultingLambda; // This is the term that will become the body of Lam(spineVarName, ...)
                                             // It might contain spineVarName as a free variable (and also other spineVars[j] for j > i).
        resultingLambda = Lam(spineVarName, icitForLambda, spineVarType, (lambdaParamVar) => {
            // lambdaParamVar is Var(spineVarName, isLambdaBound=true)
            // We need to transform `bodyToWrapInLambda` such that its free occurrences of `spineVarName`
            // (which correspond to the original spineVar that was free in bodyToWrapInLambda w.r.t this new Lam)
            // are now correctly bound by `lambdaParamVar`.
            return replaceFreeVar(bodyToWrapInLambda, spineVarName, lambdaParamVar);
        });
    }
    return resultingLambda;
}

/**
 * Computes the set of free variable names in a term.
 * @param term The term to analyze.
 * @param initialBoundScope A set of variable names considered bound from the outset.
 * @returns A Set of strings, where each string is the name of a free variable.
 */
export function getFreeVariables(term: Term, initialBoundScope: Set<string> = new Set()): Set<string> {
    const freeVars = new Set<string>();
    const visited = new Set<Term>(); // For handling shared subterms and cycles

    function find(currentTerm: Term, currentLocallyBound: Set<string>) {
        const termRef = getTermRef(currentTerm); 
        if (visited.has(termRef) && termRef.tag !== 'Var') return; 
        visited.add(termRef);

        switch (termRef.tag) {
            case 'Var':
                if (!currentLocallyBound.has(termRef.name)) {
                    freeVars.add(termRef.name);
                }
                break;
            case 'Lam':
                if (termRef.paramType) find(termRef.paramType, currentLocallyBound);
                const newScopeLam = new Set(currentLocallyBound);
                newScopeLam.add(termRef.paramName); 
                find(termRef.body(Var(termRef.paramName, true)), newScopeLam); 
                break;
            case 'Pi':
                find(termRef.paramType, currentLocallyBound);
                const newScopePi = new Set(currentLocallyBound);
                newScopePi.add(termRef.paramName); 
                find(termRef.bodyType(Var(termRef.paramName, true)), newScopePi);
                break;
            case 'App':
                find(termRef.func, currentLocallyBound);
                find(termRef.arg, currentLocallyBound);
                break;
            case 'Hole':
                if (termRef.elaboratedType) find(termRef.elaboratedType, currentLocallyBound);
                // Do not descend into termRef.ref for free variable analysis of the hole itself.
                break;
            case 'Type': case 'CatTerm': case 'SetTerm': break; 
            case 'ObjTerm': find(termRef.cat, currentLocallyBound); break;
            case 'HomTerm':
                find(termRef.cat, currentLocallyBound);
                find(termRef.dom, currentLocallyBound);
                find(termRef.cod, currentLocallyBound);
                break;
            case 'FunctorCategoryTerm': case 'FunctorTypeTerm':
                find(termRef.domainCat, currentLocallyBound);
                find(termRef.codomainCat, currentLocallyBound);
                break;
            case 'FMap0Term':
                find(termRef.functor, currentLocallyBound);
                find(termRef.objectX, currentLocallyBound);
                if (termRef.catA_IMPLICIT) find(termRef.catA_IMPLICIT, currentLocallyBound);
                if (termRef.catB_IMPLICIT) find(termRef.catB_IMPLICIT, currentLocallyBound);
                break;
            case 'FMap1Term':
                find(termRef.functor, currentLocallyBound);
                find(termRef.morphism_a, currentLocallyBound);
                if (termRef.catA_IMPLICIT) find(termRef.catA_IMPLICIT, currentLocallyBound);
                if (termRef.catB_IMPLICIT) find(termRef.catB_IMPLICIT, currentLocallyBound);
                if (termRef.objX_A_IMPLICIT) find(termRef.objX_A_IMPLICIT, currentLocallyBound);
                if (termRef.objY_A_IMPLICIT) find(termRef.objY_A_IMPLICIT, currentLocallyBound);
                break;
            case 'NatTransTypeTerm':
                find(termRef.catA, currentLocallyBound);
                find(termRef.catB, currentLocallyBound);
                find(termRef.functorF, currentLocallyBound);
                find(termRef.functorG, currentLocallyBound);
                break;
            case 'NatTransComponentTerm':
                find(termRef.transformation, currentLocallyBound);
                find(termRef.objectX, currentLocallyBound);
                if (termRef.catA_IMPLICIT) find(termRef.catA_IMPLICIT, currentLocallyBound);
                if (termRef.catB_IMPLICIT) find(termRef.catB_IMPLICIT, currentLocallyBound);
                if (termRef.functorF_IMPLICIT) find(termRef.functorF_IMPLICIT, currentLocallyBound);
                if (termRef.functorG_IMPLICIT) find(termRef.functorG_IMPLICIT, currentLocallyBound);
                break;
            case 'HomCovFunctorIdentity':
                find(termRef.domainCat, currentLocallyBound);
                find(termRef.objW_InDomainCat, currentLocallyBound);
                break;
            case 'MkFunctorTerm':
                find(termRef.domainCat, currentLocallyBound);
                find(termRef.codomainCat, currentLocallyBound);
                find(termRef.fmap0, currentLocallyBound);
                find(termRef.fmap1, currentLocallyBound);
                if (termRef.proof) find(termRef.proof, currentLocallyBound);
                break;
            default:
                const _exhaustiveCheck: never = termRef;
                throw new Error(`getFreeVariables: Unhandled term tag: ${(_exhaustiveCheck as any).tag}`);
        }
    }

    find(term, new Set(initialBoundScope));
    return freeVars;
} 