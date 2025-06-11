/**
 * @file proof.ts
 * @description Provides the API for interactive theorem proving.
 * This module contains functions to inspect the state of a proof-in-progress (which is just a term with holes)
 * and to make progress by refining those holes.
 */

import {
    Term, Context, Hole, Icit, Var, Lam, Pi, Let, Type, App,
} from './types';
import {
    getTermRef, emptyCtx, extendCtx, printTerm, globalDefs,
} from './state';
import { elaborate } from './elaboration';
import { whnf } from './reduction';
import { areEqual } from './equality';

/**
 * Traverses a term and returns a flat list of all *unsolved* holes (where ref is null/undefined).
 * @param term The term to search for holes.
 * @param visited A set to keep track of visited terms to avoid infinite loops with cycles.
 * @returns An array of unsolved Hole terms.
 */
export function findHoles(term: Term, visited: Set<Term> = new Set()): (Term & { tag: 'Hole' })[] {
    const holes: (Term & { tag: 'Hole' })[] = [];
    
    function traverse(t: Term) {
        // Use getTermRef to see "through" solved holes
        const current = getTermRef(t);

        if (visited.has(current)) return;
        visited.add(current);

        if (current.tag === 'Hole') {
            // It's an unsolved hole because getTermRef would have returned its `ref` if it were solved.
            holes.push(current);
            // Also check its elaborated type for more holes
            if (current.elaboratedType) {
                traverse(current.elaboratedType);
            }
            return;
        }

        // NEW: Handle Vars that are global definitions
        if (current.tag === 'Var') {
            const gdef = globalDefs.get(current.name);
            if (gdef && gdef.value) {
                traverse(gdef.value);
            }
            return; // Nothing more to do for a Var
        }

        // Recursive traversal for other term types
        switch (current.tag) {
            case 'App':
                traverse(current.func);
                traverse(current.arg);
                break;
            case 'Lam':
                if (current.paramType) traverse(current.paramType);
                // Instantiate body with a dummy var to find holes inside
                traverse(current.body(Var('_find_holes_dummy')));
                break;
            case 'Pi':
                traverse(current.paramType);
                // Instantiate body with a dummy var to find holes inside
                traverse(current.bodyType(Var('_find_holes_dummy')));
                break;
            case 'Let':
                if (current.letType) traverse(current.letType);
                traverse(current.letDef);
                traverse(current.body(Var('_find_holes_dummy')));
                break;
            case 'ObjTerm': traverse(current.cat); break;
            case 'HomTerm':
                traverse(current.cat);
                traverse(current.dom);
                traverse(current.cod);
                break;
            case 'FunctorCategoryTerm': case 'FunctorTypeTerm':
                traverse(current.domainCat);
                traverse(current.codomainCat);
                break;
            case 'FMap0Term':
                traverse(current.functor);
                traverse(current.objectX);
                if (current.catA_IMPLICIT) traverse(current.catA_IMPLICIT);
                if (current.catB_IMPLICIT) traverse(current.catB_IMPLICIT);
                break;
            case 'FMap1Term':
                traverse(current.functor);
                traverse(current.morphism_a);
                if (current.catA_IMPLICIT) traverse(current.catA_IMPLICIT);
                if (current.catB_IMPLICIT) traverse(current.catB_IMPLICIT);
                if (current.objX_A_IMPLICIT) traverse(current.objX_A_IMPLICIT);
                if (current.objY_A_IMPLICIT) traverse(current.objY_A_IMPLICIT);
                break;
            case 'NatTransTypeTerm':
                traverse(current.catA);
                traverse(current.catB);
                traverse(current.functorF);
                traverse(current.functorG);
                break;
            case 'NatTransComponentTerm':
                traverse(current.transformation);
                traverse(current.objectX);
                if (current.catA_IMPLICIT) traverse(current.catA_IMPLICIT);
                if (current.catB_IMPLICIT) traverse(current.catB_IMPLICIT);
                if (current.functorF_IMPLICIT) traverse(current.functorF_IMPLICIT);
                if (current.functorG_IMPLICIT) traverse(current.functorG_IMPLICIT);
                break;
            case 'HomCovFunctorIdentity':
                traverse(current.domainCat);
                traverse(current.objW_InDomainCat);
                break;
            case 'MkFunctorTerm':
                traverse(current.domainCat);
                traverse(current.codomainCat);
                traverse(current.fmap0);
                traverse(current.fmap1);
                break;
            case 'Type': case 'SetTerm': case 'CatTerm':
                return;
            default:
                const _: never = current;
                return;
        }
    }

    traverse(term);
    return holes;
}


interface GoalInfo {
    context: Context;
    type: Term;
    hole: Term & { tag: 'Hole' };
}

/**
 * Finds a specific hole by its ID and computes its local context and type.
 * @param rootTerm The top-level term of the proof.
 * @param holeId The ID of the hole to find.
 * @returns The GoalInfo object if the hole is found, otherwise null.
 */
export function getHoleGoal(rootTerm: Term, holeId: string): GoalInfo | null {
    const visited = new Set<Term>();
    function find(currentTerm: Term, ctx: Context): GoalInfo | null {
        const term = getTermRef(currentTerm);

        if (visited.has(term)) return null;
        visited.add(term);

        if (term.tag === 'Hole') {
            if (term.id === holeId) {
                if (!term.elaboratedType) {
                    throw new Error(`Hole ${holeId} has no elaborated type. Ensure the proof term is elaborated first.`);
                }
                return { context: ctx, type: term.elaboratedType, hole: term };
            }
            return null; // Not the target hole, so stop searching this branch
        }

        // NEW: Handle Vars that are global definitions
        if (term.tag === 'Var') {
            const gdef = globalDefs.get(term.name);
            if (gdef && gdef.value) {
                const foundInGdef = find(gdef.value, ctx); // Context doesn't change
                if (foundInGdef) return foundInGdef;
            }
            return null; // Var doesn't lead to the target hole
        }

        // Recursively search in sub-terms, extending the context where appropriate
        switch (term.tag) {
            case 'App':
                return find(term.func, ctx) || find(term.arg, ctx);
            case 'Lam': {
                if (term.paramType) {
                    const foundInType = find(term.paramType, ctx);
                    if (foundInType) return foundInType;
                }
                const extendedCtx = extendCtx(ctx, term.paramName, term.paramType || Hole('_lam_param_type'), term.icit);
                return find(term.body(Var(term.paramName, true)), extendedCtx);
            }
            case 'Pi': {
                const foundInType = find(term.paramType, ctx);
                if (foundInType) return foundInType;
                const extendedCtx = extendCtx(ctx, term.paramName, term.paramType, term.icit);
                return find(term.bodyType(Var(term.paramName, true)), extendedCtx);
            }
            case 'Let': {
                if (term.letType) {
                    const foundInType = find(term.letType, ctx);
                    if (foundInType) return foundInType;
                }
                const foundInDef = find(term.letDef, ctx);
                if (foundInDef) return foundInDef;
                
                // For the body, we must extend the context with the let-binding.
                // The context should know both the type and the definition for reduction purposes.
                const letType = term.letType || Hole('_let_type_goal_finder');
                const extendedCtx = extendCtx(ctx, term.letName, letType, Icit.Expl, term.letDef);
                return find(term.body(Var(term.letName, true)), extendedCtx);
            }
            // Add other term types as needed for traversal...
            case 'ObjTerm': return find(term.cat, ctx);
            case 'HomTerm':
                return find(term.cat, ctx) || find(term.dom, ctx) || find(term.cod, ctx);
            case 'FunctorCategoryTerm': case 'FunctorTypeTerm':
                return find(term.domainCat, ctx) || find(term.codomainCat, ctx);
            case 'FMap0Term':
                return find(term.functor, ctx) || find(term.objectX, ctx) ||
                       (term.catA_IMPLICIT ? find(term.catA_IMPLICIT, ctx) : null) ||
                       (term.catB_IMPLICIT ? find(term.catB_IMPLICIT, ctx) : null);
            case 'FMap1Term':
                 return find(term.functor, ctx) || find(term.morphism_a, ctx) ||
                        (term.catA_IMPLICIT ? find(term.catA_IMPLICIT, ctx) : null) ||
                        (term.catB_IMPLICIT ? find(term.catB_IMPLICIT, ctx) : null) ||
                        (term.objX_A_IMPLICIT ? find(term.objX_A_IMPLICIT, ctx) : null) ||
                        (term.objY_A_IMPLICIT ? find(term.objY_A_IMPLICIT, ctx) : null);
            case 'NatTransTypeTerm':
                return find(term.catA, ctx) || find(term.catB, ctx) || find(term.functorF, ctx) || find(term.functorG, ctx);
            case 'NatTransComponentTerm':
                return find(term.transformation, ctx) || find(term.objectX, ctx) ||
                       (term.catA_IMPLICIT ? find(term.catA_IMPLICIT, ctx) : null) ||
                       (term.catB_IMPLICIT ? find(term.catB_IMPLICIT, ctx) : null) ||
                       (term.functorF_IMPLICIT ? find(term.functorF_IMPLICIT, ctx) : null) ||
                       (term.functorG_IMPLICIT ? find(term.functorG_IMPLICIT, ctx) : null);
            case 'HomCovFunctorIdentity':
                return find(term.domainCat, ctx) || find(term.objW_InDomainCat, ctx);
            case 'MkFunctorTerm':
                return find(term.domainCat, ctx) || find(term.codomainCat, ctx) || find(term.fmap0, ctx) || find(term.fmap1, ctx);
            case 'Type': case 'SetTerm': case 'CatTerm':
                return null;
            default:
                // This `_` will now correctly be of type `never` if all cases are handled above
                const _: never = term;
                return null;
        }
    }
    // Start the search with the root term in an empty context.
    // In a real scenario, the root might be a global with its own context.
    return find(rootTerm, emptyCtx);
}


/**
 * Generates a human-readable string report of the current proof state.
 * @param proofTerm The term representing the current proof.
 * @returns A string describing all unsolved goals.
 */
export function reportProofState(proofTerm: Term): string {
  const unsolvedHoles = findHoles(proofTerm);
  if (unsolvedHoles.length === 0) {
    return "Proof complete. No goals remain.";
  }

  let reportStr = `Proof has ${unsolvedHoles.length} unsolved goal(s):\n`;
  
  for (const hole of unsolvedHoles) {
    reportStr += `\n- Goal ${hole.id}:\n`;
    const goalInfo = getHoleGoal(proofTerm, hole.id);
    if (goalInfo) {
        goalInfo.context.forEach(v => {
            const defStr = v.definition ? ` = ${printTerm(v.definition)}` : '';
            reportStr += `  ${v.name} : ${printTerm(v.type)}${defStr}\n`;
        });
        reportStr += `  ⊢ ${printTerm(goalInfo.type)}\n`;
    } else {
        reportStr += `  (Could not retrieve context for ${hole.id})\n`;
    }
  }
  return reportStr;
}

/**
 * The core primitive for making progress on a proof. It refines a hole with a given term.
 * @param proofTerm The entire term representing the proof-in-progress.
 * @param holeId The ID of the hole to refine.
 * @param refinementTerm The term to use for refining the hole.
 * @returns The same proofTerm, which is mutated internally by solving the hole.
 */
export function refine(proofTerm: Term, holeId: string, refinementTerm: Term): Term {
    const goalInfo = getHoleGoal(proofTerm, holeId);
    if (!goalInfo) {
        throw new Error(`Hole with ID ${holeId} not found in the proof term.`);
    }

    if (goalInfo.hole.ref) {
        throw new Error(`Hole ${holeId} is already solved.`);
    }

    // Elaborate the refinement term in the context of the hole.
    // The elaborate function will check if the refinement term has the correct type
    // and will create new holes for any subgoals.
    const elaboratedRefinement = elaborate(
        refinementTerm,
        goalInfo.type,
        goalInfo.context,
        { normalizeResultTerm: false } // We don't want to normalize away the structure we just built
    );

    // Mutate the hole's `ref` to solve it. This is a key design choice for simplicity,
    // making the Hole act like a mutable cell in an otherwise immutable-seeming structure.
    goalInfo.hole.ref = elaboratedRefinement.term;

    return proofTerm;
}

// --- Convenience "Tactics" ---

/**
 * Introduces a lambda, turning a goal `Π x:A. B` into a subgoal `B` with `x:A` in the context.
 * @param proofTerm The proof term.
 * @param holeId The ID of the hole to apply the introduction to.
 * @param varName Optional name for the introduced variable.
 * @returns The mutated proof term.
 */
export function intro(proofTerm: Term, holeId: string, varName?: string): Term {
    const goalInfo = getHoleGoal(proofTerm, holeId);
    if (!goalInfo) throw new Error(`Hole ${holeId} not found.`);

    const goalType = whnf(goalInfo.type, goalInfo.context);
    if (goalType.tag !== 'Pi') {
        throw new Error(`'intro' tactic requires a function type (Π-type) goal, but got ${printTerm(goalType)}.`);
    }

    const introVarName = varName || goalType.paramName;
    // The refinement term is a lambda with a new hole in its body.
    // `elaborate` will create and type this new hole for us.
    const bodyHole = Hole(`?h_intro_body_${introVarName}`);
    const refinement = Lam(
        introVarName,
        goalType.icit,
        goalType.paramType,
        _ => bodyHole
    );

    return refine(proofTerm, holeId, refinement);
}

/**
 * Solves a goal exactly with a given term.
 * @param proofTerm The proof term.
 * @param holeId The ID of the hole to solve.
 * @param solutionTerm The term that is claimed to solve the goal.
 * @returns The mutated proof term.
 */
export function exact(proofTerm: Term, holeId: string, solutionTerm: Term): Term {
    // `exact` is just a direct call to `refine`.
    // The `elaborate` call inside `refine` will ensure the solutionTerm is complete and has the right type.
    return refine(proofTerm, holeId, solutionTerm);
}

/**
 * Applies a function to a goal, creating new subgoals for the function's arguments.
 * @param proofTerm The proof term.
 * @param holeId The ID of the hole to apply the function to.
 * @param funcTerm The function term to apply.
 * @returns The mutated proof term.
 */
export function apply(proofTerm: Term, holeId: string, funcTerm: Term): Term {
    const goalInfo = getHoleGoal(proofTerm, holeId);
    if (!goalInfo) throw new Error(`Hole ${holeId} not found.`);

    // We need to figure out how many arguments to apply.
    // We can infer the type of `funcTerm` and see how many Pi-binders it has.
    // For simplicity here, we'll let `elaborate` handle this by trying to unify
    // `funcTerm`'s type with a series of Pi-types until it matches the goal type.
    
    // A simple `apply` can just be `refine` with the function.
    // Elaboration will insert implicit arguments as holes.
    // For explicit arguments, we need a more complex tactic that creates `App(funcTerm, ?h1, ?h2...)`.
    
    // This is a simplified version where we assume `elaborate` + `unify` are powerful enough.
    // We create a term that is just the function, and let the type checker's implicit
    // argument insertion mechanism generate the holes for us.
    // If the goal is `T`, and we apply `f : A -> B -> T`, refine will check `f` against
    // `T`. Unification will see `A -> B -> T` and `T`, and will try to match.
    // A better way is to construct the application with holes. Let's do that.

    const { type: funcType } = elaborate(funcTerm, undefined, goalInfo.context, { normalizeResultTerm: false });

    let currentFuncType = whnf(funcType, goalInfo.context);
    let refinement = funcTerm;
    let argCounter = 0;

    // Keep applying new holes as arguments as long as the type is a Pi-type
    while (currentFuncType.tag === 'Pi') {
        const newHole = Hole(`?h_apply_${argCounter++}`);
        refinement = App(refinement, newHole, currentFuncType.icit);
        currentFuncType = whnf(currentFuncType.bodyType(newHole), goalInfo.context);
    }

    return refine(proofTerm, holeId, refinement);
}