/**
 * @file state.ts
 *
 * Manages the global state of the Emdash system.
 * This includes global definitions, rewrite/unification rules,
 * pending constraints, fresh name generation, and context operations.
 * It also holds flags and constants influencing system behavior.
 */

import {
    Term, Context, GlobalDef, StoredRewriteRule, UnificationRule, Constraint, Icit, Binding, Hole
} from './types';

// Global context for definitions and rules
export let globalDefs: Map<string, GlobalDef> = new Map();
export let userRewriteRules: StoredRewriteRule[] = [];
export let userUnificationRules: UnificationRule[] = [];
export let constraints: Constraint[] = [];
export const emptyCtx: Context = [];

// --- Fresh Name Generation ---
let nextVarIdCounter = 0;
export const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarIdCounter++}`;

let nextHoleIdCounter = 0;
export const freshHoleName = (): string => `?h${nextHoleIdCounter++}`;

export const resetVarId = () => { nextVarIdCounter = 0; };
export const resetHoleId = () => { nextHoleIdCounter = 0; };

/**
 * Creates a fresh hole term. Utility shorthand.
 */
export const FH = (): Term & { tag: 'Hole' } => Hole(freshHoleName());

// --- Constraint Management ---
export function addConstraint(t1: Term, t2: Term, origin?: string) {
    constraints.push({ t1, t2, origin });
}

/**
 * Control structure to prevent deep re-entrancy in solveConstraints.
 */
export const solveConstraintsControl = { depth: 0 };

// --- Term Utilities ---

/**
 * Dereferences a term, following Hole references until a non-Hole term
 * or an unassigned Hole is found. Detects cycles.
 * @param term The term to dereference.
 * @returns The resolved term.
 */
export function getTermRef(term: Term): Term {
    let current = term;
    const visited = new Set<Term>();
    while (current.tag === 'Hole' && current.ref) {
        if (visited.has(current)) {
            // This should ideally not happen with proper occurs checks and unification.
            console.warn(`Cycle detected in Hole references starting from ${term.tag === 'Hole' ? term.id : 'original term'}. Returning current hole: ${current.id}`);
            return current; // Return the hole that starts the cycle to prevent infinite loop.
        }
        visited.add(current);
        current = current.ref;
    }
    return current;
}

/**
 * A no-op clone function. In a system with mutable terms, this would perform a deep clone.
 * Currently, terms are treated as mostly immutable or structurally shared after creation,
 * with Hole references being the main mutable aspect.
 * @param term The term to "clone".
 * @returns The same term instance.
 */
export function cloneTerm(term: Term): Term {
    // If terms were mutable beyond Hole.ref, a deep clone would be needed here.
    // For now, structural sharing is used, and mutations are localized (e.g. Hole.ref).
    return term;
}

// --- Context Operations ---

/**
 * Extends a context with a new binding.
 * @param ctx The context to extend.
 * @param name The name of the variable.
 * @param type The type of the variable.
 * @param icit The implicitness of the variable.
 * @param definition Optional definition for the variable (for local lets).
 * @returns A new context with the binding prepended.
 */
export const extendCtx = (ctx: Context, name:string, type: Term, icit: Icit = Icit.Expl, definition?: Term): Context => {
    return [{ name, type, icit, definition }, ...ctx];
};

/**
 * Looks up a binding in the context by name.
 * @param ctx The context to search.
 * @param name The name of the variable to find.
 * @returns The binding if found, otherwise undefined.
 */
export const lookupCtx = (ctx: Context, name: string): Binding | undefined => ctx.find(b => b.name === name);


// --- Kernel Symbol Properties ---

/**
 * Tags of terms that are considered structural constants and should generally bypass rewrite rules.
 */
export const EMDASH_KERNEL_CONSTANT_TAGS = new Set<string>([
    'CatTerm', 'SetTerm', 'Type',
    'FunctorCategoryTerm', 'NatTransTypeTerm', 'HomCovFunctorIdentity', 'FunctorTypeTerm'
]);

/**
 * Tags of term constructors that are considered injective for unification.
 * If `Constructor(args1) = Constructor(args2)`, then `args1 = args2`.
 * Note: `Var` is injective by name. `App` injectivity depends on its head's properties.
 */
export const EMDASH_UNIFICATION_INJECTIVE_TAGS = new Set<string>([
    'CatTerm', 'ObjTerm', 'HomTerm',
    'FunctorCategoryTerm', 'NatTransTypeTerm', 'SetTerm',
    'FunctorTypeTerm', 'HomCovFunctorIdentity', // HomCovFunctorIdentity is injective in its arguments
    // FMap0Term, FMap1Term, NatTransComponentTerm are injective in their arguments IF their functor/transformation part is.
    // The general unification logic handles this more granularly.
    // For this list, we focus on inherently injective structural tags.
]);

/**
 * Checks if a term is structurally a kernel constant symbol that should bypass general rewrite rules.
 * This helps prevent unintended rewriting of fundamental structures.
 * @param term The term to check.
 * @returns True if the term is a kernel constant symbol structurally.
 */
export function isKernelConstantSymbolStructurally(term: Term): boolean {
    const rt = getTermRef(term);
    if (rt.tag === 'Var') {
        const gdef = globalDefs.get(rt.name);
        return !!(gdef && gdef.isConstantSymbol); // True if it's a Var defined as a constant
    }
    // Check against the set of tags that are considered kernel constants.
    // Terms like ObjTerm, HomTerm, FMap0Term, FMap1Term, NatTransComponentTerm are NOT listed
    // here because they *should* be subject to specific definitional rewrite rules (e.g., Obj_mkCat_eval).
    return EMDASH_KERNEL_CONSTANT_TAGS.has(rt.tag);
}

/**
 * Checks if a term tag corresponds to a constructor that is structurally injective for unification.
 * @param tag The tag string of the term constructor.
 * @returns True if the constructor is structurally injective.
 */
export function isEmdashUnificationInjectiveStructurally(tag: string): boolean {
    return EMDASH_UNIFICATION_INJECTIVE_TAGS.has(tag);
}

// --- Debugging ---
let _debug_verbose_flag = false;

export function setDebugVerbose(value: boolean): void {
    _debug_verbose_flag = value;
}

export function getDebugVerbose(): boolean {
    return _debug_verbose_flag;
}

/**
 * Maximum stack depth for core recursive operations like WHNF, unify, check, infer.
 * This helps prevent stack overflow errors for deeply nested computations.
 */
export const CORE_MAX_STACK_DEPTH = 20000; // Renamed from MAX_STACK_DEPTH to be specific