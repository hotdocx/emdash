/**
 * @file state.ts
 * @description Manages the global state of the emdash system, including
 * global definitions, rewrite/unification rules, constraints,
 * fresh name generation, context manipulation utilities, and term printing.
 */

import {
    Term, Context, GlobalDef, StoredRewriteRule, UnificationRule, Constraint, Icit,
    Hole, Binding, BaseTerm, Var
} from './types'; // Assuming all type constructors (Type, Var, etc.) are exported from types.ts

// Global Flags
const flags = {
    etaEquality: false,
    printImplicits: false,
    printContexts: false,
    printDomains: false,
    printMetaTypes: false,
    printMetaArgs: false,
};

export type FlagName = keyof typeof flags;

export function setFlag(name: FlagName, value: boolean) {
    if (name in flags) {
        flags[name] = value;
    } else {
        console.warn(`Attempted to set unknown flag: ${name}`);
    }
}

export function getFlag(name: FlagName): boolean {
    return flags[name] ?? false;
}

export function resetFlags() {
    flags.etaEquality = false;
    flags.printImplicits = false;
    flags.printContexts = false;
    flags.printDomains = false;
    flags.printMetaTypes = false;
    flags.printMetaArgs = false;
}

// Global context for definitions and rules
export let globalDefs: Map<string, GlobalDef> = new Map();
export let userRewriteRules: StoredRewriteRule[] = [];
export let userUnificationRules: UnificationRule[] = [];
export let constraints: Constraint[] = [];
export const emptyCtx: Context = [];

// Fresh name generation
let nextVarId = 0;
export const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarId++}`;

let nextHoleId = 0;
export const freshHoleName = (): string => `?h${nextHoleId++}`;

export const resetVarId = () => { nextVarId = 0; };
export const resetHoleId = () => { nextHoleId = 0; };

/**
 * Creates a fresh hole term. Useful shorthand.
 */
export const FH = (): Term & { tag: 'Hole' } => Hole(freshHoleName());

// Constraint Management
export function addConstraint(t1: Term, t2: Term, origin?: string) { constraints.push({ t1, t2, origin }); }

/**
 * Control object for solveConstraints to prevent deep re-entrant calls.
 */
export const solveConstraintsControl = { depth: 0 };

// Term Reference Resolution
/**
 * Dereferences a term, following Hole references until a non-Hole term or an unassigned Hole is found.
 * Includes cycle detection.
 * @param term The term to dereference.
 * @returns The dereferenced term.
 */
export function getTermRef(term: Term): Term {
    let current = term;
    const visited = new Set<Term>();
    while (current.tag === 'Hole' && current.ref) {
        if (visited.has(current)) {
            console.warn(`Cycle detected in Hole references starting from ${term.tag === 'Hole' ? term.id : 'original term'}. Returning current hole: ${current.id}`);
            return current;
        }
        visited.add(current);
        current = current.ref;
    }
    return current;
}

// Context Manipulation
/**
 * Extends a context with a new binding.
 * @param ctx The context to extend.
 * @param name The name of the variable.
 * @param type The type of the variable.
 * @param icit The implicitness of the variable.
 * @param definition Optional definition for the variable (for local lets).
 * @returns The new, extended context.
 */
export const extendCtx = (ctx: Context, name: string, type: Term, icit: Icit = Icit.Expl, definition?: Term): Context => {
    return [{ name, type, icit, definition }, ...ctx];
};

/**
 * Looks up a variable name in the context.
 * @param ctx The context to search.
 * @param name The name to look up.
 * @returns The binding if found, otherwise undefined.
 */
export const lookupCtx = (ctx: Context, name: string): Binding | undefined => ctx.find(b => b.name === name);

// Kernel Constant and Injectivity Checks
export const EMDASH_CONSTANT_SYMBOLS_TAGS = new Set<string>(['CatTerm', 'SetTerm']);
export const EMDASH_UNIFICATION_INJECTIVE_TAGS = new Set<string>([
    'Type',  'Var', 'CatTerm', 'ObjTerm', 'HomTerm',
    'FunctorCategoryTerm', 'NatTransTypeTerm', 'SetTerm',
    'FunctorTypeTerm'
]);

/**
 * Checks if a term is structurally a kernel constant symbol.
 * These symbols typically bypass user rewrite rules.
 * @param term The term to check.
 * @returns True if the term is a kernel constant, false otherwise.
 */
export function isKernelConstantSymbolStructurally(term: Term): boolean {
    const rt = getTermRef(term);
    if (rt.tag === 'Var') {
        const gdef = globalDefs.get(rt.name);
        return !!(gdef && gdef.isConstantSymbol); // True if it's a Var defined as a constant
    }

    switch (rt.tag) {
        case 'CatTerm':
        case 'FunctorCategoryTerm':
        case 'NatTransTypeTerm':
        case 'HomCovFunctorIdentity':
        case 'SetTerm':
        case 'FunctorTypeTerm':
            return true;
        case 'FMap0Term':
        case 'FMap1Term':
        case 'NatTransComponentTerm':
        case 'ObjTerm':
        case 'HomTerm':
            return false;
        case 'Type':
            return true;
        default:
            return false;
    }
}

/**
 * Checks if a term tag corresponds to a structurally injective constructor for unification.
 * @param tag The tag string of the term.
 * @returns True if the tag is for an injective constructor, false otherwise.
 */
export function isEmdashUnificationInjectiveStructurally(tag: string): boolean {
    return EMDASH_UNIFICATION_INJECTIVE_TAGS.has(tag);
}

// Debugging Utilities
let _debug_verbose_flag = false;

export function setDebugVerbose(value: boolean): void {
    _debug_verbose_flag = value;
}

export function getDebugVerbose(): boolean {
    return _debug_verbose_flag;
}

export function consoleLog(message?: any, ...optionalParams: any[]): void {
    if (_debug_verbose_flag) {
        console.log("[VERBOSE]", message, ...optionalParams);
    }
}

/**
 * Clones a term. Currently, this is a shallow clone (returns the term itself)
 * as terms are largely immutable or use functional updates for bodies.
 * TODO: Review if deep cloning is ever necessary.
 * @param term The term to clone.
 * @returns The "cloned" term.
 */
export function cloneTerm(term: Term): Term {
    // This was the original implementation. If deep cloning becomes necessary,
    // it needs to handle function bodies (Lam, Pi) correctly,
    // possibly by reconstructing them or by a more involved cloning mechanism.
    return term;
}

// Term Printing
const PRINT_TERM_MAX_STACK_DEPTH = 40;

/**
 * Pretty-prints a term to a string representation.
 * @param term The term to print.
 * @param boundVarsMap A map to handle bound variable names for pretty printing.
 * @param stackDepth Current recursion depth for stack overflow prevention.
 * @returns A string representation of the term.
 */
export function printTerm(term: Term, boundVarsMap: Map<string, string> = new Map(), stackDepth = 0): string {
    if (stackDepth > PRINT_TERM_MAX_STACK_DEPTH) return "<print_depth_exceeded>";
    if (!term) return "<null_term>";

    const current = getTermRef(term);

    const getUniqueName = (baseName: string): string => {
        if (!boundVarsMap.has(baseName) && !globalDefs.has(baseName) && !Array.from(boundVarsMap.values()).includes(baseName)) {
            return baseName;
        }
        let uniqueName = baseName;
        let suffix = 1;
        while (globalDefs.has(uniqueName) || Array.from(boundVarsMap.values()).includes(uniqueName) || boundVarsMap.has(uniqueName) ) {
            uniqueName = `${baseName}_${suffix++}`;
            if (suffix > 100) return `${baseName}_too_many`;
        }
        return uniqueName;
    };

    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return boundVarsMap.get(current.name) || current.name;
        case 'Hole': {
            let typeInfo = "";
            if (current.elaboratedType && getTermRef(current.elaboratedType) !== current) {
                const elabTypeRef = getTermRef(current.elaboratedType);
                const isSelfRefPrint = (elabTypeRef.tag === 'Hole' && elabTypeRef.id === current.id && elabTypeRef.elaboratedType === current.elaboratedType);
                // Avoid printing Type : Type for ?h : Type
                const isTypeForHoleType = elabTypeRef.tag === 'Type' && current.elaboratedType && getTermRef(current.elaboratedType).tag === 'Type';

                if (!isSelfRefPrint && !isTypeForHoleType) {
                    const elabTypePrint = printTerm(elabTypeRef, new Map(boundVarsMap), stackDepth + 1);
                     if(!elabTypePrint.startsWith("?h") || elabTypePrint.length > current.id.length + 3 ) {
                        typeInfo = `(:${elabTypePrint})`;
                    }
                } else if (isTypeForHoleType && elabTypeRef.tag === 'Type' && !typeInfo) {
                     // Explicitly show : Type if it's the type of a hole, unless already covered
                    typeInfo = `(:Type)`;
                }
            }
            return (current.id === '_' ? '_' : (boundVarsMap.get(current.id) || current.id)) + typeInfo;
        }
        case 'Lam': {
            const paramDisplayName = getUniqueName(current.paramName);
            const newBoundVars = new Map(boundVarsMap);
            newBoundVars.set(current.paramName, paramDisplayName);

            const typeAnnotation = (current._isAnnotated && current.paramType)
                ? ` : ${printTerm(current.paramType, new Map(boundVarsMap), stackDepth + 1)}`
                : '';
            const bodyTerm = current.body(Var(current.paramName, true));
            const binder = current.icit === Icit.Impl ? `{${paramDisplayName}${typeAnnotation}}` : `(${paramDisplayName}${typeAnnotation})`;
            return `(λ ${binder}. ${printTerm(bodyTerm, newBoundVars, stackDepth + 1)})`;
        }
        case 'App':
            const funcStr = printTerm(current.func, new Map(boundVarsMap), stackDepth + 1);
            const argStr = printTerm(current.arg, new Map(boundVarsMap), stackDepth + 1);
            return current.icit === Icit.Impl ? `(${funcStr} {${argStr}})` : `(${funcStr} ${argStr})`;
        case 'Pi': {
            const paramDisplayName = getUniqueName(current.paramName);
            const newBoundVars = new Map(boundVarsMap);
            newBoundVars.set(current.paramName, paramDisplayName);

            const paramTypeStr = printTerm(current.paramType, new Map(boundVarsMap), stackDepth + 1);
            const bodyTypeTerm = current.bodyType(Var(current.paramName, true));
            const binder = current.icit === Icit.Impl ? `{${paramDisplayName} : ${paramTypeStr}}` : `(${paramDisplayName} : ${paramTypeStr})`;
            return `(Π ${binder}. ${printTerm(bodyTypeTerm, newBoundVars, stackDepth + 1)})`;
        }
        case 'CatTerm': return 'Cat';
        case 'ObjTerm': return `(Obj ${printTerm(current.cat, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'HomTerm':
            return `(Hom ${printTerm(current.cat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.dom, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.cod, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'FunctorTypeTerm':
            return `(FunctorType ${printTerm(current.domainCat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.codomainCat, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'FunctorCategoryTerm':
            return `(Functor ${printTerm(current.domainCat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.codomainCat, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'FMap0Term':
            return `(fmap0 ${printTerm(current.functor, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.objectX, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'FMap1Term':
            return `(fmap1 ${printTerm(current.functor, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.morphism_a, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'NatTransTypeTerm':
            return `(Transf ${printTerm(current.catA, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.catB, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.functorF, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.functorG, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'NatTransComponentTerm':
            return `(tapp ${printTerm(current.transformation, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.objectX, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'HomCovFunctorIdentity':
            return `(HomCovFunctor ${printTerm(current.domainCat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.objW_InDomainCat, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'SetTerm': return 'Set';
        default:
            const exhaustiveCheck: never = current;
            throw new Error(`printTerm: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
}