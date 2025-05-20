import { Term, GlobalDef, RewriteRule, PatternVarDecl, UnificationRule, Constraint } from './types';

export let nextVarId = 0;
export const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarId++}`;

export let nextHoleId = 0;
export const freshHoleName = (): string => `?h${nextHoleId++}`;

export let globalDefs: Map<string, GlobalDef> = new Map();

export function defineGlobal(name: string, type: Term, value?: Term, isConstantSymbol: boolean = false) {
    if (globalDefs.has(name)) console.warn(`Warning: Redefining global ${name}`);
    if (isConstantSymbol && value !== undefined) {
        throw new Error(`Constant symbol ${name} cannot have a definition/value.`);
    }
    globalDefs.set(name, { name, type, value, isConstantSymbol });
}

export let userRewriteRules: RewriteRule[] = [];
export function addRewriteRule(rule: RewriteRule) {
    userRewriteRules.push(rule);
}

export let userUnificationRules: UnificationRule[] = [];
export function addUnificationRule(rule: UnificationRule) {
    userUnificationRules.push(rule);
}

export let constraints: Constraint[] = [];
export function addConstraint(t1: Term, t2: Term, origin?: string) { constraints.push({ t1, t2, origin }); }

export function getTermRef(term: Term): Term {
    if (term.tag === 'Hole' && term.ref) return getTermRef(term.ref);
    return term;
}

export const MAX_WHNF_ITERATIONS = 1000; // Max iterations for whnf reduction loop
export const MAX_STACK_DEPTH = 200; // General recursion depth limit
export let DEBUG_VERBOSE = false;

export const EMDASH_CONSTANT_SYMBOLS_TAGS = new Set<string>(['CatTerm', 'MkCat_']);
export const EMDASH_UNIFICATION_INJECTIVE_TAGS = new Set<string>(['IdentityMorph', 'CatTerm', 'ObjTerm', 'HomTerm', 'MkCat_']);

export function isKernelConstantSymbolStructurally(term: Term): boolean {
    const t = getTermRef(term);
    if (EMDASH_CONSTANT_SYMBOLS_TAGS.has(t.tag)) return true;
    if (t.tag === 'Var' && globalDefs.get(t.name)?.isConstantSymbol) return true;
    return false;
}

export function isEmdashUnificationInjectiveStructurally(tag: string): boolean {
    return EMDASH_UNIFICATION_INJECTIVE_TAGS.has(tag);
} 