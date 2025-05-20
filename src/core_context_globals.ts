import { Term, Context, GlobalDef, RewriteRule, PatternVarDecl, UnificationRule, Constraint, CatTerm, ObjTerm, HomTerm, Type, Var, App, Pi, IdentityMorph, ComposeMorph } from './core_types';
import { printTerm } from './core_elaboration';

export let nextVarId = 0;
export const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarId++}`;

export let nextHoleId = 0;
export const freshHoleName = (): string => `?h${nextHoleId++}`;

export const resetVarId = () => { nextVarId = 0; };
export const resetHoleId = () => { nextHoleId = 0; };

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

export const emptyCtx: Context = [];
export const extendCtx = (ctx: Context, name: string, type: Term): Context => [{ name, type }, ...ctx];
export const lookupCtx = (ctx: Context, name: string): GlobalDef | undefined => ctx.find(b => b.name === name) as GlobalDef | undefined; // Cast to satisfy GlobalDef, thought it is Binding

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

export let DEBUG_VERBOSE = false;

export function consoleLog(message?: any, ...optionalParams: any[]): void {
    if (DEBUG_VERBOSE) {
        console.log(message, ...optionalParams);
    }
}

export function resetMyLambdaPi() {
    constraints.length = 0; // Clear constraints by setting length to 0
    globalDefs.clear();
    userRewriteRules.length = 0;
    userUnificationRules.length = 0;
    resetVarId();
    resetHoleId();
}

export function setupPhase1GlobalsAndRules() {
    defineGlobal("NatType", Type(), undefined, true); 
    defineGlobal("BoolType", Type(), undefined, true);

    const pvarCat = { name: "CAT_pv", type: CatTerm() };
    const pvarX_obj = { name: "X_obj_pv", type: ObjTerm(Var("CAT_pv")) }; 
    const pvarY_obj = { name: "Y_obj_pv", type: ObjTerm(Var("CAT_pv")) };

    const pvar_g_XY = { name: "g_XY_pv", type: HomTerm(Var("CAT_pv"), Var("X_obj_pv"), Var("Y_obj_pv")) };
    addRewriteRule({
        name: "comp_g_idX_fwd", 
        patternVars: [pvarCat, pvarX_obj, pvarY_obj, pvar_g_XY],
        lhs: ComposeMorph(
            Var("g_XY_pv"),                                     
            IdentityMorph(Var("X_obj_pv"), Var("CAT_pv")),      
            Var("CAT_pv"),                                      
            Var("X_obj_pv"),                                    
            Var("X_obj_pv"),                                    
            Var("Y_obj_pv")                                     
        ),
        rhs: Var("g_XY_pv")
    });

    const pvar_f_XY = { name: "f_XY_pv", type: HomTerm(Var("CAT_pv"), Var("X_obj_pv"), Var("Y_obj_pv")) };
    addRewriteRule({
        name: "comp_idY_f_fwd", 
        patternVars: [pvarCat, pvarX_obj, pvarY_obj, pvar_f_XY],
        lhs: ComposeMorph(
            IdentityMorph(Var("Y_obj_pv"), Var("CAT_pv")),      
            Var("f_XY_pv"),                                     
            Var("CAT_pv"),                                      
            Var("X_obj_pv"),                                    
            Var("Y_obj_pv"),                                    
            Var("Y_obj_pv")                                     
        ),
        rhs: Var("f_XY_pv")
    });
}

export function resetMyLambdaPi_Emdash() { 
    resetMyLambdaPi();
} 