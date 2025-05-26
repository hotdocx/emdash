import { Term, Context, GlobalDef, RewriteRule, PatternVarDecl, UnificationRule, Constraint, StoredRewriteRule, Icit, Type, CatTerm, Var, Hole, App, Lam, Pi, ObjTerm, HomTerm, MkCat_, IdentityMorph, ComposeMorph, Binding } from './core_types';
import { printTerm, infer, check } from './core_elaboration'; // infer, check needed for addRewriteRule
import { whnf, solveConstraints, areEqual } from './core_logic'; // solveConstraints, whnf for addRewriteRule

export let nextVarId = 0;
export const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarId++}`; ////`$$fresh_${hint}${nextVarId++}`;

export let nextHoleId = 0;
export const freshHoleName = (): string => `?h${nextHoleId++}`;

export const resetVarId = () => { nextVarId = 0; };
export const resetHoleId = () => { nextHoleId = 0; };

export let globalDefs: Map<string, GlobalDef> = new Map();

export function defineGlobal(name: string, type: Term, value?: Term, isConstantSymbol: boolean = false, isInjective?: boolean) {
    if (globalDefs.has(name)) console.warn(`Warning: Redefining global ${name}`);
    if (isConstantSymbol && value !== undefined) {
        throw new Error(`Constant symbol ${name} cannot have a definition/value.`);
    }
    globalDefs.set(name, { name, type, value, isConstantSymbol, isInjective });
}

export let rawUserRewriteRules: RewriteRule[] = []; // Stores raw rules before elaboration
export let userRewriteRules: StoredRewriteRule[] = []; // Stores elaborated rules

// Helper for deep cloning
export function cloneTerm(term: Term, clonedObjects: Map<Term, Term> = new Map()): Term {
    if (clonedObjects.has(term)) {
        return clonedObjects.get(term)!;
    }

    let result: Term;

    switch (term.tag) {
        case 'Type': result = Type(); break;
        case 'CatTerm': result = CatTerm(); break;
        case 'Var': result = Var(term.name); break;
        case 'Hole':
            const newHole = Hole(term.id);
            clonedObjects.set(term, newHole); // Add to map *before* recursive calls
            if (term.ref) {
                (newHole as Term & { tag: 'Hole' }).ref = cloneTerm(term.ref, clonedObjects);
            }
            if (term.elaboratedType) {
                (newHole as Term & { tag: 'Hole' }).elaboratedType = cloneTerm(term.elaboratedType, clonedObjects);
            }
            result = newHole;
            break;
        case 'App':
            result = App(
                cloneTerm(term.func, clonedObjects),
                cloneTerm(term.arg, clonedObjects),
                term.icit
            );
            break;
        case 'Lam': {
            const clonedParamType = term.paramType ? cloneTerm(term.paramType, clonedObjects) : undefined;
            const originalBodyFn = term.body;
            const newClonedBodyFn = (v_bound: Term): Term => {
                const originalBodyInstance = originalBodyFn(v_bound);
                return cloneTerm(originalBodyInstance, clonedObjects);
            };
            // Direct construction for robustness, avoiding smart constructor overload issues
            result = {
                tag: 'Lam',
                paramName: term.paramName,
                icit: term.icit,
                paramType: clonedParamType,
                body: newClonedBodyFn,
                _isAnnotated: term._isAnnotated
            };
            break;
        }
        case 'Pi': {
            const clonedParamType = cloneTerm(term.paramType, clonedObjects);
            const originalBodyTypeFn = term.bodyType;
            const newClonedBodyTypeFn = (v_bound: Term): Term => {
                const originalBodyTypeInstance = originalBodyTypeFn(v_bound);
                return cloneTerm(originalBodyTypeInstance, clonedObjects);
            };
            result = Pi(term.paramName, term.icit, clonedParamType, newClonedBodyTypeFn);
            break;
        }
        case 'ObjTerm': result = ObjTerm(cloneTerm(term.cat, clonedObjects)); break;
        case 'HomTerm':
            result = HomTerm(
                cloneTerm(term.cat, clonedObjects),
                cloneTerm(term.dom, clonedObjects),
                cloneTerm(term.cod, clonedObjects)
            ); break;
        case 'MkCat_':
            result = MkCat_(
                cloneTerm(term.objRepresentation, clonedObjects),
                cloneTerm(term.homRepresentation, clonedObjects),
                cloneTerm(term.composeImplementation, clonedObjects)
            ); break;
        case 'IdentityMorph':
            result = IdentityMorph(
                cloneTerm(term.obj, clonedObjects),
                term.cat_IMPLICIT ? cloneTerm(term.cat_IMPLICIT, clonedObjects) : undefined
            ); break;
        case 'ComposeMorph':
            result = ComposeMorph(
                cloneTerm(term.g, clonedObjects),
                cloneTerm(term.f, clonedObjects),
                term.cat_IMPLICIT ? cloneTerm(term.cat_IMPLICIT, clonedObjects) : undefined,
                term.objX_IMPLICIT ? cloneTerm(term.objX_IMPLICIT, clonedObjects) : undefined,
                term.objY_IMPLICIT ? cloneTerm(term.objY_IMPLICIT, clonedObjects) : undefined,
                term.objZ_IMPLICIT ? cloneTerm(term.objZ_IMPLICIT, clonedObjects) : undefined
            ); break;
        default:
            const exhaustiveCheck: never = term;
            throw new Error(`cloneTerm: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
    if (term.tag !== 'Var' && term.tag !== 'Type' && term.tag !== 'CatTerm') { // Avoid storing simple immutable singletons
         clonedObjects.set(term, result);
    }
    return result;
}


export function addRewriteRule(
    ruleName: string,
    userPatternVars: PatternVarDecl[],
    rawLhsTerm: Term,
    rawRhsTerm: Term,
    ctx: Context // Global context for type lookups
) {
    rawUserRewriteRules.push({ name: ruleName, patternVars: userPatternVars, lhs: rawLhsTerm, rhs: rawRhsTerm}); // Store raw for reference

    const originalConstraintsBackup = [...constraints];
    constraints.length = 0; // Isolate constraint solving for this rule

    let elaboratedLhs: Term;
    let elaboratedRhs: Term;
    const solvedPatVarTypes = new Map<PatternVarDecl, Term>();

    try {
        // --- 1. Elaborate LHS ---
        const lhsToElaborate = cloneTerm(rawLhsTerm);
        let lhsElabCtx: Context = [...ctx]; // Start with global context
        for (const pVarName of userPatternVars) {
            if (!pVarName.startsWith('$')) throw new Error(`Pattern variable ${pVarName} in rule '${ruleName}' must start with '$'.`);
            // Pattern vars get a Hole type in their own elaboration context
            lhsElabCtx = extendCtx(lhsElabCtx, pVarName, Hole(freshHoleName() + "_type_pvar_" + pVarName.substring(1)), Icit.Expl); // Icit doesn't matter much here
        }

        // `infer` will fill Holes in lhsToElaborate, making it the "elaboratedLhsPattern"
        infer(lhsElabCtx, lhsToElaborate, 0); // Result type not immediately needed here, side-effects on lhsToElaborate

        if (!solveConstraints(lhsElabCtx)) {
            const remaining = constraints.map(c => `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`).join('; ');
            throw new Error(`Rule '${ruleName}' LHS pattern (${printTerm(rawLhsTerm)}) is ill-typed or inconsistent. Unsolved constraints: ${remaining}`);
        }
        elaboratedLhs = getTermRef(lhsToElaborate); // This is the structurally elaborated LHS

        // Extract solved types for pattern variables from lhsElabCtx
        for (const pVarName of userPatternVars) {
            const binding = lookupCtx(lhsElabCtx, pVarName);
            if (binding) {
                 solvedPatVarTypes.set(pVarName, getTermRef(binding.type)); // Store the (potentially solved) Hole
            } else { // Should not happen
                 console.warn(`Pattern variable ${pVarName} not found in LHS elaboration context for rule '${ruleName}'.`);
                 solvedPatVarTypes.set(pVarName, Hole(freshHoleName() + "_type_pvar_unfound_" + pVarName.substring(1)));
            }
        }

        // --- 2. Elaborate RHS & Type Check for Preservation ---
        const rhsToElaborate = cloneTerm(rawRhsTerm);
        let rhsElabCtx: Context = [...ctx]; // Start with global context
        for (const pVarName of userPatternVars) {
            const pVarType = solvedPatVarTypes.get(pVarName) || Hole(freshHoleName() + "_type_pvar_rhs_missing_" + pVarName.substring(1));
            rhsElabCtx = extendCtx(rhsElabCtx, pVarName, pVarType, Icit.Expl); // Icit assumed Expl for vars
        }

        // The type of the elaborated LHS, inferred in the *global* context (not lhsElabCtx)
        // This is the type the RHS must also have.
        constraints.length = 0; // Clear for LHS type inference
        const typeOfGlobalLhs = infer(lhsElabCtx, elaboratedLhs, 0);
         if (!solveConstraints(ctx)) { // Solve constraints related to LHS's global type
            throw new Error(`Rule '${ruleName}': Could not establish a consistent global type for the elaborated LHS ${printTerm(elaboratedLhs)}.`);
        }
        const targetRhsType = whnf(getTermRef(typeOfGlobalLhs.type), ctx);


        constraints.length = 0; // Clear for RHS checking
        check(rhsElabCtx, rhsToElaborate, targetRhsType, 0);

        if (!solveConstraints(rhsElabCtx)) {
            const remaining = constraints.map(c => `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`).join('; ');
            throw new Error(`Rule '${ruleName}' RHS (${printTerm(rawRhsTerm)}) is ill-typed or does not match LHS type (${printTerm(targetRhsType)}). Unsolved constraints: ${remaining}`);
        }
        elaboratedRhs = getTermRef(rhsToElaborate);

        userRewriteRules.push({ name: ruleName, patternVars: userPatternVars, elaboratedLhs, elaboratedRhs });
        consoleLog(`Rule '${ruleName}' added and elaborated successfully.`);

    } catch (e) {
        console.error(`Failed to add rewrite rule '${ruleName}': ${(e as Error).message}. Stack: ${(e as Error).stack}`);
        // Optionally rethrow or collect errors
    } finally {
        constraints.splice(0, constraints.length, ...originalConstraintsBackup); // Restore global constraints
    }
}


export let userUnificationRules: UnificationRule[] = [];
export function addUnificationRule(rule: UnificationRule) {
    userUnificationRules.push(rule);
}

export let constraints: Constraint[] = [];
export function addConstraint(t1: Term, t2: Term, origin?: string) { constraints.push({ t1, t2, origin }); }

export function getTermRef(term: Term): Term {
    let current = term;
    const visited = new Set<Term>(); // To detect cycles in Hole references
    while (current.tag === 'Hole' && current.ref) {
        if (visited.has(current)) {
            console.warn(`Cycle detected in Hole references starting from ${term.tag === 'Hole' ? term.id : 'original term'}. Returning current hole: ${current.id}`);
            return current; // Break cycle
        }
        visited.add(current);
        current = current.ref;
    }
    return current;
}


export const emptyCtx: Context = [];

// <<< MODIFIED HERE
export const extendCtx = (ctx: Context, name: string, type: Term, icit: Icit = Icit.Expl, definition?: Term): Context => {
    return [{ name, type, icit, definition }, ...ctx];
};

export const lookupCtx = (ctx: Context, name: string): Binding | undefined => ctx.find(b => b.name === name);

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

let _debug_verbose_flag = false;

export function setDebugVerbose(value: boolean): void {
    _debug_verbose_flag = value;
}

export function getDebugVerbose(): boolean {
    return _debug_verbose_flag;
}

export function consoleLog(message?: any, ...optionalParams: any[]): void {
    if (_debug_verbose_flag) {
        console.log(message, ...optionalParams);
    }
}

export function resetMyLambdaPi() {
    constraints.length = 0;
    globalDefs.clear();
    rawUserRewriteRules.length = 0;
    userRewriteRules.length = 0;
    userUnificationRules.length = 0;
    resetVarId();
    resetHoleId();
    setDebugVerbose(false); // Reset debug flag as well
}

export function setupPhase1GlobalsAndRules() {
    defineGlobal("NatType", Type(), undefined, true); 
    defineGlobal("BoolType", Type(), undefined, true);

    const pvarCat = "$CAT_pv";
    const pvarX_obj = "$X_obj_pv";
    const pvarY_obj = "$Y_obj_pv";
    const pvar_g_XY = "$g_XY_pv";

    addRewriteRule(
        "comp_g_idX_fwd",
        [pvarCat, pvarX_obj, pvarY_obj, pvar_g_XY],
        ComposeMorph(
            Var(pvar_g_XY),
            IdentityMorph(Var(pvarX_obj), Var(pvarCat)),
            Var(pvarCat),
            Var(pvarX_obj),
            Var(pvarX_obj),
            Var(pvarY_obj)
        ),
        Var(pvar_g_XY),
        emptyCtx 
    );

    const pvar_f_XY = "$f_XY_pv";
    addRewriteRule(
        "comp_idY_f_fwd",
        [pvarCat, pvarX_obj, pvarY_obj, pvar_f_XY],
        ComposeMorph(
            IdentityMorph(Var(pvarY_obj), Var(pvarCat)),
            Var(pvar_f_XY),
            Var(pvarCat),
            Var(pvarX_obj),
            Var(pvarY_obj),
            Var(pvarY_obj)
        ),
        Var(pvar_f_XY),
        emptyCtx
    );
}

export function resetMyLambdaPi_Emdash() { 
    resetMyLambdaPi();
} 