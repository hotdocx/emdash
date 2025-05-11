// --- MyLambdaPi Final: Bidirectional, Unification, Defs, Rewrite Rules ---

// --- Report on Changed Specification (as detailed above) ---
// This implementation focuses on a core lambda calculus with Pi types,
// bidirectional type checking, unification-based hole solving,
// user-defined global symbols with delta reduction, and
// user-provided first-order rewrite rules with type preservation checks.
// Identity types are omitted.
// Fixes for previous errors related to lambda elaboration and hole type querying are included.
// --- End Report ---

let nextVarId = 0;
const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarId++}`;

let nextHoleId = 0;
const freshHoleName = (): string => `?h${nextHoleId++}`;


type PatternVar = { tag: 'PatternVar', name: string };

type BaseTerm =
    | { tag: 'Type' }
    | { tag: 'Var', name: string }
    | { tag: 'Lam', paramName: string, paramType?: Term, body: (v: Term) => Term, _isAnnotated: boolean }
    | { tag: 'App', func: Term, arg: Term }
    | { tag: 'Pi', paramName: string, paramType: Term, bodyType: (v: Term) => Term }
    | { tag: 'Hole', id: string, ref?: Term, elaboratedType?: Term };

type Term = BaseTerm;
type PatternTerm = BaseTerm | PatternVar;


// --- Constructors ---
const Type = (): Term => ({ tag: 'Type' });
const Var = (name: string): Term => ({ tag: 'Var', name });
const Lam = (paramName: string, body: (v: Term) => Term, paramType?: Term): Term & { tag: 'Lam' } =>
    ({ tag: 'Lam', paramName, paramType, body, _isAnnotated: !!paramType });
const App = (func: Term, arg: Term): Term => ({ tag: 'App', func, arg });
const Pi = (paramName: string, paramType: Term, bodyType: (v: Term) => Term): Term =>
    ({ tag: 'Pi', paramName, paramType, bodyType });

const Hole = (id?: string): Term & { tag: 'Hole' } => {
    const holeId = id || freshHoleName();
    return { tag: 'Hole', id: holeId, ref: undefined, elaboratedType: undefined };
};
const MPatternVar = (name: string): PatternVar => ({tag: 'PatternVar', name});


// --- Contexts and Global Definitions ---
type Binding = { name: string, type: Term };
type Context = Binding[];

const emptyCtx: Context = [];
const extendCtx = (ctx: Context, name: string, type: Term): Context => [{ name, type }, ...ctx];
const lookupCtx = (ctx: Context, name: string): Binding | undefined => ctx.find(b => b.name === name);

interface GlobalDef { name: string; type: Term; value?: Term; }
const globalDefs: Map<string, GlobalDef> = new Map();

function defineGlobal(name: string, type: Term, value?: Term) {
    if (globalDefs.has(name)) console.warn(`Warning: Redefining global ${name}`);
    globalDefs.set(name, { name, type, value });
}

// --- Rewrite Rules ---
interface RewriteRule {
    name: string;
    patternVars: Array<{ name: string, type: Term }>;
    lhs: PatternTerm;
    rhs: PatternTerm;
}
const userRewriteRules: RewriteRule[] = [];

function addRewriteRule(rule: RewriteRule) {
    userRewriteRules.push(rule);
}

type Substitution = Map<string, Term>;


// --- Constraints and Unification ---
interface Constraint { t1: Term; t2: Term; origin?: string; }
const constraints: Constraint[] = [];

function addConstraint(t1: Term, t2: Term, origin?: string) {
    constraints.push({ t1, t2, origin });
}

function getTermRef(term: Term): Term {
    if (term.tag === 'Hole' && term.ref) return getTermRef(term.ref);
    return term;
}


// --- Normalization (WHNF and Full) ---
const MAX_RECURSION_DEPTH = 100; // For normalization loops (delta/rules)
const MAX_STACK_DEPTH = 70;     // For recursive calls in normalize/whnf

function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("WHNF stack depth exceeded");
    let current = getTermRef(term);

    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        const L_current = current; // Term at start of this iteration

        // 1. Delta Reduction
        if (L_current.tag === 'Var') {
            const gdef = globalDefs.get(L_current.name);
            if (gdef && gdef.value) {
                current = getTermRef(gdef.value); // current is now the definition
                if (L_current !== current) continue; // Restart loop if something changed
            }
        }

        // 2. Rewrite Rules
        let ruleAppliedThisIter = false;
        for (const rule of userRewriteRules) {
            // Match against `current` which has undergone delta in this loop iter if applicable
            const subst = matchPattern(rule.lhs, current, ctx, rule.patternVars, undefined, stackDepth + 1);
            if (subst) {
                current = getTermRef(applySubstToPatternTerm(rule.rhs, subst, rule.patternVars));
                ruleAppliedThisIter = true;
                break;
            }
        }
        if (ruleAppliedThisIter && L_current !== current) continue; // Restart loop if rule changed term

        // If no delta or rule changed `current` in this iteration, break pre-processing.
        // Compare `L_current` (start of iter) with `current` (after delta/rules in this iter).
        // A more robust check would be structural equality if printing is too slow/unreliable.
        if (L_current === current || (L_current.tag === current.tag && printTerm(L_current) === printTerm(current))) break;
    }
    // current is now the result of delta/rewrite reductions at this level.

    // 3. Beta Reduction
    if (current.tag === 'App') {
        const funcNorm = whnf(current.func, ctx, stackDepth + 1);
        if (funcNorm.tag === 'Lam') {
            return whnf(funcNorm.body(current.arg), ctx, stackDepth + 1);
        }
        // Reconstruct if func part changed, even if not a Lam (e.g., rule made it a Var)
        if (funcNorm !== getTermRef(current.func)) return App(funcNorm, current.arg);
        return current; // Original App, or App(funcNorm, arg) if funcNorm is just current.func
    }
    return current;
}

function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("Normalize stack depth exceeded");
    let current = getTermRef(term);

    // Top-level delta/rewrite loop, similar to WHNF
    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        const L_current = current;
        if (L_current.tag === 'Var') {
            const gdef = globalDefs.get(L_current.name);
            if (gdef && gdef.value) {
                current = getTermRef(gdef.value);
                if (L_current !== current) continue;
            }
        }
        let ruleAppliedThisIter = false;
        for (const rule of userRewriteRules) {
            const subst = matchPattern(rule.lhs, current, ctx, rule.patternVars, undefined, stackDepth + 1);
            if (subst) {
                current = getTermRef(applySubstToPatternTerm(rule.rhs, subst, rule.patternVars));
                ruleAppliedThisIter = true;
                break;
            }
        }
        if (ruleAppliedThisIter && L_current !== current) continue;
        if (L_current === current || (L_current.tag === current.tag && printTerm(L_current) === printTerm(current))) break;
    }
    // current is now term after top-level delta/rewrite. Now, structural normalization.

    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': return current;
        case 'Lam':
            const lamParamTypeRef = current.paramType ? getTermRef(current.paramType) : undefined;
            const normLamParamType = lamParamTypeRef ? normalize(lamParamTypeRef, ctx, stackDepth + 1) : undefined;
            
            // The body function `current.body` needs to be preserved.
            // When we normalize the result of `current.body(v)`, `v` should be a generic variable.
            const freshVLam = Var(freshVarName(current.paramName));
            const lamCtxType = normLamParamType || (current._isAnnotated && current.paramType ? getTermRef(current.paramType) : Hole());
            const extendedLamCtx = extendCtx(ctx, freshVLam.name, lamCtxType);

            // Reconstruct Lam with potentially normalized paramType and a body that normalizes on application
            const newLam = Lam(current.paramName,
                v_arg => normalize(current.body(v_arg), extendedLamCtx, stackDepth + 1), // Pass extended Ctx here? No, ctx of normalize call.
                                                                                        // The original ctx is used when current.body is called.
                                                                                        // The problem is, normalize needs the current context
                                                                                        // of the body, which means extend the *caller's* ctx.
                normLamParamType);
            (newLam as { _isAnnotated?: boolean })._isAnnotated = current._isAnnotated; // Preserve annotation status
            return newLam;
        case 'App':
            const normFunc = normalize(current.func, ctx, stackDepth + 1);
            const normArg = normalize(current.arg, ctx, stackDepth + 1);
            if (normFunc.tag === 'Lam') {
                return normalize(normFunc.body(normArg), ctx, stackDepth + 1);
            }
            return App(normFunc, normArg);
        case 'Pi':
            const normPiParamType = normalize(current.paramType, ctx, stackDepth + 1);
            const freshVPi = Var(freshVarName(current.paramName));
            const extendedPiCtx = extendCtx(ctx, freshVPi.name, normPiParamType);
             return Pi(current.paramName, normPiParamType,
                v_arg => normalize(current.bodyType(v_arg), extendedPiCtx, stackDepth + 1));
    }
    throw new Error(`normalize: Unhandled term tag ${(current as any).tag}`);
}


// --- Equality and Unification (largely same as before, ensure depth params are passed) ---
function areEqual(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) throw new Error("Equality check depth exceeded");

    const normT1 = whnf(t1, ctx, depth + 1);
    const normT2 = whnf(t2, ctx, depth + 1);

    const rt1 = getTermRef(normT1);
    const rt2 = getTermRef(normT2);

    if (rt1.tag === 'Hole' || rt2.tag === 'Hole') {
        return (rt1.tag === 'Hole' && rt2.tag === 'Hole' && rt1.id === rt2.id);
    }
    if (rt1.tag !== rt2.tag) return false;

    switch (rt1.tag) {
        case 'Type': return true;
        case 'Var': return rt1.name === (rt2 as typeof rt1).name;
        case 'App':
            return areEqual(rt1.func, (rt2 as typeof rt1).func, ctx, depth + 1) &&
                   areEqual(rt1.arg, (rt2 as typeof rt1).arg, ctx, depth + 1);
        case 'Lam': {
            const lam2 = rt2 as typeof rt1;
             // Check _isAnnotated consistency and paramType equality if both annotated
            if (rt1._isAnnotated !== lam2._isAnnotated) return false; // Must have same annotation status for equality here
            if (rt1._isAnnotated && lam2._isAnnotated) { // Both should be annotated
                if (!rt1.paramType || !lam2.paramType) return false; // Should not happen if _isAnnotated is true
                if (!areEqual(rt1.paramType, lam2.paramType, ctx, depth + 1)) return false;
            } else if (rt1.paramType || lam2.paramType) { // One annotated, one not (runtime, after whnf)
                return false;
            }

            const freshVar = Var(freshVarName("eqLam"));
            const CtxType = rt1.paramType ? getTermRef(rt1.paramType) : Hole(); // Type for the fresh var context
            const extendedCtx = extendCtx(ctx, freshVar.name, CtxType);
            return areEqual(rt1.body(freshVar), lam2.body(freshVar), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const pi2 = rt2 as typeof rt1;
            if (!areEqual(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            const freshVar = Var(freshVarName("eqPi"));
            const extendedCtx = extendCtx(ctx, freshVar.name, getTermRef(rt1.paramType));
            return areEqual(rt1.bodyType(freshVar), pi2.bodyType(freshVar), extendedCtx, depth + 1);
        }
    }
    return false;
}

function termContainsHole(term: Term, holeId: string, visited: Set<string>, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) return false; // Safety for deep terms, assume no containment

    const current = getTermRef(term);
    if (current.tag === 'Hole') return current.id === holeId;

    const termStr = printTerm(current);
    if (visited.has(termStr)) return false;
    visited.add(termStr);

    switch (current.tag) {
        case 'Type': case 'Var': return false;
        case 'App':
            return termContainsHole(current.func, holeId, visited, depth + 1) ||
                   termContainsHole(current.arg, holeId, visited, depth + 1);
        case 'Lam': {
            const paramTypeContains = current.paramType ? termContainsHole(current.paramType, holeId, visited, depth + 1) : false;
            if (paramTypeContains) return true;
            // HOAS body - occurs check simplification
            return false;
        }
        case 'Pi': {
            const paramTypeContains = termContainsHole(current.paramType, holeId, visited, depth + 1);
            if (paramTypeContains) return true;
            // HOAS bodyType - occurs check simplification
            return false;
        }
    }
    return false;
}


function unify(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) {
        throw new Error(`Unification stack depth exceeded`);
    }

    const rt1 = getTermRef(t1);
    const rt2 = getTermRef(t2);

    if (rt1 === rt2 && rt1.tag !== 'Hole') return true;
    if (areEqual(rt1, rt2, ctx, depth + 1)) return true;

    if (rt1.tag === 'Hole') return unifyHole(rt1, rt2, ctx, depth + 1);
    if (rt2.tag === 'Hole') return unifyHole(rt2, rt1, ctx, depth + 1);

    if (rt1.tag !== rt2.tag) return false;

    switch (rt1.tag) {
        case 'App':
            return unify(rt1.func, (rt2 as typeof rt1).func, ctx, depth + 1) &&
                   unify(rt1.arg, (rt2 as typeof rt1).arg, ctx, depth + 1);
        case 'Lam': {
            const lam2 = rt2 as typeof rt1;
             // For unification, if one is annotated and other is not, this requires inference to make them same.
             // Direct unification might be too strict here.
             // Relies on `check` having aligned annotations or types being holes.
            if (rt1._isAnnotated !== lam2._isAnnotated) return false; // Require same annotation status
            if (rt1._isAnnotated) { // Both annotated
                if (!rt1.paramType || !lam2.paramType || !unify(rt1.paramType, lam2.paramType, ctx, depth + 1)) return false;
            }
            const freshVar = Var(freshVarName("unifyLam"));
            const CtxType = rt1.paramType ? getTermRef(rt1.paramType) : Hole();
            const extendedCtx = extendCtx(ctx, freshVar.name, CtxType);
            return unify(rt1.body(freshVar), lam2.body(freshVar), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const pi2 = rt2 as typeof rt1;
            if (!unify(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            const freshVar = Var(freshVarName("unifyPi"));
            const extendedCtx = extendCtx(ctx, freshVar.name, getTermRef(rt1.paramType));
            return unify(rt1.bodyType(freshVar), pi2.bodyType(freshVar), extendedCtx, depth + 1);
        }
    }
    return false;
}

function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
    const normTerm = getTermRef(term);

    if (normTerm.tag === 'Hole') {
        if (hole.id === normTerm.id) return true;
        if (hole.id < normTerm.id) hole.ref = normTerm; else (normTerm as Term & {tag:'Hole'}).ref = hole;
        return true;
    }
    if (termContainsHole(normTerm, hole.id, new Set(), depth + 1)) return false;
    hole.ref = normTerm;
    return true;
}

function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("solveConstraints stack depth exceeded");
    let changedInIteration = true;
    let iterations = 0;
    const maxIterations = constraints.length * 5 + 50;

    while (changedInIteration && iterations < maxIterations) {
        changedInIteration = false;
        iterations++;
        for (let i = 0; i < constraints.length; i++) {
            const constraint = constraints[i];
            if (areEqual(constraint.t1, constraint.t2, ctx, stackDepth + 1)) continue;
            try {
                if (unify(constraint.t1, constraint.t2, ctx, stackDepth + 1)) {
                    changedInIteration = true;
                } else {
                    return false;
                }
            } catch (e) { return false; }
        }
    }
    if (iterations >= maxIterations && changedInIteration) { /* console.warn("Constraint solving max iterations."); */ }
    for (const constraint of constraints) {
        if (!areEqual(constraint.t1, constraint.t2, ctx, stackDepth + 1)) return false;
    }
    return true;
}

// --- Bidirectional Type Checking ---
function infer(ctx: Context, term: Term, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Infer stack depth exceeded for ${printTerm(term)}`);
    const current = getTermRef(term);

    if (current.tag === 'Var') {
        const gdef = globalDefs.get(current.name);
        if (gdef) return gdef.type;
        const binding = lookupCtx(ctx, current.name);
        if (!binding) throw new Error(`Unbound variable: ${current.name}`);
        return binding.type;
    }

    switch (current.tag) {
        case 'Type': return Type();
        case 'Hole':
            if (current.elaboratedType) return getTermRef(current.elaboratedType);
            const newTypeForHole = Hole(freshHoleName());
            (current as { elaboratedType?: Term }).elaboratedType = newTypeForHole;
            return newTypeForHole;
        case 'App': {
            const funcType = infer(ctx, current.func, stackDepth + 1);
            const normFuncType = whnf(funcType, ctx, stackDepth + 1);
            if (normFuncType.tag === 'Hole') {
                const argTypeHole = Hole(freshHoleName());
                const resultTypeHole = Hole(freshHoleName());
                addConstraint(normFuncType, Pi(freshVarName("appArg"), argTypeHole, _ => resultTypeHole), `App func type hole`);
                check(ctx, current.arg, argTypeHole, stackDepth + 1);
                return resultTypeHole;
            }
            if (normFuncType.tag !== 'Pi') throw new Error(`Cannot apply non-function: ${printTerm(current.func)} : ${printTerm(normFuncType)}`);
            check(ctx, current.arg, normFuncType.paramType, stackDepth + 1);
            return normFuncType.bodyType(current.arg);
        }
        case 'Lam': {
            const paramName = current.paramName || freshVarName("lam");
            if (current._isAnnotated && current.paramType) {
                check(ctx, current.paramType, Type(), stackDepth + 1);
                const extendedCtx = extendCtx(ctx, paramName, current.paramType);
                const bodyType = infer(extendedCtx, current.body(Var(paramName)), stackDepth + 1);
                return Pi(paramName, current.paramType, _ => bodyType);
            } else {
                const paramTypeHole = Hole(freshHoleName());
                const extendedCtx = extendCtx(ctx, paramName, paramTypeHole);
                const bodyType = infer(extendedCtx, current.body(Var(paramName)), stackDepth + 1);
                return Pi(paramName, paramTypeHole, _ => bodyType);
            }
        }
        case 'Pi': {
            check(ctx, current.paramType, Type(), stackDepth + 1);
            const paramName = current.paramName || freshVarName("pi");
            const extendedCtx = extendCtx(ctx, paramName, current.paramType);
            check(extendedCtx, current.bodyType(Var(paramName)), Type(), stackDepth + 1);
            return Type();
        }
    }
    throw new Error(`infer: Unhandled term tag ${(current as any).tag}`);
}

function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0): void {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Check stack depth exceeded`);
    const current = getTermRef(term);
    const normExpectedType = whnf(expectedType, ctx, stackDepth + 1);

    if (current.tag === 'Lam' && !current._isAnnotated && normExpectedType.tag === 'Pi') {
        const paramName = current.paramName || freshVarName("lamChk");
        (current as {paramType?: Term}).paramType = normExpectedType.paramType; // Mutate for elaboration
        (current as {_isAnnotated?: boolean})._isAnnotated = true;
        const extendedCtx = extendCtx(ctx, paramName, normExpectedType.paramType);
        check(extendedCtx, current.body(Var(paramName)), normExpectedType.bodyType(Var(paramName)), stackDepth + 1);
        return;
    }
    if (current.tag === 'Hole') {
        const inferredHoleType = infer(ctx, current, stackDepth + 1);
        addConstraint(inferredHoleType, normExpectedType, `Hole ${current.id} checked`);
        return;
    }
    const inferredType = infer(ctx, current, stackDepth + 1);
    addConstraint(inferredType, normExpectedType, `Check general case`);
}

interface ElaborationResult { term: Term; type: Term; }

function elaborate(term: Term, expectedType?: Term, initialCtx: Context = emptyCtx): ElaborationResult {
    constraints.length = 0; nextHoleId = 0; nextVarId = 0; // Reset for this top-level call

    let finalTypeToReport: Term;
    try {
        if (expectedType) {
            check(initialCtx, term, expectedType);
            finalTypeToReport = expectedType;
        } else {
            finalTypeToReport = infer(initialCtx, term);
        }

        if (!solveConstraints(initialCtx)) {
            const fc = constraints.find(c => !areEqual(getTermRef(c.t1), getTermRef(c.t2), initialCtx));
            const fcMsg = fc ? `${printTerm(fc.t1)} vs ${printTerm(fc.t2)} (orig: ${fc.origin})` : "Unknown";
            throw new Error(`Type error: Could not solve constraints. Approx failing: ${fcMsg}`);
        }
    } catch (e) {
        // console.error(`Elaboration error: ${(e as Error).message} \nStack: ${(e as Error).stack}`);
        throw e; // Re-throw
    }

    const elaboratedTerm = normalize(term, initialCtx);
    const finalTypeNormalized = normalize(finalTypeToReport, initialCtx);
    return { term: elaboratedTerm, type: finalTypeNormalized };
}

// --- Pattern Matching and Rewrite Rule Application ---
function ptermIsBaseTerm(pt: PatternTerm): pt is BaseTerm {
    return pt.tag !== 'PatternVar';
}

function matchPattern(
    pattern: PatternTerm, term: Term, ctx: Context,
    patternVarDecls: Array<{name: string, type: Term}>,
    currentSubst?: Substitution, stackDepth = 0
): Substitution | null {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("matchPattern stack depth exceeded");

    const subst = currentSubst || new Map<string, Term>();
    const normTerm = whnf(term, ctx, stackDepth + 1); // Match against WHNF

    if (pattern.tag === 'PatternVar') {
        const pvarName = pattern.name;
        const existing = subst.get(pvarName);
        if (existing) return areEqual(normTerm, existing, ctx, stackDepth + 1) ? subst : null;
        subst.set(pvarName, normTerm);
        return subst;
    }
    const rt = getTermRef(normTerm);
    if (rt.tag === 'Hole') return null;
    if (pattern.tag !== rt.tag) return null;

    switch (pattern.tag) {
        case 'Type': return subst;
        case 'Var': return pattern.name === (rt as typeof pattern).name ? subst : null;
        case 'App': {
            const termApp = rt as typeof pattern;
            const s1 = matchPattern(pattern.func, termApp.func, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s1) return null;
            return matchPattern(pattern.arg, termApp.arg, ctx, patternVarDecls, s1, stackDepth + 1);
        }
        // Simplified Lam/Pi matching for first-order patterns:
        // Assume pattern variables don't bind variables within the matched term's body.
        // If a Lam/Pi pattern appears, it's matched structurally, or an inner part is a PVar.
        case 'Lam':
        case 'Pi': return areEqual(pattern, rt, ctx, stackDepth + 1) ? subst : null; // Fallback
        case 'Hole': return null;
    }
    return null;
}

function applySubstToPatternTerm(
    pt: PatternTerm, subst: Substitution,
    patternVarDecls: Array<{name: string, type: Term}> // To identify PVars appearing as Var
): Term {
    if (pt.tag === 'PatternVar') {
        const r = subst.get(pt.name);
        if (!r) throw new Error(`Unbound PVar ${pt.name} in RHS subst`); return r;
    }
    if (pt.tag === 'Var' && patternVarDecls.some(pvd => pvd.name === pt.name)) {
        const r = subst.get(pt.name);
        if (!r) throw new Error(`Unbound PVar ${pt.name} (as Var) in RHS subst`); return r;
    }
    if (!ptermIsBaseTerm(pt)) throw new Error("Invalid PatternTerm structure in RHS");

    switch (pt.tag) {
        case 'Type': case 'Var': case 'Hole': return pt;
        case 'App':
            return App(
                applySubstToPatternTerm(pt.func, subst, patternVarDecls),
                applySubstToPatternTerm(pt.arg, subst, patternVarDecls)
            );
        case 'Lam':
            const lamParam = pt.paramType ? applySubstToPatternTerm(pt.paramType, subst, patternVarDecls) : undefined;
            const newLam = Lam(pt.paramName, v => applySubstToPatternTerm(pt.body(v), subst, patternVarDecls), lamParam);
            (newLam as {_isAnnotated?: boolean})._isAnnotated = pt._isAnnotated;
            return newLam;
        case 'Pi':
            return Pi(pt.paramName, applySubstToPatternTerm(pt.paramType, subst, patternVarDecls),
                v => applySubstToPatternTerm(pt.bodyType(v), subst, patternVarDecls)
            );
    }
    throw new Error(`applySubstToPatternTerm: unhandled tag ${(pt as any).tag}`);
}

function checkRewriteRule(rule: RewriteRule, baseCtx: Context): boolean {
    let patternCtx = baseCtx;
    const pVarAsVarMap: { [key: string]: Term } = {};
    for (const pv of rule.patternVars) {
        patternCtx = extendCtx(patternCtx, pv.name, pv.type);
        pVarAsVarMap[pv.name] = Var(pv.name);
    }

    function rulePartToTerm(pt: PatternTerm): Term {
        if (pt.tag === 'PatternVar') return pVarAsVarMap[pt.name];
        if (pt.tag === 'Var' && pVarAsVarMap[pt.name]) return pVarAsVarMap[pt.name];
        if (!ptermIsBaseTerm(pt)) throw new Error("Invalid structure in rulePartToTerm");
        switch (pt.tag) {
            case 'Type': case 'Var': case 'Hole': return pt;
            case 'App': return App(rulePartToTerm(pt.func), rulePartToTerm(pt.arg));
            case 'Lam':
                const lamP = pt.paramType ? rulePartToTerm(pt.paramType) : undefined;
                const nLam = Lam(pt.paramName, v => rulePartToTerm(pt.body(v)), lamP);
                (nLam as {_isAnnotated?:boolean})._isAnnotated = pt._isAnnotated;
                return nLam;
            case 'Pi': return Pi(pt.paramName, rulePartToTerm(pt.paramType), v => rulePartToTerm(pt.bodyType(v)));
        }
        throw new Error(`rulePartToTerm: unhandled tag ${(pt as any).tag}`);
    }

    const ruleCheckConstraints: Constraint[] = []; // Use a local constraint store for rule checking
    const originalConstraintsRef = constraints; // Save global constraints
    (globalThis as any).constraints = ruleCheckConstraints; // Temporarily override global for this check

    try {
        const lhsAsTerm = rulePartToTerm(rule.lhs);
        const rhsAsTerm = rulePartToTerm(rule.rhs);
        const lhsType = infer(patternCtx, lhsAsTerm);
        const rhsType = infer(patternCtx, rhsAsTerm);
        addConstraint(lhsType, rhsType, `Rewrite rule ${rule.name} type preservation`);
        if (!solveConstraints(patternCtx)) {
            console.error(`Rule ${rule.name} does not preserve types.`);
            return false;
        }
        return true;
    } catch (e) {
        console.error(`Error checking rule ${rule.name}: ${(e as Error).message}`);
        return false;
    } finally {
        (globalThis as any).constraints = originalConstraintsRef; // Restore global constraints
    }
}


// --- Pretty Printer (ensure stackDepth for recursive calls) ---
function printTerm(term: Term | PatternTerm, boundVars: string[] = [], stackDepth = 0): string {
    if (stackDepth > MAX_STACK_DEPTH) return "<print_depth_exceeded>";
    if (!term) return "<null_term>";

    if (term.tag === 'PatternVar') return `?${term.name}`;
    const current = (term.tag === 'Hole' && term.ref) ? getTermRef(term) : term;
    if (current.tag === 'PatternVar') return `?${current.name}`;

    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return current.name;
        case 'Hole':
            let s = current.id;
            // Avoid printing elaboratedType if it's too complex or recursive during print
            // if (current.elaboratedType) s += `(:${printTerm(current.elaboratedType, boundVars, stackDepth + 1)})`;
            return s;
        case 'Lam': {
            const paramName = current.paramName || `x${boundVars.length}`;
            const typeAnnotation = current._isAnnotated && current.paramType ? ` : ${printTerm(current.paramType, boundVars, stackDepth + 1)}` : '';
            return `(λ ${paramName}${typeAnnotation}. ${printTerm(current.body(Var(paramName)), [...boundVars, paramName], stackDepth + 1)})`;
        }
        case 'App':
            return `(${printTerm(current.func, boundVars, stackDepth + 1)} ${printTerm(current.arg, boundVars, stackDepth + 1)})`;
        case 'Pi': {
            const paramName = current.paramName || `x${boundVars.length}`;
            return `(Π ${paramName} : ${printTerm(current.paramType, boundVars, stackDepth + 1)}. ${printTerm(current.bodyType(Var(paramName)), [...boundVars, paramName], stackDepth + 1)})`;
        }
    }
    return "<unknown_term>";
}

function resetMyLambdaPi() {
    constraints.length = 0; globalDefs.clear(); userRewriteRules.length = 0;
    nextVarId = 0; nextHoleId = 0;
    (globalThis as any).constraints = constraints; // Ensure global constraints points to the main array
}


// --- Example Usage (Copied from previous, with resetMyLambdaPi calls) ---
console.log("--- MyLambdaPi Final: Bidirectional, Unification, Defs, Rewrite Rules ---");

const Nat = Var("Nat");
const Bool = Var("Bool");

try {
    resetMyLambdaPi();
    defineGlobal("Nat", Type());
    defineGlobal("Bool", Type());
    defineGlobal("zero", Nat);
    defineGlobal("succ", Pi("n", Nat, _ => Nat));
    defineGlobal("true", Bool);
    defineGlobal("expectsNatFunc", Pi("f", Pi("_", Nat, _ => Nat), _ => Bool));

    const baseCtx = emptyCtx;

    console.log("\n--- Example 1: Infer (λx:Nat. x) ---");
    const idNatAnnotated = Lam("x", x => x, Nat);
    let result = elaborate(idNatAnnotated, undefined, baseCtx);
    console.log(`   Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    const expectedT1 = Pi("x", Nat, _ => Nat);
    if (!areEqual(result.type, expectedT1, baseCtx)) throw new Error("Type mismatch for ex1");
    console.log("   Correct.");

    console.log("\n--- Example 2: Check (λx. x) against (Πx:Nat. Nat) ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type());
    const idUnannotated = Lam("x", x => x);
    const targetType2 = Pi("x", Nat, _ => Nat);
    result = elaborate(idUnannotated, targetType2, baseCtx);
    console.log(`   Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    if (!areEqual(result.type, targetType2, baseCtx)) throw new Error("Type mismatch for ex2 type");
    const elaboratedLam2 = getTermRef(result.term);
    if (elaboratedLam2.tag === 'Lam' && elaboratedLam2._isAnnotated && elaboratedLam2.paramType && areEqual(elaboratedLam2.paramType, Nat, baseCtx)) {
         console.log("   Correct, lambda param annotated.");
    } else {
        throw new Error(`Lambda not annotated as expected for ex2. Got: ${printTerm(elaboratedLam2)}`);
    }

    console.log("\n--- Example 3: Infer (λx. x) ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type());
    const idUnannotatedInfer = Lam("x", x => x);
    result = elaborate(idUnannotatedInfer, undefined, baseCtx);
    console.log(`   Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    const resT3 = getTermRef(result.type);
    if (resT3.tag === 'Pi' && getTermRef(resT3.paramType).tag === 'Hole') {
        const paramHole = getTermRef(resT3.paramType) as Term & {tag:'Hole'};
        const bodyYieldsParamHole = areEqual(resT3.bodyType(Var("_")), paramHole, baseCtx);
        if (bodyYieldsParamHole) {
             console.log(`   Correct: Type is Πx:${paramHole.id}. ${paramHole.id}`);
        } else throw new Error("Body type of Pi does not match param hole for ex3");
    } else throw new Error("Inferred type for unannotated id not Pi with hole for ex3: " + printTerm(resT3));

    console.log("\n--- Example 4: Check ((λx:Nat. x) ?argHole) against Nat ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type());
    const idFunc4 = Lam("x", x => x, Nat);
    const myHole4 = Hole("argHole");
    const appWithHole4 = App(idFunc4, myHole4);
    result = elaborate(appWithHole4, Nat, baseCtx);
    console.log(`   Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    if(getTermRef(result.term).id !== myHole4.id) throw new Error(`Term not ${myHole4.id} for ex4, got ${printTerm(result.term)}`);
    const typeOfMyHole4 = myHole4.elaboratedType ? getTermRef(myHole4.elaboratedType) : Type() /* dummy */;
    console.log(`   Type of ?argHole: ${printTerm(typeOfMyHole4)}`);
    if (!areEqual(typeOfMyHole4, Nat, baseCtx)) throw new Error("Hole type not Nat for ex4: " + printTerm(typeOfMyHole4));
    console.log("   Correct.");

    console.log("\n--- Example 5: Infer (λf. λx. f x) ---");
    resetMyLambdaPi();
    const complexLam5 = Lam("f", f => Lam("x", x => App(f, x)));
    result = elaborate(complexLam5, undefined, baseCtx);
    console.log(`   Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    const resT5 = getTermRef(result.type);
    if (resT5.tag === 'Pi') {
        const typeOfF = getTermRef(resT5.paramType);
        const bodyTypeOuter = getTermRef(resT5.bodyType(Var("dummyF")));
        if (typeOfF.tag === 'Pi' && getTermRef(typeOfF.paramType).tag === 'Hole' &&
            bodyTypeOuter.tag === 'Pi' && getTermRef(bodyTypeOuter.paramType).tag === 'Hole' &&
            (getTermRef(typeOfF.paramType) as Term & {tag:'Hole'}).id === (getTermRef(bodyTypeOuter.paramType) as Term & {tag:'Hole'}).id) {
            const typeOfF_body = getTermRef(typeOfF.bodyType(Var("dummyY")));
            const bodyTypeOuter_body = getTermRef(bodyTypeOuter.bodyType(Var("dummyX")));
            if (typeOfF_body.tag === 'Hole' && bodyTypeOuter_body.tag === 'Hole' &&
                (typeOfF_body as Term & {tag:'Hole'}).id === (bodyTypeOuter_body as Term & {tag:'Hole'}).id) {
                console.log(`   Correct type structure: Πf:(Πy:${(getTermRef(typeOfF.paramType) as Term & {tag:'Hole'}).id}. ${(typeOfF_body as Term & {tag:'Hole'}).id}). Πx:${(getTermRef(bodyTypeOuter.paramType) as Term & {tag:'Hole'}).id}. ${(bodyTypeOuter_body as Term & {tag:'Hole'}).id}`);
            } else throw new Error("?B holes do not match for ex5: " +printTerm(typeOfF_body) + " vs " + printTerm(bodyTypeOuter_body));
        } else throw new Error("?A holes do not match or structure incorrect for ex5: " + printTerm(resT5));
    } else throw new Error("Overall type not Pi for ex5");

    console.log("\n--- Example 6: Check (λx:Nat. x) against Bool (expected error) ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type()); defineGlobal("Bool", Type());
    const idNat6 = Lam("x", x => x, Nat);
    try {
        elaborate(idNat6, Bool, baseCtx);
        console.error("   Error: Type error was NOT caught for ex6.");
    } catch (e) {
        console.log(`   Correctly caught error: ${(e as Error).message.slice(0,150)}...`);
    }

    console.log("\n--- Example 7: Infer (expectsNatFunc ?f_hole) ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type()); defineGlobal("Bool", Type());
    defineGlobal("expectsNatFunc", Pi("f", Pi("_", Nat, _ => Nat), _ => Bool));
    const fHole7 = Hole("f_hole");
    const appTerm7 = App(Var("expectsNatFunc"), fHole7);
    result = elaborate(appTerm7, undefined, baseCtx);
    console.log(`   Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    if (!areEqual(result.type, Bool, baseCtx)) throw new Error("App result type not Bool for ex7");
    const typeOfFHole7 = fHole7.elaboratedType ? getTermRef(fHole7.elaboratedType) : Type() /* dummy */;
    const expectedFHoleType7 = Pi("_", Nat, _ => Nat);
    console.log(`   Type of ?f_hole: ${printTerm(typeOfFHole7)}`);
    if (!areEqual(typeOfFHole7, expectedFHoleType7, baseCtx)) throw new Error("Hole type for f not Nat->Nat for ex7: " + printTerm(typeOfFHole7));
    console.log("   Correct.");

    console.log("\n--- Example 8: Nat = Bool constraint (expected error) ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type()); defineGlobal("Bool", Type());
    constraints.length = 0; addConstraint(Nat, Bool, "Nat = Bool direct test");
    if (solveConstraints(baseCtx)) {
        console.error("   Error: Nat = Bool constraint incorrectly solved for ex8.");
    } else {
        console.log("   Correctly failed to solve Nat = Bool constraint.");
    }
    constraints.length = 0;

    console.log("\n--- Example 9: Check polymorphic id against concrete type ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type());
    const polyId9 = Lam("f", f => Lam("x", x => App(f, x)));
    const concretePiType9 = Pi("f", Pi("_y", Nat, _ => Nat), _fVal => Pi("_x", Nat, _xVal => Nat));
    result = elaborate(polyId9, concretePiType9, baseCtx);
    console.log(`   Term (Elaborated): ${printTerm(result.term)}`);
    console.log(`   Type (Checked): ${printTerm(result.type)}`);
    if (!areEqual(result.type, concretePiType9, baseCtx)) throw new Error("Type mismatch for ex9");
    const elabTerm9 = getTermRef(result.term);
    if(elabTerm9.tag === 'Lam' && elabTerm9._isAnnotated && elabTerm9.paramType && getTermRef(elabTerm9.paramType).tag === 'Pi' &&
      (getTermRef(elabTerm9.paramType) as Term & {tag:'Pi'}).paramType === Nat &&
      (getTermRef(elabTerm9.paramType) as Term & {tag:'Pi'}).bodyType(Var("_")) === Nat &&
      (getTermRef(elabTerm9.body(Var("f"))) as Term & {tag:'Lam'})._isAnnotated &&
      (getTermRef(elabTerm9.body(Var("f"))) as Term & {tag:'Lam'}).paramType === Nat
    ) {
        console.log("   Correct (term structure suggests annotation).");
    } else {
        throw new Error("Term not fully annotated as expected for ex9: " + printTerm(elabTerm9));
    }

    console.log("\n--- Example 10: Delta Reduction ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type()); defineGlobal("zero", Nat);
    defineGlobal("succ", Pi("_", Nat, _ => Nat));
    defineGlobal("one", Nat, App(Var("succ"), Var("zero")));
    result = elaborate(Var("one"), Nat, baseCtx);
    console.log(`   Term (Var("one")): ${printTerm(Var("one"))}`);
    console.log(`   Elaborated Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    if (!areEqual(result.term, App(Var("succ"), Var("zero")), baseCtx)) throw new Error("Delta reduction failed for ex10: " + printTerm(result.term));
    console.log("   Correct.");

    console.log("\n--- Example 11: Rewrite Rule ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type()); defineGlobal("zero", Nat);
    defineGlobal("succ", Pi("_", Nat, _ => Nat));
    defineGlobal("add", Pi("_", Nat, _ => Pi("__", Nat, _ => Nat)));
    const pvarN = { name: "N", type: Nat };
    const ruleAddZ: RewriteRule = {
        name: "add_Z_N", patternVars: [pvarN],
        lhs: App(App(Var("add"), Var("zero")), MPatternVar("N")),
        rhs: MPatternVar("N")
    };
    if (checkRewriteRule(ruleAddZ, baseCtx)) {
        addRewriteRule(ruleAddZ); console.log(`   Rule ${ruleAddZ.name} added.`);
    } else { throw new Error(`Rule ${ruleAddZ.name} failed type preservation check for ex11.`); }
    const termToAdd = App(App(Var("add"), Var("zero")), App(Var("succ"), Var("zero")));
    result = elaborate(termToAdd, Nat, baseCtx);
    console.log(`   Original term: add zero (succ zero)`);
    console.log(`   Elaborated Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    if (!areEqual(result.term, App(Var("succ"), Var("zero")), baseCtx)) throw new Error("Rewrite rule application failed for ex11: " + printTerm(result.term));
    console.log("   Correct.");

} catch (e) {
    console.error("\n*** A TEST SCENARIO FAILED ***");
    console.error((e as Error).message);
    console.error((e as Error).stack);
}