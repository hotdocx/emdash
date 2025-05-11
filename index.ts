// --- MyLambdaPi Final Corrected: Bidirectional, Unification, Defs, Rewrite Rules ---

// --- Report on Changed Specification (Same as previous detailed report) ---
// This implementation focuses on a core lambda calculus with Pi types,
// bidirectional type checking, unification-based hole solving,
// user-defined global symbols with delta reduction, and
// user-provided first-order rewrite rules with type preservation checks.
// Identity types are omitted.
// Fixes for previous errors related to lambda elaboration, hole type querying,
// and TypeScript type errors are included.
// --- End Report ---

let nextVarId = 0;
const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarId++}`;

let nextHoleId = 0;
const freshHoleName = (): string => `?h${nextHoleId++}`;

// --- Term and PatternTerm Types ---
// PatternVar is only a tag for the pattern structure, not a full Term itself.
// In LHS/RHS of rules, actual pattern variables are represented as Var nodes
// whose names are declared in rule.patternVars.

type BaseTerm =
    | { tag: 'Type' }
    | { tag: 'Var', name: string }
    | { tag: 'Lam', paramName: string, paramType?: Term, body: (v: Term) => Term, _isAnnotated: boolean }
    | { tag: 'App', func: Term, arg: Term }
    | { tag: 'Pi', paramName: string, paramType: Term, bodyType: (v: Term) => Term }
    | { tag: 'Hole', id: string, ref?: Term, elaboratedType?: Term };

type Term = BaseTerm;

// For rule definition, LHS/RHS can conceptually include pattern variables.
// We'll represent these as `Var` nodes whose names are in `rule.patternVars`.
// PatternTerm is mostly for conceptual clarity during rule definition; the actual
// structure stored in rule.lhs/rhs will be `Term`.
type PatternVarDecl = { name: string, type: Term };
// PatternTerm is not strictly needed as a separate type if we use Var for pattern vars.


// --- Constructors ---
const Type = (): Term => ({ tag: 'Type' });
const Var = (name: string): Term & { tag: 'Var' } => ({ tag: 'Var', name });
const Lam = (paramName: string, body: (v: Term) => Term, paramType?: Term): Term & { tag: 'Lam' } =>
    ({ tag: 'Lam', paramName, paramType, body, _isAnnotated: !!paramType });
const App = (func: Term, arg: Term): Term => ({ tag: 'App', func, arg });
const Pi = (paramName: string, paramType: Term, bodyType: (v: Term) => Term): Term =>
    ({ tag: 'Pi', paramName, paramType, bodyType });

const Hole = (id?: string): Term & { tag: 'Hole' } => {
    const holeId = id || freshHoleName();
    return { tag: 'Hole', id: holeId, ref: undefined, elaboratedType: undefined };
};

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
    patternVars: PatternVarDecl[];
    lhs: Term; // LHS is a Term where some Vars are pattern vars
    rhs: Term; // RHS is a Term where some Vars are pattern vars
}
const userRewriteRules: RewriteRule[] = [];

function addRewriteRule(rule: RewriteRule) {
    userRewriteRules.push(rule);
}

type Substitution = Map<string, Term>; // Maps pattern var name to Term


// --- Constraints and Unification ---
interface Constraint { t1: Term; t2: Term; origin?: string; }
let constraints: Constraint[] = []; // Changed to let for resetMyLambdaPi

function addConstraint(t1: Term, t2: Term, origin?: string) {
    constraints.push({ t1, t2, origin });
}

function getTermRef(term: Term): Term {
    if (term.tag === 'Hole' && term.ref) return getTermRef(term.ref);
    return term;
}


// --- Normalization (WHNF and Full) ---
const MAX_RECURSION_DEPTH = 100;
const MAX_STACK_DEPTH = 70;

function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("WHNF stack depth exceeded");
    let current = getTermRef(term);
    let iterationTerm = current; // Term at the start of the current fixed-point iteration

    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        const prevIterationTerm = iterationTerm; // Save term from start of *this* iteration

        // 1. Delta Reduction
        if (current.tag === 'Var') {
            const gdef = globalDefs.get(current.name);
            if (gdef && gdef.value) {
                current = getTermRef(gdef.value);
            }
        }

        // 2. Rewrite Rules
        let ruleAppliedThisIter = false;
        for (const rule of userRewriteRules) {
            const subst = matchPattern(rule.lhs, current, ctx, rule.patternVars, undefined, stackDepth + 1);
            if (subst) {
                current = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                ruleAppliedThisIter = true;
                break;
            }
        }
        
        iterationTerm = current; // Update term for next fixed-point check
        // If no change after delta and one rule pass, break fixed-point loop
        if (areEqual(prevIterationTerm, iterationTerm, ctx, stackDepth + 1)) {
            break;
        }
        if (i === MAX_RECURSION_DEPTH -1) console.warn("WHNF reached max iterations for delta/rules");
    }
    // current is now the result of delta/rewrite reductions at this level.

    // 3. Beta Reduction
    current = getTermRef(current); // Re-chase refs after delta/rules
    if (current.tag === 'App') {
        const funcNorm = whnf(current.func, ctx, stackDepth + 1);
        if (funcNorm.tag === 'Lam') {
            return whnf(funcNorm.body(current.arg), ctx, stackDepth + 1);
        }
        if (funcNorm !== getTermRef(current.func)) return App(funcNorm, current.arg);
        return current;
    }
    return current;
}

function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("Normalize stack depth exceeded");
    let current = getTermRef(term);
    let iterationTerm = current;

    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        const prevIterationTerm = iterationTerm;
        if (current.tag === 'Var') {
            const gdef = globalDefs.get(current.name);
            if (gdef && gdef.value) {
                current = getTermRef(gdef.value);
            }
        }
        let ruleAppliedThisIter = false;
        for (const rule of userRewriteRules) {
            const subst = matchPattern(rule.lhs, current, ctx, rule.patternVars, undefined, stackDepth + 1);
            if (subst) {
                current = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                ruleAppliedThisIter = true;
                break;
            }
        }
        iterationTerm = current;
        if (areEqual(prevIterationTerm, iterationTerm, ctx, stackDepth + 1)) break;
        if (i === MAX_RECURSION_DEPTH -1) console.warn("Normalize reached max iterations for delta/rules");
    }
    current = getTermRef(current);

    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': return current;
        case 'Lam':
            const lamParamTypeRef = current.paramType ? getTermRef(current.paramType) : undefined;
            const normLamParamType = lamParamTypeRef ? normalize(lamParamTypeRef, ctx, stackDepth + 1) : undefined;
            
            // For HOAS body, normalization should "look inside" by applying to a generic var
            // and normalizing the result in an appropriately extended context.
            const newLam = Lam(current.paramName,
                (v_arg: Term) => {
                    // The context for normalizing body(v_arg) should be the original context 'ctx'
                    // extended with v_arg : (type of param).
                    const paramTypeForBodyCtx = normLamParamType || (current._isAnnotated && current.paramType ? getTermRef(current.paramType) : Hole());
                    // If v_arg is a Var, its name should be fresh or match current.paramName
                    let bodyCtx = ctx;
                    if (v_arg.tag === 'Var') { // This is typical for HOAS
                        bodyCtx = extendCtx(ctx, v_arg.name, paramTypeForBodyCtx);
                    }
                    return normalize(current.body(v_arg), bodyCtx, stackDepth + 1);
                },
                normLamParamType);
            newLam._isAnnotated = current._isAnnotated;
            return newLam;
        case 'App':
            const normFunc = normalize(current.func, ctx, stackDepth + 1);
            const normArg = normalize(current.arg, ctx, stackDepth + 1);
            if (normFunc.tag === 'Lam') {
                return normalize(normFunc.body(normArg), ctx, stackDepth + 1); // Beta reduction
            }
            return App(normFunc, normArg);
        case 'Pi':
            const normPiParamType = normalize(current.paramType, ctx, stackDepth + 1);
            const newPi = Pi(current.paramName, normPiParamType,
                (v_arg: Term) => {
                    let bodyTypeCtx = ctx;
                    if (v_arg.tag === 'Var') {
                        bodyTypeCtx = extendCtx(ctx, v_arg.name, normPiParamType);
                    }
                    return normalize(current.bodyType(v_arg), bodyTypeCtx, stackDepth + 1);
                });
            return newPi;
    }
    throw new Error(`normalize: Unhandled term tag ${(current as Term).tag}`);
}


// --- Equality and Unification ---
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
            if (rt1._isAnnotated !== lam2._isAnnotated) return false;
            if (rt1._isAnnotated) { // Both should be annotated
                if (!rt1.paramType || !lam2.paramType || !areEqual(rt1.paramType, lam2.paramType, ctx, depth + 1)) return false;
            }
            const freshV = Var(freshVarName(rt1.paramName));
            const CtxType = rt1.paramType ? getTermRef(rt1.paramType) : Hole();
            const extendedCtx = extendCtx(ctx, freshV.name, CtxType);
            return areEqual(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const pi2 = rt2 as typeof rt1;
            if (!areEqual(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            const freshV = Var(freshVarName(rt1.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(rt1.paramType));
            return areEqual(rt1.bodyType(freshV), pi2.bodyType(freshV), extendedCtx, depth + 1);
        }
    }
    return false;
}

function termContainsHole(term: Term, holeId: string, visited: Set<string>, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) return false;

    const current = getTermRef(term);
    if (current.tag === 'Hole') return current.id === holeId;

    const termStr = printTerm(current, [], 0); // Simple print for visited set key
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
            // HOAS body - occurs check simplification: for `?h = λx. ...?h...`
            // This is complex. A common simplification is to not allow a hole to be instantiated
            // with a function that *closes over* that same hole.
            // The `visited` set helps for non-HOAS cycles.
            return false;
        }
        case 'Pi': {
            const paramTypeContains = termContainsHole(current.paramType, holeId, visited, depth + 1);
            if (paramTypeContains) return true;
            return false;
        }
    }
    return false;
}


function unify(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Unification stack depth exceeded`);

    const rt1 = getTermRef(t1);
    const rt2 = getTermRef(t2);

    if (rt1 === rt2 && rt1.tag !== 'Hole') return true;
    if (areEqual(rt1, rt2, ctx, depth + 1)) return true;

    if (rt1.tag === 'Hole') return unifyHole(rt1, rt2, ctx, depth + 1);
    if (rt2.tag === 'Hole') return unifyHole(rt2, rt1, ctx, depth + 1);

    if (rt1.tag !== rt2.tag) return false;

    switch (rt1.tag) {
        case 'Type': return rt2.tag === 'Type'; // Type = Type
        case 'Var': return rt2.tag === 'Var' && rt1.name === rt2.name;
        case 'App':
            return rt2.tag === 'App' &&
                   unify(rt1.func, rt2.func, ctx, depth + 1) &&
                   unify(rt1.arg, rt2.arg, ctx, depth + 1);
        case 'Lam': {
            if (rt2.tag !== 'Lam') return false;
            if (rt1._isAnnotated !== rt2._isAnnotated) return false;
            if (rt1._isAnnotated) {
                if (!rt1.paramType || !rt2.paramType || !unify(rt1.paramType, rt2.paramType, ctx, depth + 1)) return false;
            }
            const freshV = Var(freshVarName(rt1.paramName));
            const CtxType = rt1.paramType ? getTermRef(rt1.paramType) : Hole();
            const extendedCtx = extendCtx(ctx, freshV.name, CtxType);
            return unify(rt1.body(freshV), rt2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': {
            if (rt2.tag !== 'Pi') return false;
            if (!unify(rt1.paramType, rt2.paramType, ctx, depth + 1)) return false;
            const freshV = Var(freshVarName(rt1.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(rt1.paramType));
            return unify(rt1.bodyType(freshV), rt2.bodyType(freshV), extendedCtx, depth + 1);
        }
    }
    return false;
}

function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
    const normTerm = getTermRef(term);

    if (normTerm.tag === 'Hole') {
        if (hole.id === normTerm.id) return true;
        // Canonicalize: smaller ID points to larger ID, or some other consistent rule
        if (hole.id < normTerm.id) {
             (normTerm as Term & {tag:'Hole'}).ref = hole;
        } else {
            hole.ref = normTerm;
        }
        return true;
    }
    if (termContainsHole(normTerm, hole.id, new Set(), depth + 1)) {
        // console.warn(`Occurs check failed: ${hole.id} in ${printTerm(normTerm)}`);
        return false;
    }
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
            } catch (e) {
                return false;
            }
        }
    }
    if (iterations >= maxIterations && changedInIteration) { /* console.warn("Constraint solving max iterations."); */ }
    for (const constraint of constraints) {
        if (!areEqual(constraint.t1, constraint.t2, ctx, stackDepth + 1)) {
            return false;
        }
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
            current.elaboratedType = newTypeForHole; // Mutate to store its type
            return newTypeForHole;
        case 'App': {
            const funcType = infer(ctx, current.func, stackDepth + 1);
            const normFuncType = whnf(funcType, ctx, stackDepth + 1);
            if (normFuncType.tag === 'Hole') {
                const argTypeHole = Hole(freshHoleName());
                const resultTypeHole = Hole(freshHoleName());
                const freshPN = freshVarName("appArg");
                addConstraint(normFuncType, Pi(freshPN, argTypeHole, _ => resultTypeHole), `App func type hole`);
                check(ctx, current.arg, argTypeHole, stackDepth + 1);
                return resultTypeHole;
            }
            if (normFuncType.tag !== 'Pi') throw new Error(`Cannot apply non-function: ${printTerm(current.func)} : ${printTerm(normFuncType)}`);
            check(ctx, current.arg, normFuncType.paramType, stackDepth + 1);
            return normFuncType.bodyType(current.arg);
        }
        case 'Lam': {
            const paramName = current.paramName; // Use given name
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
            const paramName = current.paramName;
            const extendedCtx = extendCtx(ctx, paramName, current.paramType);
            check(extendedCtx, current.bodyType(Var(paramName)), Type(), stackDepth + 1);
            return Type();
        }
    }
    throw new Error(`infer: Unhandled term tag ${(current as Term).tag}`);
}

function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0): void {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Check stack depth exceeded`);
    const current = getTermRef(term); // Important to chase refs for `term` as well
    const normExpectedType = whnf(expectedType, ctx, stackDepth + 1);

    if (current.tag === 'Lam' && !current._isAnnotated && normExpectedType.tag === 'Pi') {
        const paramName = current.paramName;
        current.paramType = normExpectedType.paramType; // Mutate for elaboration
        current._isAnnotated = true;
        const extendedCtx = extendCtx(ctx, paramName, normExpectedType.paramType);
        check(extendedCtx, current.body(Var(paramName)), normExpectedType.bodyType(Var(paramName)), stackDepth + 1);
        return;
    }
    if (current.tag === 'Hole') {
        const inferredHoleType = infer(ctx, current, stackDepth + 1); // This gets/sets current.elaboratedType
        addConstraint(inferredHoleType, normExpectedType, `Hole ${current.id} checked`);
        return;
    }
    const inferredType = infer(ctx, current, stackDepth + 1);
    addConstraint(inferredType, normExpectedType, `Check general case: ${printTerm(current)} : ${printTerm(inferredType)} vs ${printTerm(normExpectedType)}`);
}

interface ElaborationResult { term: Term; type: Term; }

function elaborate(term: Term, expectedType?: Term, initialCtx: Context = emptyCtx): ElaborationResult {
    constraints = []; nextHoleId = 0; nextVarId = 0;

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
            const fcMsg = fc ? `${printTerm(getTermRef(fc.t1))} vs ${printTerm(getTermRef(fc.t2))} (orig: ${fc.origin})` : "Unknown constraint";
            throw new Error(`Type error: Could not solve constraints. Approx failing: ${fcMsg}`);
        }
    } catch (e) {
        throw e;
    }

    const elaboratedTerm = normalize(term, initialCtx);
    const finalTypeNormalized = normalize(finalTypeToReport, initialCtx);
    return { term: elaboratedTerm, type: finalTypeNormalized };
}

// --- Pattern Matching and Rewrite Rule Application ---
// Helper to check if a Var name is a declared pattern variable
function isPatternVarName(name: string, patternVarDecls: PatternVarDecl[]): boolean {
    return patternVarDecls.some(pvd => pvd.name === name);
}

function matchPattern(
    pattern: Term, term: Term, ctx: Context,
    patternVarDecls: PatternVarDecl[],
    currentSubst?: Substitution, stackDepth = 0
): Substitution | null {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("matchPattern stack depth exceeded");

    const subst = currentSubst || new Map<string, Term>();
    const normTerm = whnf(term, ctx, stackDepth + 1);

    // If pattern is Var and its name is in patternVarDecls, it's a pattern variable
    if (pattern.tag === 'Var' && isPatternVarName(pattern.name, patternVarDecls)) {
        const pvarName = pattern.name;
        const existing = subst.get(pvarName);
        if (existing) return areEqual(normTerm, existing, ctx, stackDepth + 1) ? subst : null;
        subst.set(pvarName, normTerm);
        return subst;
    }

    const rtPattern = getTermRef(pattern); // Pattern itself should not contain holes to be solved
    const rtTerm = getTermRef(normTerm);

    if (rtTerm.tag === 'Hole') return null; // Cannot match concrete pattern against hole term
    if (rtPattern.tag !== rtTerm.tag) return null;

    switch (rtPattern.tag) {
        case 'Type': return subst;
        case 'Var': // This is a constant Var in pattern, not a pattern variable
            return rtTerm.tag === 'Var' && rtPattern.name === rtTerm.name ? subst : null;
        case 'App': {
            if (rtTerm.tag !== 'App') return null;
            const s1 = matchPattern(rtPattern.func, rtTerm.func, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s1) return null;
            return matchPattern(rtPattern.arg, rtTerm.arg, ctx, patternVarDecls, s1, stackDepth + 1);
        }
        case 'Lam': {
            if (rtTerm.tag !== 'Lam') return null;
            // For first-order patterns, lambda parameters are not pattern variables.
            // Match parameter types if both annotated.
            if (rtPattern._isAnnotated !== rtTerm._isAnnotated) return null;
            if (rtPattern._isAnnotated) {
                 if (!rtPattern.paramType || !rtTerm.paramType) return null; // Should not happen
                 const sType = matchPattern(rtPattern.paramType, rtTerm.paramType, ctx, patternVarDecls, subst, stackDepth + 1);
                 if (!sType) return null;
            }
            // For bodies, we need to be careful. If the pattern's body contains
            // pattern variables, this simple equality check isn't enough.
            // For now, assume first-order means pattern vars don't appear *bound* inside pattern's lambda.
            // Fallback to areEqual for Lam/Pi bodies, which is HOAS-aware but won't bind pattern vars.
            // A more sophisticated matcher for patterns like `λx. ?F x` is needed for deeper HOAS patterns.
             return areEqual(rtPattern, rtTerm, ctx, stackDepth+1) ? subst : null;
        }
        case 'Pi': {
            if (rtTerm.tag !== 'Pi') return null;
             const sType = matchPattern(rtPattern.paramType, rtTerm.paramType, ctx, patternVarDecls, subst, stackDepth + 1);
             if (!sType) return null;
            return areEqual(rtPattern, rtTerm, ctx, stackDepth+1) ? subst : null; // Similar to Lam
        }
    }
    return null;
}

function applySubst(
    term: Term, subst: Substitution,
    patternVarDecls: PatternVarDecl[]
): Term {
    const current = getTermRef(term);

    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        const replacement = subst.get(current.name);
        if (!replacement) throw new Error(`Unbound PVar ${current.name} in RHS subst`);
        return replacement;
    }

    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': return current; // Var here is a non-pattern var
        case 'App':
            return App(
                applySubst(current.func, subst, patternVarDecls),
                applySubst(current.arg, subst, patternVarDecls)
            );
        case 'Lam':
            const lamParam = current.paramType ? applySubst(current.paramType, subst, patternVarDecls) : undefined;
            // HOAS body: if pattern variables are captured, they are substituted when `body(v)` is called.
            // This relies on substitution "distributing" over the HOAS function.
            // The body function itself is (v => bodyTerm). If bodyTerm contains a pattern var `?P`,
            // and `?P` is substituted by `S_P`, then the new body is effectively (v => bodyTerm[S_P/?P]).
            // This happens naturally if `applySubst` is called on the result of `current.body(v)`.
            const newLam = Lam(current.paramName,
                (v_arg: Term) => applySubst(current.body(v_arg), subst, patternVarDecls),
                lamParam
            );
            newLam._isAnnotated = current._isAnnotated;
            return newLam;
        case 'Pi':
            return Pi(current.paramName, applySubst(current.paramType, subst, patternVarDecls),
                (v_arg: Term) => applySubst(current.bodyType(v_arg), subst, patternVarDecls)
            );
    }
    throw new Error(`applySubst: unhandled tag ${(current as Term).tag}`);
}


function checkRewriteRule(rule: RewriteRule, baseCtx: Context): boolean {
    let patternCtx = baseCtx;
    for (const pv of rule.patternVars) {
        patternCtx = extendCtx(patternCtx, pv.name, pv.type);
    }

    const ruleCheckConstraintsBackup = [...constraints]; // Backup global constraints
    constraints = []; // Use a local constraint store for rule checking

    try {
        const lhsType = infer(patternCtx, rule.lhs);
        const rhsType = infer(patternCtx, rule.rhs);
        addConstraint(lhsType, rhsType, `Rewrite rule ${rule.name} type preservation`);
        if (!solveConstraints(patternCtx)) {
            console.error(`Rule ${rule.name} does not preserve types.`);
            const fc = constraints.find(c => !areEqual(getTermRef(c.t1), getTermRef(c.t2), patternCtx));
            if (fc) console.error(`  Failing constraint: ${printTerm(getTermRef(fc.t1))} = ${printTerm(getTermRef(fc.t2))}`);
            return false;
        }
        return true;
    } catch (e) {
        console.error(`Error checking rule ${rule.name}: ${(e as Error).message}`);
        return false;
    } finally {
        constraints = ruleCheckConstraintsBackup; // Restore global constraints
    }
}

// --- Pretty Printer ---
function printTerm(term: Term, boundVars: string[] = [], stackDepth = 0): string {
    if (stackDepth > MAX_STACK_DEPTH) return "<print_depth_exceeded>";
    if (!term) return "<null_term>";

    const current = getTermRef(term);

    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return current.name;
        case 'Hole':
            let s = current.id;
            // if (current.elaboratedType) s += `(:${printTerm(current.elaboratedType, boundVars, stackDepth + 1)})`;
            return s;
        case 'Lam': {
            const paramName = current.paramName; // Use the actual param name
            const typeAnnotation = current._isAnnotated && current.paramType ? ` : ${printTerm(current.paramType, boundVars, stackDepth + 1)}` : '';
            const freshV = Var(paramName); // Use paramName for the HOAS application
            return `(λ ${paramName}${typeAnnotation}. ${printTerm(current.body(freshV), [...boundVars, paramName], stackDepth + 1)})`;
        }
        case 'App':
            return `(${printTerm(current.func, boundVars, stackDepth + 1)} ${printTerm(current.arg, boundVars, stackDepth + 1)})`;
        case 'Pi': {
            const paramName = current.paramName;
            const freshV = Var(paramName);
            return `(Π ${paramName} : ${printTerm(current.paramType, boundVars, stackDepth + 1)}. ${printTerm(current.bodyType(freshV), [...boundVars, paramName], stackDepth + 1)})`;
        }
    }
    return "<unknown_term_in_print>";
}

function resetMyLambdaPi() {
    constraints = []; globalDefs.clear(); userRewriteRules.length = 0;
    nextVarId = 0; nextHoleId = 0;
}


// --- Example Usage (Copied and adapted for Var in rules) ---
console.log("--- MyLambdaPi Final Corrected: Bidirectional, Unification, Defs, Rewrite Rules ---");

const Nat = Var("Nat");
const Bool = Var("Bool");
const Zero = Var("zero"); // For rule convenience
const Succ = Var("succ");
const Add = Var("add");


try {
    resetMyLambdaPi();
    defineGlobal("Nat", Type());
    defineGlobal("Bool", Type());
    defineGlobal("zero", Nat);
    defineGlobal("succ", Pi("n", Nat, _ => Nat));
    defineGlobal("true", Bool);
    defineGlobal("expectsNatFunc", Pi("f", Pi("ff_arg", Nat, _ => Nat), _ => Bool));

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
        const freshV3 = Var(resT3.paramName); // Use the Pi's own param name
        const bodyYieldsParamHole = areEqual(resT3.bodyType(freshV3), paramHole, baseCtx);
        if (bodyYieldsParamHole) {
             console.log(`   Correct: Type is Π ${resT3.paramName}:${paramHole.id}. ${paramHole.id}`);
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
    if(getTermRef(result.term).tag !== 'Hole' || (getTermRef(result.term) as Term & {tag:'Hole'}).id !== myHole4.id) throw new Error(`Term not ${myHole4.id} for ex4, got ${printTerm(result.term)}`);
    const typeOfMyHole4 = myHole4.elaboratedType ? getTermRef(myHole4.elaboratedType) : Hole() /* dummy */;
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
        const bodyTypeOuter = getTermRef(resT5.bodyType(Var(resT5.paramName)));
        if (typeOfF.tag === 'Pi' && getTermRef(typeOfF.paramType).tag === 'Hole' &&
            bodyTypeOuter.tag === 'Pi' && getTermRef(bodyTypeOuter.paramType).tag === 'Hole' &&
            (getTermRef(typeOfF.paramType) as Term & {tag:'Hole'}).id === (getTermRef(bodyTypeOuter.paramType) as Term & {tag:'Hole'}).id) {
            const typeOfF_body = getTermRef(typeOfF.bodyType(Var(typeOfF.paramName)));
            const bodyTypeOuter_body = getTermRef(bodyTypeOuter.bodyType(Var(bodyTypeOuter.paramName)));
            if (typeOfF_body.tag === 'Hole' && bodyTypeOuter_body.tag === 'Hole' &&
                (typeOfF_body as Term & {tag:'Hole'}).id === (bodyTypeOuter_body as Term & {tag:'Hole'}).id) {
                console.log(`   Correct type structure: Π ${resT5.paramName}:(Π ${typeOfF.paramName}:${(getTermRef(typeOfF.paramType) as Term & {tag:'Hole'}).id}. ${(typeOfF_body as Term & {tag:'Hole'}).id}). Π ${bodyTypeOuter.paramName}:${(getTermRef(bodyTypeOuter.paramType) as Term & {tag:'Hole'}).id}. ${(bodyTypeOuter_body as Term & {tag:'Hole'}).id}`);
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
    defineGlobal("expectsNatFunc", Pi("f", Pi("ff_arg", Nat, _ => Nat), _ => Bool));
    const fHole7 = Hole("f_hole");
    const appTerm7 = App(Var("expectsNatFunc"), fHole7);
    result = elaborate(appTerm7, undefined, baseCtx);
    console.log(`   Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    if (!areEqual(result.type, Bool, baseCtx)) throw new Error("App result type not Bool for ex7");
    const typeOfFHole7 = fHole7.elaboratedType ? getTermRef(fHole7.elaboratedType) : Hole();
    const expectedFHoleType7 = Pi("ff_arg", Nat, _ => Nat);
    console.log(`   Type of ?f_hole: ${printTerm(typeOfFHole7)}`);
    if (!areEqual(typeOfFHole7, expectedFHoleType7, baseCtx)) throw new Error("Hole type for f not Nat->Nat for ex7: " + printTerm(typeOfFHole7));
    console.log("   Correct.");

    console.log("\n--- Example 8: Nat = Bool constraint (expected error) ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type()); defineGlobal("Bool", Type());
    constraints = []; addConstraint(Nat, Bool, "Nat = Bool direct test");
    if (solveConstraints(baseCtx)) {
        console.error("   Error: Nat = Bool constraint incorrectly solved for ex8.");
    } else {
        console.log("   Correctly failed to solve Nat = Bool constraint.");
    }
    constraints = [];

    console.log("\n--- Example 9: Check polymorphic id against concrete type ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type());
    const polyId9 = Lam("f", f => Lam("x", x => App(f, x)));
    const concretePiType9 = Pi("f", Pi("y", Nat, _ => Nat), _fVal => Pi("x", Nat, _xVal => Nat));
    result = elaborate(polyId9, concretePiType9, baseCtx);
    console.log(`   Term (Elaborated): ${printTerm(result.term)}`);
    console.log(`   Type (Checked): ${printTerm(result.type)}`);
    if (!areEqual(result.type, concretePiType9, baseCtx)) throw new Error("Type mismatch for ex9");
    const elabTerm9 = getTermRef(result.term);
    if(elabTerm9.tag === 'Lam' && elabTerm9._isAnnotated && elabTerm9.paramType && getTermRef(elabTerm9.paramType).tag === 'Pi') {
        const elabFType = getTermRef(elabTerm9.paramType) as Term & {tag:'Pi'};
        const elabXLam = getTermRef(elabTerm9.body(Var("f_"))) as Term & {tag:'Lam'};
        if(areEqual(elabFType.paramType, Nat, baseCtx) && areEqual(elabFType.bodyType(Var("y_")), Nat, baseCtx) &&
           elabXLam._isAnnotated && elabXLam.paramType && areEqual(elabXLam.paramType, Nat, baseCtx)
        ) {
             console.log("   Correct (term structure suggests annotation).");
        } else {
            throw new Error("Term not fully annotated as expected for ex9 (inner parts): " + printTerm(elabTerm9));
        }
    } else {
        throw new Error("Term not fully annotated as expected for ex9 (outer): " + printTerm(elabTerm9));
    }

    console.log("\n--- Example 10: Delta Reduction ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type()); defineGlobal("zero", Nat);
    defineGlobal("succ", Pi("n", Nat, _ => Nat));
    defineGlobal("one", Nat, App(Succ, Zero));
    result = elaborate(Var("one"), Nat, baseCtx);
    console.log(`   Term (Var("one")): ${printTerm(Var("one"))}`);
    console.log(`   Elaborated Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    if (!areEqual(result.term, App(Succ, Zero), baseCtx)) throw new Error("Delta reduction failed for ex10: " + printTerm(result.term));
    console.log("   Correct.");

    console.log("\n--- Example 11: Rewrite Rule ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type()); defineGlobal("zero", Nat);
    defineGlobal("succ", Pi("n", Nat, _ => Nat));
    defineGlobal("add", Pi("m", Nat, _ => Pi("n_", Nat, _ => Nat)));
    const pvarN_decl: PatternVarDecl = { name: "N", type: Nat };
    // LHS and RHS use Var for pattern variables
    const ruleAddZ: RewriteRule = {
        name: "add_Z_N", patternVars: [pvarN_decl],
        lhs: App(App(Add, Zero), Var("N")), // Var("N") is the pattern var
        rhs: Var("N")                       // Var("N") is the pattern var
    };
    if (checkRewriteRule(ruleAddZ, baseCtx)) {
        addRewriteRule(ruleAddZ); console.log(`   Rule ${ruleAddZ.name} added.`);
    } else { throw new Error(`Rule ${ruleAddZ.name} failed type preservation check for ex11.`); }
    const termToAdd = App(App(Add, Zero), App(Succ, Zero));
    result = elaborate(termToAdd, Nat, baseCtx);
    console.log(`   Original term: add zero (succ zero)`);
    console.log(`   Elaborated Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    if (!areEqual(result.term, App(Succ, Zero), baseCtx)) throw new Error("Rewrite rule application failed for ex11: " + printTerm(result.term));
    console.log("   Correct.");

} catch (e) {
    console.error("\n*** A TEST SCENARIO FAILED ***");
    console.error((e as Error).message);
    // console.error((e as Error).stack); // Can be very long
}