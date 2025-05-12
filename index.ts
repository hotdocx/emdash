// --- MyLambdaPi Final Corrected (v10): Fix WHNF/Normalize Loop ---
// --- WITH NEW FEATURE: User-Provided Unification Rules ---

// ... (previous code up to resetMyLambdaPi, unchanged) ...
let nextVarId = 0;
const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarId++}`;

let nextHoleId = 0;
const freshHoleName = (): string => `?h${nextHoleId++}`;

type BaseTerm =
    | { tag: 'Type' }
    | { tag: 'Var', name: string }
    | { tag: 'Lam', paramName: string, paramType?: Term, body: (v: Term) => Term, _isAnnotated: boolean }
    | { tag: 'App', func: Term, arg: Term }
    | { tag: 'Pi', paramName: string, paramType: Term, bodyType: (v: Term) => Term }
    | { tag: 'Hole', id: string, ref?: Term, elaboratedType?: Term };

type Term = BaseTerm;
type PatternVarDecl = { name: string, type: Term };

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

interface RewriteRule { name: string; patternVars: PatternVarDecl[]; lhs: Term; rhs: Term; }
const userRewriteRules: RewriteRule[] = [];
function addRewriteRule(rule: RewriteRule) { userRewriteRules.push(rule); }

// --- New: Unification Rules ---
interface UnificationRule {
    name: string;
    patternVars: PatternVarDecl[]; // All pattern variables used in the rule
    lhsPattern1: Term;             // Pattern P1 for P1 === P2
    lhsPattern2: Term;             // Pattern P2 for P1 === P2
    rhsNewConstraints: Array<{ t1: Term, t2: Term }>; // List of new problems [Q1 === R1, Q2 === R2, ...]
}
const userUnificationRules: UnificationRule[] = [];
function addUnificationRule(rule: UnificationRule) {
    userUnificationRules.push(rule);
}
// --- End New: Unification Rules ---

type Substitution = Map<string, Term>;
interface Constraint { t1: Term; t2: Term; origin?: string; }
let constraints: Constraint[] = [];

function addConstraint(t1: Term, t2: Term, origin?: string) { constraints.push({ t1, t2, origin }); }
function getTermRef(term: Term): Term {
    if (term.tag === 'Hole' && term.ref) return getTermRef(term.ref);
    return term;
}

const MAX_RECURSION_DEPTH = 100;
const MAX_STACK_DEPTH = 70; // Reduced from 70 to make space for deeper unify calls

function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`WHNF stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    let current = getTermRef(term);

    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        let changedInThisPass = false; 
        const termBeforePass = current; 

        if (current.tag === 'Var') {
            const gdef = globalDefs.get(current.name);
            if (gdef && gdef.value) {
                const valRef = getTermRef(gdef.value);
                if (valRef !== current) { 
                     current = valRef;
                     changedInThisPass = true; // Mark change if physical ref changes
                } else if (gdef.value !== current) { // Or if the value itself is different but ref was same (e.g. hole assigned)
                    changedInThisPass = true;
                }
            }
        }

        const termAfterDeltaThisPass = current; 
        for (const rule of userRewriteRules) {
            const subst = matchPattern(rule.lhs, termAfterDeltaThisPass, ctx, rule.patternVars, undefined, stackDepth + 1);
            if (subst) {
                const rhsApplied = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                if (rhsApplied !== termAfterDeltaThisPass) {
                    current = rhsApplied;
                    changedInThisPass = true;
                } else { // Rule applied but resulted in same term reference
                    // This can happen for X -> X. To ensure this pass is counted as "action taken",
                    // we mark changedInThisPass = true if subst was non-empty or rule RHS wasn't identical to LHS structurally before subst.
                    // For simplicity, if a rule *matches*, assume it's a meaningful step.
                    // The crucial part is that `current` must be updated if it changes to break the loop.
                    // If rhsApplied IS termAfterDeltaThisPass, then `current` doesn't change, and if delta didn't change, loop may stop.
                    // This seems fine. Let's make sure changedInThisPass is true if a rule *fires*.
                    if (rhsApplied === termAfterDeltaThisPass) {
                        // A rule fired but produced the same term reference. We still consider this a "change"
                        // for the purpose of the loop, to allow other rules or delta to take effect if this
                        // was an identity rule like A -> A.
                        // However, the *outer* `changedInThisPass` logic relies on `current` reference changing.
                        // Let's simplify: if a rule applies, it's considered a change for *this inner rule loop breaking*.
                        // The outer fixed point based on `current` reference change is the ultimate arbiter.
                    }
                     changedInThisPass = true; // A rule fired.
                break; 
            }
        }
        
        if (!changedInThisPass && current === termBeforePass) { // Check both flag and actual reference
            break;
        }
        current = getTermRef(current); // Re-chase in case a rule pointed to a hole that got filled by another.
        if (i === MAX_RECURSION_DEPTH -1) console.warn(`WHNF reached max iterations for delta/rules on: ${printTerm(termBeforePass)} -> ${printTerm(current)}`);
    }
    current = getTermRef(current);

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
}

function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Normalize stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    let current = getTermRef(term);

    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        let changedInThisPass = false;
        const termBeforePass = current;

        if (current.tag === 'Var') {
            const gdef = globalDefs.get(current.name);
            if (gdef && gdef.value) {
                const valRef = getTermRef(gdef.value);
                 if (valRef !== current) { 
                    current = valRef;
                    changedInThisPass = true;
                } else if (gdef.value !== current) {
                    changedInThisPass = true;
                }
            }
        }
        
        const termAfterDeltaThisPass = current;
        for (const rule of userRewriteRules) {
            const subst = matchPattern(rule.lhs, termAfterDeltaThisPass, ctx, rule.patternVars, undefined, stackDepth + 1);
            if (subst) {
                const rhsApplied = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                 if (rhsApplied !== termAfterDeltaThisPass) {
                    current = rhsApplied;
                    changedInThisPass = true;
                } else {
                    // as in WHNF, if rule fired, consider it a change for this inner break
                }
                changedInThisPass = true; // A rule fired.
                break;
            }
        }

        if (!changedInThisPass && current === termBeforePass) {
             break;
        }
        current = getTermRef(current);
        if (i === MAX_RECURSION_DEPTH -1) console.warn(`Normalize reached max iterations for delta/rules head on: ${printTerm(termBeforePass)} -> ${printTerm(current)}`);
    }
    current = getTermRef(current); 

    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': return current;
        case 'Lam': {
            const currentLam = current;
            const normLamParamType = currentLam.paramType ? normalize(currentLam.paramType, ctx, stackDepth + 1) : undefined;
            const newLam = Lam(currentLam.paramName,
                (v_arg: Term) => {
                    const paramTypeForBodyCtx = normLamParamType || 
                        (currentLam._isAnnotated && currentLam.paramType ? getTermRef(currentLam.paramType) : Hole());
                    let bodyCtx = ctx;
                    if (v_arg.tag === 'Var') { bodyCtx = extendCtx(ctx, v_arg.name, paramTypeForBodyCtx); }
                    return normalize(currentLam.body(v_arg), bodyCtx, stackDepth + 1);
                }, normLamParamType);
            newLam._isAnnotated = currentLam._isAnnotated;
            return newLam;
        }
        case 'App':
            const normFunc = normalize(current.func, ctx, stackDepth + 1);
            const normArg = normalize(current.arg, ctx, stackDepth + 1);
            const finalNormFunc = getTermRef(normFunc);
            if (finalNormFunc.tag === 'Lam') {
                return normalize(finalNormFunc.body(normArg), ctx, stackDepth + 1);
            }
            return App(normFunc, normArg);
        case 'Pi': {
            const currentPi = current;
            const normPiParamType = normalize(currentPi.paramType, ctx, stackDepth + 1);
            return Pi(currentPi.paramName, normPiParamType, (v_arg: Term) => {
                let bodyTypeCtx = ctx;
                if (v_arg.tag === 'Var') { bodyTypeCtx = extendCtx(ctx, v_arg.name, normPiParamType); }
                return normalize(currentPi.bodyType(v_arg), bodyTypeCtx, stackDepth + 1);
            });
        }
    }
}

function areEqual(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Equality check depth exceeded (areEqual depth: ${depth})`);
    const normT1 = whnf(t1, ctx, depth + 1);
    const normT2 = whnf(t2, ctx, depth + 1);
    const rt1 = getTermRef(normT1);
    const rt2 = getTermRef(normT2);

    if (rt1.tag === 'Hole' && rt2.tag === 'Hole') return rt1.id === rt2.id;
    if (rt1.tag === 'Hole' || rt2.tag === 'Hole') return false;
    if (rt1.tag !== rt2.tag) return false;

    switch (rt1.tag) {
        case 'Type': return true;
        case 'Var': return rt1.name === (rt2 as Term & {tag:'Var'}).name;
        case 'App': {
            const app2 = rt2 as Term & {tag:'App'};
            return areEqual(rt1.func, app2.func, ctx, depth + 1) &&
                   areEqual(rt1.arg, app2.arg, ctx, depth + 1);
        }
        case 'Lam': {
            const lam2 = rt2 as Term & {tag:'Lam'};
            if (rt1._isAnnotated !== lam2._isAnnotated) return false;
            if (rt1._isAnnotated) {
                if (!rt1.paramType || !lam2.paramType || !areEqual(rt1.paramType, lam2.paramType, ctx, depth + 1)) return false;
            }
            const freshV = Var(freshVarName(rt1.paramName));
            const CtxType = rt1.paramType ? getTermRef(rt1.paramType) : Hole();
            const extendedCtx = extendCtx(ctx, freshV.name, CtxType);
            return areEqual(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            if (!areEqual(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            const freshV = Var(freshVarName(rt1.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(rt1.paramType));
            return areEqual(rt1.bodyType(freshV), pi2.bodyType(freshV), extendedCtx, depth + 1);
        }
    }
}

function termContainsHole(term: Term, holeId: string, visited: Set<string>, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) {
        console.warn(`termContainsHole depth exceeded for ${holeId} in ${printTerm(term)}`);
        return true; // Fail safe: assume it contains the hole to prevent unsound unification.
    }
    const current = getTermRef(term);

    switch (current.tag) {
        case 'Hole': return current.id === holeId;
        case 'Type': case 'Var': return false;
        default: {
            // For HOAS terms, string representation for visited set is problematic
            // as bodies are functions. A more robust cycle detection for HOAS might be needed if used with `termContainsHole`.
            // For now, assuming patterns and terms being unified against holes are not deeply HOAS-cyclic in problematic ways.
            const termStrKey = `${current.tag}:${Object.keys(current).filter(k => k !== 'body' && k !== 'bodyType').map(k => (current as any)[k]?.toString()).join(',')}`;
            if (visited.has(termStrKey)) return false;
            visited.add(termStrKey);

            if (current.tag === 'App') {
                return termContainsHole(current.func, holeId, visited, depth + 1) ||
                       termContainsHole(current.arg, holeId, visited, depth + 1);
            } else if (current.tag === 'Lam') {
                 // Cannot easily check HOAS body without applying it.
                 // Occurs check for HOAS body needs careful thought. Assuming for now it's fine.
                return (current.paramType && termContainsHole(current.paramType, holeId, visited, depth + 1));
            } else if (current.tag === 'Pi') {
                // Similar to Lam
                return termContainsHole(current.paramType, holeId, visited, depth + 1);
            }
            return false; 
        }
    }
}

// --- Modified Unification Logic ---
enum UnifyResult { Solved, Failed, RewrittenByRule, Progress }

function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
    const normTerm = getTermRef(term); // Ensure we are unifying with the resolved term
    if (normTerm.tag === 'Hole') {
        if (hole.id === normTerm.id) return true; // ?x = ?x
        // Arbitrarily assign ?h_smaller_id = ?h_larger_id to break cycles if both are holes
        if (hole.id < normTerm.id) (normTerm as Term & {tag:'Hole'}).ref = hole; 
        else hole.ref = normTerm;
        return true;
    }
    if (termContainsHole(normTerm, hole.id, new Set(), depth + 1)) { // Occurs check
        console.warn(`Occurs check failed: ${hole.id} in ${printTerm(normTerm)}`);
        return false;
    }
    hole.ref = normTerm;
    return true;
}

function unify(t1: Term, t2: Term, ctx: Context, depth = 0): UnifyResult {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Unification stack depth exceeded (Unify depth: ${depth}, ${printTerm(t1)} vs ${printTerm(t2)})`);
    const rt1 = getTermRef(t1);
    const rt2 = getTermRef(t2);

    if (rt1 === rt2 && rt1.tag !== 'Hole') return UnifyResult.Solved;

    if (areEqual(rt1, rt2, ctx, depth + 1)) return UnifyResult.Solved;

    if (rt1.tag === 'Hole') {
        if (unifyHole(rt1, rt2, ctx, depth + 1)) return UnifyResult.Solved;
        else return tryUnificationRules(rt1, rt2, ctx, depth + 1);
    }
    if (rt2.tag === 'Hole') {
        if (unifyHole(rt2, rt1, ctx, depth + 1)) return UnifyResult.Solved;
        else return tryUnificationRules(rt1, rt2, ctx, depth + 1);
    }

    if (rt1.tag !== rt2.tag) return tryUnificationRules(rt1, rt2, ctx, depth + 1);

    switch (rt1.tag) {
        case 'Type': return UnifyResult.Solved;
        case 'Var':
            if (rt1.name === (rt2 as Term & {tag:'Var'}).name) return UnifyResult.Solved;
            else return tryUnificationRules(rt1, rt2, ctx, depth + 1);
        
        case 'App': {
            const app2 = rt2 as Term & {tag:'App'};
            let madeProgressFlag = false;

            const resFunc = unify(rt1.func, app2.func, ctx, depth + 1);
            if (resFunc === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);
            if (resFunc === UnifyResult.RewrittenByRule || resFunc === UnifyResult.Progress) madeProgressFlag = true;

            const resArg = unify(rt1.arg, app2.arg, ctx, depth + 1);
            if (resArg === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);
            if (resArg === UnifyResult.RewrittenByRule || resArg === UnifyResult.Progress) madeProgressFlag = true;
            
            if (!madeProgressFlag && resFunc === UnifyResult.Solved && resArg === UnifyResult.Solved) {
                 if (areEqual(rt1, rt2, ctx, depth + 1)) return UnifyResult.Solved;
                 else return UnifyResult.Progress; 
            }
            return UnifyResult.Progress;
        }
        case 'Lam': {
            const lam2 = rt2 as Term & {tag:'Lam'};
            if (rt1._isAnnotated !== lam2._isAnnotated) return tryUnificationRules(rt1, rt2, ctx, depth + 1);
            
            let madeProgressFlag = false;
            let paramTypesSolved = true; // Assume true if not annotated

            if (rt1._isAnnotated) {
                if (!rt1.paramType || !lam2.paramType) return tryUnificationRules(rt1, rt2, ctx, depth +1);
                const resParamType = unify(rt1.paramType, lam2.paramType, ctx, depth + 1);
                if (resParamType === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);
                if (resParamType === UnifyResult.RewrittenByRule || resParamType === UnifyResult.Progress) madeProgressFlag = true;
                if (resParamType !== UnifyResult.Solved) paramTypesSolved = false;
            }

            const freshV = Var(freshVarName(rt1.paramName));
            // Use the potentially refined paramType for context if available
            const CtxParamType = rt1.paramType ? getTermRef(rt1.paramType) : Hole(); 
            const extendedCtx = extendCtx(ctx, freshV.name, CtxParamType);
            
            const resBody = unify(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
            if (resBody === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);
            if (resBody === UnifyResult.RewrittenByRule || resBody === UnifyResult.Progress) madeProgressFlag = true;

            if (!madeProgressFlag && paramTypesSolved && resBody === UnifyResult.Solved) {
                if (areEqual(rt1, rt2, ctx, depth + 1)) return UnifyResult.Solved;
                else return UnifyResult.Progress;
            }
            return UnifyResult.Progress;
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            let madeProgressFlag = false;

            const resParamType = unify(rt1.paramType, pi2.paramType, ctx, depth + 1);
            if (resParamType === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);
            if (resParamType === UnifyResult.RewrittenByRule || resParamType === UnifyResult.Progress) madeProgressFlag = true;

            const freshV = Var(freshVarName(rt1.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(rt1.paramType));
            
            const resBodyType = unify(rt1.bodyType(freshV), pi2.bodyType(freshV), extendedCtx, depth + 1);
            if (resBodyType === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);
            if (resBodyType === UnifyResult.RewrittenByRule || resBodyType === UnifyResult.Progress) madeProgressFlag = true;
            
            if (!madeProgressFlag && resParamType === UnifyResult.Solved && resBodyType === UnifyResult.Solved) {
                 if (areEqual(rt1, rt2, ctx, depth + 1)) return UnifyResult.Solved;
                 else return UnifyResult.Progress;
            }
            return UnifyResult.Progress;
        }
    }
}

function collectPatternVars(term: Term, patternVarDecls: PatternVarDecl[], collectedVars: Set<string>, visited: Set<Term> = new Set()): void {
    const current = getTermRef(term);
    if (visited.has(current)) return;
    visited.add(current);

    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        collectedVars.add(current.name);
    }
    switch (current.tag) {
        case 'App':
            collectPatternVars(current.func, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.arg, patternVarDecls, collectedVars, visited);
            break;
        case 'Lam':
            if (current.paramType) collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            // body is HOAS, cannot inspect directly for schematic variables. Assume they are not hidden there.
            break;
        case 'Pi':
            collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            // bodyType is HOAS.
            break;
    }
}

function applyAndAddRuleConstraints(rule: UnificationRule, subst: Substitution, ctx: Context): void {
    const lhsVars = new Set<string>();
    collectPatternVars(rule.lhsPattern1, rule.patternVars, lhsVars);
    collectPatternVars(rule.lhsPattern2, rule.patternVars, lhsVars);

    const finalSubst = new Map(subst);

    // Add fresh holes for RHS variables not in LHS patterns
    for (const pVarDecl of rule.patternVars) {
        const pVarName = pVarDecl.name;
        // Check if this var appears in any RHS constraint term
        let appearsInRhsConstraints = false;
        for (const constrPair of rule.rhsNewConstraints) {
            const tempRhsVars = new Set<string>();
            collectPatternVars(constrPair.t1, rule.patternVars, tempRhsVars);
            collectPatternVars(constrPair.t2, rule.patternVars, tempRhsVars);
            if (tempRhsVars.has(pVarName)) {
                appearsInRhsConstraints = true;
                break;
            }
        }

        if (appearsInRhsConstraints && !lhsVars.has(pVarName)) {
            // This var is in RHS constraints but not in LHS patterns. It needs to be a fresh hole
            // if it's not already bound (e.g. if it appeared in one LHS pattern term but not others,
            // and thus not in `lhsVars` if `lhsVars` was defined narrowly).
            // Safer: If it's not in `lhsVars` (i.e. not bound by matching LHS patterns), it must be fresh.
             if (!finalSubst.has(pVarName)) { // Ensure it's not already in subst from some partial LHS match
                finalSubst.set(pVarName, Hole(freshHoleName()));
             }
        }
    }
    
    for (const constrPair of rule.rhsNewConstraints) {
        const newT1 = applySubst(constrPair.t1, finalSubst, rule.patternVars);
        const newT2 = applySubst(constrPair.t2, finalSubst, rule.patternVars);
        addConstraint(newT1, newT2, `UnifRule ${rule.name}`);
    }
}

function tryUnificationRules(t1: Term, t2: Term, ctx: Context, depth: number): UnifyResult {
    for (const rule of userUnificationRules) {
        // Try match (t1, t2) with (lhsPattern1, lhsPattern2)
        let subst = matchPattern(rule.lhsPattern1, t1, ctx, rule.patternVars, undefined, depth + 1);
        if (subst) {
            subst = matchPattern(rule.lhsPattern2, t2, ctx, rule.patternVars, subst, depth + 1);
            if (subst) {
                applyAndAddRuleConstraints(rule, subst, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }

        // Try match (t2, t1) with (lhsPattern1, lhsPattern2) -- commutativity
        subst = matchPattern(rule.lhsPattern1, t2, ctx, rule.patternVars, undefined, depth + 1);
        if (subst) {
            subst = matchPattern(rule.lhsPattern2, t1, ctx, rule.patternVars, subst, depth + 1);
            if (subst) {
                applyAndAddRuleConstraints(rule, subst, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }
    }
    return UnifyResult.Failed;
}


function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("solveConstraints stack depth exceeded");
    let changedInIteration = true;
    let iterations = 0;
    const maxIterations = (constraints.length + 10) * 20 + 50; // Adjusted for potentially more constraints

    while (changedInIteration && iterations < maxIterations) {
        changedInIteration = false;
        iterations++;
        
        const constraintsToRemoveIndices: number[] = [];

        for (let i = 0; i < constraints.length; i++) {
            const constraint = constraints[i];
            // Get refs for current state of constraint terms
            const c_t1_ref = getTermRef(constraint.t1);
            const c_t2_ref = getTermRef(constraint.t2);

            // Check if already equal before attempting unification.
            // This relies on `areEqual` not involving unification rules itself.
            if (areEqual(c_t1_ref, c_t2_ref, ctx, stackDepth + 1)) {
                continue; 
            }

            try {
                const unifyResult = unify(c_t1_ref, c_t2_ref, ctx, stackDepth + 1);
                
                if (unifyResult === UnifyResult.Solved) {
                    // A hole was solved, or terms became equal. This is a change.
                    changedInIteration = true; 
                } else if (unifyResult === UnifyResult.RewrittenByRule) {
                    changedInIteration = true;
                    constraintsToRemoveIndices.push(i); 
                } else if (unifyResult === UnifyResult.Progress) {
                    changedInIteration = true;
                } else { // UnifyResult.Failed
                    console.warn(`Unification failed for: ${printTerm(c_t1_ref)} === ${printTerm(c_t2_ref)} (origin: ${constraint.origin || 'unknown'})`);
                    return false; 
                }
            } catch (e) {
                console.error(`Error during unification of ${printTerm(c_t1_ref)} and ${printTerm(c_t2_ref)} (origin: ${constraint.origin || 'unknown'}): ${(e as Error).message}`);
                console.error((e as Error).stack);
                return false; 
            }
        }
        
        if (constraintsToRemoveIndices.length > 0) {
            constraintsToRemoveIndices.sort((a, b) => b - a); 
            for (const index of constraintsToRemoveIndices) {
                constraints.splice(index, 1);
            }
            // Removing constraints implies new ones were added, or problem transformed.
            changedInIteration = true; 
        }
    }

    if (iterations >= maxIterations && changedInIteration) { 
        console.warn("Constraint solving reached max iterations and was still making changes. Constraints list size: " + constraints.length);
        if (constraints.length > 0) {
             console.warn("Remaining constraints:");
             constraints.slice(0, 5).forEach(c => console.warn(`  ${printTerm(getTermRef(c.t1))} =?= ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`));
        }
    }

    for (const constraint of constraints) {
        if (!areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
            console.warn(`Final check failed for constraint: ${printTerm(getTermRef(constraint.t1))} === ${printTerm(getTermRef(constraint.t2))} (origin: ${constraint.origin || 'unknown'})`);
            return false;
        }
    }
    return true;
}


// --- End Modified Unification Logic ---

function infer(ctx: Context, term: Term, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Infer stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
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
            current.elaboratedType = newTypeForHole;
            return newTypeForHole;
        case 'App': {
            const funcType = infer(ctx, current.func, stackDepth + 1);
            const normFuncType = whnf(funcType, ctx, stackDepth + 1);
            if (normFuncType.tag === 'Hole') {
                const argTypeHole = Hole(freshHoleName());
                const resultTypeHole = Hole(freshHoleName());
                const freshPN = freshVarName("appArgInfer");
                addConstraint(normFuncType, Pi(freshPN, argTypeHole, _ => resultTypeHole), `App func type hole for ${printTerm(current.func)}`);
                check(ctx, current.arg, argTypeHole, stackDepth + 1);
                return resultTypeHole;
            }
            if (normFuncType.tag !== 'Pi') throw new Error(`Cannot apply non-function: ${printTerm(current.func)} of type ${printTerm(normFuncType)}`);
            check(ctx, current.arg, normFuncType.paramType, stackDepth + 1);
            return normFuncType.bodyType(current.arg);
        }
        case 'Lam': {
            const lam = current;
            const paramName = lam.paramName;
            if (lam._isAnnotated && lam.paramType) {
                check(ctx, lam.paramType, Type(), stackDepth + 1); 
                const extendedCtx = extendCtx(ctx, paramName, lam.paramType);
                const bodyTermInstance = lam.body(Var(paramName));
                const bodyType = infer(extendedCtx, bodyTermInstance, stackDepth + 1);
                return Pi(paramName, lam.paramType, _ => bodyType); 
            } else { 
                const paramTypeHole = Hole(freshHoleName());
                const extendedCtx = extendCtx(ctx, paramName, paramTypeHole);
                const bodyTermInstance = lam.body(Var(paramName));
                const bodyType = infer(extendedCtx, bodyTermInstance, stackDepth + 1);
                return Pi(paramName, paramTypeHole, _ => bodyType);
            }
        }
        case 'Pi': {
            const pi = current;
            check(ctx, pi.paramType, Type(), stackDepth + 1);
            const paramName = pi.paramName;
            const extendedCtx = extendCtx(ctx, paramName, pi.paramType);
            const bodyTypeInstance = pi.bodyType(Var(paramName));
            check(extendedCtx, bodyTypeInstance, Type(), stackDepth + 1);
            return Type();
        }
    }
}

function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0): void {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Check stack depth exceeded (depth: ${stackDepth}, term ${printTerm(term)}, expType ${printTerm(expectedType)})`);
    const current = getTermRef(term);
    const normExpectedType = whnf(expectedType, ctx, stackDepth + 1);

    if (current.tag === 'Lam' && !current._isAnnotated && normExpectedType.tag === 'Pi') {
        const lamTerm = current; 
        const expectedPi = normExpectedType; 

        const paramName = lamTerm.paramName;
        lamTerm.paramType = expectedPi.paramType;
        lamTerm._isAnnotated = true;

        const originalBodyFn = lamTerm.body; 

        lamTerm.body = (v_arg: Term): Term => {
            const freshInnerRawTerm = originalBodyFn(v_arg); 
            let ctxForInnerBody = ctx;
            const currentLamParamType = lamTerm.paramType!; 
            if (v_arg.tag === 'Var') { 
                ctxForInnerBody = extendCtx(ctx, v_arg.name, currentLamParamType);
            } 
            const expectedTypeForInnerBody = expectedPi.bodyType(v_arg);
            check(ctxForInnerBody, freshInnerRawTerm, expectedTypeForInnerBody, stackDepth); 
            return freshInnerRawTerm; 
        };
        const tempVarForOriginalCheck = Var(paramName);
        const extendedCtx = extendCtx(ctx, tempVarForOriginalCheck.name, lamTerm.paramType);
        check(extendedCtx, originalBodyFn(tempVarForOriginalCheck), expectedPi.bodyType(tempVarForOriginalCheck), stackDepth + 1);
        return;
    }

    if (current.tag === 'Hole') {
        const inferredHoleType = infer(ctx, current, stackDepth + 1);
        addConstraint(inferredHoleType, normExpectedType, `Hole ${current.id} checked against ${printTerm(normExpectedType)}`);
        return;
    }

    const inferredType = infer(ctx, current, stackDepth + 1);
    addConstraint(inferredType, normExpectedType, `Check general case for ${printTerm(current)}`);
}


interface ElaborationResult { term: Term; type: Term; }
function elaborate(term: Term, expectedType?: Term, initialCtx: Context = emptyCtx): ElaborationResult {
    constraints = []; nextHoleId = 0; nextVarId = 0; // Reset global state for elaboration
    let finalTypeToReport: Term;
    const termToElaborate = term; 

    try {
        if (expectedType) {
            check(initialCtx, termToElaborate, expectedType);
            finalTypeToReport = expectedType;
        } else {
            finalTypeToReport = infer(initialCtx, termToElaborate);
        }

        if (!solveConstraints(initialCtx)) {
            const fc = constraints.find(c => !areEqual(getTermRef(c.t1), getTermRef(c.t2), initialCtx));
            const fc_t1 = fc ? getTermRef(fc.t1) : null;
            const fc_t2 = fc ? getTermRef(fc.t2) : null;
            const fcMsg = fc && fc_t1 && fc_t2 ? `${printTerm(fc_t1)} vs ${printTerm(fc_t2)} (orig: ${fc.origin})` : "Unknown constraint";
            // Log all remaining constraints for debugging
            console.error("Remaining constraints on failure:");
            constraints.forEach(c => {
                 const c_t1 = getTermRef(c.t1); const c_t2 = getTermRef(c.t2);
                 console.error(`  ${printTerm(c_t1)} ${areEqual(c_t1, c_t2, initialCtx) ? "===" : "=/="} ${printTerm(c_t2)} (origin: ${c.origin})`);
            });
            throw new Error(`Type error: Could not solve constraints. Approx failing: ${fcMsg}`);
        }
    } catch (e) { throw e; }
    
    const finalElaboratedTermStructure = termToElaborate;
    // Normalizing after elaboration ensures solved holes are propagated.
    const normalizedElaboratedTerm = normalize(finalElaboratedTermStructure, initialCtx);
    // Also normalize the reported type, as it might contain holes that were solved.
    const finalTypeNormalized = normalize(finalTypeToReport, initialCtx); 
    return { term: normalizedElaboratedTerm, type: finalTypeNormalized };
}

function isPatternVarName(name: string, patternVarDecls: PatternVarDecl[]): boolean {
    return patternVarDecls.some(pvd => pvd.name === name);
}

function matchPattern(
    pattern: Term, termToMatch: Term, ctx: Context, 
    patternVarDecls: PatternVarDecl[],
    currentSubst?: Substitution, stackDepth = 0
): Substitution | null {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("matchPattern stack depth exceeded");
    const subst = currentSubst ? new Map(currentSubst) : new Map<string, Term>(); // Work on a copy
    
    const currentTermStruct = getTermRef(termToMatch);
    const rtPattern = getTermRef(pattern); // Resolve pattern refs too, though typically they are not holes

    if (rtPattern.tag === 'Var' && isPatternVarName(rtPattern.name, patternVarDecls)) {
        const pvarName = rtPattern.name;
        const existing = subst.get(pvarName);
        if (existing) { // Non-linear pattern: variable already bound
             // Must match the term it was bound to. Use areEqual for semantic match.
            return areEqual(currentTermStruct, existing, ctx, stackDepth + 1) ? subst : null;
        }
        subst.set(pvarName, currentTermStruct); 
        return subst;
    }

    if (currentTermStruct.tag === 'Hole' && rtPattern.tag !== 'Hole') return null; 
    if (rtPattern.tag === 'Hole' && currentTermStruct.tag !== 'Hole') return null;
    if (rtPattern.tag === 'Hole' && currentTermStruct.tag === 'Hole') { // ?patHole vs ?termHole
        // This case is tricky for pattern matching.
        // Standard first-order patterns usually don't have metavariables in the pattern itself.
        // If they do, it means the pattern hole must match the term hole *exactly*.
        return (rtPattern as Term & {tag:'Hole'}).id === (currentTermStruct as Term & {tag:'Hole'}).id ? subst : null;
    }
    if (rtPattern.tag !== currentTermStruct.tag) return null;

    switch (rtPattern.tag) {
        case 'Type': return subst;
        case 'Var': return rtPattern.name === (currentTermStruct as Term & {tag:'Var'}).name ? subst : null;
        case 'App': {
            const termApp = currentTermStruct as Term & {tag:'App'};
            const s1 = matchPattern(rtPattern.func, termApp.func, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s1) return null;
            return matchPattern(rtPattern.arg, termApp.arg, ctx, patternVarDecls, s1, stackDepth + 1);
        }
        case 'Lam': {
            const lamP = rtPattern as Term & {tag:'Lam'}; 
            const lamT = currentTermStruct as Term & {tag:'Lam'}; 
            if (lamP._isAnnotated !== lamT._isAnnotated) return null;
            let tempSubst = subst;
            if (lamP._isAnnotated) {
                if (!lamP.paramType || !lamT.paramType) return null; 
                 const sType = matchPattern(lamP.paramType, lamT.paramType, ctx, patternVarDecls, tempSubst, stackDepth + 1);
                 if (!sType) return null;
                 tempSubst = sType;
            }
            // For HOAS bodies in patterns: match structurally using areEqual under fresh var.
            // This assumes pattern variables in the body of lamP are handled by applySubst if this match is part of a larger substitution process.
            // Or, pattern variables are not allowed free in HOAS bodies of patterns.
            const freshV = Var(freshVarName(lamP.paramName));
            const CtxType = lamP.paramType ? getTermRef(lamP.paramType) : Hole();
            const extendedCtx = extendCtx(ctx, freshV.name, CtxType); // Context for comparing bodies
            
            // If lamP.body(freshV) contains pattern variables, areEqual won't substitute them.
            // This means first-order matching: the structure of bodies must be same up to alpha-equiv.
            // This is standard for first-order patterns.
            return areEqual(lamP.body(freshV), lamT.body(freshV), extendedCtx, stackDepth + 1) ? tempSubst : null;
        }
        case 'Pi': {
            const piP = rtPattern as Term & {tag:'Pi'};
            const piT = currentTermStruct as Term & {tag:'Pi'};
            const sType = matchPattern(piP.paramType, piT.paramType, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!sType) return null;
            const freshV = Var(freshVarName(piP.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(piP.paramType));
            return areEqual(piP.bodyType(freshV), piT.bodyType(freshV), extendedCtx, stackDepth+1) ? sType : null;
        }
    }
}

function applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[]): Term {
    const current = getTermRef(term); // Operate on the resolved term
    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        const replacement = subst.get(current.name);
        // If replacement is not found, it means a pattern variable declared for the rule
        // (and used in RHS) was not bound by LHS matching and also not made a fresh hole.
        // This should ideally be caught by the fresh hole creation logic.
        if (!replacement) throw new Error(`Unbound pattern variable ${current.name} during substitution in rule RHS. Declared vars: ${patternVarDecls.map(pvd=>pvd.name).join(', ')}, Subst keys: ${Array.from(subst.keys()).join(', ')}`);
        return replacement;
    }
    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': return current; // Non-pattern vars and non-substituted holes are returned as is
        case 'App':
            return App(applySubst(current.func, subst, patternVarDecls), applySubst(current.arg, subst, patternVarDecls));
        case 'Lam': {
            const lam = current;
            const lamParamType = lam.paramType ? applySubst(lam.paramType, subst, patternVarDecls) : undefined;
            const newLam = Lam(lam.paramName,
                (v_arg: Term) => applySubst(lam.body(v_arg), subst, patternVarDecls), 
                lamParamType);
            newLam._isAnnotated = lam._isAnnotated;
            return newLam;
        }
        case 'Pi': {
            const pi = current;
            return Pi(pi.paramName, applySubst(pi.paramType, subst, patternVarDecls),
                (v_arg: Term) => applySubst(pi.bodyType(v_arg), subst, patternVarDecls));
        }
    }
}

function checkRewriteRule(rule: RewriteRule, baseCtx: Context): boolean {
    let patternCtx = baseCtx;
    for (const pv of rule.patternVars) { patternCtx = extendCtx(patternCtx, pv.name, pv.type); }
    const ruleCheckConstraintsBackup = [...constraints]; // Save global constraints
    const ruleCheckNextHoleIdBackup = nextHoleId;
    
    constraints = []; // Use fresh set for this rule check
    nextHoleId = 0; // Reset hole counter for rule check scope

    try {
        const lhsType = infer(patternCtx, rule.lhs);
        const rhsType = infer(patternCtx, rule.rhs);
        addConstraint(lhsType, rhsType, `Rewrite rule ${rule.name} type preservation`);
        if (!solveConstraints(patternCtx)) {
            console.error(`Rule ${rule.name} does not preserve types.`);
            const fc = constraints.find(constraint => !areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), patternCtx));
            if (fc) console.error(`  Failing constraint for rule type check: ${printTerm(getTermRef(fc.t1))} = ${printTerm(getTermRef(fc.t2))}`);
            return false;
        }
        return true;
    } catch (e) {
        console.error(`Error checking rule ${rule.name}: ${(e as Error).message}`);
        return false;
    } finally { 
        constraints = ruleCheckConstraintsBackup; // Restore global constraints
        nextHoleId = ruleCheckNextHoleIdBackup; // Restore hole counter
    }
}

function printTerm(term: Term, boundVars: string[] = [], stackDepth = 0): string {
    if (stackDepth > MAX_STACK_DEPTH) return "<print_depth_exceeded>";
    if (!term) return "<null_term>";
    const current = getTermRef(term); // Always print the resolved term
    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return current.name;
        case 'Hole': return current.id + (current.elaboratedType ? `(:${printTerm(current.elaboratedType, boundVars, stackDepth+1)})` : '');
        case 'Lam': {
            const paramName = current.paramName; // Avoid clash with existing boundVars if possible, but freshVarName not used here
            let uniqueParamName = paramName;
            let suffix = 1;
            while(boundVars.includes(uniqueParamName)) { uniqueParamName = `${paramName}_${suffix++}`; }

            const typeAnnotation = current._isAnnotated && current.paramType ? ` : ${printTerm(current.paramType, boundVars, stackDepth + 1)}` : '';
            // When printing, the HOAS body is called with a Var representing the bound variable.
            // Its name should be the unique one for this printing context.
            const bodyTerm = current.body(Var(uniqueParamName)); 
            return `(λ ${uniqueParamName}${typeAnnotation}. ${printTerm(bodyTerm, [...boundVars, uniqueParamName], stackDepth + 1)})`;
        }
        case 'App':
            return `(${printTerm(current.func, boundVars, stackDepth + 1)} ${printTerm(current.arg, boundVars, stackDepth + 1)})`;
        case 'Pi': {
            const paramName = current.paramName;
            let uniqueParamName = paramName;
            let suffix = 1;
            while(boundVars.includes(uniqueParamName)) { uniqueParamName = `${paramName}_${suffix++}`; }
            
            const bodyTypeTerm = current.bodyType(Var(uniqueParamName));
            return `(Π ${uniqueParamName} : ${printTerm(current.paramType, boundVars, stackDepth + 1)}. ${printTerm(bodyTypeTerm, [...boundVars, uniqueParamName], stackDepth + 1)})`;
        }
    }
}
function resetMyLambdaPi() {
    constraints = []; globalDefs.clear(); 
    userRewriteRules.length = 0; 
    userUnificationRules.length = 0; // Reset new unification rules
    nextVarId = 0; nextHoleId = 0;
}

// --- Example Usage (Adjusted Example 9 test logic if needed, but v4 change should handle it) ---
// (Keep existing tests, they should still pass. New tests for unif rules will be needed later)
console.log("--- MyLambdaPi with Unification Rules Feature ---");
// ... (rest of the example code from the prompt)
const Nat = Var("Nat");
const Bool = Var("Bool");
const Zero = Var("zero"); 
const Succ = Var("succ");
const Add = Var("add");

try {
    resetMyLambdaPi();
    defineGlobal("Nat", Type());
    defineGlobal("Bool", Type());
    defineGlobal("zero", Nat);
    defineGlobal("succ", Pi("n", Nat, _ => Nat));
    defineGlobal("true", Bool); // Assuming a term 'true' of type Bool
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
        const freshV3 = Var(resT3.paramName);
        // The body type of the Pi should be the same hole as the param type hole.
        const bodyTypeAsTerm = resT3.bodyType(freshV3); // This is `_ => bodyType` applied to freshV3
        if (areEqual(bodyTypeAsTerm, paramHole, baseCtx)) { // Compare the resulting type with the paramHole
             console.log(`   Correct: Type is ${printTerm(result.type)}`);
        } else throw new Error(`Body type of Pi (${printTerm(bodyTypeAsTerm)}) does not match param hole (${printTerm(paramHole)}) for ex3`);
    } else throw new Error("Inferred type for unannotated id not Pi with hole for ex3: " + printTerm(resT3));


    console.log("\n--- Example 4: Check ((λx:Nat. x) ?argHole) against Nat ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type());
    const idFunc4 = Lam("x", x => x, Nat);
    const myHole4 = Hole("argHole");
    const appWithHole4 = App(idFunc4, myHole4);
    result = elaborate(appWithHole4, Nat, baseCtx);
    console.log(`   Term: ${printTerm(result.term)}`); // Should be ?argHole, which got unified with something that is Nat
    console.log(`   Type: ${printTerm(result.type)}`); // Should be Nat
    
    const resTerm4_ref = getTermRef(result.term); // This will be the value ?argHole was unified with
    const myHole4_ref = getTermRef(myHole4);    // This will be the same value if ?argHole was solved

    console.log(`   ?argHole after elab: ${printTerm(myHole4)}`);
    console.log(`   Type of ?argHole solution: ${myHole4_ref.tag !== 'Hole' ? printTerm(infer(baseCtx,myHole4_ref)) : "unsolved or points to hole"}`);

    if (!areEqual(result.type, Nat, baseCtx)) throw new Error("Overall type not Nat for ex4");
    // myHole4 should have been solved to something of type Nat.
    // The result.term is the normalized version of App(idFunc4, solution_of_myHole4), which beta-reduces to solution_of_myHole4.
    // So result.term should be the solution of myHole4.
    if (myHole4_ref.tag === 'Hole' && myHole4_ref.id === myHole4.id) throw new Error("argHole was not solved for ex4");
    if (!areEqual(infer(baseCtx, myHole4_ref), Nat, baseCtx)) throw new Error("Solved argHole is not of type Nat for ex4");
    console.log("   Correct.");


    console.log("\n--- Example 5: Infer (λf. λx. f x) ---");
    resetMyLambdaPi();
    const complexLam5 = Lam("f", f => Lam("x", x => App(f, x)));
    result = elaborate(complexLam5, undefined, baseCtx);
    console.log(`   Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    const resT5 = getTermRef(result.type); // Π f : (?A -> ?B). Π x : ?A. ?B
    if (resT5.tag === 'Pi') { // Outer Pi for f
        const typeOfF_pi = getTermRef(resT5.paramType); // ?A -> ?B
        if (typeOfF_pi.tag !== 'Pi') throw new Error("Type of f is not a Pi type for ex5: " + printTerm(typeOfF_pi));
        
        const typeOfF_param = getTermRef(typeOfF_pi.paramType); // ?A
        if (typeOfF_param.tag !== 'Hole') throw new Error("Param type of f's type is not a hole for ex5: " + printTerm(typeOfF_param));
        
        const typeOfF_body = getTermRef(typeOfF_pi.bodyType(Var(typeOfF_pi.paramName))); // ?B
        if (typeOfF_body.tag !== 'Hole') throw new Error("Body type of f's type is not a hole for ex5: " + printTerm(typeOfF_body));

        const bodyTypeOuter_pi = getTermRef(resT5.bodyType(Var(resT5.paramName))); // Pi x : ?A. ?B
        if (bodyTypeOuter_pi.tag !== 'Pi') throw new Error("Outer body type is not a Pi type for ex5: " + printTerm(bodyTypeOuter_pi));

        const bodyTypeOuter_param = getTermRef(bodyTypeOuter_pi.paramType); // ?A
        if (bodyTypeOuter_param.tag !== 'Hole') throw new Error("Param type of outer body type is not a hole for ex5: " + printTerm(bodyTypeOuter_param));
        
        const bodyTypeOuter_body = getTermRef(bodyTypeOuter_pi.bodyType(Var(bodyTypeOuter_pi.paramName))); // ?B
        if (bodyTypeOuter_body.tag !== 'Hole') throw new Error("Body type of outer body type is not a hole for ex5: " + printTerm(bodyTypeOuter_body));

        if (!areEqual(typeOfF_param, bodyTypeOuter_param, baseCtx)) throw new Error("?A holes do not match for ex5");
        if (!areEqual(typeOfF_body, bodyTypeOuter_body, baseCtx)) throw new Error("?B holes do not match for ex5");
        
        console.log(`   Correct type structure found.`);
    } else throw new Error("Overall type not Pi for ex5: " + printTerm(resT5));


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
    const polyId9_source = Lam("f", f => Lam("x", x => App(f, x)));
    const concretePiType9 = Pi("f", Pi("y", Nat, _ => Nat), _fVal => Pi("x", Nat, _xVal => Nat));
    result = elaborate(polyId9_source, concretePiType9, baseCtx);
    console.log(`   Term (Elaborated): ${printTerm(result.term)}`);
    console.log(`   Type (Checked): ${printTerm(result.type)}`);
    if (!areEqual(result.type, concretePiType9, baseCtx)) throw new Error("Type mismatch for ex9 overall type");

    const elabTerm9 = getTermRef(result.term);
    if (elabTerm9.tag === 'Lam' && elabTerm9._isAnnotated && elabTerm9.paramType && getTermRef(elabTerm9.paramType).tag === 'Pi') {
        const elabFType_pi = getTermRef(elabTerm9.paramType) as Term & {tag:'Pi'};
        if(!(elabFType_pi.paramType && areEqual(elabFType_pi.paramType, Nat, baseCtx) && areEqual(elabFType_pi.bodyType(Var('y')), Nat, baseCtx))) {
            throw new Error(`Outer lambda param type incorrect. Expected Π y:Nat.Nat, got ${printTerm(elabFType_pi)}`);
        }
        
        const actualInnerLam = getTermRef(elabTerm9.body(Var("f_for_test"))); 
        
        if (actualInnerLam.tag === 'Lam' && actualInnerLam._isAnnotated && actualInnerLam.paramType &&
            areEqual(actualInnerLam.paramType, Nat, baseCtx)) {
            
            const ctxForInnerBodyCheck = extendCtx(extendCtx(baseCtx, "f_for_test", elabFType_pi), actualInnerLam.paramName, actualInnerLam.paramType);
            const innerLamBodyResult = actualInnerLam.body(Var(actualInnerLam.paramName));
            const innerLamBodyResultType = infer(ctxForInnerBodyCheck, innerLamBodyResult);
            
            if (areEqual(innerLamBodyResultType, Nat, ctxForInnerBodyCheck)) {
                console.log("   Correct (deep annotation preserved through normalization).");
            } else {
                throw new Error(`Inner lambda body type mismatch. Expected Nat, got ${printTerm(innerLamBodyResultType)} (body: ${printTerm(innerLamBodyResult)})`);
            }
        } else {
            throw new Error(`Normalized inner lambda not annotated as expected: ${printTerm(actualInnerLam)}. Expected param type Nat.`);
        }
    } else {
        throw new Error("Normalized outer lambda not annotated as expected: " + printTerm(elabTerm9));
    }


    console.log("\n--- Example 10: Delta Reduction ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type()); defineGlobal("zero", Nat);
    defineGlobal("succ", Pi("n", Nat, _ => Nat));
    defineGlobal("one", Nat, App(Succ, Zero));
    result = elaborate(Var("one"), Nat, baseCtx); // Check Var("one") against Nat
    console.log(`   Term (Var("one")): ${printTerm(Var("one"))}`);
    console.log(`   Elaborated Term (normalized of Var("one")): ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    if (!areEqual(result.term, App(Succ, Zero), baseCtx)) throw new Error("Delta reduction failed for ex10: " + printTerm(result.term));
    console.log("   Correct.");

    console.log("\n--- Example 11: Rewrite Rule ---");
    resetMyLambdaPi(); defineGlobal("Nat", Type()); defineGlobal("zero", Nat);
    defineGlobal("succ", Pi("n", Nat, _ => Nat));
    defineGlobal("add", Pi("m", Nat, _ => Pi("n_", Nat, _ => Nat)));
    const pvarN_decl: PatternVarDecl = { name: "N", type: Nat };
    const ruleAddZ: RewriteRule = {
        name: "add_Z_N", patternVars: [pvarN_decl],
        lhs: App(App(Add, Zero), Var("N")),
        rhs: Var("N")
    };
    if (checkRewriteRule(ruleAddZ, baseCtx)) {
        addRewriteRule(ruleAddZ); console.log(`   Rule ${ruleAddZ.name} added.`);
    } else { throw new Error(`Rule ${ruleAddZ.name} failed type preservation check for ex11.`); }
    const termToAdd = App(App(Add, Zero), App(Succ, Zero)); // add zero (succ zero)
    result = elaborate(termToAdd, Nat, baseCtx); // Check this term against Nat
    console.log(`   Original term: add zero (succ zero)`);
    console.log(`   Elaborated Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    if (!areEqual(result.term, App(Succ, Zero), baseCtx)) throw new Error("Rewrite rule application failed for ex11: " + printTerm(result.term));
    console.log("   Correct.");

    // --- New test for Unification Rules ---
    console.log("\n--- Example 12: Unification Rule Test ---");
    resetMyLambdaPi();
    // Setup: T ?x === Bool  becomes ?x === bool_term
    // Globals:
    //   SomeType : Type
    //   Bool_val : SomeType  (represents the term 'Bool')
    //   T_ctor : SomeType -> SomeType (represents the constructor 'T')
    //   bool_term : SomeType (represents the term 'bool')
    defineGlobal("SomeType", Type());
    const ST = Var("SomeType");
    defineGlobal("Bool_val", ST);
    defineGlobal("T_ctor", Pi("_", ST, _ => ST));
    defineGlobal("bool_term", ST);

    const pvar_t_decl_unif: PatternVarDecl = { name: "t", type: ST };
    addUnificationRule({
        name: "T_Bool_to_bool",
        patternVars: [pvar_t_decl_unif],
        lhsPattern1: Var("Bool_val"), // This is 'Bool' the term
        lhsPattern2: App(Var("T_ctor"), Var("t")), // This is 'T $t'
        rhsNewConstraints: [{ t1: Var("t"), t2: Var("bool_term") }] // '$t = bool_term'
    });
    console.log("   Unification rule 'T_Bool_to_bool' added.");

    const myHole_ex12 = Hole("?x_ex12");
    // We want to create a situation where T_ctor(?x_ex12) === Bool_val is a constraint.
    // Let's define a global that expects something of type (T_ctor Bool_val)
    // e.g. id_T_Bool : (T_ctor Bool_val) -> (T_ctor Bool_val)
    // defineGlobal("id_T_Bool_type", Pi("arg", App(Var("T_ctor"), Var("Bool_val")), _ => App(Var("T_ctor"), Var("Bool_val"))));
    // Then elaborate App(Var("id_T_Bool_type"), App(Var("T_ctor"), myHole_ex12) )
    // The check will enforce App(Var("T_ctor"), Var("Bool_val")) === type of App(Var("T_ctor"), myHole_ex12)
    // infer(App(Var("T_ctor"), myHole_ex12)) is T_ctor (type of myHole_ex12)
    // This isn't quite matching the example structure "T ?x === Bool" directly as a constraint.

    // Let's try to force the constraint more directly in elaboration:
    // Check `myHole_ex12` against `ST` such that during solving, some other constraint
    // forces `App(Var("T_ctor"), myHole_ex12)` to be equal to `Var("Bool_val")`.
    
    // Consider this: let `f : (Π z : SomeType. SomeType)` be a global.
    // We check `(f (T_ctor myHole_ex12))` against `(f Bool_val)`.
    // This will generate constraint `T_ctor myHole_ex12 === Bool_val`.
    defineGlobal("f_generic", Pi("z", ST, _ => ST));
    const term_LHS = App(Var("f_generic"), App(Var("T_ctor"), myHole_ex12));
    const term_RHS = App(Var("f_generic"), Var("Bool_val"));
    
    // We don't have a direct way to add `term_LHS === term_RHS` other than through check/infer.
    // Let's make a wrapper function that causes this constraint:
    // `Wrapper : (Π _:ST. ST) -> ST`
    // `check (Wrapper (λy. y)) against (Wrapper (λy. if y == T_ctor ?x then Bool_val else ...))`
    // This is getting too complex for a direct test.

    // Alternative: create two holes, ?h1 and ?h2.
    // Add constraint ?h1 = App(Var("T_ctor"), myHole_ex12)
    // Add constraint ?h1 = Var("Bool_val")
    // This implies App(Var("T_ctor"), myHole_ex12) = Var("Bool_val")
    constraints = []; // Start fresh for this specific test scenario
    const h1_ex12 = Hole("?h1_ex12");
    addConstraint(h1_ex12, App(Var("T_ctor"), myHole_ex12), "Constraint 1 for ex12");
    addConstraint(h1_ex12, Var("Bool_val"), "Constraint 2 for ex12");
    
    console.log(`   Initial state of myHole_ex12: ${printTerm(myHole_ex12)}`);
    if (solveConstraints(baseCtx)) {
        console.log("   Constraints solved successfully.");
        const myHole_ex12_val = getTermRef(myHole_ex12);
        console.log(`   Solved value of myHole_ex12: ${printTerm(myHole_ex12_val)}`);
        if (areEqual(myHole_ex12_val, Var("bool_term"), baseCtx)) {
            console.log("   Correct: myHole_ex12 unified with bool_term via unification rule.");
        } else {
            throw new Error(`Incorrect unification for myHole_ex12. Expected bool_term, got ${printTerm(myHole_ex12_val)}`);
        }
    } else {
        throw new Error("Failed to solve constraints for ex12 unification rule test.");
    }


} catch (e) {
    console.error("\n*** A TEST SCENARIO FAILED ***");
    console.error((e as Error).message);
    console.error((e as Error).stack);
}
