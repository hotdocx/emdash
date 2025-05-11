// --- MyLambdaPi Final Corrected (v7): Fix Infer Regression & MatchPattern WHNF ---

// --- Report on Changed Specification ---
// 1. Corrected `infer` for `Lam` to ensure the `Pi` type's `bodyType` function
//    uses the correct variable scoping, fixing the "Unbound variable" regression.
// 2. Modified `matchPattern`: it no longer calls `whnf` on the term it's trying
//    to match. The `whnf` (or `normalize`) function is responsible for passing
//    the appropriately head-reduced term to `matchPattern`. This aligns better
//    with standard rewrite rule application strategies where matching doesn't
//    perform arbitrary other reductions on the subject term.
// 3. The `whnf`/`normalize` head reduction loop termination remains based on
//    detecting if `current` term reference changes after a delta or rule step.
// All other features (deep elaboration, etc.) remain.
// --- End Report ---

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

type Substitution = Map<string, Term>;
interface Constraint { t1: Term; t2: Term; origin?: string; }
let constraints: Constraint[] = [];

function addConstraint(t1: Term, t2: Term, origin?: string) { constraints.push({ t1, t2, origin }); }
function getTermRef(term: Term): Term {
    if (term.tag === 'Hole' && term.ref) return getTermRef(term.ref);
    return term;
}

const MAX_RECURSION_DEPTH = 100;
const MAX_STACK_DEPTH = 70;

function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`WHNF stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    let current = getTermRef(term);

    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        let changedInThisPass = false;
        const termBeforePass = current;

        // 1. Delta Reduction
        if (current.tag === 'Var') {
            const gdef = globalDefs.get(current.name);
            if (gdef && gdef.value) {
                const valRef = getTermRef(gdef.value);
                if (valRef !== current) { 
                     current = valRef;
                     changedInThisPass = true;
                }
            }
        }
        
        // 2. Rewrite Rules
        const termAfterDeltaThisPass = current;
        let ruleMatchedAndAltered = false;
        for (const rule of userRewriteRules) {
            // `matchPattern` now takes termAfterDeltaThisPass as is (already head-reduced by prior WHNF iterations)
            const subst = matchPattern(rule.lhs, termAfterDeltaThisPass, ctx, rule.patternVars, undefined, stackDepth + 1);
            if (subst) {
                const rhsApplied = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                if (rhsApplied !== termAfterDeltaThisPass) { 
                    current = rhsApplied;
                    changedInThisPass = true; // A semantic change happened
                }
                ruleMatchedAndAltered = true; // A rule was processed (even if it was identity)
                break; 
            }
        }
        // If a rule matched (even if identity), we set changedInThisPass to true to force re-evaluation of head,
        // unless no delta happened AND the rule was identity. This is subtle.
        // Simpler: if a rule matched, consider it a step.
        if (ruleMatchedAndAltered && !changedInThisPass && current === termAfterDeltaThisPass) {
            // This means a rule matched, produced the same physical term, and delta also didn't change.
            // This can happen for `X -> X` if `applySubst` returns original `X`.
            // To ensure progress if other rules might apply or if delta might apply after this identity rule,
            // we could force changedInThisPass = true. But the current logic to break if !changedInThisPass is usually okay.
            // Let's stick to: change means `current` is a new reference or different value.
        }
        
        if (!changedInThisPass) {
            break; 
        }

        if (i === MAX_RECURSION_DEPTH -1) {
             console.warn(`WHNF reached max iterations for delta/rules. Start: ${printTerm(termBeforePass)}, End: ${printTerm(current)}`);
        }
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

function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Normalize stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    let current = getTermRef(term);

    // Head reduction loop (delta & rules)
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
                }
            }
        }
        
        const termAfterDeltaThisPass = current;
        let ruleMatchedAndAltered = false;
        for (const rule of userRewriteRules) {
            const subst = matchPattern(rule.lhs, termAfterDeltaThisPass, ctx, rule.patternVars, undefined, stackDepth + 1);
            if (subst) {
                const rhsApplied = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                 if (rhsApplied !== termAfterDeltaThisPass) {
                    current = rhsApplied;
                    changedInThisPass = true;
                }
                ruleMatchedAndAltered = true;
                break;
            }
        }

        if (!changedInThisPass) {
            break;
        }
        if (i === MAX_RECURSION_DEPTH -1) {
            console.warn(`Normalize head loop reached max iterations. Start: ${printTerm(termBeforePass)}, End: ${printTerm(current)}`);
        }
    }
    current = getTermRef(current);

    // Structural recursion for normalization
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
            if (rt1._isAnnotated) { // Both must be annotated and types equal
                if (!rt1.paramType || !lam2.paramType || !areEqual(rt1.paramType, lam2.paramType, ctx, depth + 1)) return false;
            }
            const freshV = Var(freshVarName(rt1.paramName)); // Use paramName hint for easier debugging
            // Determine type for freshV in context: use annotated type if present, else Hole
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
    if (depth > MAX_STACK_DEPTH) return false;
    const current = getTermRef(term);

    switch (current.tag) {
        case 'Hole': return current.id === holeId;
        case 'Type': case 'Var': return false;
        default: { 
            const termStr = printTerm(current); 
            if (visited.has(termStr)) return false;
            visited.add(termStr);

            if (current.tag === 'App') {
                return termContainsHole(current.func, holeId, visited, depth + 1) ||
                       termContainsHole(current.arg, holeId, visited, depth + 1);
            } else if (current.tag === 'Lam') {
                return (current.paramType && termContainsHole(current.paramType, holeId, visited, depth + 1)) ||
                       false; 
            } else if (current.tag === 'Pi') {
                return termContainsHole(current.paramType, holeId, visited, depth + 1) ||
                       false;
            }
            return false; 
        }
    }
}


function unify(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Unification stack depth exceeded (depth: ${depth})`);
    const rt1 = getTermRef(t1);
    const rt2 = getTermRef(t2);

    if (rt1 === rt2 && rt1.tag !== 'Hole') return true; // Physical identity
    if (areEqual(rt1, rt2, ctx, depth + 1)) return true; // Definitional equality

    if (rt1.tag === 'Hole') return unifyHole(rt1, rt2, ctx, depth + 1);
    if (rt2.tag === 'Hole') return unifyHole(rt2, rt1, ctx, depth + 1);

    if (rt1.tag !== rt2.tag) return false; // Different constructors

    // At this point, rt1 and rt2 are not holes, have the same tag, and are not def-equal
    switch (rt1.tag) {
        case 'Type': return true; // Should have been caught by areEqual
        case 'Var': return rt1.name === (rt2 as Term & {tag:'Var'}).name; // Should have been caught by areEqual
        case 'App': {
            const app2 = rt2 as Term & {tag:'App'};
            return unify(rt1.func, app2.func, ctx, depth + 1) &&
                   unify(rt1.arg, app2.arg, ctx, depth + 1);
        }
        case 'Lam': {
            const lam2 = rt2 as Term & {tag:'Lam'};
            if (rt1._isAnnotated !== lam2._isAnnotated) return false; // Must match annotation status for unification here
            if (rt1._isAnnotated) {
                if (!rt1.paramType || !lam2.paramType || !unify(rt1.paramType, lam2.paramType, ctx, depth + 1)) return false;
            }
            const freshV = Var(freshVarName(rt1.paramName));
            const CtxType = rt1.paramType ? getTermRef(rt1.paramType) : Hole();
            const extendedCtx = extendCtx(ctx, freshV.name, CtxType);
            return unify(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            if (!unify(rt1.paramType, pi2.paramType, ctx, depth + 1)) return false;
            const freshV = Var(freshVarName(rt1.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(rt1.paramType));
            return unify(rt1.bodyType(freshV), pi2.bodyType(freshV), extendedCtx, depth + 1);
        }
    }
}

function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
    const normTerm = getTermRef(term); // Term to equate with hole
    if (normTerm.tag === 'Hole') { // Unifying hole with hole
        if (hole.id === normTerm.id) return true; // ?h = ?h
        // Convention: smaller ID points to larger ID to form chains, or some other consistent choice
        if (hole.id < normTerm.id) (normTerm as Term & {tag:'Hole'}).ref = hole; 
        else hole.ref = normTerm;
        return true;
    }
    // Occurs check: ?h = T containing ?h
    if (termContainsHole(normTerm, hole.id, new Set(), depth + 1)) {
        // console.warn(`Occurs check failed: trying to unify ${hole.id} with ${printTerm(normTerm)}`);
        return false;
    }
    hole.ref = normTerm; // Instantiate hole
    return true;
}

function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("solveConstraints stack depth exceeded");
    let changedInIteration = true;
    let iterations = 0;
    const maxIterations = constraints.length * 10 + 50; 

    while (changedInIteration && iterations < maxIterations) {
        changedInIteration = false;
        iterations++;
        for (let i = 0; i < constraints.length; i++) {
            const constraint = constraints[i];
            if (areEqual(constraint.t1, constraint.t2, ctx, stackDepth + 1)) continue; // Already equal
            try {
                if (unify(constraint.t1, constraint.t2, ctx, stackDepth + 1)) { 
                    changedInIteration = true; // Unification succeeded and might have set a hole
                } else { 
                    return false; // Hard unification failure
                }
            } catch (e) { 
                // console.error(`Error during unify in solveConstraints: ${(e as Error).message}`);
                return false; // Error during unification
            }
        }
    }
    if (iterations >= maxIterations && changedInIteration) { console.warn("Constraint solving max iterations and still changing."); }
    // Final check
    for (const constraint of constraints) {
        if (!areEqual(constraint.t1, constraint.t2, ctx, stackDepth + 1)) return false;
    }
    return true;
}

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
            return normFuncType.bodyType(current.arg); // HOAS applies arg here
        }
        case 'Lam': {
            const lam = current;
            const originalParamName = lam.paramName; // Use the name from the source
            if (lam._isAnnotated && lam.paramType) {
                check(ctx, lam.paramType, Type(), stackDepth + 1);
                // The Pi's bodyType function must use the variable IT is given for context.
                return Pi(originalParamName, lam.paramType, (v_pi_arg: Term) => {
                    let tempCtx = ctx;
                    // The context for inferring the body uses v_pi_arg
                    if (v_pi_arg.tag === 'Var') { tempCtx = extendCtx(ctx, v_pi_arg.name, lam.paramType!); }
                    else { tempCtx = extendCtx(ctx, "$_internal_binder_val", lam.paramType!); } // Non-var binder val
                    // lam.body expects a term to substitute for originalParamName.
                    // We give it v_pi_arg.
                    return infer(tempCtx, lam.body(v_pi_arg), stackDepth + 1);
                });
            } else { 
                const paramTypeHole = Hole(freshHoleName());
                return Pi(originalParamName, paramTypeHole, (v_pi_arg: Term) => {
                    let tempCtx = ctx;
                    if (v_pi_arg.tag === 'Var') { tempCtx = extendCtx(ctx, v_pi_arg.name, paramTypeHole); }
                    else { tempCtx = extendCtx(ctx, "$_internal_binder_val", paramTypeHole); }
                    return infer(tempCtx, lam.body(v_pi_arg), stackDepth + 1);
                });
            }
        }
        case 'Pi': {
            const pi = current;
            check(ctx, pi.paramType, Type(), stackDepth + 1);
            const paramName = pi.paramName; // Original name from source Pi
            const extendedCtx = extendCtx(ctx, paramName, pi.paramType);
            // pi.bodyType is already (v => TypeStructure). We need to check that TypeStructure is Type.
            const bodyTypeInstance = pi.bodyType(Var(paramName)); // Get instance of the body type
            check(extendedCtx, bodyTypeInstance, Type(), stackDepth + 1); // Check this instance is a Type
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
        // This new body function, when called by normalize/printTerm/areEqual,
        // will ensure the term it returns has been elaborated.
        lamTerm.body = (v_arg_for_body: Term): Term => {
            const freshInnerRawTerm = originalBodyFn(v_arg_for_body); 
            let ctxForInnerElaboration = ctx; 
            const currentLamParamTypeForCtx = lamTerm.paramType!; 
            if (v_arg_for_body.tag === 'Var') {
                ctxForInnerElaboration = extendCtx(ctx, v_arg_for_body.name, currentLamParamTypeForCtx);
            }
            const expectedTypeForInnerBody = expectedPi.bodyType(v_arg_for_body);
            // Recursively call `check` to elaborate `freshInnerRawTerm`.
            // This `check` is called when `lamTerm.body` is invoked.
            check(ctxForInnerElaboration, freshInnerRawTerm, expectedTypeForInnerBody, stackDepth + 1); // Increment stack depth for the recursive check call
            return freshInnerRawTerm; 
        };

        // Generate constraints for *this* lambda's immediate body based on its *original* structure.
        const tempVarForOriginalBodyCheck = Var(paramName);
        const extendedCtxForOriginalBody = extendCtx(ctx, tempVarForOriginalBodyCheck.name, lamTerm.paramType);
        check(extendedCtxForOriginalBody, originalBodyFn(tempVarForOriginalBodyCheck), expectedPi.bodyType(tempVarForOriginalBodyCheck), stackDepth + 1);
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
    constraints = []; nextHoleId = 0; nextVarId = 0;
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
            const fcMsg = fc ? `${printTerm(getTermRef(fc.t1))} vs ${printTerm(getTermRef(fc.t2))} (orig: ${fc.origin})` : "Unknown constraint";
            throw new Error(`Type error: Could not solve constraints. Approx failing: ${fcMsg}`);
        }
    } catch (e) { throw e; }
    const finalElaboratedTermStructure = termToElaborate;
    const normalizedElaboratedTerm = normalize(finalElaboratedTermStructure, initialCtx);
    const finalTypeNormalized = normalize(finalTypeToReport, initialCtx);
    return { term: normalizedElaboratedTerm, type: finalTypeNormalized };
}

function isPatternVarName(name: string, patternVarDecls: PatternVarDecl[]): boolean {
    return patternVarDecls.some(pvd => pvd.name === name);
}

function matchPattern(
    pattern: Term, termToMatch: Term, ctx: Context, // Renamed `term` to `termToMatch`
    patternVarDecls: PatternVarDecl[],
    currentSubst?: Substitution, stackDepth = 0
): Substitution | null {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("matchPattern stack depth exceeded");
    const subst = currentSubst || new Map<string, Term>();
    // `termToMatch` is passed as is from whnf/normalize loop (already head-reduced for that loop's iteration)
    // No additional whnf(termToMatch) here.
    const currentTermStruct = getTermRef(termToMatch);


    if (pattern.tag === 'Var' && isPatternVarName(pattern.name, patternVarDecls)) {
        const pvarName = pattern.name;
        const existing = subst.get(pvarName);
        if (existing) return areEqual(currentTermStruct, existing, ctx, stackDepth + 1) ? subst : null;
        subst.set(pvarName, currentTermStruct); // Substitute with the term as it is (could be non-WHNF if that's the strategy)
        return subst;
    }

    const rtPattern = getTermRef(pattern);

    if (currentTermStruct.tag === 'Hole') return null; // Cannot match concrete pattern against hole term
    if (rtPattern.tag === 'Hole') return null; 
    if (rtPattern.tag !== currentTermStruct.tag) return null;

    // Both are not Holes and have the same tag
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
            const freshV = Var(freshVarName(lamP.paramName));
            const CtxType = lamP.paramType ? getTermRef(lamP.paramType) : Hole();
            const extendedCtx = extendCtx(ctx, freshV.name, CtxType);
            // For first-order patterns, `areEqual` is used for bodies.
            // This means bodies must be alpha-beta-eta equivalent *after* pattern vars in the
            // pattern's body are substituted. This is implicitly handled if `areEqual` normalizes.
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
    const current = getTermRef(term);
    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        const replacement = subst.get(current.name);
        if (!replacement) throw new Error(`Unbound PVar ${current.name} in RHS subst`);
        return replacement;
    }
    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': return current;
        case 'App':
            return App(applySubst(current.func, subst, patternVarDecls), applySubst(current.arg, subst, patternVarDecls));
        case 'Lam': {
            const lam = current;
            const lamParam = lam.paramType ? applySubst(lam.paramType, subst, patternVarDecls) : undefined;
            const newLam = Lam(lam.paramName,
                (v_arg: Term) => applySubst(lam.body(v_arg), subst, patternVarDecls), lamParam);
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
    const ruleCheckConstraintsBackup = [...constraints];
    constraints = [];
    try {
        const lhsType = infer(patternCtx, rule.lhs);
        const rhsType = infer(patternCtx, rule.rhs);
        addConstraint(lhsType, rhsType, `Rewrite rule ${rule.name} type preservation`);
        if (!solveConstraints(patternCtx)) {
            console.error(`Rule ${rule.name} does not preserve types.`);
            const fc = constraints.find(constraint => !areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), patternCtx));
            if (fc) console.error(`  Failing constraint: ${printTerm(getTermRef(fc.t1))} = ${printTerm(getTermRef(fc.t2))}`);
            return false;
        }
        return true;
    } catch (e) {
        console.error(`Error checking rule ${rule.name}: ${(e as Error).message}`);
        return false;
    } finally { constraints = ruleCheckConstraintsBackup; }
}

function printTerm(term: Term, boundVars: string[] = [], stackDepth = 0): string {
    if (stackDepth > MAX_STACK_DEPTH) return "<print_depth_exceeded>";
    if (!term) return "<null_term>";
    const current = getTermRef(term);
    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return current.name;
        case 'Hole': return current.id;
        case 'Lam': {
            const paramName = current.paramName;
            const typeAnnotation = current._isAnnotated && current.paramType ? ` : ${printTerm(current.paramType, boundVars, stackDepth + 1)}` : '';
            const freshV = Var(paramName); 
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
}
function resetMyLambdaPi() {
    constraints = []; globalDefs.clear(); userRewriteRules.length = 0;
    nextVarId = 0; nextHoleId = 0;
}

// --- Example Usage (Example 9 test unchanged from v4 as deep elaboration in `check` should make it pass) ---
console.log("--- MyLambdaPi Final Corrected (v7): Fix Infer Regression & MatchPattern WHNF ---");
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
        const freshV3 = Var(resT3.paramName);
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
    const resTerm4 = getTermRef(result.term);
    if(resTerm4.tag !== 'Hole' || resTerm4.id !== myHole4.id) throw new Error(`Term not ${myHole4.id} for ex4, got ${printTerm(result.term)}`);
    const typeOfMyHole4 = myHole4.elaboratedType ? getTermRef(myHole4.elaboratedType) : Hole();
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
    const polyId9_source = Lam("f", f => Lam("x", x => App(f, x)));
    const concretePiType9 = Pi("f", Pi("y", Nat, _ => Nat), _fVal => Pi("x", Nat, _xVal => Nat));
    result = elaborate(polyId9_source, concretePiType9, baseCtx);
    console.log(`   Term (Elaborated): ${printTerm(result.term)}`);
    console.log(`   Type (Checked): ${printTerm(result.type)}`);
    if (!areEqual(result.type, concretePiType9, baseCtx)) throw new Error("Type mismatch for ex9 overall type");

    const elabTerm9 = getTermRef(result.term); 
    if (elabTerm9.tag === 'Lam' && elabTerm9._isAnnotated && elabTerm9.paramType && getTermRef(elabTerm9.paramType).tag === 'Pi') {
        const elabFType = getTermRef(elabTerm9.paramType) as Term & {tag:'Pi'};
        const actualInnerLam = getTermRef(elabTerm9.body(Var("f_for_test"))); 
        
        if (actualInnerLam.tag === 'Lam' && actualInnerLam._isAnnotated && actualInnerLam.paramType &&
            areEqual(actualInnerLam.paramType, Nat, baseCtx)) {
            
            const ctxForInnerBodyCheck = extendCtx(extendCtx(baseCtx, "f_for_test", elabFType), actualInnerLam.paramName, actualInnerLam.paramType);
            const innerLamBodyResultType = infer(ctxForInnerBodyCheck, actualInnerLam.body(Var(actualInnerLam.paramName)));
            
            if (areEqual(innerLamBodyResultType, Nat, ctxForInnerBodyCheck)) {
                console.log("   Correct (deep annotation preserved through normalization).");
            } else {
                throw new Error(`Inner lambda body type mismatch. Expected Nat, got ${printTerm(innerLamBodyResultType)}`);
            }
        } else {
            throw new Error(`Normalized inner lambda not annotated as expected: ${printTerm(actualInnerLam)}. Expected param type Nat. IsAnnotated: ${actualInnerLam.tag === 'Lam' && actualInnerLam._isAnnotated}, ParamType: ${actualInnerLam.tag === 'Lam' && actualInnerLam.paramType ? printTerm(actualInnerLam.paramType) : 'N/A'}`);
        }
    } else {
        throw new Error("Normalized outer lambda not annotated as expected: " + printTerm(elabTerm9));
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
    const ruleAddZ: RewriteRule = {
        name: "add_Z_N", patternVars: [pvarN_decl],
        lhs: App(App(Add, Zero), Var("N")),
        rhs: Var("N")
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
    console.error((e as Error).stack);
}