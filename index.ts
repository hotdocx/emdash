// --- MyLambdaPi Revised: Bidirectional with Unification ---

// --- Report on Changed Specification (as detailed above) ---
// This implementation focuses on a core lambda calculus with Pi types,
// bidirectional type checking, and unification-based hole solving.
// Identity types and user rewrite rules are omitted for this version.
// --- End Report ---

let nextVarId = 0;
const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarId++}`;

let nextHoleId = 0;
const freshHoleName = (): string => `?h${nextHoleId++}`;

type Term =
    | { tag: 'Type' }
    | { tag: 'Var', name: string }
    | { tag: 'Lam', paramName: string, paramType?: Term, body: (v: Term) => Term, _isAnnotated?: boolean } // _isAnnotated helps printer/debugger
    | { tag: 'App', func: Term, arg: Term }
    | { tag: 'Pi', paramName: string, paramType: Term, bodyType: (v: Term) => Term }
    | { tag: 'Hole', id: string, ref?: Term };

const Type = (): Term => ({ tag: 'Type' });
const Var = (name: string): Term => ({ tag: 'Var', name });
const Lam = (paramName: string, body: (v: Term) => Term, paramType?: Term): Term =>
    ({ tag: 'Lam', paramName, paramType, body, _isAnnotated: !!paramType });
const App = (func: Term, arg: Term): Term => ({ tag: 'App', func, arg });
const Pi = (paramName: string, paramType: Term, bodyType: (v: Term) => Term): Term =>
    ({ tag: 'Pi', paramName, paramType, bodyType });
const Hole = (id?: string): Term => ({ tag: 'Hole', id: id || freshHoleName(), ref: undefined });

type Binding = { name: string, type: Term };
type Context = Binding[];
const emptyCtx: Context = [];
const extendCtx = (ctx: Context, name: string, type: Term): Context => [{ name, type }, ...ctx];
const lookupCtx = (ctx: Context, name: string): Binding | undefined => ctx.find(b => b.name === name);

interface Constraint { t1: Term; t2: Term; origin?: string; }
const constraints: Constraint[] = []; // Global store for constraints

function addConstraint(t1: Term, t2: Term, origin?: string) {
    constraints.push({ t1, t2, origin });
}

function getTermRef(term: Term): Term {
    if (term.tag === 'Hole' && term.ref) return getTermRef(term.ref);
    return term;
}

function whnf(term: Term, ctx: Context, depth: number = 0): Term {
    if (depth > 100) throw new Error("WHNF depth exceeded");
    const current = getTermRef(term);

    if (current.tag === 'App') {
        const funcNorm = whnf(current.func, ctx, depth + 1);
        if (funcNorm.tag === 'Lam') {
            return whnf(funcNorm.body(current.arg), ctx, depth + 1);
        }
        return App(funcNorm, current.arg); // Reconstruct with normalized function part
    }
    return current;
}

function normalize(term: Term, ctx: Context, depth: number = 0): Term {
    if (depth > 100) throw new Error("Normalize depth exceeded");
    const current = getTermRef(term);

    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': return current;
        case 'Lam':
            const normParamType = current.paramType ? normalize(current.paramType, ctx, depth + 1) : undefined;
            // To normalize body, apply to a fresh var under extended context
            // This is needed if we want to see solved holes *inside* the body structure for printing.
            // For HOAS, the body function itself doesn't change unless its captured env changes or it's re-constructed.
            const freshNameLam = freshVarName(current.paramName);
            const freshVLam = Var(freshNameLam);
            const lamCtxType = normParamType || (current.paramType ? normalize(current.paramType, ctx) : Hole()); // Best guess for context
            const extendedLamCtx = extendCtx(ctx, freshNameLam, lamCtxType);

            // Create a new lambda with potentially normalized type and body structure
            return Lam(current.paramName, v => normalize(current.body(v), extendedLamCtx, depth +1), normParamType);
        case 'App':
            const normFunc = normalize(current.func, ctx, depth + 1);
            const normArg = normalize(current.arg, ctx, depth + 1);
            if (normFunc.tag === 'Lam') {
                return normalize(normFunc.body(normArg), ctx, depth + 1);
            }
            return App(normFunc, normArg);
        case 'Pi':
            const normPiParamType = normalize(current.paramType, ctx, depth + 1);
            const freshNamePi = freshVarName(current.paramName);
            const freshVPi = Var(freshNamePi);
            const extendedPiCtx = extendCtx(ctx, freshNamePi, normPiParamType);
            return Pi(current.paramName, normPiParamType, v => normalize(current.bodyType(v), extendedPiCtx, depth + 1));
    }
}

function areEqual(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > 50) throw new Error("Equality check depth exceeded");

    const normT1 = whnf(t1, ctx); // Use WHNF for equality check efficiency
    const normT2 = whnf(t2, ctx);

    if (normT1.tag === 'Hole' || normT2.tag === 'Hole') {
        return (normT1.tag === 'Hole' && normT2.tag === 'Hole' && normT1.id === normT2.id);
    }
    if (normT1.tag !== normT2.tag) return false;

    switch (normT1.tag) {
        case 'Type': return true;
        case 'Var': return normT1.name === (normT2 as typeof normT1).name;
        case 'App':
            return areEqual(normT1.func, (normT2 as typeof normT1).func, ctx, depth + 1) &&
                   areEqual(normT1.arg, (normT2 as typeof normT1).arg, ctx, depth + 1);
        case 'Lam': {
            const t2Lam = normT2 as typeof normT1;
            const paramTypesOk = (!normT1.paramType && !t2Lam.paramType) ||
                                 (normT1.paramType && t2Lam.paramType && areEqual(normT1.paramType, t2Lam.paramType, ctx, depth + 1));
            if (!paramTypesOk) return false;
            const freshNameEqLam = freshVarName("eqLam");
            const freshVarEqLam = Var(freshNameEqLam);
            const CtxType = normT1.paramType || Hole(); // Use specified type or a placeholder
            const extendedCtx = extendCtx(ctx, freshNameEqLam, CtxType);
            return areEqual(normT1.body(freshVarEqLam), t2Lam.body(freshVarEqLam), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const t2Pi = normT2 as typeof normT1;
            if (!areEqual(normT1.paramType, t2Pi.paramType, ctx, depth + 1)) return false;
            const freshNameEqPi = freshVarName("eqPi");
            const freshVarEqPi = Var(freshNameEqPi);
            const extendedCtx = extendCtx(ctx, freshNameEqPi, normT1.paramType);
            return areEqual(normT1.bodyType(freshVarEqPi), t2Pi.bodyType(freshVarEqPi), extendedCtx, depth + 1);
        }
    }
    return false; // Should be exhaustive
}

function termContainsHole(term: Term, holeId: string, visited: Set<string>): boolean {
    const current = getTermRef(term); // Follow existing refs
    if (current.tag === 'Hole') {
        if (current.id === holeId) return true;
        // If current.ref was already followed by getTermRef, this path is redundant.
        // But if current.ref could point to another hole, this check is useful.
        // However, getTermRef is recursive. So if current is a hole, it's an unsolved one.
        return false;
    }
    if (visited.has(printTerm(current))) return false; // Avoid cycles in non-HOAS term graph
    visited.add(printTerm(current));


    switch (current.tag) {
        case 'Type': case 'Var': return false;
        case 'App':
            return termContainsHole(current.func, holeId, visited) ||
                   termContainsHole(current.arg, holeId, visited);
        case 'Lam':
            return (current.paramType && termContainsHole(current.paramType, holeId, visited)) ||
                   false; // Simplification: Not inspecting HOAS body for free hole occurrences
                          // A true occurs check for HOAS is much more involved.
                          // Assume a hole cannot be defined in terms of itself via a lambda it is part of.
        case 'Pi':
            return termContainsHole(current.paramType, holeId, visited) ||
                   false; // Similar simplification for Pi bodyType
    }
    return false;
}


function unify(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    if (depth > 50) throw new Error(`Unification depth exceeded: ${printTerm(t1)} vs ${printTerm(t2)}`);

    const normT1 = getTermRef(t1); // Chase refs
    const normT2 = getTermRef(t2);

    if (normT1 === normT2 && normT1.tag !== 'Hole') return true; // Physical identity (and not an unsolved hole)
    if (areEqual(normT1, normT2, ctx)) return true; // Already definitionally equal

    // Handle hole cases (symmetric)
    if (normT1.tag === 'Hole') return unifyHole(normT1, normT2, ctx, depth);
    if (normT2.tag === 'Hole') return unifyHole(normT2, normT1, ctx, depth);

    // Different tags, not holes -> fail
    if (normT1.tag !== normT2.tag) return false;

    switch (normT1.tag) {
        case 'App':
            return unify(normT1.func, (normT2 as typeof normT1).func, ctx, depth + 1) &&
                   unify(normT1.arg, (normT2 as typeof normT1).arg, ctx, depth + 1);
        case 'Lam': {
            const t2Lam = normT2 as typeof normT1;
            // Parameter types: if both exist, unify. If one exists and other doesn't, this is tricky.
            // If `λx:A.B` vs `λx.B'`, need to make `?paramTypeOfSecond = A`.
            // This should typically be handled by `check` creating constraints earlier.
            // For direct unification:
            if (normT1.paramType && t2Lam.paramType) {
                if (!unify(normT1.paramType, t2Lam.paramType, ctx, depth + 1)) return false;
            } else if (normT1.paramType && !t2Lam.paramType) { // t2Lam.paramType becomes normT1.paramType (via a hole if t2Lam was `λx.?T.B`)
                 // This case implies t2Lam's paramType should be a hole that gets unified.
                 // If t2Lam was truly unnanotated with no hole, direct unify is harder.
                 // Assume constraints handle this, or direct structural mismatch here.
                 return false;
            } else if (!normT1.paramType && t2Lam.paramType) {
                 return false;
            }
            // Bodies:
            const freshNameUnifyLam = freshVarName("unifyLam");
            const freshVarUnifyLam = Var(freshNameUnifyLam);
            // Use the (now unified, if present) param type for context
            const CtxType = normT1.paramType ? getTermRef(normT1.paramType) : Hole();
            const extendedCtx = extendCtx(ctx, freshNameUnifyLam, CtxType);
            return unify(normT1.body(freshVarUnifyLam), t2Lam.body(freshVarUnifyLam), extendedCtx, depth + 1);
        }
        case 'Pi': {
            const t2Pi = normT2 as typeof normT1;
            if (!unify(normT1.paramType, t2Pi.paramType, ctx, depth + 1)) return false;
            const freshNameUnifyPi = freshVarName("unifyPi");
            const freshVarUnifyPi = Var(freshNameUnifyPi);
            const extendedCtx = extendCtx(ctx, freshNameUnifyPi, getTermRef(normT1.paramType)); // Use unified type
            return unify(normT1.bodyType(freshVarUnifyPi), t2Pi.bodyType(freshVarUnifyPi), extendedCtx, depth + 1);
        }
    }
    return false; // Var, Type should be caught by areEqual or hole unification
}

function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
    // hole.ref should have been chased by getTermRef before calling unifyHole
    // So, `hole` here is an unsolved hole.
    const normTerm = getTermRef(term); // Ensure term is also fully dereferenced

    if (normTerm.tag === 'Hole') { // ?H1 = ?H2
        if (hole.id === normTerm.id) return true; // ?H = ?H
        // Set one to point to the other. Arbitrarily, make normTerm (the arg) point to `hole`.
        // This means `hole` becomes the representative.
        (normTerm as Term & {tag: 'Hole'}).ref = hole;
        return true;
    }

    // Occurs check: ?H = ...?H...
    if (termContainsHole(normTerm, hole.id, new Set())) {
        // console.warn(`Occurs check failed: ${hole.id} in ${printTerm(normTerm)}`);
        return false;
    }

    hole.ref = normTerm;
    return true;
}

function solveConstraints(ctx: Context): boolean {
    let changedInIteration = true;
    let iterations = 0;
    const maxIterations = constraints.length * 2 + 20; // Safety break

    while (changedInIteration && iterations < maxIterations) {
        changedInIteration = false;
        iterations++;
        for (let i = 0; i < constraints.length; i++) {
            const constraint = constraints[i];
            const t1Ref = getTermRef(constraint.t1);
            const t2Ref = getTermRef(constraint.t2);

            if (areEqual(t1Ref, t2Ref, ctx)) continue; // Already satisfied

            if (unify(t1Ref, t2Ref, ctx)) {
                changedInIteration = true; // Unification succeeded, might have set a hole ref
            } else {
                 // If unify hard fails for non-holes, or for holes due to occurs check/mismatch
                // console.error(`Failed to unify constraint: ${printTerm(constraint.t1)} (${printTerm(t1Ref)}) = ${printTerm(constraint.t2)} (${printTerm(t2Ref)}) ${constraint.origin ? `(${constraint.origin})` : ''}`);
                return false; // Unification failed for this constraint
            }
        }
    }

    if (iterations >= maxIterations && changedInIteration) {
        console.warn("Constraint solving reached max iterations and was still making changes.");
    }

    // Final check: all constraints must be definitionally equal
    for (const constraint of constraints) {
        if (!areEqual(constraint.t1, constraint.t2, ctx)) {
            console.error(`Unsolved constraint after iterations: ${printTerm(constraint.t1)} = ${printTerm(constraint.t2)} ${constraint.origin ? `(${constraint.origin})` : ''}`);
            return false;
        }
    }
    return true;
}

function infer(ctx: Context, term: Term, depth: number = 0): Term {
    if (depth > 50) throw new Error(`Type inference depth exceeded for ${printTerm(term)}`);
    const current = getTermRef(term);

    switch (current.tag) {
        case 'Type': return Type();
        case 'Var':
            const binding = lookupCtx(ctx, current.name);
            if (!binding) throw new Error(`Unbound variable: ${current.name}`);
            return binding.type;
        case 'Hole':
            const holeType = Hole(freshHoleName()); // Type of a hole is another hole: ?h : ?h_type
            // Implicitly, the system will try to solve holeType if possible
            // For example, if ?h is an argument to `succ : Nat -> Nat`, then ?h_type will be Nat.
            return holeType;
        case 'App': {
            const funcType = infer(ctx, current.func, depth + 1);
            const normFuncType = whnf(funcType, ctx); // WHNF to expose Pi or Hole

            if (normFuncType.tag === 'Hole') { // funcType is ?alpha. Expect ?alpha = Pi x:?T1. ?T2
                const argTypeHole = Hole(freshHoleName());
                const resultTypeHole = Hole(freshHoleName());
                const expectedPiForFunc = Pi(freshVarName("appArg"), argTypeHole, _ => resultTypeHole);
                addConstraint(normFuncType, expectedPiForFunc, `App func type hole ${printTerm(current.func)}`);
                check(ctx, current.arg, argTypeHole, depth + 1); // Arg must match ?T1
                return resultTypeHole; // Result is ?T2
            }
            if (normFuncType.tag !== 'Pi') {
                throw new Error(`Cannot apply non-function: ${printTerm(current.func)} of type ${printTerm(normFuncType)}`);
            }
            check(ctx, current.arg, normFuncType.paramType, depth + 1);
            return normFuncType.bodyType(current.arg); // HOAS substitution for dependent type
        }
        case 'Lam': {
            if (current.paramType) { // Annotated: λx:A. body
                check(ctx, current.paramType, Type(), depth + 1); // A must be a type
                const paramName = current.paramName || freshVarName("lam");
                const extendedCtx = extendCtx(ctx, paramName, current.paramType);
                const bodyType = infer(extendedCtx, current.body(Var(paramName)), depth + 1);
                return Pi(paramName, current.paramType, _ => bodyType); // Body type might depend on param
            } else { // Unannotated: λx. body
                const paramName = current.paramName || freshVarName("lam");
                const paramTypeHole = Hole(freshHoleName());
                const extendedCtx = extendCtx(ctx, paramName, paramTypeHole);
                const bodyType = infer(extendedCtx, current.body(Var(paramName)), depth + 1);
                return Pi(paramName, paramTypeHole, _ => bodyType);
            }
        }
        case 'Pi': { // Πx:A. B
            check(ctx, current.paramType, Type(), depth + 1); // A must be a type
            const paramName = current.paramName || freshVarName("pi");
            const extendedCtx = extendCtx(ctx, paramName, current.paramType);
            check(extendedCtx, current.bodyType(Var(paramName)), Type(), depth + 1); // B(x) must be a type
            return Type(); // Pi types live in Type
        }
    }
}

function check(ctx: Context, term: Term, expectedType: Term, depth: number = 0): void {
    if (depth > 50) throw new Error(`Type checking depth exceeded for ${printTerm(term)} : ${printTerm(expectedType)}`);
    const current = getTermRef(term);
    const normExpectedType = whnf(expectedType, ctx); // WHNF for expected type to expose Pi/Hole

    // Bidirectional rule for unannotated lambda:
    if (current.tag === 'Lam' && !current.paramType && normExpectedType.tag === 'Pi') {
        const paramName = current.paramName || freshVarName("lamChk");
        // Fill in the paramType of the Lam term instance if it was a hole and got solved
        // This is for elaboration, making the term more explicit.
        // (current as {paramType?: Term}).paramType = normExpectedType.paramType; // Mutating original term for elaboration
        
        const extendedCtx = extendCtx(ctx, paramName, normExpectedType.paramType);
        check(extendedCtx, current.body(Var(paramName)), normExpectedType.bodyType(Var(paramName)), depth + 1);
        return;
    }
    // Rule for holes: if checking ?h against type T, then type of ?h must be T.
    // infer(?h) produces ?h_type. So add constraint ?h_type = T.
    if (current.tag === 'Hole') {
        const inferredHoleType = infer(ctx, current, depth + 1); // This will be a new hole, e.g. ?type_of_current_hole
        addConstraint(inferredHoleType, normExpectedType, `Hole ${current.id} checked against ${printTerm(normExpectedType)}`);
        return;
    }

    // General case: infer type and check if it's unifiable with expectedType
    const inferredType = infer(ctx, current, depth + 1);
    addConstraint(inferredType, normExpectedType, `Check general case: ${printTerm(current)}`);
}

interface ElaborationResult { term: Term; type: Term; }

function elaborate(term: Term, expectedType?: Term, initialCtx: Context = emptyCtx): ElaborationResult {
    constraints.length = 0;
    nextVarId = 0; nextHoleId = 0; // Reset gensym counters

    let finalTypeToReport: Term;
    if (expectedType) {
        check(initialCtx, term, expectedType);
        finalTypeToReport = expectedType;
    } else {
        finalTypeToReport = infer(initialCtx, term);
    }

    if (!solveConstraints(initialCtx)) {
        const failingConstraint = constraints.find(c => !areEqual(getTermRef(c.t1), getTermRef(c.t2), initialCtx));
        const fcMsg = failingConstraint ? `${printTerm(failingConstraint.t1)} = ${printTerm(failingConstraint.t2)} (origin: ${failingConstraint.origin})` : "Unknown constraint";
        throw new Error(`Type error: Could not solve constraints. Last failing (approx): ${fcMsg}`);
    }

    const elaboratedTerm = normalize(term, initialCtx); // Normalize to fill in solved hole refs
    const finalTypeNormalized = normalize(finalTypeToReport, initialCtx);

    return { term: elaboratedTerm, type: finalTypeNormalized };
}

function printTerm(term: Term, boundVars: string[] = []): string {
    const current = getTermRef(term); // Always print the resolved reference

    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return current.name;
        case 'Hole': return current.id;
        case 'Lam': {
            const paramName = current.paramName || `x${boundVars.length}`;
            const newBoundVars = [...boundVars, paramName];
            // Use the potentially elaborated paramType if it exists
            const typeAnnotation = current.paramType ? ` : ${printTerm(current.paramType, boundVars)}` : '';
            return `(λ ${paramName}${typeAnnotation}. ${printTerm(current.body(Var(paramName)), newBoundVars)})`;
        }
        case 'App':
            return `(${printTerm(current.func, boundVars)} ${printTerm(current.arg, boundVars)})`;
        case 'Pi': {
            const paramName = current.paramName || `x${boundVars.length}`;
            const newBoundVars = [...boundVars, paramName];
            return `(Π ${paramName} : ${printTerm(current.paramType, boundVars)}. ${printTerm(current.bodyType(Var(paramName)), newBoundVars)})`;
        }
    }
}

// --- Example Usage ---
console.log("--- MyLambdaPi Revised Examples (Bidirectional + Unification) ---");

const Nat = Var("Nat");
const Bool = Var("Bool");

let baseCtx = emptyCtx;
baseCtx = extendCtx(baseCtx, "Nat", Type());
baseCtx = extendCtx(baseCtx, "Bool", Type());
baseCtx = extendCtx(baseCtx, "zero", Nat);
baseCtx = extendCtx(baseCtx, "succ", Pi("n", Nat, _ => Nat));
baseCtx = extendCtx(baseCtx, "true", Bool);
baseCtx = extendCtx(baseCtx, "expectsNatFunc", Pi("f", Pi("_", Nat, _ => Nat), _ => Bool));


// 1. Infer type of annotated identity function λx:Nat. x
try {
    const idNatAnnotated = Lam("x", x => x, Nat);
    const result = elaborate(idNatAnnotated, undefined, baseCtx);
    console.log(`\n1. Infer (λx:Nat. x)`);
    console.log(`   Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`); // Expected: Πx:Nat. Nat
    const expected = Pi("x", Nat, _ => Nat);
    if (!areEqual(result.type, expected, baseCtx)) throw new Error("Type mismatch for ex1");
    console.log("   Correct.");
} catch (e) { console.error("Error in example 1:", (e as Error).message); }


// 2. Check unannotated identity function λx. x against Πx:Nat. Nat
try {
    const idUnannotated = Lam("x", x => x);
    const targetType = Pi("x", Nat, _ => Nat);
    const result = elaborate(idUnannotated, targetType, baseCtx);
    console.log(`\n2. Check (λx. x) against (Πx:Nat. Nat)`);
    console.log(`   Term: ${printTerm(result.term)}`); // Expected: (λ x : Nat. x)
    console.log(`   Type: ${printTerm(result.type)}`); // Expected: (Π x : Nat. Nat)
    if (!areEqual(result.type, targetType, baseCtx)) throw new Error("Type mismatch for ex2 type");
    if (result.term.tag === 'Lam' && result.term.paramType && areEqual(result.term.paramType, Nat, baseCtx)) {
         console.log("   Correct, lambda param annotated.");
    } else {
        throw new Error("Lambda not annotated as expected for ex2");
    }
} catch (e) { console.error("Error in example 2:", (e as Error).message); }

// 3. Infer type of unannotated identity function λx. x
try {
    const idUnannotatedInfer = Lam("x", x => x);
    const result = elaborate(idUnannotatedInfer, undefined, baseCtx);
    console.log(`\n3. Infer (λx. x)`);
    console.log(`   Term: ${printTerm(result.term)}`); // (λ x : ?hA. x)
    console.log(`   Type: ${printTerm(result.type)}`); // (Π x : ?hA. ?hA)
    if (result.type.tag === 'Pi' && result.type.paramType.tag === 'Hole') {
        const paramHole = result.type.paramType;
        const bodyYieldsParamHole = areEqual(result.type.bodyType(Var("_")), paramHole, baseCtx);
        if (bodyYieldsParamHole) {
             console.log(`   Correct: Type is Πx:${paramHole.id}. ${paramHole.id}`);
        } else throw new Error("Body type of Pi does not match param hole for ex3");
    } else throw new Error("Inferred type for unannotated id not Pi with hole for ex3");
} catch (e) { console.error("Error in example 3:", (e as Error).message); }


// 4. Application with a hole: (λx:Nat. x) _
try {
    const idFunc = Lam("x", x => x, Nat);
    const myHole = Hole("argHole");
    const appWithHole = App(idFunc, myHole);
    const result = elaborate(appWithHole, Nat, baseCtx); // Check overall expr is Nat
    console.log(`\n4. Check ((λx:Nat. x) ?argHole) against Nat`);
    console.log(`   Term: ${printTerm(result.term)}`); // (λx:Nat. x) ?argHole OR ?argHole after normalization
    console.log(`   Type: ${printTerm(result.type)}`); // Nat

    // Check type of the hole itself by inferring it in a new elaboration
    const holeTypeResult = elaborate(myHole, undefined, baseCtx);
    console.log(`   Inferred type of ?argHole: ${printTerm(holeTypeResult.type)}`); // Expected Nat
    if (!areEqual(holeTypeResult.type, Nat, baseCtx)) throw new Error("Hole type not Nat for ex4");
    console.log("   Correct.");
} catch (e) { console.error("Error in example 4:", (e as Error).message); }


// 5. Infer type of (λf. λx. f x)
try {
    const complexLam = Lam("f", f => Lam("x", x => App(f, x)));
    const result = elaborate(complexLam, undefined, baseCtx);
    console.log(`\n5. Infer (λf. λx. f x)`);
    console.log(`   Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`);
    // Expected: Πf:(Πy:?A. ?B). Πx:?A. ?B
    if (result.type.tag === 'Pi') { // Outer Pi for f
        const typeOfF = result.type.paramType; // Should be Pi y:?A. ?B
        const bodyTypeOuter = result.type.bodyType(Var("dummyF")); // Should be Pi x:?A. ?B
        if (typeOfF.tag === 'Pi' && typeOfF.paramType.tag === 'Hole' &&
            bodyTypeOuter.tag === 'Pi' && bodyTypeOuter.paramType.tag === 'Hole' &&
            typeOfF.paramType.id === bodyTypeOuter.paramType.id) { // ?A matches
            const typeOfF_body = typeOfF.bodyType(Var("dummyY"));
            const bodyTypeOuter_body = bodyTypeOuter.bodyType(Var("dummyX"));
            if (typeOfF_body.tag === 'Hole' && bodyTypeOuter_body.tag === 'Hole' &&
                typeOfF_body.id === bodyTypeOuter_body.id) { // ?B matches
                console.log(`   Correct type structure: Πf:(Πy:${typeOfF.paramType.id}. ${typeOfF_body.id}). Πx:${bodyTypeOuter.paramType.id}. ${bodyTypeOuter_body.id}`);
            } else throw new Error("?B holes do not match for ex5");
        } else throw new Error("?A holes do not match or structure incorrect for ex5");
    } else throw new Error("Overall type not Pi for ex5");
} catch (e) { console.error("Error in example 5:", (e as Error).message); }


// 6. Type error: checking (λx:Nat. x) against Bool
try {
    const idNat = Lam("x", x => x, Nat);
    elaborate(idNat, Bool, baseCtx);
    console.error("\nError in example 6: Type error was NOT caught.");
} catch (e) {
    console.log(`\n6. Check (λx:Nat. x) against Bool: Caught expected error: ${(e as Error).message.slice(0,100)}...`);
}

// 7. Application whose function type needs to be inferred via a hole
// (expectsNatFunc _ ) where expectsNatFunc : ( (Nat->Nat) -> Bool ) and _ is the argument
try {
    const fHole = Hole("f_hole");
    const appTerm = App(Var("expectsNatFunc"), fHole); // expectsNatFunc(?f_hole)
    const result = elaborate(appTerm, undefined, baseCtx); // Infer type, should be Bool
    console.log(`\n7. Infer (expectsNatFunc ?f_hole)`);
    console.log(`   Term: ${printTerm(result.term)}`);
    console.log(`   Type: ${printTerm(result.type)}`); // Expected: Bool

    if (!areEqual(result.type, Bool, baseCtx)) throw new Error("App result type not Bool for ex7");

    // Check type of fHole
    const fHoleTypeResult = elaborate(fHole, undefined, baseCtx);
    const expectedFHoleType = Pi("_", Nat, _ => Nat);
    console.log(`   Inferred type of ?f_hole: ${printTerm(fHoleTypeResult.type)}`); // Expected: Nat -> Nat
    if (!areEqual(fHoleTypeResult.type, expectedFHoleType, baseCtx)) throw new Error("Hole type for f not Nat->Nat for ex7");
    console.log("   Correct.");
} catch (e) { console.error("Error in example 7:", (e as Error).message); }


// 8. Unification that should fail: Nat = Bool
try {
    constraints.length = 0;
    addConstraint(Nat, Bool, "Nat = Bool direct test");
    if (solveConstraints(baseCtx)) {
        console.error("\nError in example 8: Nat = Bool constraint incorrectly solved.");
    } else {
        console.log("\n8. Nat = Bool constraint correctly failed to solve.");
    }
} catch (e) { console.error("Error in example 8:", (e as Error).message); }

// 9. Check polymorphic id `λf. λx. f x` against a concrete type
// Πf:(Nat -> Nat). Πx:Nat. Nat
try {
    const polyId = Lam("f", f => Lam("x", x => App(f, x)));
    const concretePiType = Pi("f", Pi("_y", Nat, _ => Nat), _fVal => Pi("_x", Nat, _xVal => Nat));
    
    const result = elaborate(polyId, concretePiType, baseCtx);
    console.log(`\n9. Check (λf. λx. f x) against (Πf:(Nat→Nat). Πx:Nat. Nat)`);
    console.log(`   Term (Elaborated): ${printTerm(result.term)}`);
    console.log(`   Type (Checked): ${printTerm(result.type)}`);
     if (!areEqual(result.type, concretePiType, baseCtx)) throw new Error("Type mismatch for ex9");
    console.log("   Correct.");
} catch (e) { console.error("Error in example 9:", (e as Error).message); }