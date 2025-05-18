// --- MyLambdaPi with Emdash Phase 1: Core Categories ---

let nextVarId = 0;
const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarId++}`;

let nextHoleId = 0;
const freshHoleName = (): string => `?h${nextHoleId++}`;

// --- Term Definition ---
type BaseTerm =
    | { tag: 'Type' }
    | { tag: 'Var', name: string }
    | { tag: 'Lam', paramName: string, paramType?: Term, body: (v: Term) => Term, _isAnnotated: boolean }
    | { tag: 'App', func: Term, arg: Term }
    | { tag: 'Pi', paramName: string, paramType: Term, bodyType: (v: Term) => Term }
    | { tag: 'Hole', id: string, ref?: Term, elaboratedType?: Term }
    // Emdash Phase 1: Core Categories
    | { tag: 'CatTerm' } // Represents the type "Cat"
    | { tag: 'ObjTerm', cat: Term } // Represents "Obj C", the type of objects in category C
    | { tag: 'HomTerm', cat: Term, dom: Term, cod: Term } // Represents "Hom C X Y"
    | { tag: 'MkCat_',
        objRepresentation: Term, // A term of type Type, e.g., Var("Nat")
        homRepresentation: Term, // A term of type Pi(X:objR, Pi(Y:objR, Type)), e.g., Lam(X => Lam(Y => Arrow(X,Y)))
        composeImplementation: Term // A term for composition
      }
    | { tag: 'IdentityMorph', // id_X
        obj: Term,
        cat_IMPLICIT?: Term // The category A to which X:Obj(A) belongs
      }
    | { tag: 'ComposeMorph', // g . f
        g: Term,
        f: Term,
        cat_IMPLICIT?: Term,
        objX_IMPLICIT?: Term, // dom f
        objY_IMPLICIT?: Term, // cod f / dom g
        objZ_IMPLICIT?: Term  // cod g
      };

type Term = BaseTerm;
type PatternVarDecl = { name: string, type: Term };

// --- Term Constructors ---
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

// Emdash Phase 1 Constructors
const CatTerm = (): Term & { tag: 'CatTerm' } => ({ tag: 'CatTerm' });
const ObjTerm = (cat: Term): Term & { tag: 'ObjTerm' } => ({ tag: 'ObjTerm', cat });
const HomTerm = (cat: Term, dom: Term, cod: Term): Term & { tag: 'HomTerm' } => ({ tag: 'HomTerm', cat, dom, cod });
const MkCat_ = (objRepresentation: Term, homRepresentation: Term, composeImplementation: Term): Term & { tag: 'MkCat_' } =>
    ({ tag: 'MkCat_', objRepresentation, homRepresentation, composeImplementation });
const IdentityMorph = (obj: Term, cat_IMPLICIT?: Term): Term & { tag: 'IdentityMorph' } =>
    ({ tag: 'IdentityMorph', obj, cat_IMPLICIT });
const ComposeMorph = (g: Term, f: Term, cat_IMPLICIT?: Term, objX_IMPLICIT?: Term, objY_IMPLICIT?: Term, objZ_IMPLICIT?: Term): Term & { tag: 'ComposeMorph' } =>
    ({ tag: 'ComposeMorph', g, f, cat_IMPLICIT, objX_IMPLICIT, objY_IMPLICIT, objZ_IMPLICIT });


type Binding = { name: string, type: Term };
type Context = Binding[];
const emptyCtx: Context = [];
const extendCtx = (ctx: Context, name: string, type: Term): Context => [{ name, type }, ...ctx];
const lookupCtx = (ctx: Context, name: string): Binding | undefined => ctx.find(b => b.name === name);

interface GlobalDef {
    name: string;
    type: Term;
    value?: Term;
    isConstantSymbol?: boolean; // For `constant symbol` which cannot have a value and no rewrite head
}
const globalDefs: Map<string, GlobalDef> = new Map();

function defineGlobal(name: string, type: Term, value?: Term, isConstantSymbol: boolean = false) {
    if (globalDefs.has(name)) console.warn(`Warning: Redefining global ${name}`);
    if (isConstantSymbol && value !== undefined) {
        throw new Error(`Constant symbol ${name} cannot have a definition/value.`);
    }
    globalDefs.set(name, { name, type, value, isConstantSymbol });
}


interface RewriteRule { name: string; patternVars: PatternVarDecl[]; lhs: Term; rhs: Term; }
const userRewriteRules: RewriteRule[] = [];
function addRewriteRule(rule: RewriteRule) {
    // Future: could check if rule.lhs.tag is a 'constant' EMDASH term tag.
    // For now, whnf/normalize handles this.
    userRewriteRules.push(rule);
}

interface UnificationRule {
    name: string;
    patternVars: PatternVarDecl[];
    lhsPattern1: Term;
    lhsPattern2: Term;
    rhsNewConstraints: Array<{ t1: Term, t2: Term }>;
}
const userUnificationRules: UnificationRule[] = [];
function addUnificationRule(rule: UnificationRule) {
    userUnificationRules.push(rule);
}

type Substitution = Map<string, Term>;
interface Constraint { t1: Term; t2: Term; origin?: string; }
let constraints: Constraint[] = [];

function addConstraint(t1: Term, t2: Term, origin?: string) { constraints.push({ t1, t2, origin }); }
function getTermRef(term: Term): Term {
    if (term.tag === 'Hole' && term.ref) return getTermRef(term.ref);
    return term;
}

const MAX_RECURSION_DEPTH = 100;
const MAX_STACK_DEPTH = 70; // Careful with deep structures

// --- Symbol Properties ---
// For Emdash, certain term tags imply these properties.
// `constant symbol` implies unification-injective and no rewrite rule with it as head.
const EMDASH_CONSTANT_SYMBOLS = new Set<string>(['CatTerm', 'ObjTerm', 'HomTerm', 'MkCat_']);
const EMDASH_UNIFICATION_INJECTIVE_SYMBOLS = new Set<string>(['IdentityMorph', /* Not ComposeMorph */]);
// Note: MkCat_ is constant, so its injectivity is handled by its 'constant' nature.
// ObjTerm(C1) vs ObjTerm(C2) -> C1 vs C2 due to injectivity implied by being constant type formers.
// HomTerm(C1,D1,CD1) vs HomTerm(C2,D2,CD2) -> C1vC2, D1vD2, CD1vCD2

function isEmdashConstantSymbolTag(tag: string): boolean {
    return EMDASH_CONSTANT_SYMBOLS.has(tag);
}
function isEmdashUnificationInjectiveTag(tag: string): boolean {
    // A constant symbol is also unification injective in its structure by definition for us.
    return EMDASH_CONSTANT_SYMBOLS.has(tag) || EMDASH_UNIFICATION_INJECTIVE_SYMBOLS.has(tag);
}

// --- WHNF & Normalize (with Emdash considerations) ---

function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`WHNF stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    let current = getTermRef(term);

    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        let changedInThisIteration = false;
        const termAtStartOfIteration = current;

        // 1. Delta Reduction (for Vars)
        if (current.tag === 'Var') {
            const gdef = globalDefs.get(current.name);
            if (gdef && gdef.value && !gdef.isConstantSymbol) { // Constant symbols don't unfold
                const valRef = getTermRef(gdef.value);
                if (valRef !== current) {
                     current = valRef;
                     changedInThisIteration = true;
                }
            }
        }

        // Specific Emdash Reductions (treated like high-priority rewrite rules)
        const termAfterDelta = current;
        let termAfterEmdashRules = termAfterDelta;

        if (termAfterEmdashRules.tag === 'ObjTerm' && getTermRef(termAfterEmdashRules.cat).tag === 'MkCat_') {
            const mkCatTerm = getTermRef(termAfterEmdashRules.cat) as Term & {tag: 'MkCat_'};
            termAfterEmdashRules = mkCatTerm.objRepresentation; // Rule: Obj(MkCat(O,H,C)) -> O
        } else if (termAfterEmdashRules.tag === 'HomTerm' && getTermRef(termAfterEmdashRules.cat).tag === 'MkCat_') {
            const mkCatTerm = getTermRef(termAfterEmdashRules.cat) as Term & {tag: 'MkCat_'};
            const H_repr = mkCatTerm.homRepresentation;
            // Rule: Hom(MkCat(O,H,C), X, Y) -> H X Y
            termAfterEmdashRules = App(App(H_repr, termAfterEmdashRules.dom), termAfterEmdashRules.cod);
        } else if (termAfterEmdashRules.tag === 'ComposeMorph') {
            const comp = termAfterEmdashRules;
            const catVal = comp.cat_IMPLICIT ? getTermRef(comp.cat_IMPLICIT) : undefined; // cat must be resolved for this rule
            if (catVal && catVal.tag === 'MkCat_') {
                const C_impl = catVal.composeImplementation;
                // Rule: Comp(g,f, cat=MkCat(O,H,Cimpl), X,Y,Z) -> Cimpl X Y Z g f
                // All objX/Y/Z must be resolved now.
                if (comp.objX_IMPLICIT && comp.objY_IMPLICIT && comp.objZ_IMPLICIT) {
                    termAfterEmdashRules = App(App(App(App(App(C_impl, getTermRef(comp.objX_IMPLICIT)), getTermRef(comp.objY_IMPLICIT)), getTermRef(comp.objZ_IMPLICIT)), comp.g), comp.f);
                }
            }
        }
        // Add identity/composition rules here if they are to be treated as direct reductions not user rules
        // Example: Compose(g, Id(X)) -> g
        // For now, let's put them in userRewriteRules setup for Phase 1.

        if (termAfterEmdashRules !== termAfterDelta) {
            current = termAfterEmdashRules;
            changedInThisIteration = true;
        }

        // 2. User-Defined Rewrite Rules (if not a constant symbol head)
        const termBeforeUserRules = current;
        if (!isEmdashConstantSymbolTag(current.tag) && !(current.tag === 'Var' && globalDefs.get(current.name)?.isConstantSymbol)) {
            for (const rule of userRewriteRules) {
                const subst = matchPattern(rule.lhs, termBeforeUserRules, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    const rhsApplied = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                    if (rhsApplied !== termBeforeUserRules) {
                        current = rhsApplied;
                        changedInThisIteration = true;
                    }
                    break; 
                }
            }
        }
        
        current = getTermRef(current);

        if (!changedInThisIteration && current === termAtStartOfIteration) {
            break;
        }
        if (i === MAX_RECURSION_DEPTH - 1 && (changedInThisIteration || current !== termAtStartOfIteration) ) {
             console.warn(`WHNF reached max iterations for delta/rules on: ${printTerm(term)} -> ${printTerm(current)}`);
        }
    }

    // Beta Reduction
    if (current.tag === 'App') {
        const funcNorm = whnf(current.func, ctx, stackDepth + 1); 
        if (funcNorm.tag === 'Lam') {
            return whnf(funcNorm.body(current.arg), ctx, stackDepth + 1); 
        }
        if (funcNorm !== getTermRef(current.func)) return App(funcNorm, current.arg); // Reconstruct if func changed
        return current; 
    }
    return current;
}

function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Normalize stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    
    // Head reduction part (similar to whnf but without recursive whnf on App's function)
    let current = getTermRef(term);
    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        let changedInThisIteration = false;
        const termAtStartOfIteration = current;

        // Delta
        if (current.tag === 'Var') {
            const gdef = globalDefs.get(current.name);
            if (gdef && gdef.value && !gdef.isConstantSymbol) {
                const valRef = getTermRef(gdef.value);
                if (valRef !== current) { current = valRef; changedInThisIteration = true; }
            }
        }

        // Emdash specific reductions
        const termAfterDelta = current;
        let termAfterEmdashRules = termAfterDelta;
        if (termAfterEmdashRules.tag === 'ObjTerm' && getTermRef(termAfterEmdashRules.cat).tag === 'MkCat_') {
            termAfterEmdashRules = (getTermRef(termAfterEmdashRules.cat) as Term & {tag: 'MkCat_'}).objRepresentation;
        } else if (termAfterEmdashRules.tag === 'HomTerm' && getTermRef(termAfterEmdashRules.cat).tag === 'MkCat_') {
            const mkCatTerm = getTermRef(termAfterEmdashRules.cat) as Term & {tag: 'MkCat_'};
            termAfterEmdashRules = App(App(mkCatTerm.homRepresentation, termAfterEmdashRules.dom), termAfterEmdashRules.cod);
        } else if (termAfterEmdashRules.tag === 'ComposeMorph') {
            const comp = termAfterEmdashRules;
            const catVal = comp.cat_IMPLICIT ? getTermRef(comp.cat_IMPLICIT) : undefined;
            if (catVal && catVal.tag === 'MkCat_') {
                if (comp.objX_IMPLICIT && comp.objY_IMPLICIT && comp.objZ_IMPLICIT) {
                     termAfterEmdashRules = App(App(App(App(App(catVal.composeImplementation, getTermRef(comp.objX_IMPLICIT)), getTermRef(comp.objY_IMPLICIT)), getTermRef(comp.objZ_IMPLICIT)), comp.g), comp.f);
                }
            }
        }
        if (termAfterEmdashRules !== termAfterDelta) {
            current = termAfterEmdashRules; changedInThisIteration = true;
        }
        
        // User Rewrite Rules
        const termBeforeUserRules = current;
        if (!isEmdashConstantSymbolTag(current.tag) && !(current.tag === 'Var' && globalDefs.get(current.name)?.isConstantSymbol)) {
            for (const rule of userRewriteRules) {
                const subst = matchPattern(rule.lhs, termBeforeUserRules, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    const rhsApplied = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                    if (rhsApplied !== termBeforeUserRules) { current = rhsApplied; changedInThisIteration = true; }
                    break;
                }
            }
        }
        current = getTermRef(current);
        if (!changedInThisIteration && current === termAtStartOfIteration) break;
        if (i === MAX_RECURSION_DEPTH -1 && (changedInThisIteration || current !== termAtStartOfIteration)) {
             console.warn(`Normalize (head) reached max iterations: ${printTerm(term)} -> ${printTerm(current)}`);
        }
    }
    // `current` is now head-stable. Now normalize subterms.

    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': case 'CatTerm':
            return current;
        case 'ObjTerm':
            return ObjTerm(normalize(current.cat, ctx, stackDepth + 1));
        case 'HomTerm':
            return HomTerm(
                normalize(current.cat, ctx, stackDepth + 1),
                normalize(current.dom, ctx, stackDepth + 1),
                normalize(current.cod, ctx, stackDepth + 1)
            );
        case 'MkCat_':
            return MkCat_(
                normalize(current.objRepresentation, ctx, stackDepth + 1),
                normalize(current.homRepresentation, ctx, stackDepth + 1),
                normalize(current.composeImplementation, ctx, stackDepth + 1)
            );
        case 'IdentityMorph':
            return IdentityMorph(
                normalize(current.obj, ctx, stackDepth + 1),
                current.cat_IMPLICIT ? normalize(current.cat_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'ComposeMorph':
            // Check for beta reduction opportunity if C_impl was applied
            // `current` has been head-reduced by the loop above. Check its final tag.
            // Assert `current` as `Term` to satisfy the type checker, as its tag might have changed via reduction.
            if ((current as Term).tag === 'App') { // It might have reduced to an App sequence
                return normalize(current as Term, ctx, stackDepth + 1); // Normalize the result of the C_impl application
            }
            // If it didn't reduce via MkCat_ rule, then it's still a ComposeMorph tag. Normalize args.
            return ComposeMorph(
                normalize(current.g, ctx, stackDepth + 1),
                normalize(current.f, ctx, stackDepth + 1),
                current.cat_IMPLICIT ? normalize(current.cat_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objX_IMPLICIT ? normalize(current.objX_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objY_IMPLICIT ? normalize(current.objY_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objZ_IMPLICIT ? normalize(current.objZ_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
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
            // Head should have been reduced by the loop above if it was a Lam.
            // Or if it was a ComposeMorph that turned into Apps.
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


// --- Equality (areEqual) ---
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
        case 'Type': case 'CatTerm': return true;
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
            const CtxType = rt1.paramType && rt1._isAnnotated ? getTermRef(rt1.paramType) : Hole(); 
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
        // Emdash Phase 1
        case 'ObjTerm':
            return areEqual(rt1.cat, (rt2 as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
        case 'HomTerm':
            const hom2 = rt2 as Term & {tag:'HomTerm'};
            return areEqual(rt1.cat, hom2.cat, ctx, depth + 1) &&
                   areEqual(rt1.dom, hom2.dom, ctx, depth + 1) &&
                   areEqual(rt1.cod, hom2.cod, ctx, depth + 1);
        case 'MkCat_':
            const mkcat2 = rt2 as Term & {tag:'MkCat_'};
            return areEqual(rt1.objRepresentation, mkcat2.objRepresentation, ctx, depth + 1) &&
                   areEqual(rt1.homRepresentation, mkcat2.homRepresentation, ctx, depth + 1) &&
                   areEqual(rt1.composeImplementation, mkcat2.composeImplementation, ctx, depth + 1);
        case 'IdentityMorph':
            const id2 = rt2 as Term & {tag:'IdentityMorph'};
            // cat_IMPLICIT should be resolved by whnf if possible, or unified during check/infer
            const cat1_eq = rt1.cat_IMPLICIT ? getTermRef(rt1.cat_IMPLICIT) : Hole(); // Treat undefined as a temp hole for comparison
            const cat2_eq = id2.cat_IMPLICIT ? getTermRef(id2.cat_IMPLICIT) : Hole();
            if (!areEqual(cat1_eq, cat2_eq, ctx, depth + 1) && !(cat1_eq.tag === 'Hole' || cat2_eq.tag === 'Hole')) return false; // only fail if both non-hole and different
            return areEqual(rt1.obj, id2.obj, ctx, depth + 1);
        case 'ComposeMorph':
            const comp2 = rt2 as Term & {tag:'ComposeMorph'};
            // Similar to IdentityMorph for implicits
            const comp_cat1_eq = rt1.cat_IMPLICIT ? getTermRef(rt1.cat_IMPLICIT) : Hole();
            const comp_cat2_eq = comp2.cat_IMPLICIT ? getTermRef(comp2.cat_IMPLICIT) : Hole();
            if (!areEqual(comp_cat1_eq, comp_cat2_eq, ctx, depth+1) && !(comp_cat1_eq.tag === 'Hole' || comp_cat2_eq.tag === 'Hole')) return false;
            // And so on for objX, objY, objZ_IMPLICIT if they are to be compared strictly here.
            // However, for ComposeMorph, equality is more about what they reduce to via rewrite rules.
            // If whnf didn't change them, then structural equality of f and g matters.
            return areEqual(rt1.g, comp2.g, ctx, depth + 1) &&
                   areEqual(rt1.f, comp2.f, ctx, depth + 1);
    }
}

// --- Unification ---
function termContainsHole(term: Term, holeId: string, visited: Set<string>, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) {
        console.warn(`termContainsHole depth exceeded for ${holeId} in ${printTerm(term)}`);
        return true; 
    }
    const current = getTermRef(term);

    switch (current.tag) {
        case 'Hole': return current.id === holeId;
        case 'Type': case 'Var': case 'CatTerm': return false;
        default: {
            const termStrKey = printTerm(current); 
            if (visited.has(termStrKey)) return false;
            visited.add(termStrKey);

            if (current.tag === 'App') {
                return termContainsHole(current.func, holeId, visited, depth + 1) ||
                       termContainsHole(current.arg, holeId, visited, depth + 1);
            } else if (current.tag === 'Lam') {
                return (current.paramType && termContainsHole(current.paramType, holeId, visited, depth + 1));
            } else if (current.tag === 'Pi') {
                return termContainsHole(current.paramType, holeId, visited, depth + 1);
            }
            // Emdash Phase 1
            else if (current.tag === 'ObjTerm') {
                return termContainsHole(current.cat, holeId, visited, depth + 1);
            } else if (current.tag === 'HomTerm') {
                return termContainsHole(current.cat, holeId, visited, depth + 1) ||
                       termContainsHole(current.dom, holeId, visited, depth + 1) ||
                       termContainsHole(current.cod, holeId, visited, depth + 1);
            } else if (current.tag === 'MkCat_') {
                return termContainsHole(current.objRepresentation, holeId, visited, depth + 1) ||
                       termContainsHole(current.homRepresentation, holeId, visited, depth + 1) ||
                       termContainsHole(current.composeImplementation, holeId, visited, depth + 1);
            } else if (current.tag === 'IdentityMorph') {
                return (current.cat_IMPLICIT && termContainsHole(current.cat_IMPLICIT, holeId, visited, depth + 1)) ||
                       termContainsHole(current.obj, holeId, visited, depth + 1);
            } else if (current.tag === 'ComposeMorph') {
                return termContainsHole(current.g, holeId, visited, depth + 1) ||
                       termContainsHole(current.f, holeId, visited, depth + 1) ||
                       (current.cat_IMPLICIT && termContainsHole(current.cat_IMPLICIT, holeId, visited, depth + 1)) ||
                       (current.objX_IMPLICIT && termContainsHole(current.objX_IMPLICIT, holeId, visited, depth + 1)) ||
                       (current.objY_IMPLICIT && termContainsHole(current.objY_IMPLICIT, holeId, visited, depth + 1)) ||
                       (current.objZ_IMPLICIT && termContainsHole(current.objZ_IMPLICIT, holeId, visited, depth + 1));
            }
            return false; 
        }
    }
}

enum UnifyResult { Solved, Failed, RewrittenByRule, Progress }

function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
    const normTerm = getTermRef(term); // Use resolved term for occurs check and assignment
    if (normTerm.tag === 'Hole') {
        if (hole.id === normTerm.id) return true; 
        if (hole.id < normTerm.id) (normTerm as Term & {tag:'Hole'}).ref = hole; 
        else hole.ref = normTerm;
        return true;
    }
    if (termContainsHole(normTerm, hole.id, new Set(), depth + 1)) {
        // console.warn(`Occurs check failed: trying to unify ${hole.id} with ${printTerm(normTerm)} which contains ${hole.id}`);
        return false;
    }
    hole.ref = normTerm;
    return true;
}

// Helper for unifying arguments of injective symbols
function unifyArgs(args1: (Term | undefined)[], args2: (Term | undefined)[], ctx: Context, depth: number, rt1_print: string, rt2_print: string): UnifyResult {
    if (args1.length !== args2.length) return UnifyResult.Failed; // Should not happen for same tag

    let overallStatus = UnifyResult.Solved;
    for (let i = 0; i < args1.length; i++) {
        const t1_arg = args1[i];
        const t2_arg = args2[i];

        if (t1_arg === undefined && t2_arg === undefined) continue;
        if (t1_arg === undefined || t2_arg === undefined) { // One undefined, other not; can't unify if not holes
             // This case needs careful handling if implicits are involved.
             // For now, assume if one is undef, they must both be for structural match.
             // Or, if one is undef and other is hole, try to unify hole with a conceptual 'missing'
             // This is complex. Let's assume for Phase 1 that corresponding args must be present or both holes.
            overallStatus = UnifyResult.Progress; // Or Failed, needs refinement.
            continue;
        }


        const argStatus = unify(t1_arg, t2_arg, ctx, depth + 1);
        if (argStatus === UnifyResult.Failed) return UnifyResult.Failed;
        if (argStatus === UnifyResult.RewrittenByRule || argStatus === UnifyResult.Progress) {
            overallStatus = UnifyResult.Progress;
        }
    }
    // If all args solved and overallStatus still Solved, then good.
    // If overallStatus is Progress, it means some args made progress but not all fully solved yet.
    if (overallStatus === UnifyResult.Solved) {
         // Final check after all args are "Solved" from unify calls.
         // This is needed because unify(Hole, X) returns Solved, but areEqual(Hole,X) is false.
         // We need to ensure the original rt1 and rt2 are now equal.
        if (areEqual(Var(rt1_print), Var(rt2_print), ctx, depth +1)) return UnifyResult.Solved; // hacky use of Var to re-trigger areEqual
        else return UnifyResult.Progress; // Args individually fine, but whole structure not yet equal implies work still needed
    }
    return overallStatus;
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

    // At this point, rt1.tag === rt2.tag, and they are not Holes, and not areEqual.
    // Try unification rules first if symbols are not unification-injective.
    // If they *are* unification-injective, we go directly to unifying args.

    if (isEmdashUnificationInjectiveTag(rt1.tag)) {
        let args1: (Term|undefined)[] = [];
        let args2: (Term|undefined)[] = [];
        switch (rt1.tag) {
            case 'CatTerm': return UnifyResult.Solved; // Cat === Cat
            case 'ObjTerm':
                args1 = [rt1.cat]; args2 = [(rt2 as Term & {tag:'ObjTerm'}).cat];
                break;
            case 'HomTerm':
                const hom1 = rt1 as Term & {tag:'HomTerm'}; const hom2 = rt2 as Term & {tag:'HomTerm'};
                args1 = [hom1.cat, hom1.dom, hom1.cod]; args2 = [hom2.cat, hom2.dom, hom2.cod];
                break;
            case 'MkCat_':
                const mk1 = rt1 as Term & {tag:'MkCat_'}; const mk2 = rt2 as Term & {tag:'MkCat_'};
                args1 = [mk1.objRepresentation, mk1.homRepresentation, mk1.composeImplementation];
                args2 = [mk2.objRepresentation, mk2.homRepresentation, mk2.composeImplementation];
                break;
            case 'IdentityMorph':
                const id1 = rt1 as Term & {tag:'IdentityMorph'}; const id2 = rt2 as Term & {tag:'IdentityMorph'};
                // Implicits must be handled: if one is Hole and other defined, unify them.
                args1 = [id1.cat_IMPLICIT, id1.obj]; args2 = [id2.cat_IMPLICIT, id2.obj];
                break;
            // No other injective symbols in Phase 1 by default
            default: // Should not happen if isEmdashUnificationInjectiveTag is comprehensive
                return tryUnificationRules(rt1, rt2, ctx, depth + 1);
        }
        const argStatus = unifyArgs(args1, args2, ctx, depth, printTerm(rt1), printTerm(rt2)); // Pass printed terms for re-check
        if (argStatus === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth +1); // If injective path fails, try rules for the S===S problem
        return argStatus; // Progress or Solved
    }

    // Default structural unification for non-injective or non-Emdash types
    switch (rt1.tag) {
        case 'Type': return UnifyResult.Solved; // Should have been caught by areEqual
        case 'Var': return tryUnificationRules(rt1, rt2, ctx, depth + 1); // Vars not equal implies failure or rule
        
        case 'App': {
            const app2 = rt2 as Term & {tag:'App'};
            const funcUnifyStatus = unify(rt1.func, app2.func, ctx, depth + 1);
            if (funcUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);

            const argUnifyStatus = unify(rt1.arg, app2.arg, ctx, depth + 1);
            if (argUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);

            if (funcUnifyStatus === UnifyResult.Solved && argUnifyStatus === UnifyResult.Solved) {
                if (areEqual(rt1, rt2, ctx, depth + 1)) return UnifyResult.Solved; // Re-check after sub-unifications
                return tryUnificationRules(rt1, rt2, ctx, depth + 1); // Not equal even if args are, try rules.
            }
            return UnifyResult.Progress;
        }
        case 'Lam': { 
            const lam2 = rt2 as Term & {tag:'Lam'};
            // Logic for Lam, similar to App, involving paramType and body
            // This part needs to be careful if implicits or annotations differ
            if (rt1._isAnnotated !== lam2._isAnnotated) return tryUnificationRules(rt1, rt2, ctx, depth +1);
            let paramTypeStatus = UnifyResult.Solved;
            if (rt1._isAnnotated) {
                if(!rt1.paramType || !lam2.paramType) return tryUnificationRules(rt1, rt2, ctx, depth +1); // Should not happen
                paramTypeStatus = unify(rt1.paramType, lam2.paramType, ctx, depth + 1);
                if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth +1);
            }
            const freshV = Var(freshVarName(rt1.paramName));
            const CtxParamType = rt1.paramType ? getTermRef(rt1.paramType) : Hole();
            const extendedCtx = extendCtx(ctx, freshV.name, CtxParamType);
            const bodyStatus = unify(rt1.body(freshV), lam2.body(freshV), extendedCtx, depth + 1);
            if(bodyStatus === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);

            if(paramTypeStatus === UnifyResult.Solved && bodyStatus === UnifyResult.Solved) {
                if(areEqual(rt1, rt2, ctx, depth+1)) return UnifyResult.Solved;
                return tryUnificationRules(rt1, rt2, ctx, depth + 1);
            }
            return UnifyResult.Progress;
        }
        case 'Pi': { 
            const pi2 = rt2 as Term & {tag:'Pi'};
            // Logic for Pi, similar to Lam
            const paramTypeStatus = unify(rt1.paramType, pi2.paramType, ctx, depth + 1);
            if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);

            const freshV = Var(freshVarName(rt1.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(rt1.paramType));
            const bodyTypeStatus = unify(rt1.bodyType(freshV), pi2.bodyType(freshV), extendedCtx, depth + 1);
            if(bodyTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);

            if(paramTypeStatus === UnifyResult.Solved && bodyTypeStatus === UnifyResult.Solved) {
                if(areEqual(rt1, rt2, ctx, depth+1)) return UnifyResult.Solved;
                return tryUnificationRules(rt1, rt2, ctx, depth + 1);
            }
            return UnifyResult.Progress;
        }
        // Emdash cases that are NOT unification-injective by default (e.g., ComposeMorph)
        case 'ComposeMorph': // Not injective in f,g. Relies on rewrite rules / areEqual.
            // If areEqual failed, tryUnificationRules.
            return tryUnificationRules(rt1, rt2, ctx, depth + 1);

        default: // Unhandled same-tag case, or non-injective Emdash symbol
            return tryUnificationRules(rt1, rt2, ctx, depth + 1);
    }
}


// solveConstraints, applyAndAddRuleConstraints, tryUnificationRules remain mostly the same
// Small change in solveConstraints: use while loop for iterating and removing
function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("solveConstraints stack depth exceeded");
    let changedInOuterLoop = true;
    let iterations = 0;
    const maxIterations = (constraints.length + userUnificationRules.length + 20) * 30 + 100; // Generous limit

    while (changedInOuterLoop && iterations < maxIterations) {
        changedInOuterLoop = false;
        iterations++;
        
        let currentConstraintIdx = 0;
        while(currentConstraintIdx < constraints.length) {
            const constraint = constraints[currentConstraintIdx];
            const c_t1_ref = getTermRef(constraint.t1);
            const c_t2_ref = getTermRef(constraint.t2);

            if (areEqual(c_t1_ref, c_t2_ref, ctx, stackDepth + 1)) {
                constraints.splice(currentConstraintIdx, 1); 
                changedInOuterLoop = true; 
                // Do not increment currentConstraintIdx, as list shifted
                continue; 
            }

            try {
                const unifyResult = unify(c_t1_ref, c_t2_ref, ctx, stackDepth + 1);
                
                if (unifyResult === UnifyResult.Solved) {
                    // areEqual should have caught this, but if unify solved a hole leading to equality...
                    // To be safe, mark change and let areEqual confirm in next pass or earlier.
                    changedInOuterLoop = true; 
                    // If unify says solved, we can often remove it, but depends on if it was by hole assignment
                    // Let's assume areEqual is the ultimate check for removal of non-rewritten constraints.
                    // If unify assigned a hole, areEqual will find them equal next time.
                    currentConstraintIdx++; // Constraint remains for now, but progress made.
                } else if (unifyResult === UnifyResult.RewrittenByRule) {
                    constraints.splice(currentConstraintIdx, 1); 
                    changedInOuterLoop = true;
                    // No increment, list shifted.
                } else if (unifyResult === UnifyResult.Progress) {
                    changedInOuterLoop = true;
                    currentConstraintIdx++; 
                } else { 
                    // console.warn(`Unification failed for: ${printTerm(c_t1_ref)} === ${printTerm(c_t2_ref)} (origin: ${constraint.origin || 'unknown'})`);
                    return false; 
                }
            } catch (e) {
                // console.error(`Error during unification of ${printTerm(c_t1_ref)} and ${printTerm(c_t2_ref)} (origin: ${constraint.origin || 'unknown'}): ${(e as Error).message}`);
                // console.error((e as Error).stack);
                return false; 
            }
        }
    }

    if (iterations >= maxIterations && changedInOuterLoop) { 
        console.warn("Constraint solving reached max iterations and was still making changes. Constraints list size: " + constraints.length);
        if (constraints.length > 0) {
             console.warn("Remaining constraints on max iterations:");
             constraints.slice(0, 5).forEach(c => console.warn(`  ${printTerm(getTermRef(c.t1))} =?= ${printTerm(getTermRef(c.t2))} (orig: ${c.origin})`));
        }
    }
    // Final check: all remaining constraints must be satisfied
    for (const constraint of constraints) {
        if (!areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
            // console.warn(`Final check failed for constraint: ${printTerm(getTermRef(constraint.t1))} === ${printTerm(getTermRef(constraint.t2))} (origin: ${constraint.origin || 'unknown'})`);
            return false;
        }
    }
     // Success if no constraints remain OR all remaining constraints are true.
     // The loop above removes constraints if areEqual is true.
     // So if we exit, and all remaining constraints are areEqual, it should be empty.
    return constraints.length === 0;
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
            // Cannot inspect HOAS body for schematic vars without application.
            // Assume pattern variables are not free inside HOAS function bodies in patterns.
            break;
        case 'Pi':
            collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            // Similar HOAS body limitation.
            break;
        // Emdash Phase 1
        case 'ObjTerm':
            collectPatternVars(current.cat, patternVarDecls, collectedVars, visited);
            break;
        case 'HomTerm':
            collectPatternVars(current.cat, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.dom, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.cod, patternVarDecls, collectedVars, visited);
            break;
        case 'MkCat_':
            collectPatternVars(current.objRepresentation, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.homRepresentation, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.composeImplementation, patternVarDecls, collectedVars, visited);
            break;
        case 'IdentityMorph':
            if(current.cat_IMPLICIT) collectPatternVars(current.cat_IMPLICIT, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.obj, patternVarDecls, collectedVars, visited);
            break;
        case 'ComposeMorph':
            collectPatternVars(current.g, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.f, patternVarDecls, collectedVars, visited);
            if(current.cat_IMPLICIT) collectPatternVars(current.cat_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.objX_IMPLICIT) collectPatternVars(current.objX_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.objY_IMPLICIT) collectPatternVars(current.objY_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.objZ_IMPLICIT) collectPatternVars(current.objZ_IMPLICIT, patternVarDecls, collectedVars, visited);
            break;
    }
}

function applyAndAddRuleConstraints(rule: UnificationRule, subst: Substitution, ctx: Context): void {
    const lhsVars = new Set<string>();
    // Collect all variables that actually appear in the LHS patterns
    collectPatternVars(rule.lhsPattern1, rule.patternVars, lhsVars, new Set<Term>());
    collectPatternVars(rule.lhsPattern2, rule.patternVars, lhsVars, new Set<Term>());

    const finalSubst = new Map(subst); // Copy initial substitution from LHS matching

    // For RHS variables not in LHS, create fresh holes
    for (const pVarDecl of rule.patternVars) {
        const pVarName = pVarDecl.name;
        // Check if this pVarName is used in any of the RHS constraint terms
        let usedInRhs = false;
        for(const {t1: rhs_t1, t2: rhs_t2} of rule.rhsNewConstraints) {
            const rhsTermVars = new Set<string>();
            collectPatternVars(rhs_t1, rule.patternVars, rhsTermVars, new Set<Term>());
            collectPatternVars(rhs_t2, rule.patternVars, rhsTermVars, new Set<Term>());
            if (rhsTermVars.has(pVarName)) {
                usedInRhs = true;
                break;
            }
        }

        if (usedInRhs && !lhsVars.has(pVarName)) {
            // This variable is used in RHS constraints but was not bound by LHS patterns.
            // It must become a fresh hole if not already made one (e.g. by appearing in another part of RHS).
            if (!finalSubst.has(pVarName)) { // Ensure we don't overwrite if it was somehow in subst
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
        let subst1 = matchPattern(rule.lhsPattern1, t1, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            // Pass subst1 to continue matching on the same substitution set
            let subst2 = matchPattern(rule.lhsPattern2, t2, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) {
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }

        // Try match (t2, t1) with (lhsPattern1, lhsPattern2) -- commutativity
        let substComm1 = matchPattern(rule.lhsPattern1, t2, ctx, rule.patternVars, undefined, depth + 1);
        if (substComm1) {
            let substComm2 = matchPattern(rule.lhsPattern2, t1, ctx, rule.patternVars, substComm1, depth + 1);
            if (substComm2) {
                applyAndAddRuleConstraints(rule, substComm2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }
    }
    return UnifyResult.Failed;
}


// --- Type Checking (infer/check) ---
// Helper to manage implicit arguments during inference/checking
function ensureImplicitsAsHoles(term: Term, expectedArgCount?: number): Term {
    // This function would be called at the start of infer/check for relevant Emdash terms.
    // It ensures that if an _IMPLICIT field is undefined, it's replaced by a Hole.
    // This is a form of pre-elaboration specific to our TS constructors.
    // For Phase 1, we can do this manually inside each infer/check case.
    // Example for IdentityMorph:
    if (term.tag === 'IdentityMorph' && term.cat_IMPLICIT === undefined) {
        term.cat_IMPLICIT = Hole(freshHoleName() + "_cat_of_" + printTerm(term.obj).replace(/\W/g, ''));
    }
    if (term.tag === 'ComposeMorph') {
        if (term.cat_IMPLICIT === undefined) term.cat_IMPLICIT = Hole(freshHoleName() + "_comp_cat");
        if (term.objX_IMPLICIT === undefined) term.objX_IMPLICIT = Hole(freshHoleName() + "_comp_X");
        if (term.objY_IMPLICIT === undefined) term.objY_IMPLICIT = Hole(freshHoleName() + "_comp_Y");
        if (term.objZ_IMPLICIT === undefined) term.objZ_IMPLICIT = Hole(freshHoleName() + "_comp_Z");
    }
    return term; // Returning term in case we switch to immutable elaboration later
}


function infer(ctx: Context, term: Term, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Infer stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    
    const currentTermPreElab = getTermRef(term); // Get ref before ensuring implicits
    const current = ensureImplicitsAsHoles(currentTermPreElab); // Ensure _IMPLICIT fields are holes if undefined

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
            const newTypeForHole = Hole(freshHoleName() + "_type_of_" + current.id.replace("?","")); 
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
                const paramTypeHole = Hole(freshHoleName() + "_lam_" + paramName);
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
        // Emdash Phase 1
        case 'CatTerm': return Type(); // Cat : Type
        case 'ObjTerm': // Obj C : Type
            check(ctx, current.cat, CatTerm(), stackDepth + 1);
            return Type();
        case 'HomTerm': // Hom C X Y : Type
            check(ctx, current.cat, CatTerm(), stackDepth + 1);
            // X and Y must be objects of current.cat
            // This requires inferring types of X and Y and constraining them.
            const X_type = infer(ctx, current.dom, stackDepth + 1);
            const Y_type = infer(ctx, current.cod, stackDepth + 1);
            addConstraint(X_type, ObjTerm(current.cat), `Hom.dom ${printTerm(current.dom)} must be Obj of ${printTerm(current.cat)}`);
            addConstraint(Y_type, ObjTerm(current.cat), `Hom.cod ${printTerm(current.cod)} must be Obj of ${printTerm(current.cat)}`);
            return Type();
        case 'MkCat_': // MkCat_ O H C : Cat
            // O : Type
            check(ctx, current.objRepresentation, Type(), stackDepth + 1);
            const O_repr = getTermRef(current.objRepresentation);
            // H : Pi X:O. Pi Y:O. Type
            const expected_H_type = Pi("X", O_repr, _X => Pi("Y", O_repr, _Y => Type()));
            check(ctx, current.homRepresentation, expected_H_type, stackDepth + 1);
            const H_repr = getTermRef(current.homRepresentation);
            // C : Pi X:O. Pi Y:O. Pi Z:O. Pi g:(H Y Z). Pi f:(H X Y). (H X Z)
            const expected_C_type = Pi("Xarg", O_repr, Xarg_term =>
                                    Pi("Yarg", O_repr, Yarg_term =>
                                    Pi("Zarg", O_repr, Zarg_term =>
                                    Pi("g", App(App(H_repr, Yarg_term), Zarg_term), _g_term =>
                                    Pi("f", App(App(H_repr, Xarg_term), Yarg_term), _f_term =>
                                    App(App(H_repr, Xarg_term), Zarg_term)
                                )))));
            check(ctx, current.composeImplementation, expected_C_type, stackDepth + 1);
            return CatTerm();
        case 'IdentityMorph': // id_X : Hom A X X
            // obj : Obj A (for some A)
            // cat_IMPLICIT should be unified with A
            const objType = infer(ctx, current.obj, stackDepth + 1); // e.g. ObjTerm(cat_actual) or ?type_of_obj
            // current.cat_IMPLICIT is already a Hole if it was undefined.
            addConstraint(objType, ObjTerm(current.cat_IMPLICIT!), `Object ${printTerm(current.obj)} of id must be in cat ${printTerm(current.cat_IMPLICIT!)}`);
            return HomTerm(current.cat_IMPLICIT!, current.obj, current.obj);
        case 'ComposeMorph': // g . f : Hom A X Z
            // f : Hom A X Y
            // g : Hom A Y Z
            // Implicits cat, X, Y, Z are already holes if undefined
            const type_f = infer(ctx, current.f, stackDepth + 1);
            const type_g = infer(ctx, current.g, stackDepth + 1);

            addConstraint(type_f, HomTerm(current.cat_IMPLICIT!, current.objX_IMPLICIT!, current.objY_IMPLICIT!), `Arg f of Compose`);
            addConstraint(type_g, HomTerm(current.cat_IMPLICIT!, current.objY_IMPLICIT!, current.objZ_IMPLICIT!), `Arg g of Compose`);
            
            return HomTerm(current.cat_IMPLICIT!, current.objX_IMPLICIT!, current.objZ_IMPLICIT!);
    }
}

function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0): void {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Check stack depth exceeded (depth: ${stackDepth}, term ${printTerm(term)}, expType ${printTerm(expectedType)})`);
    
    const currentTermPreElab = getTermRef(term);
    const current = ensureImplicitsAsHoles(currentTermPreElab); // Ensure _IMPLICIT fields are holes

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

    // Rule for IdentityMorph with expected type
    if (current.tag === 'IdentityMorph' && normExpectedType.tag === 'HomTerm') {
        const idTerm = current;
        const expHom = normExpectedType;
        // id_X : Hom A X X
        // Expected: Hom C D E
        // Constraints: C=A, D=X, E=X
        addConstraint(idTerm.cat_IMPLICIT!, expHom.cat, `id.cat vs expected hom.cat`);
        addConstraint(idTerm.obj, expHom.dom, `id.obj vs expected hom.dom`);
        addConstraint(idTerm.obj, expHom.cod, `id.obj vs expected hom.cod`);
        // After these, type of idTerm should match. No need to call infer then addConstraint.
        return;
    }
    
    // Rule for ComposeMorph with expected type
    if (current.tag === 'ComposeMorph' && normExpectedType.tag === 'HomTerm') {
        const compTerm = current;
        const expHom = normExpectedType;
        // g . f : Hom A X Z
        // Expected: Hom C D E
        // Constraints: C=A, D=X, E=Z
        addConstraint(compTerm.cat_IMPLICIT!, expHom.cat, `comp.cat vs expected hom.cat`);
        addConstraint(compTerm.objX_IMPLICIT!, expHom.dom, `comp.X vs expected hom.dom`);
        addConstraint(compTerm.objZ_IMPLICIT!, expHom.cod, `comp.Z vs expected hom.cod`);

        // Additional constraints from inferring f and g
        // f : Hom A X Y,  g : Hom A Y Z
        const type_f = infer(ctx, compTerm.f, stackDepth + 1);
        const type_g = infer(ctx, compTerm.g, stackDepth + 1);
        addConstraint(type_f, HomTerm(compTerm.cat_IMPLICIT!, compTerm.objX_IMPLICIT!, compTerm.objY_IMPLICIT!), `Check comp.f type`);
        addConstraint(type_g, HomTerm(compTerm.cat_IMPLICIT!, compTerm.objY_IMPLICIT!, compTerm.objZ_IMPLICIT!), `Check comp.g type`);
        return;
    }


    if (current.tag === 'Hole') {
        if (!current.elaboratedType) {
             current.elaboratedType = normExpectedType; 
        }
        const inferredHoleType = infer(ctx, current, stackDepth + 1); 
        addConstraint(inferredHoleType, normExpectedType, `Hole ${current.id} checked against ${printTerm(normExpectedType)}`);
        return;
    }

    const inferredType = infer(ctx, current, stackDepth + 1);
    addConstraint(inferredType, normExpectedType, `Check general case for ${printTerm(current)} against ${printTerm(normExpectedType)}`);
}


interface ElaborationResult { term: Term; type: Term; }
function elaborate(term: Term, expectedType?: Term, initialCtx: Context = emptyCtx): ElaborationResult {
    constraints = []; nextHoleId = 0; nextVarId = 0;
    let finalTypeToReport: Term;
    // Create a "copy" for elaboration only if it's a complex object, not for simple vars/types
    // Our ensureImplicitsAsHoles mutates, so termToElaborate is the original object.
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
            let fcMsg = "Unknown constraint";
            if (fc && fc_t1 && fc_t2) {
                fcMsg = `${printTerm(fc_t1)} vs ${printTerm(fc_t2)} (orig: ${fc.origin || 'unspecified'})`;
            } else if (fc) {
                fcMsg = `Constraint involving ${fc.t1 ? printTerm(fc.t1) : '<undef>'} and ${fc.t2 ? printTerm(fc.t2) : '<undef>'} (orig: ${fc.origin || 'unspecified'})`
            }

            // console.error("Remaining constraints on failure during elaboration:");
            // constraints.forEach(c => {
            //      const c_t1_dbg = getTermRef(c.t1); const c_t2_dbg = getTermRef(c.t2);
            //      console.error(`  ${printTerm(c_t1_dbg)} ${areEqual(c_t1_dbg, c_t2_dbg, initialCtx) ? "===" : "=/="} ${printTerm(c_t2_dbg)} (origin: ${c.origin})`);
            // });
            throw new Error(`Type error: Could not solve constraints. Approx failing: ${fcMsg}`);
        }
    } catch (e) { 
        if (e instanceof Error && (e.message.startsWith("Type error:") || e.message.startsWith("Unbound variable:") || e.message.startsWith("Cannot apply non-function:"))) {
            throw e;
        }
        // console.error("Unexpected error during elaboration:", e);
        throw new Error(`Elaboration error: ${(e as Error).message} on term ${printTerm(term)}`);
    }
    
    const finalElaboratedTermStructure = termToElaborate; 
    const normalizedElaboratedTerm = normalize(finalElaboratedTermStructure, initialCtx);
    // finalTypeToReport might contain holes that were solved during constraint solving.
    // We must normalize it to get their values.
    const finalTypeNormalized = normalize(getTermRef(finalTypeToReport), initialCtx); 
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
    const subst = currentSubst ? new Map(currentSubst) : new Map<string, Term>();
    
    const currentTermStruct = getTermRef(termToMatch); 
    const rtPattern = getTermRef(pattern); 

    if (rtPattern.tag === 'Var' && isPatternVarName(rtPattern.name, patternVarDecls)) {
        const pvarName = rtPattern.name;
        if (pvarName === '_') return subst; // Wildcard, matches anything, no binding
        const existing = subst.get(pvarName);
        if (existing) {
            return areEqual(currentTermStruct, existing, ctx, stackDepth + 1) ? subst : null;
        }
        subst.set(pvarName, currentTermStruct); 
        return subst;
    }
    // Handle explicit Hole in pattern as wildcard, similar to Var '_'
    if (rtPattern.tag === 'Hole' && rtPattern.id === '_') return subst;


    if (currentTermStruct.tag === 'Hole' && rtPattern.tag !== 'Hole') return null; 
    if (rtPattern.tag === 'Hole' && currentTermStruct.tag !== 'Hole') return null;
    if (rtPattern.tag === 'Hole' && currentTermStruct.tag === 'Hole') {
        return (rtPattern as Term & {tag:'Hole'}).id === (currentTermStruct as Term & {tag:'Hole'}).id ? subst : null;
    }
    if (rtPattern.tag !== currentTermStruct.tag) return null;

    switch (rtPattern.tag) {
        case 'Type': case 'CatTerm': return subst;
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
        // Emdash Phase 1
        case 'ObjTerm':
            return matchPattern(rtPattern.cat, (currentTermStruct as Term & {tag:'ObjTerm'}).cat, ctx, patternVarDecls, subst, stackDepth + 1);
        case 'HomTerm': {
            const homP = rtPattern as Term & {tag:'HomTerm'};
            const homT = currentTermStruct as Term & {tag:'HomTerm'};
            let s = matchPattern(homP.cat, homT.cat, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s) return null;
            s = matchPattern(homP.dom, homT.dom, ctx, patternVarDecls, s, stackDepth + 1);
            if (!s) return null;
            return matchPattern(homP.cod, homT.cod, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'MkCat_': {
            const mkP = rtPattern as Term & {tag:'MkCat_'};
            const mkT = currentTermStruct as Term & {tag:'MkCat_'};
            let s = matchPattern(mkP.objRepresentation, mkT.objRepresentation, ctx, patternVarDecls, subst, stackDepth + 1);
            if(!s) return null;
            s = matchPattern(mkP.homRepresentation, mkT.homRepresentation, ctx, patternVarDecls, s, stackDepth + 1);
            if(!s) return null;
            return matchPattern(mkP.composeImplementation, mkT.composeImplementation, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'IdentityMorph': {
            const idP = rtPattern as Term & {tag:'IdentityMorph'};
            const idT = currentTermStruct as Term & {tag:'IdentityMorph'};
            let s = subst;
            if (idP.cat_IMPLICIT) { // Pattern specifies implicit cat
                if (!idT.cat_IMPLICIT) return null; // Term must also have it for this kind of match
                s = matchPattern(idP.cat_IMPLICIT, idT.cat_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1);
                if(!s) return null;
            } // else: pattern's cat_IMPLICIT is wildcard, matches whether idT.cat_IMPLICIT is defined or not.
            return matchPattern(idP.obj, idT.obj, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'ComposeMorph': {
            const compP = rtPattern as Term & {tag:'ComposeMorph'};
            const compT = currentTermStruct as Term & {tag:'ComposeMorph'};
            let s = subst;
            // Match implicits if pattern specifies them
            if (compP.cat_IMPLICIT) {
                if (!compT.cat_IMPLICIT) return null;
                s = matchPattern(compP.cat_IMPLICIT, compT.cat_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            }
            if (compP.objX_IMPLICIT) {
                if (!compT.objX_IMPLICIT) return null;
                s = matchPattern(compP.objX_IMPLICIT, compT.objX_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            }
            if (compP.objY_IMPLICIT) {
                if (!compT.objY_IMPLICIT) return null;
                s = matchPattern(compP.objY_IMPLICIT, compT.objY_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            }
            if (compP.objZ_IMPLICIT) {
                if (!compT.objZ_IMPLICIT) return null;
                s = matchPattern(compP.objZ_IMPLICIT, compT.objZ_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            }
            s = matchPattern(compP.g, compT.g, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            return matchPattern(compP.f, compT.f, ctx, patternVarDecls, s, stackDepth + 1);
        }

    }
}

function applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[]): Term {
    const current = getTermRef(term);
    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        if (current.name === '_') return Hole('_'); // Wildcard var becomes wildcard hole on RHS. Or error?
        const replacement = subst.get(current.name);
        if (!replacement) throw new Error(`Unbound pattern variable ${current.name} during substitution in rule RHS. Declared vars: ${patternVarDecls.map(pvd=>pvd.name).join(', ')}, Subst keys: ${Array.from(subst.keys()).join(', ')}`);
        return replacement;
    }
    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': case 'CatTerm': return current;
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
        // Emdash Phase 1
        case 'ObjTerm':
            return ObjTerm(applySubst(current.cat, subst, patternVarDecls));
        case 'HomTerm':
            return HomTerm(
                applySubst(current.cat, subst, patternVarDecls),
                applySubst(current.dom, subst, patternVarDecls),
                applySubst(current.cod, subst, patternVarDecls)
            );
        case 'MkCat_':
            return MkCat_(
                applySubst(current.objRepresentation, subst, patternVarDecls),
                applySubst(current.homRepresentation, subst, patternVarDecls),
                applySubst(current.composeImplementation, subst, patternVarDecls)
            );
        case 'IdentityMorph':
            return IdentityMorph(
                applySubst(current.obj, subst, patternVarDecls),
                current.cat_IMPLICIT ? applySubst(current.cat_IMPLICIT, subst, patternVarDecls) : undefined
            );
        case 'ComposeMorph':
            return ComposeMorph(
                applySubst(current.g, subst, patternVarDecls),
                applySubst(current.f, subst, patternVarDecls),
                current.cat_IMPLICIT ? applySubst(current.cat_IMPLICIT, subst, patternVarDecls) : undefined,
                current.objX_IMPLICIT ? applySubst(current.objX_IMPLICIT, subst, patternVarDecls) : undefined,
                current.objY_IMPLICIT ? applySubst(current.objY_IMPLICIT, subst, patternVarDecls) : undefined,
                current.objZ_IMPLICIT ? applySubst(current.objZ_IMPLICIT, subst, patternVarDecls) : undefined
            );
    }
}

// checkRewriteRule remains the same

// --- PrintTerm ---
function printTerm(term: Term, boundVars: string[] = [], stackDepth = 0): string {
    if (stackDepth > MAX_STACK_DEPTH) return "<print_depth_exceeded>";
    if (!term) return "<null_term>";
    const current = getTermRef(term);
    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return current.name;
        case 'Hole': 
            let typeInfo = "";
            if (current.elaboratedType) {
                const elabTypeRef = getTermRef(current.elaboratedType);
                if (!(elabTypeRef.tag === 'Hole' && elabTypeRef.id === current.id)) {
                    const elabTypePrint = printTerm(elabTypeRef, boundVars, stackDepth + 1);
                    if(!elabTypePrint.startsWith("?h") && elabTypePrint !== 'Type') {
                        typeInfo = `(:${elabTypePrint})`;
                    }
                }
            }
            return (current.id === '_' ? '_' : current.id) + typeInfo;
        case 'Lam': {
            const paramName = current.paramName;
            let uniqueParamName = paramName;
            let suffix = 1;
            while(boundVars.includes(uniqueParamName)) { uniqueParamName = `${paramName}_${suffix++}`; }

            const typeAnnotation = current._isAnnotated && current.paramType ? ` : ${printTerm(current.paramType, boundVars, stackDepth + 1)}` : '';
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
        // Emdash Phase 1
        case 'CatTerm': return 'Cat';
        case 'ObjTerm': return `(Obj ${printTerm(current.cat, boundVars, stackDepth + 1)})`;
        case 'HomTerm':
            return `(Hom ${printTerm(current.cat, boundVars, stackDepth + 1)} ${printTerm(current.dom, boundVars, stackDepth + 1)} ${printTerm(current.cod, boundVars, stackDepth + 1)})`;
        case 'MkCat_':
            return `(mkCat_ {O=${printTerm(current.objRepresentation, boundVars, stackDepth + 1)}, H=${printTerm(current.homRepresentation, boundVars, stackDepth + 1)}, C=${printTerm(current.composeImplementation, boundVars, stackDepth + 1)}})`;
        case 'IdentityMorph':
            const catIdStr = current.cat_IMPLICIT ? ` [cat=${printTerm(current.cat_IMPLICIT, boundVars, stackDepth + 1)}]` : "";
            return `(id${catIdStr} ${printTerm(current.obj, boundVars, stackDepth + 1)})`;
        case 'ComposeMorph':
            const catCompStr = current.cat_IMPLICIT ? ` [cat=${printTerm(current.cat_IMPLICIT, boundVars, stackDepth + 1)}]` : "";
            // Could add X,Y,Z to print if available and resolved.
            return `(${printTerm(current.g, boundVars, stackDepth + 1)} ∘${catCompStr} ${printTerm(current.f, boundVars, stackDepth + 1)})`;

    }
}

function resetMyLambdaPi() {
    constraints = []; globalDefs.clear(); 
    userRewriteRules.length = 0; 
    userUnificationRules.length = 0;
    nextVarId = 0; nextHoleId = 0;
}

// --- Phase 1 Setup & Tests ---
console.log("--- MyLambdaPi with Emdash Phase 1: Core Categories ---");

function setupPhase1Globals() {
    // Define 'NatType' as a type the user might use for objects
    defineGlobal("NatType", Type(), undefined, true); // NatType is a constant Type
    defineGlobal("BoolType", Type(), undefined, true);
}

function runPhase1Tests() {
    const baseCtx = emptyCtx;
    const NatObj = Var("NatType"); // This is a term of type Type, used as Obj repr.
    const BoolObj = Var("BoolType");

    // Test 1: CatTerm, ObjTerm, HomTerm type checking
    console.log("\n--- Test 1: Basic Cat/Obj/Hom Types ---");
    resetMyLambdaPi(); setupPhase1Globals();
    let testTerm: Term; // Declare with broader type
    testTerm = CatTerm();
    let elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.1 failed: Cat is not Type");

    const someCat = Hole("?MyCat"); // A hole for a category
    addConstraint(someCat, CatTerm(), "Force ?MyCat to be Cat"); // Manually add for test setup
    if(!solveConstraints(baseCtx)) throw new Error("Test 1.2 setup failed");
    
    testTerm = ObjTerm(someCat);
    elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.2 failed: Obj ?MyCat is not Type");
    
    const objX = Hole("?X"); const objY = Hole("?Y");
    addConstraint(infer(baseCtx, objX), ObjTerm(someCat), "Force ?X : Obj ?MyCat");
    addConstraint(infer(baseCtx, objY), ObjTerm(someCat), "Force ?Y : Obj ?MyCat");
    if(!solveConstraints(baseCtx)) throw new Error("Test 1.3 setup failed");

    testTerm = HomTerm(someCat, objX, objY);
    elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.3 failed: Hom ?MyCat ?X ?Y is not Type");
    console.log("Test 1 Passed.");

    // Test 2: MkCat_ type checking and projection rules
    console.log("\n--- Test 2: MkCat_ and Projections ---");
    resetMyLambdaPi(); setupPhase1Globals();
    // H_repr: fun X Y => Arrow X Y (if Arrow was defined)
    // For simplicity, use Pi X. Pi Y. Type as hom-type representation for now
    const H_repr_Nat = Lam("X", _X => Lam("Y", _Y => Type())); // A function that returns Type for any X,Y
    // C_impl: fun X Y Z g f => Hole() (dummy composition)
    const C_impl_Nat = Lam("X", _X => Lam("Y", _Y => Lam("Z", _Z => Lam("g", _g => Lam("f", _f => Hole("comp_result"))))));
    
    const NatCat = MkCat_(NatObj, H_repr_Nat, C_impl_Nat);
    testTerm = NatCat; // Assign NatCat to the now broadly typed testTerm
    elabRes = elaborate(testTerm, undefined, baseCtx); // Infer type of NatCat
    console.log(`NatCat Term: ${printTerm(elabRes.term)}`);
    console.log(`NatCat Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'CatTerm') throw new Error("Test 2.1 failed: MkCat_ type is not Cat");

    // Test Obj projection
    const ObjOfNatCat = ObjTerm(NatCat);
    elabRes = elaborate(ObjOfNatCat, undefined, baseCtx); // Infer, should reduce via whnf
    console.log(`Obj(NatCat) Term (norm): ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if (!areEqual(elabRes.term, NatObj, baseCtx)) throw new Error(`Test 2.2 failed: Obj(NatCat) did not reduce to NatType. Got ${printTerm(elabRes.term)}`);

    // Test Hom projection
    const X_in_NatCat = Var("someNatVal1"); // Assume this var is of type NatType
    const Y_in_NatCat = Var("someNatVal2"); // Assume this var is of type NatType
    const HomInNatCat = HomTerm(NatCat, X_in_NatCat, Y_in_NatCat);
    // Need to define someNatVal1/2 in context for H_repr_Nat to type check if it used them.
    // Our H_repr_Nat is just Lam(X => Lam(Y => Type())), so it doesn't use X,Y values.
    testTerm = HomInNatCat; // Assign HomInNatCat
    elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Hom(NatCat,X,Y) Term (norm): ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    const expectedHomReduced = App(App(H_repr_Nat, X_in_NatCat), Y_in_NatCat); // H X Y
    // Normalizing expectedHomReduced will give Type()
    if (!areEqual(elabRes.term, normalize(expectedHomReduced, baseCtx), baseCtx)) throw new Error(`Test 2.3 failed: Hom(NatCat,X,Y) did not reduce correctly. Expected ${printTerm(normalize(expectedHomReduced,baseCtx))} Got ${printTerm(elabRes.term)}`);
    console.log("Test 2 Passed.");

    // Test 3: IdentityMorph
    console.log("\n--- Test 3: IdentityMorph ---");
    resetMyLambdaPi(); setupPhase1Globals();
    // Use NatCat from before
    const H_repr_Nat3 = Lam("X", _X => Lam("Y", _Y => Type()));
    const C_impl_Nat3 = Lam("X", _X => Lam("Y", _Y => Lam("Z", _Z => Lam("g", _g => Lam("f", _f => Hole("comp_result"))))));
    const MyNatCat = MkCat_(NatObj, H_repr_Nat3, C_impl_Nat3);
    
    const anObjX = Var("x_obj_for_id"); // This needs to be of type Obj(MyNatCat), i.e., NatType
    defineGlobal("x_obj_for_id", NatObj); // So x_obj_for_id : NatType

    const id_x = IdentityMorph(anObjX); // Implicit category
    elabRes = elaborate(id_x, undefined, baseCtx);
    console.log(`Term id_x: ${printTerm(elabRes.term)}`);
    console.log(`Type id_x: ${printTerm(elabRes.type)}`);
    // Expected type: HomTerm(CAT, anObjX, anObjX) where CAT is inferred for anObjX
    // The cat_IMPLICIT field of elabRes.term (which is id_x after mutation) should be solved.
    const idTermSolved = getTermRef(elabRes.term) as Term & {tag:"IdentityMorph"};
    if (!idTermSolved.cat_IMPLICIT) throw new Error("Test 3.1 failed: id_x cat_IMPLICIT not filled.");
    
    // We need to check if idTermSolved.cat_IMPLICIT is indeed MyNatCat (or something equal)
    // This is tricky as MyNatCat is a complex term.
    // For now, let's check the structure of the type.
    if (elabRes.type.tag !== 'HomTerm') throw new Error("Test 3.1 failed: id_x type not HomTerm.");
    const homType = elabRes.type as Term & {tag:"HomTerm"};
    if(!areEqual(homType.dom, anObjX, baseCtx) || !areEqual(homType.cod, anObjX, baseCtx)) throw new Error("Test 3.1 failed: id_x type not Hom A X X form.");
    // Check that homType.cat is constrained to be the cat of anObjX
    // We know anObjX : NatObj. ObjTerm(MyNatCat) reduces to NatObj.
    // So, if infer(anObjX) is ObjTerm(C), then C should be MyNatCat.
    // Let's check if homType.cat is (or unifies with) MyNatCat.
    // This test is a bit indirect.
    if (!areEqual(ObjTerm(homType.cat), NatObj, baseCtx)) throw new Error(`Test 3.1: Cat of id_x's type does not seem to be MyNatCat. Obj(inf_cat)=${printTerm(ObjTerm(homType.cat))}`);
    console.log("Test 3 (inference part) Passed.");

    // Test 4: ComposeMorph
    console.log("\n--- Test 4: ComposeMorph ---");
    resetMyLambdaPi(); setupPhase1Globals();
    const MyNatCat4 = MkCat_(NatObj, H_repr_Nat, C_impl_Nat); // Reusing from Test 2 for brevity
    defineGlobal("obj_x", NatObj); defineGlobal("obj_y", NatObj); defineGlobal("obj_z", NatObj);
    const x = Var("obj_x"); const y = Var("obj_y"); const z = Var("obj_z");

    const f_morph = Hole("?f_xy"); // ?f : Hom MyNatCat4 x y
    const g_morph = Hole("?g_yz"); // ?g : Hom MyNatCat4 y z
    
    const comp_gf = ComposeMorph(g_morph, f_morph); // All implicits are holes
    elabRes = elaborate(comp_gf, undefined, baseCtx);
    console.log(`Term comp_gf: ${printTerm(elabRes.term)}`);
    console.log(`Type comp_gf: ${printTerm(elabRes.type)}`);
    
    const compTermSolved = getTermRef(elabRes.term) as Term & {tag:"ComposeMorph"};
    if (!compTermSolved.cat_IMPLICIT || !compTermSolved.objX_IMPLICIT || !compTermSolved.objY_IMPLICIT || !compTermSolved.objZ_IMPLICIT) {
        throw new Error("Test 4.1 failed: ComposeMorph implicits not filled.");
    }
    // Check type structure: Hom (cat_hole_solved) (X_hole_solved) (Z_hole_solved)
    if (elabRes.type.tag !== 'HomTerm') throw new Error("Test 4.1 failed: comp_gf type not HomTerm.");
    const compHomType = elabRes.type as Term & {tag:"HomTerm"};

    // Check that the implicit objects in the type match those in the term
    if(!areEqual(compHomType.cat, compTermSolved.cat_IMPLICIT, baseCtx)) throw new Error("Test 4.1: comp.cat type mismatch");
    if(!areEqual(compHomType.dom, compTermSolved.objX_IMPLICIT, baseCtx)) throw new Error("Test 4.1: comp.dom type mismatch");
    if(!areEqual(compHomType.cod, compTermSolved.objZ_IMPLICIT, baseCtx)) throw new Error("Test 4.1: comp.cod type mismatch");
    
    // Check constraints on f and g
    const f_type = (f_morph as Term & {tag:"Hole"}).elaboratedType;
    const g_type = (g_morph as Term & {tag:"Hole"}).elaboratedType;
    if (!f_type || !g_type) throw new Error("Test 4.1: f or g did not get elaborated types.");

    const expected_f_type = HomTerm(compTermSolved.cat_IMPLICIT, compTermSolved.objX_IMPLICIT, compTermSolved.objY_IMPLICIT);
    const expected_g_type = HomTerm(compTermSolved.cat_IMPLICIT, compTermSolved.objY_IMPLICIT, compTermSolved.objZ_IMPLICIT);

    if (!areEqual(getTermRef(f_type), expected_f_type, baseCtx)) throw new Error(`Test 4.1: ?f_xy type mismatch. Got ${printTerm(getTermRef(f_type))}, expected ${printTerm(expected_f_type)}`);
    if (!areEqual(getTermRef(g_type), expected_g_type, baseCtx)) throw new Error(`Test 4.1: ?g_yz type mismatch. Got ${printTerm(getTermRef(g_type))}, expected ${printTerm(expected_g_type)}`);
    
    console.log("Test 4 (inference part) Passed.");


    // Test 5: Rewrite rule for Compose with Identity
    console.log("\n--- Test 5: comp (g (id X)) ---");
    resetMyLambdaPi(); setupPhase1Globals();
    const C5 = MkCat_(NatObj, H_repr_Nat, C_impl_Nat);
    defineGlobal("C5_cat", CatTerm(), C5, true); // Make C5 available as a global constant Cat
    
    defineGlobal("x5", NatObj); defineGlobal("y5", NatObj);
    const X5 = Var("x5"); const Y5 = Var("y5");
    const g5 = Hole("?g_XY_5"); // g: Hom C5 X5 Y5
    
    // Setup rewrite rule: g o idX = g
    // lhs: ComposeMorph(g_pat, IdentityMorph(X_pat, cat_pat), cat_pat, Y_pat, X_pat, X_pat)
    // For simplicity, assume cat_pat, X_pat, Y_pat are specific for this rule or use wildcards.
    // Let's make a rule specific to our C5 and its objects for this test.
    const pvar_g = { name: "g_morph_pat", type: HomTerm(Var("C5_cat"), X5, Y5) };
    // Simpler rule: $g \circ id = $g
    // This requires id to be (id $X) and $g to be $g: Hom $Y $X (if composition is g after f)
    // Lambdapi: rule compose_morph $g (identity_morph $A $X) ↪ $g;  (if $A $X match domain of $g)
    // Here our compose is (G, F) meaning G after F.
    // So, F is identity: ComposeMorph(G_pat, IdentityMorph(X_pat, CAT_pat), CAT_pat, Z_pat_eq_cod_G, X_pat_eq_dom_G, X_pat_eq_dom_F )
    // For g o id_X = g, means f = id_X. So ComposeMorph(g, id_X).
    // The rule should be: ComposeMorph (Var "g_pat") (IdentityMorph (Var "X_pat") (Var "cat_pat")) (Var "cat_pat") (Var "Y_pat") (Var "X_pat") (Var "X_pat") -> Var "g_pat"
    // This is too complex to setup variables that match Y_pat to codomain of g_pat etc. in pattern.
    // Let's use a simpler pattern with specific category for the test.
    
    const pvar_G = {name: "G", type: HomTerm(Var("C5_cat"), X5, Y5)}; // G: Hom C5 X5 Y5
    const pvar_X = {name: "X_obj", type: ObjTerm(Var("C5_cat"))}; // X_obj : Obj C5_cat (e.g. NatObj)

    addRewriteRule({
        name: "comp_g_id",
        patternVars: [pvar_G, pvar_X],
        // lhs: ComposeMorph(g, id_X) where g: Hom Y X, id_X: Hom X X. Result Hom Y X.
        // Our ComposeMorph(G,F) means G after F.
        // So rule F_pat o id_X_pat -> F_pat. F_pat is g. id_X_pat is f.
        // So we need g_pat o id_X_pat -> g_pat
        lhs: ComposeMorph(Var("G"), IdentityMorph(Var("X_obj"), Var("C5_cat")), Var("C5_cat"), Y5, Var("X_obj"), Var("X_obj")),
        rhs: Var("G")
    });
    
    const id_X5_term = IdentityMorph(X5, Var("C5_cat"));
    const test_comp_g_id = ComposeMorph(g5, id_X5_term, Var("C5_cat"), Y5, X5, X5);
    
    // We need g5 to be some concrete term for this to fully reduce, or it'll be ?g_XY_5
    // Let g5 be a global constant morphism for testing reduction
    defineGlobal("concrete_g", HomTerm(Var("C5_cat"), X5, Y5)); 
    const concrete_g_term = Var("concrete_g");
    const test_comp_concrete_g_id = ComposeMorph(concrete_g_term, id_X5_term, Var("C5_cat"), Y5, X5, X5);

    elabRes = elaborate(test_comp_concrete_g_id, undefined, baseCtx); // Type will be Hom C5 X5 Y5
    console.log(`Term (g o id): ${printTerm(elabRes.term)}`);
    console.log(`Type (g o id): ${printTerm(elabRes.type)}`);

    if (!areEqual(elabRes.term, concrete_g_term, baseCtx)) {
        throw new Error(`Test 5 failed: g o id did not reduce to g. Got ${printTerm(elabRes.term)}, expected ${printTerm(concrete_g_term)}`);
    }
    console.log("Test 5 Passed.");


}

// --- Main Execution ---
try {
    runPhase1Tests();
    console.log("\nAll Phase 1 tests passed successfully!");
} catch (e) {
    console.error("\n*** PHASE 1 TEST SCENARIO FAILED ***");
    console.error((e as Error).message);
    console.error((e as Error).stack);
}

// Reset function, just in case it's called from elsewhere or for future use
function resetMyLambdaPi_Emdash() {
    resetMyLambdaPi(); // Calls the existing reset
}