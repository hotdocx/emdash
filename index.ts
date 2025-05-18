// --- MyLambdaPi with Emdash Phase 1: Core Categories (Attempt 2) ---

// [PREVIOUS CODE UNCHANGED UP TO resetMyLambdaPi and Symbol Properties]
// ... (keep all previous definitions: Term, constructors, context, globals, rules, utils, symbol properties etc.)
// Make sure all previous functions are here: printTerm, applySubst, matchPattern, whnf, normalize, 
// areEqual, termContainsHole, unifyHole, unifyArgs, unify, solveConstraints, 
// collectPatternVars, applyAndAddRuleConstraints, tryUnificationRules,
// ensureImplicitsAsHoles.
// The following are only the changed/new parts for infer, check, elaborate, and tests.

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
    | { tag: 'CatTerm' } 
    | { tag: 'ObjTerm', cat: Term } 
    | { tag: 'HomTerm', cat: Term, dom: Term, cod: Term } 
    | { tag: 'MkCat_',
        objRepresentation: Term, 
        homRepresentation: Term, 
        composeImplementation: Term 
      }
    | { tag: 'IdentityMorph', 
        obj: Term,
        cat_IMPLICIT?: Term 
      }
    | { tag: 'ComposeMorph', 
        g: Term,
        f: Term,
        cat_IMPLICIT?: Term,
        objX_IMPLICIT?: Term, 
        objY_IMPLICIT?: Term, 
        objZ_IMPLICIT?: Term  
      };

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
    isConstantSymbol?: boolean; 
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
const MAX_STACK_DEPTH = 70; 

const EMDASH_CONSTANT_SYMBOLS = new Set<string>(['CatTerm', 'ObjTerm', 'HomTerm', 'MkCat_']);
const EMDASH_UNIFICATION_INJECTIVE_SYMBOLS = new Set<string>(['IdentityMorph']);
// MkCat_ itself is constant, implies its args are unified injectively.
// ObjTerm, HomTerm are type constructors; their injectivity on arguments is handled by unify.

function isEmdashConstantSymbolTag(tag: string): boolean {
    return EMDASH_CONSTANT_SYMBOLS.has(tag);
}
function isEmdashUnificationInjectiveTag(tag: string): boolean {
    return EMDASH_CONSTANT_SYMBOLS.has(tag) || EMDASH_UNIFICATION_INJECTIVE_SYMBOLS.has(tag);
}

function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`WHNF stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    let current = getTermRef(term);

    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        let changedInThisIteration = false;
        const termAtStartOfIteration = current;

        if (current.tag === 'Var') {
            const gdef = globalDefs.get(current.name);
            if (gdef && gdef.value && !gdef.isConstantSymbol) { 
                const valRef = getTermRef(gdef.value);
                if (valRef !== current) {
                     current = valRef;
                     changedInThisIteration = true;
                }
            }
        }

        const termAfterDelta = current;
        let termAfterEmdashRules = termAfterDelta;

        if (termAfterEmdashRules.tag === 'ObjTerm' && getTermRef(termAfterEmdashRules.cat).tag === 'MkCat_') {
            const mkCatTerm = getTermRef(termAfterEmdashRules.cat) as Term & {tag: 'MkCat_'};
            termAfterEmdashRules = mkCatTerm.objRepresentation; 
        } else if (termAfterEmdashRules.tag === 'HomTerm' && getTermRef(termAfterEmdashRules.cat).tag === 'MkCat_') {
            const mkCatTerm = getTermRef(termAfterEmdashRules.cat) as Term & {tag: 'MkCat_'};
            const H_repr = mkCatTerm.homRepresentation;
            termAfterEmdashRules = App(App(H_repr, termAfterEmdashRules.dom), termAfterEmdashRules.cod);
        } else if (termAfterEmdashRules.tag === 'ComposeMorph') {
            const comp = termAfterEmdashRules;
            const catVal = comp.cat_IMPLICIT ? getTermRef(comp.cat_IMPLICIT) : undefined; 
            if (catVal && catVal.tag === 'MkCat_') {
                const C_impl = catVal.composeImplementation;
                if (comp.objX_IMPLICIT && comp.objY_IMPLICIT && comp.objZ_IMPLICIT) {
                    termAfterEmdashRules = App(App(App(App(App(C_impl, getTermRef(comp.objX_IMPLICIT)), getTermRef(comp.objY_IMPLICIT)), getTermRef(comp.objZ_IMPLICIT)), comp.g), comp.f);
                }
            }
        }
        
        if (termAfterEmdashRules !== termAfterDelta) {
            current = termAfterEmdashRules;
            changedInThisIteration = true;
        }

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
             // console.warn(`WHNF reached max iterations for delta/rules on: ${printTerm(term)} -> ${printTerm(current)}`);
        }
    }

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
    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        let changedInThisIteration = false;
        const termAtStartOfIteration = current;

        if (current.tag === 'Var') {
            const gdef = globalDefs.get(current.name);
            if (gdef && gdef.value && !gdef.isConstantSymbol) {
                const valRef = getTermRef(gdef.value);
                if (valRef !== current) { current = valRef; changedInThisIteration = true; }
            }
        }

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
                if (comp.objX_IMPLICIT && comp.objY_IMPLICIT && comp.objZ_IMPLICIT) { // Ensure implicits are resolved
                     termAfterEmdashRules = App(App(App(App(App(catVal.composeImplementation, getTermRef(comp.objX_IMPLICIT)), getTermRef(comp.objY_IMPLICIT)), getTermRef(comp.objZ_IMPLICIT)), comp.g), comp.f);
                }
            }
        }
        if (termAfterEmdashRules !== termAfterDelta) {
            current = termAfterEmdashRules; changedInThisIteration = true;
        }
        
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
            // console.warn(`Normalize (head) reached max iterations: ${printTerm(term)} -> ${printTerm(current)}`);
        }
    }

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
            const headReducedCompose = current; 
            if ((headReducedCompose as Term).tag === 'App') { 
                return normalize(headReducedCompose, ctx, stackDepth + 1); 
            }
            return ComposeMorph(
                normalize(headReducedCompose.g, ctx, stackDepth + 1),
                normalize(headReducedCompose.f, ctx, stackDepth + 1),
                headReducedCompose.cat_IMPLICIT ? normalize(headReducedCompose.cat_IMPLICIT, ctx, stackDepth + 1) : undefined,
                headReducedCompose.objX_IMPLICIT ? normalize(headReducedCompose.objX_IMPLICIT, ctx, stackDepth + 1) : undefined,
                headReducedCompose.objY_IMPLICIT ? normalize(headReducedCompose.objY_IMPLICIT, ctx, stackDepth + 1) : undefined,
                headReducedCompose.objZ_IMPLICIT ? normalize(headReducedCompose.objZ_IMPLICIT, ctx, stackDepth + 1) : undefined
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
            const cat1_eq = rt1.cat_IMPLICIT ? getTermRef(rt1.cat_IMPLICIT) : Hole(); 
            const cat2_eq = id2.cat_IMPLICIT ? getTermRef(id2.cat_IMPLICIT) : Hole();
            if (!areEqual(cat1_eq, cat2_eq, ctx, depth + 1) && !(cat1_eq.tag === 'Hole' || cat2_eq.tag === 'Hole')) return false;
            return areEqual(rt1.obj, id2.obj, ctx, depth + 1);
        case 'ComposeMorph': // Equality depends on whnf applying rewrite rules. If still ComposeMorph, compare sub-parts.
            const comp2 = rt2 as Term & {tag:'ComposeMorph'};
            const comp_cat1_eq = rt1.cat_IMPLICIT ? getTermRef(rt1.cat_IMPLICIT) : Hole();
            const comp_cat2_eq = comp2.cat_IMPLICIT ? getTermRef(comp2.cat_IMPLICIT) : Hole();
            if (!areEqual(comp_cat1_eq, comp_cat2_eq, ctx, depth+1) && !(comp_cat1_eq.tag === 'Hole' || comp_cat2_eq.tag === 'Hole')) return false;
            // Check other implicits if they are strictly part of the structure after whnf.
            // For now, focus on g and f as they are the explicit payload.
            return areEqual(rt1.g, comp2.g, ctx, depth + 1) &&
                   areEqual(rt1.f, comp2.f, ctx, depth + 1);
    }
}

function termContainsHole(term: Term, holeId: string, visited: Set<string>, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) {
        // console.warn(`termContainsHole depth exceeded for ${holeId} in ${printTerm(term)}`);
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
    const normTerm = getTermRef(term);
    if (normTerm.tag === 'Hole') {
        if (hole.id === normTerm.id) return true; 
        if (hole.id < normTerm.id) (normTerm as Term & {tag:'Hole'}).ref = hole; 
        else hole.ref = normTerm;
        return true;
    }
    if (termContainsHole(normTerm, hole.id, new Set(), depth + 1)) {
        return false;
    }
    hole.ref = normTerm;
    return true;
}

function unifyArgs(args1: (Term | undefined)[], args2: (Term | undefined)[], ctx: Context, depth: number, parentRt1: Term, parentRt2: Term): UnifyResult {
    if (args1.length !== args2.length) return UnifyResult.Failed;

    let madeProgress = false;
    for (let i = 0; i < args1.length; i++) {
        const t1_arg = args1[i];
        const t2_arg = args2[i];

        if (t1_arg === undefined && t2_arg === undefined) continue;
        // If one is undefined and other not (and not a hole that can absorb it), this is tricky.
        // Assuming for injective unification that corresponding args must be structurally present or both be holes.
        // If an implicit arg was undefined and became a hole, it should be handled by unify.
        if ((t1_arg === undefined && t2_arg !== undefined && t2_arg.tag !== 'Hole') ||
            (t2_arg === undefined && t1_arg !== undefined && t1_arg.tag !== 'Hole')) {
            return UnifyResult.Failed; // Structure mismatch for injective comparison
        }
        // If one is undefined, the other must be a hole or also undefined.
        // If t1_arg is undefined, and t2_arg is a hole, t2_arg should unify with a conceptual "absent" or this is failure.
        // This logic is subtle. For now, if one is defined, the other must be.
        if (!t1_arg || !t2_arg) { // one is undefined, the other must be too.
            if (t1_arg !== t2_arg) return UnifyResult.Failed; // (undef vs hole) or (hole vs undef) fails here.
            continue;
        }

        const argStatus = unify(t1_arg, t2_arg, ctx, depth + 1);
        if (argStatus === UnifyResult.Failed) return UnifyResult.Failed;
        if (argStatus === UnifyResult.RewrittenByRule || argStatus === UnifyResult.Progress) {
            madeProgress = true;
        }
    }
    
    if (madeProgress) return UnifyResult.Progress;

    // All args individually "solved" (not failed, not progress, not rewritten).
    // Now check if the parent terms are actually equal.
    if (areEqual(parentRt1, parentRt2, ctx, depth + 1)) return UnifyResult.Solved;
    
    // Args are fine, but parents not equal implies some subtle mismatch or further reduction needed.
    // This can happen if, e.g., unifying ?h with X makes sub-parts "solved" but ?h=X isn't fully propagated yet.
    return UnifyResult.Progress; 
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

    if (isEmdashUnificationInjectiveTag(rt1.tag)) {
        let args1: (Term|undefined)[] = [];
        let args2: (Term|undefined)[] = [];
        switch (rt1.tag) {
            case 'CatTerm': return UnifyResult.Solved; 
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
                args1 = [id1.cat_IMPLICIT, id1.obj]; args2 = [id2.cat_IMPLICIT, id2.obj];
                break;
            default: 
                return tryUnificationRules(rt1, rt2, ctx, depth + 1); // Should have been covered by isEmdashUnificationInjectiveTag
        }
        const argStatus = unifyArgs(args1, args2, ctx, depth, rt1, rt2); // Pass original rt1, rt2
        if (argStatus === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth +1); 
        return argStatus; 
    }

    switch (rt1.tag) {
        case 'Type': return UnifyResult.Solved; 
        case 'Var': return tryUnificationRules(rt1, rt2, ctx, depth + 1);
        case 'App': { /* ... unchanged ... */ 
            const app2 = rt2 as Term & {tag:'App'};
            const funcUnifyStatus = unify(rt1.func, app2.func, ctx, depth + 1);
            if (funcUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);

            const argUnifyStatus = unify(rt1.arg, app2.arg, ctx, depth + 1);
            if (argUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);

            if (funcUnifyStatus === UnifyResult.Solved && argUnifyStatus === UnifyResult.Solved) {
                if (areEqual(rt1, rt2, ctx, depth + 1)) return UnifyResult.Solved;
                return tryUnificationRules(rt1, rt2, ctx, depth + 1);
            }
            return UnifyResult.Progress;
        }
        case 'Lam': { /* ... unchanged ... */
            const lam2 = rt2 as Term & {tag:'Lam'};
            if (rt1._isAnnotated !== lam2._isAnnotated) return tryUnificationRules(rt1, rt2, ctx, depth +1);
            let paramTypeStatus = UnifyResult.Solved;
            if (rt1._isAnnotated) {
                if(!rt1.paramType || !lam2.paramType) return tryUnificationRules(rt1, rt2, ctx, depth +1); 
                paramTypeStatus = unify(rt1.paramType, lam2.paramType, ctx, depth + 1);
                if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1, rt2, ctx, depth + 1);
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
        case 'Pi': { /* ... unchanged ... */
            const pi2 = rt2 as Term & {tag:'Pi'};
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
        case 'ComposeMorph': 
            return tryUnificationRules(rt1, rt2, ctx, depth + 1);
        default: 
             // This case should ideally not be reached if all Emdash constant symbols are handled by isEmdashUnificationInjectiveTag
            return tryUnificationRules(rt1, rt2, ctx, depth + 1);
    }
}

function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("solveConstraints stack depth exceeded");
    let changedInOuterLoop = true;
    let iterations = 0;
    const maxIterations = (constraints.length + userUnificationRules.length + 20) * 30 + 100;

    while (changedInOuterLoop && iterations < maxIterations) {
        changedInOuterLoop = false;
        iterations++;
        
        let currentConstraintIdx = 0;
        while(currentConstraintIdx < constraints.length) {
            const constraint = constraints[currentConstraintIdx];
            // It's crucial to getTermRef *before* areEqual or unify, as they might fill holes.
            const c_t1_current_ref = getTermRef(constraint.t1);
            const c_t2_current_ref = getTermRef(constraint.t2);

            if (areEqual(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1)) {
                constraints.splice(currentConstraintIdx, 1); 
                changedInOuterLoop = true; 
                continue; 
            }

            try {
                // Pass the current refs to unify
                const unifyResult = unify(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1);
                
                if (unifyResult === UnifyResult.Solved) {
                    // If unify solved it (e.g. by hole assignment), areEqual should catch it next round or above.
                    // We mark progress. The constraint might be removed if areEqual confirms.
                    changedInOuterLoop = true; 
                    currentConstraintIdx++; 
                } else if (unifyResult === UnifyResult.RewrittenByRule) {
                    constraints.splice(currentConstraintIdx, 1); 
                    changedInOuterLoop = true;
                } else if (unifyResult === UnifyResult.Progress) {
                    changedInOuterLoop = true;
                    currentConstraintIdx++; 
                } else { // UnifyResult.Failed
                    return false; 
                }
            } catch (e) {
                return false; 
            }
        }
    }

    if (iterations >= maxIterations && changedInOuterLoop) { 
        // console.warn("Constraint solving reached max iterations and was still making changes. Constraints list size: " + constraints.length);
    }
    for (const constraint of constraints) { // Final check
        if (!areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
            return false;
        }
    }
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

function ensureImplicitsAsHoles(term: Term): Term {
    // Ensure this modifies the term object directly or returns an elaborated copy.
    // Current implementation expects mutation for simplicity.
    const t = term; // work with the same reference for mutation
    if (t.tag === 'IdentityMorph' && t.cat_IMPLICIT === undefined) {
        t.cat_IMPLICIT = Hole(freshHoleName() + "_cat_of_" + printTerm(t.obj).replace(/\W/g, ''));
    }
    if (t.tag === 'ComposeMorph') {
        if (t.cat_IMPLICIT === undefined) t.cat_IMPLICIT = Hole(freshHoleName() + "_comp_cat");
        if (t.objX_IMPLICIT === undefined) t.objX_IMPLICIT = Hole(freshHoleName() + "_comp_X");
        if (t.objY_IMPLICIT === undefined) t.objY_IMPLICIT = Hole(freshHoleName() + "_comp_Y");
        if (t.objZ_IMPLICIT === undefined) t.objZ_IMPLICIT = Hole(freshHoleName() + "_comp_Z");
    }
    return t;
}

function infer(ctx: Context, term: Term, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Infer stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    
    const current = ensureImplicitsAsHoles(getTermRef(term));

    if (current.tag === 'Var') { /* ... unchanged ... */
        const gdef = globalDefs.get(current.name);
        if (gdef) return gdef.type;
        const binding = lookupCtx(ctx, current.name);
        if (!binding) throw new Error(`Unbound variable: ${current.name}`);
        return binding.type;
    }

    switch (current.tag) {
        case 'Type': return Type();
        case 'Hole': { /* ... unchanged ... */
            if (current.elaboratedType) return getTermRef(current.elaboratedType);
            const newTypeForHole = Hole(freshHoleName() + "_type_of_" + current.id.replace("?","")); 
            current.elaboratedType = newTypeForHole;
            return newTypeForHole;
        }
        case 'App': { /* ... unchanged ... */
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
        case 'Lam': { /* ... unchanged ... */
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
        case 'Pi': { /* ... unchanged ... */
            const pi = current;
            check(ctx, pi.paramType, Type(), stackDepth + 1); 
            const paramName = pi.paramName;
            const extendedCtx = extendCtx(ctx, paramName, pi.paramType);
            const bodyTypeInstance = pi.bodyType(Var(paramName)); 
            check(extendedCtx, bodyTypeInstance, Type(), stackDepth + 1); 
            return Type(); 
        }
        // Emdash Phase 1
        case 'CatTerm': return Type();
        case 'ObjTerm':
            check(ctx, current.cat, CatTerm(), stackDepth + 1);
            return Type();
        case 'HomTerm':
            check(ctx, current.cat, CatTerm(), stackDepth + 1);
            const catForHom = getTermRef(current.cat); // Use resolved cat for ObjTerm checks
            check(ctx, current.dom, ObjTerm(catForHom), stackDepth + 1);
            check(ctx, current.cod, ObjTerm(catForHom), stackDepth + 1);
            return Type();
        case 'MkCat_': 
            check(ctx, current.objRepresentation, Type(), stackDepth + 1);
            const O_repr = getTermRef(current.objRepresentation);
            
            const expected_H_type = Pi("X", O_repr, _X => Pi("Y", O_repr, _Y => Type()));
            check(ctx, current.homRepresentation, expected_H_type, stackDepth + 1);
            const H_repr_func = getTermRef(current.homRepresentation); // This is the H function itself

            // The type of g and f in C_impl refer to applications of H_repr_func
            const type_of_hom_X_Y = (X_val: Term, Y_val: Term) => App(App(H_repr_func, X_val), Y_val);

            const expected_C_type = 
                Pi("Xarg", O_repr, Xarg_term =>
                Pi("Yarg", O_repr, Yarg_term =>
                Pi("Zarg", O_repr, Zarg_term =>
                Pi("g", type_of_hom_X_Y(Yarg_term, Zarg_term), _g_term =>
                Pi("f", type_of_hom_X_Y(Xarg_term, Yarg_term), _f_term =>
                type_of_hom_X_Y(Xarg_term, Zarg_term)
                )))));
            check(ctx, current.composeImplementation, expected_C_type, stackDepth + 1);
            return CatTerm();
        case 'IdentityMorph': 
            const objType = infer(ctx, current.obj, stackDepth + 1); 
            addConstraint(objType, ObjTerm(current.cat_IMPLICIT!), `Object ${printTerm(current.obj)} of id must be in cat ${printTerm(current.cat_IMPLICIT!)}`);
            return HomTerm(current.cat_IMPLICIT!, current.obj, current.obj);
        case 'ComposeMorph': 
            const type_f = infer(ctx, current.f, stackDepth + 1);
            const type_g = infer(ctx, current.g, stackDepth + 1);

            addConstraint(type_f, HomTerm(current.cat_IMPLICIT!, current.objX_IMPLICIT!, current.objY_IMPLICIT!), `Arg f of Compose`);
            addConstraint(type_g, HomTerm(current.cat_IMPLICIT!, current.objY_IMPLICIT!, current.objZ_IMPLICIT!), `Arg g of Compose`);
            
            return HomTerm(current.cat_IMPLICIT!, current.objX_IMPLICIT!, current.objZ_IMPLICIT!);
    }
}

function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0): void {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Check stack depth exceeded (depth: ${stackDepth}, term ${printTerm(term)}, expType ${printTerm(expectedType)})`);
    
    const current = ensureImplicitsAsHoles(getTermRef(term)); 
    const normExpectedType = whnf(expectedType, ctx, stackDepth + 1); 

    if (current.tag === 'Lam' && !current._isAnnotated && normExpectedType.tag === 'Pi') { /* ... unchanged ... */
        const lamTerm = current as Term & {tag:"Lam"}; 
        const expectedPi = normExpectedType as Term & {tag:"Pi"}; 

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

    if (current.tag === 'IdentityMorph' && normExpectedType.tag === 'HomTerm') {
        const idTerm = current;
        const expHom = normExpectedType;
        addConstraint(idTerm.cat_IMPLICIT!, expHom.cat, `id.cat vs expected hom.cat`);
        addConstraint(idTerm.obj, expHom.dom, `id.obj vs expected hom.dom`);
        addConstraint(idTerm.obj, expHom.cod, `id.obj vs expected hom.cod`);
        // Also, check that idTerm.obj is indeed an object of idTerm.cat_IMPLICIT!
        const objTypeForId = infer(ctx, idTerm.obj, stackDepth + 1);
        addConstraint(objTypeForId, ObjTerm(idTerm.cat_IMPLICIT!), `id.obj actual type check`);
        return;
    }
    
    if (current.tag === 'ComposeMorph' && normExpectedType.tag === 'HomTerm') {
        const compTerm = current;
        const expHom = normExpectedType;
        addConstraint(compTerm.cat_IMPLICIT!, expHom.cat, `comp.cat vs expected hom.cat`);
        addConstraint(compTerm.objX_IMPLICIT!, expHom.dom, `comp.X vs expected hom.dom`);
        addConstraint(compTerm.objZ_IMPLICIT!, expHom.cod, `comp.Z vs expected hom.cod`);

        const type_f = infer(ctx, compTerm.f, stackDepth + 1);
        const type_g = infer(ctx, compTerm.g, stackDepth + 1);
        addConstraint(type_f, HomTerm(compTerm.cat_IMPLICIT!, compTerm.objX_IMPLICIT!, compTerm.objY_IMPLICIT!), `Check comp.f type`);
        addConstraint(type_g, HomTerm(compTerm.cat_IMPLICIT!, compTerm.objY_IMPLICIT!, compTerm.objZ_IMPLICIT!), `Check comp.g type`);
        return;
    }

    if (current.tag === 'Hole') { /* ... unchanged ... */
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
            throw new Error(`Type error: Could not solve constraints. Approx failing: ${fcMsg}`);
        }
    } catch (e) { 
        if (e instanceof Error && (e.message.startsWith("Type error:") || e.message.startsWith("Unbound variable:") || e.message.startsWith("Cannot apply non-function:"))) {
            throw e;
        }
        throw new Error(`Elaboration error: ${(e as Error).message} on term ${printTerm(term)}`);
    }
    
    const finalElaboratedTermStructure = termToElaborate; 
    const normalizedElaboratedTerm = normalize(finalElaboratedTermStructure, initialCtx);
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
        // Treat "_" as a special pattern variable name that matches anything but doesn't bind
        if (pvarName === '_') return subst; 
        const existing = subst.get(pvarName);
        if (existing) {
            return areEqual(currentTermStruct, existing, ctx, stackDepth + 1) ? subst : null;
        }
        subst.set(pvarName, currentTermStruct); 
        return subst;
    }
    // Also allow Hole with id "_" to be a wildcard in patterns
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
        case 'App': { /* ... unchanged ... */
            const termApp = currentTermStruct as Term & {tag:'App'};
            const s1 = matchPattern(rtPattern.func, termApp.func, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s1) return null;
            return matchPattern(rtPattern.arg, termApp.arg, ctx, patternVarDecls, s1, stackDepth + 1);
        }
        case 'Lam': { /* ... unchanged ... */
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
        case 'Pi': { /* ... unchanged ... */
            const piP = rtPattern as Term & {tag:'Pi'};
            const piT = currentTermStruct as Term & {tag:'Pi'};
            const sType = matchPattern(piP.paramType, piT.paramType, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!sType) return null;
            const freshV = Var(freshVarName(piP.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(piP.paramType));
            return areEqual(piP.bodyType(freshV), piT.bodyType(freshV), extendedCtx, stackDepth+1) ? sType : null;
        }
        case 'ObjTerm': { /* ... unchanged ... */
            return matchPattern(rtPattern.cat, (currentTermStruct as Term & {tag:'ObjTerm'}).cat, ctx, patternVarDecls, subst, stackDepth + 1);
        }
        case 'HomTerm': { /* ... unchanged ... */
            const homP = rtPattern as Term & {tag:'HomTerm'};
            const homT = currentTermStruct as Term & {tag:'HomTerm'};
            let s = matchPattern(homP.cat, homT.cat, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s) return null;
            s = matchPattern(homP.dom, homT.dom, ctx, patternVarDecls, s, stackDepth + 1);
            if (!s) return null;
            return matchPattern(homP.cod, homT.cod, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'MkCat_': { /* ... unchanged ... */
            const mkP = rtPattern as Term & {tag:'MkCat_'};
            const mkT = currentTermStruct as Term & {tag:'MkCat_'};
            let s = matchPattern(mkP.objRepresentation, mkT.objRepresentation, ctx, patternVarDecls, subst, stackDepth + 1);
            if(!s) return null;
            s = matchPattern(mkP.homRepresentation, mkT.homRepresentation, ctx, patternVarDecls, s, stackDepth + 1);
            if(!s) return null;
            return matchPattern(mkP.composeImplementation, mkT.composeImplementation, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'IdentityMorph': { /* ... unchanged ... */
            const idP = rtPattern as Term & {tag:'IdentityMorph'};
            const idT = currentTermStruct as Term & {tag:'IdentityMorph'};
            let s = subst;
            if (idP.cat_IMPLICIT) { 
                const idPcat_IMPLICIT = idP.cat_IMPLICIT;
                if (!idT.cat_IMPLICIT && idP.cat_IMPLICIT.tag !== 'Hole' && idP.cat_IMPLICIT.tag !== 'Var' && (idP.cat_IMPLICIT.tag as String === 'Var' && (idPcat_IMPLICIT as Term & {tag:'Var'}).name !== '_')) return null; // Pattern needs explicit, term doesn't have
                if (idT.cat_IMPLICIT) { // Only match if term also has it or pattern cat is wildcard
                     s = matchPattern(idP.cat_IMPLICIT, idT.cat_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1);
                     if(!s) return null;
                } else if (idP.cat_IMPLICIT.tag !== 'Hole' && !(idP.cat_IMPLICIT.tag === 'Var' && idP.cat_IMPLICIT.name === '_')) {
                    return null; // Pattern expects a specific cat, term doesn't provide one.
                }
            } 
            return matchPattern(idP.obj, idT.obj, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'ComposeMorph': { /* ... unchanged ... */
            const compP = rtPattern as Term & {tag:'ComposeMorph'};
            const compT = currentTermStruct as Term & {tag:'ComposeMorph'};
            let s = subst;
            if (compP.cat_IMPLICIT) {
                if (!compT.cat_IMPLICIT && compP.cat_IMPLICIT.tag !== 'Hole' && !(compP.cat_IMPLICIT.tag === 'Var' && compP.cat_IMPLICIT.name === '_')) return null;
                if (compT.cat_IMPLICIT) { s = matchPattern(compP.cat_IMPLICIT, compT.cat_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null; }
                else if (compP.cat_IMPLICIT.tag !== 'Hole' && !(compP.cat_IMPLICIT.tag === 'Var' && compP.cat_IMPLICIT.name === '_')) return null;
            }
            if (compP.objX_IMPLICIT) {
                if (!compT.objX_IMPLICIT && compP.objX_IMPLICIT.tag !== 'Hole' && !(compP.objX_IMPLICIT.tag === 'Var' && compP.objX_IMPLICIT.name === '_')) return null;
                if (compT.objX_IMPLICIT) { s = matchPattern(compP.objX_IMPLICIT, compT.objX_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null; }
                else if (compP.objX_IMPLICIT.tag !== 'Hole' && !(compP.objX_IMPLICIT.tag === 'Var' && compP.objX_IMPLICIT.name === '_')) return null;
            }
            if (compP.objY_IMPLICIT) {
                if (!compT.objY_IMPLICIT && compP.objY_IMPLICIT.tag !== 'Hole' && !(compP.objY_IMPLICIT.tag === 'Var' && compP.objY_IMPLICIT.name === '_')) return null;
                if (compT.objY_IMPLICIT) { s = matchPattern(compP.objY_IMPLICIT, compT.objY_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null; }
                else if (compP.objY_IMPLICIT.tag !== 'Hole' && !(compP.objY_IMPLICIT.tag === 'Var' && compP.objY_IMPLICIT.name === '_')) return null;
            }
            if (compP.objZ_IMPLICIT) {
                if (!compT.objZ_IMPLICIT && compP.objZ_IMPLICIT.tag !== 'Hole' && !(compP.objZ_IMPLICIT.tag === 'Var' && compP.objZ_IMPLICIT.name === '_')) return null;
                if (compT.objZ_IMPLICIT) { s = matchPattern(compP.objZ_IMPLICIT, compT.objZ_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null; }
                else if (compP.objZ_IMPLICIT.tag !== 'Hole' && !(compP.objZ_IMPLICIT.tag === 'Var' && compP.objZ_IMPLICIT.name === '_')) return null;
            }
            s = matchPattern(compP.g, compT.g, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null;
            return matchPattern(compP.f, compT.f, ctx, patternVarDecls, s, stackDepth + 1);
        }
    }
}


function applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[]): Term {
    const current = getTermRef(term);
    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        if (current.name === '_') return Hole('_'); 
        const replacement = subst.get(current.name);
        if (!replacement) throw new Error(`Unbound pattern variable ${current.name} during substitution`);
        return replacement;
    }
    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': case 'CatTerm': return current;
        case 'App': /* ... unchanged ... */
            return App(applySubst(current.func, subst, patternVarDecls), applySubst(current.arg, subst, patternVarDecls));
        case 'Lam': { /* ... unchanged ... */
            const lam = current;
            const lamParamType = lam.paramType ? applySubst(lam.paramType, subst, patternVarDecls) : undefined;
            const newLam = Lam(lam.paramName,
                (v_arg: Term) => applySubst(lam.body(v_arg), subst, patternVarDecls), 
                lamParamType);
            newLam._isAnnotated = lam._isAnnotated;
            return newLam;
        }
        case 'Pi': { /* ... unchanged ... */
            const pi = current;
            return Pi(pi.paramName, applySubst(pi.paramType, subst, patternVarDecls),
                (v_arg: Term) => applySubst(pi.bodyType(v_arg), subst, patternVarDecls));
        }
        case 'ObjTerm': /* ... unchanged ... */
            return ObjTerm(applySubst(current.cat, subst, patternVarDecls));
        case 'HomTerm': /* ... unchanged ... */
            return HomTerm(
                applySubst(current.cat, subst, patternVarDecls),
                applySubst(current.dom, subst, patternVarDecls),
                applySubst(current.cod, subst, patternVarDecls)
            );
        case 'MkCat_': /* ... unchanged ... */
            return MkCat_(
                applySubst(current.objRepresentation, subst, patternVarDecls),
                applySubst(current.homRepresentation, subst, patternVarDecls),
                applySubst(current.composeImplementation, subst, patternVarDecls)
            );
        case 'IdentityMorph': /* ... unchanged ... */
            return IdentityMorph(
                applySubst(current.obj, subst, patternVarDecls),
                current.cat_IMPLICIT ? applySubst(current.cat_IMPLICIT, subst, patternVarDecls) : undefined
            );
        case 'ComposeMorph': /* ... unchanged ... */
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

function checkRewriteRule(rule: RewriteRule, baseCtx: Context): boolean {
    let patternCtx = baseCtx;
    for (const pv of rule.patternVars) { patternCtx = extendCtx(patternCtx, pv.name, pv.type); }
    
    const ruleCheckConstraintsBackup = [...constraints]; 
    const ruleCheckNextHoleIdBackup = nextHoleId;
    const ruleCheckNextVarIdBackup = nextVarId;
    
    constraints = []; 
    nextHoleId = 0; 
    nextVarId = 0;

    try {
        const lhsType = infer(patternCtx, rule.lhs);
        const rhsType = infer(patternCtx, rule.rhs);
        addConstraint(lhsType, rhsType, `Rewrite rule ${rule.name} type preservation`);
        if (!solveConstraints(patternCtx)) {
            // console.error(`Rule ${rule.name} does not preserve types.`);
            // const fc = constraints.find(constraint => !areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), patternCtx));
            // if (fc) console.error(`  Failing constraint for rule type check: ${printTerm(getTermRef(fc.t1))} = ${printTerm(getTermRef(fc.t2))}`);
            return false;
        }
        return true;
    } catch (e) {
        // console.error(`Error checking rule ${rule.name}: ${(e as Error).message}`);
        return false;
    } finally { 
        constraints = ruleCheckConstraintsBackup; 
        nextHoleId = ruleCheckNextHoleIdBackup; 
        nextVarId = ruleCheckNextVarIdBackup;
    }
}

function printTerm(term: Term, boundVars: string[] = [], stackDepth = 0): string {
    if (stackDepth > MAX_STACK_DEPTH) return "<print_depth_exceeded>";
    if (!term) return "<null_term>";
    const current = getTermRef(term); // Crucial to print the resolved term
    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return current.name;
        case 'Hole':  /* ... unchanged ... */
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
        case 'Lam': { /* ... unchanged ... */
            const paramName = current.paramName;
            let uniqueParamName = paramName;
            let suffix = 1;
            while(boundVars.includes(uniqueParamName)) { uniqueParamName = `${paramName}_${suffix++}`; }

            const typeAnnotation = current._isAnnotated && current.paramType ? ` : ${printTerm(current.paramType, boundVars, stackDepth + 1)}` : '';
            const bodyTerm = current.body(Var(uniqueParamName)); 
            return `(λ ${uniqueParamName}${typeAnnotation}. ${printTerm(bodyTerm, [...boundVars, uniqueParamName], stackDepth + 1)})`;
        }
        case 'App': /* ... unchanged ... */
            return `(${printTerm(current.func, boundVars, stackDepth + 1)} ${printTerm(current.arg, boundVars, stackDepth + 1)})`;
        case 'Pi': { /* ... unchanged ... */
            const paramName = current.paramName;
            let uniqueParamName = paramName;
            let suffix = 1;
            while(boundVars.includes(uniqueParamName)) { uniqueParamName = `${paramName}_${suffix++}`; }
            
            const bodyTypeTerm = current.bodyType(Var(uniqueParamName));
            return `(Π ${uniqueParamName} : ${printTerm(current.paramType, boundVars, stackDepth + 1)}. ${printTerm(bodyTypeTerm, [...boundVars, uniqueParamName], stackDepth + 1)})`;
        }
        case 'CatTerm': return 'Cat';
        case 'ObjTerm': return `(Obj ${printTerm(current.cat, boundVars, stackDepth + 1)})`;
        case 'HomTerm':
            return `(Hom ${printTerm(current.cat, boundVars, stackDepth + 1)} ${printTerm(current.dom, boundVars, stackDepth + 1)} ${printTerm(current.cod, boundVars, stackDepth + 1)})`;
        case 'MkCat_':
            return `(mkCat_ {O=${printTerm(current.objRepresentation, boundVars, stackDepth + 1)}, H=${printTerm(current.homRepresentation, boundVars, stackDepth + 1)}, C=${printTerm(current.composeImplementation, boundVars, stackDepth + 1)}})`;
        case 'IdentityMorph': {
            let catIdStr = "";
            if (current.cat_IMPLICIT && getTermRef(current.cat_IMPLICIT).tag !== 'Hole') { // Only print if not an unsolved hole
                 catIdStr = ` [cat=${printTerm(current.cat_IMPLICIT, boundVars, stackDepth + 1)}]`;
            }
            return `(id${catIdStr} ${printTerm(current.obj, boundVars, stackDepth + 1)})`;
        }
        case 'ComposeMorph': {
            let catCompStr = "";
            if (current.cat_IMPLICIT && getTermRef(current.cat_IMPLICIT).tag !== 'Hole') {
                 catCompStr = ` [cat=${printTerm(current.cat_IMPLICIT, boundVars, stackDepth + 1)}]`;
            }
            // Could add X,Y,Z to print if available and resolved and not holes.
            return `(${printTerm(current.g, boundVars, stackDepth + 1)} ∘${catCompStr} ${printTerm(current.f, boundVars, stackDepth + 1)})`;
        }
    }
}

function resetMyLambdaPi() {
    constraints = []; globalDefs.clear(); 
    userRewriteRules.length = 0; 
    userUnificationRules.length = 0;
    nextVarId = 0; nextHoleId = 0;
}

console.log("--- MyLambdaPi with Emdash Phase 1: Core Categories (Attempt 2) ---");

function setupPhase1GlobalsAndRules() {
    defineGlobal("NatType", Type(), undefined, true); 
    defineGlobal("BoolType", Type(), undefined, true);

    // Rewrite rules for comp-id
    // g o idX = g.  LHS: ComposeMorph(g, IdentityMorph(X, C), C, cod(g), X, X)
    // idY o f = f.  LHS: ComposeMorph(IdentityMorph(Y, C), f, C, Y, Y, dom(f))
    const pvarCat = { name: "CAT", type: CatTerm() };
    const pvarX = { name: "X", type: ObjTerm(Var("CAT")) }; // X : Obj CAT
    const pvarY = { name: "Y", type: ObjTerm(Var("CAT")) }; // Y : Obj CAT
    const pvarZ = { name: "Z", type: ObjTerm(Var("CAT")) }; // Z : Obj CAT

    const pvarF = { name: "f", type: HomTerm(Var("CAT"), Var("X"), Var("Y")) }; // f : Hom CAT X Y
    const pvarG = { name: "g", type: HomTerm(Var("CAT"), Var("Y"), Var("Z")) }; // g : Hom CAT Y Z

    addRewriteRule({
        name: "comp_g_idX",
        patternVars: [pvarCat, pvarX, pvarY, pvarG], // G: Hom Y X, X_obj: Obj X
        // For ComposeMorph(G,F), if F = id_X, then G o id_X = G
        // G is pvarG (Hom Y X), F is IdentityMorph(X_obj_pat, cat_pat)
        // X_obj_pat should be dom(G)
        // Result type Hom Y X
        lhs: ComposeMorph(Var("g"), IdentityMorph(Var("X"), Var("CAT")), Var("CAT"), Var("Y"), Var("X"), Var("X")),
        rhs: Var("g")
    });

    addRewriteRule({
        name: "comp_idY_f",
        patternVars: [pvarCat, pvarX, pvarY, pvarF], // F: Hom X Y
        // For ComposeMorph(G,F), if G = id_Y, then id_Y o F = F
        // G is IdentityMorph(Y_obj_pat, cat_pat), F is pvarF (Hom X Y)
        // Y_obj_pat should be cod(F) (which is also dom(G))
        // Result type Hom X Y
        lhs: ComposeMorph(IdentityMorph(Var("Y"), Var("CAT")), Var("f"), Var("CAT"), Var("Y"), Var("Y"), Var("X")),
        rhs: Var("f")
    });
}


function runPhase1Tests() {
    const baseCtx = emptyCtx;
    const NatObjRepr = Var("NatType"); 
    const BoolObjRepr = Var("BoolType");

    console.log("\n--- Test 1: Basic Cat/Obj/Hom Types ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    let testTerm : Term;
    testTerm = CatTerm();
    let elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.1 failed: Cat is not Type");

    const someCatHole = Hole("?MyCat"); 
    const type_of_someCatHole = infer(baseCtx, someCatHole);
    addConstraint(type_of_someCatHole, CatTerm(), "Constraint: type of ?MyCat is Cat");
    if(!solveConstraints(baseCtx)) throw new Error("Test 1.2 setup failed: ?MyCat not typable as Cat");
    // Now someCatHole.elaboratedType should be CatTerm()
    
    testTerm = ObjTerm(someCatHole);
    elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.2 failed: Obj ?MyCat is not Type");
    
    const objXHole = Hole("?X"); 
    const objYHole = Hole("?Y");
    // Set types for objXHole and objYHole
    (objXHole as Term & {tag:"Hole"}).elaboratedType = ObjTerm(someCatHole);
    (objYHole as Term & {tag:"Hole"}).elaboratedType = ObjTerm(someCatHole);

    testTerm = HomTerm(someCatHole, objXHole, objYHole);
    elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.3 failed: Hom ?MyCat ?X ?Y is not Type");
    console.log("Test 1 Passed.");

    console.log("\n--- Test 2: MkCat_ and Projections ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    const H_repr_Nat = Lam("X", _X => Lam("Y", _Y => Type())); 
    const C_impl_Nat_dummy = Lam("Xobj", _Xobj => Lam("Yobj", _Yobj => Lam("Zobj", _Zobj => Lam("gmorph", _gmorph => Lam("fmorph", _fmorph => Hole("comp_res_dummy"))))));
    
    const NatCategoryTerm = MkCat_(NatObjRepr, H_repr_Nat, C_impl_Nat_dummy);
    elabRes = elaborate(NatCategoryTerm, undefined, baseCtx); 
    console.log(`NatCategoryTerm Term: ${printTerm(elabRes.term)}`);
    console.log(`NatCategoryTerm Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'CatTerm') throw new Error("Test 2.1 failed: MkCat_ type is not Cat");

    const ObjOfNatCat = ObjTerm(NatCategoryTerm);
    elabRes = elaborate(ObjOfNatCat, undefined, baseCtx); 
    console.log(`Obj(NatCategoryTerm) Term (norm): ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if (!areEqual(elabRes.term, NatObjRepr, baseCtx)) throw new Error(`Test 2.2 failed: Obj(NatCategoryTerm) did not reduce to NatType. Got ${printTerm(elabRes.term)}`);

    defineGlobal("nat_val1", NatObjRepr); // x : NatType
    defineGlobal("nat_val2", NatObjRepr); // y : NatType
    const X_in_NatCat = Var("nat_val1"); 
    const Y_in_NatCat = Var("nat_val2"); 
    const HomInNatCat = HomTerm(NatCategoryTerm, X_in_NatCat, Y_in_NatCat);
    elabRes = elaborate(HomInNatCat, undefined, baseCtx);
    console.log(`Hom(NatCat,X,Y) Term (norm): ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    const expectedHomReduced = App(App(H_repr_Nat, X_in_NatCat), Y_in_NatCat); 
    if (!areEqual(elabRes.term, normalize(expectedHomReduced, baseCtx), baseCtx)) throw new Error(`Test 2.3 failed: Hom(NatCat,X,Y) did not reduce correctly. Expected ${printTerm(normalize(expectedHomReduced,baseCtx))} Got ${printTerm(elabRes.term)}`);
    console.log("Test 2 Passed.");

    console.log("\n--- Test 3: IdentityMorph ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    const MyNatCat3 = MkCat_(NatObjRepr, H_repr_Nat, C_impl_Nat_dummy);
    defineGlobal("cat_const", CatTerm(), MyNatCat3, false); // Make it a constant global category

    defineGlobal("x_obj_for_id", ObjTerm(Var("cat_const"))); // x_obj_for_id : Obj(cat_const)
    const anObjX = Var("x_obj_for_id"); 

    const id_x = IdentityMorph(anObjX); 
    elabRes = elaborate(id_x, undefined, baseCtx);
    console.log(`Term id_x: ${printTerm(elabRes.term)}`);
    console.log(`Type id_x: ${printTerm(elabRes.type)}`);
    
    const idTermSolved = getTermRef(elabRes.term) as Term & {tag:"IdentityMorph"};
    if (!idTermSolved.cat_IMPLICIT) throw new Error("Test 3.1 failed: id_x cat_IMPLICIT not filled.");
    if (!areEqual(getTermRef(idTermSolved.cat_IMPLICIT), Var("cat_const"), baseCtx)) throw new Error("Test 3.1 failed: id_x.cat_IMPLICIT not resolved to cat_const");
    
    if (elabRes.type.tag !== 'HomTerm') throw new Error("Test 3.1 failed: id_x type not HomTerm.");
    const homType = elabRes.type as Term & {tag:"HomTerm"};
    if(!areEqual(homType.dom, anObjX, baseCtx) || !areEqual(homType.cod, anObjX, baseCtx)) throw new Error("Test 3.1 failed: id_x type not Hom A X X form.");
    if (!areEqual(homType.cat, Var("cat_const"), baseCtx)) throw new Error(`Test 3.1: Cat of id_x's type is not cat_const. Got ${printTerm(homType.cat)}`);
    console.log("Test 3 Passed.");

    console.log("\n--- Test 4: ComposeMorph Inference ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    const MyNatCat4 = MkCat_(NatObjRepr, H_repr_Nat, C_impl_Nat_dummy);
    defineGlobal("C4", CatTerm(), MyNatCat4, false);
    defineGlobal("obj_x", ObjTerm(Var("C4"))); defineGlobal("obj_y", ObjTerm(Var("C4"))); defineGlobal("obj_z", ObjTerm(Var("C4")));
    const x = Var("obj_x"); const y = Var("obj_y"); const z = Var("obj_z");

    const f_morph_hole = Hole("?f_xy"); 
    const g_morph_hole = Hole("?g_yz"); 
    
    const comp_gf = ComposeMorph(g_morph_hole, f_morph_hole); 
    // Check against expected type to drive inference of implicits for comp_gf
    const expectedCompType = HomTerm(Var("C4"), x, z);
    elabRes = elaborate(comp_gf, expectedCompType, baseCtx);

    console.log(`Term comp_gf: ${printTerm(elabRes.term)}`);
    console.log(`Type comp_gf: ${printTerm(elabRes.type)}`); // Should be Hom C4 x z
    if(!areEqual(elabRes.type, expectedCompType, baseCtx)) throw new Error(`Test 4.0 Failed: comp_gf type not as expected. Got ${printTerm(elabRes.type)}`);
    
    const compTermSolved = getTermRef(elabRes.term) as Term & {tag:"ComposeMorph"};
    if (!compTermSolved.cat_IMPLICIT || !compTermSolved.objX_IMPLICIT || !compTermSolved.objY_IMPLICIT || !compTermSolved.objZ_IMPLICIT) {
        throw new Error("Test 4.1 failed: ComposeMorph implicits not filled.");
    }
    if(!areEqual(getTermRef(compTermSolved.cat_IMPLICIT), Var("C4"), baseCtx)) throw new Error("Test 4.1 Failed: comp.cat not C4");
    if(!areEqual(getTermRef(compTermSolved.objX_IMPLICIT), x, baseCtx)) throw new Error("Test 4.1 Failed: comp.X not obj_x");
    if(!areEqual(getTermRef(compTermSolved.objY_IMPLICIT), y, baseCtx)) throw new Error("Test 4.1 Failed: comp.Y not obj_y");
    if(!areEqual(getTermRef(compTermSolved.objZ_IMPLICIT), z, baseCtx)) throw new Error("Test 4.1 Failed: comp.Z not obj_z");
        
    const f_type = (f_morph_hole as Term & {tag:"Hole"}).elaboratedType;
    const g_type = (g_morph_hole as Term & {tag:"Hole"}).elaboratedType;
    if (!f_type || !g_type) throw new Error("Test 4.1: f or g did not get elaborated types.");

    const expected_f_type = HomTerm(Var("C4"), x, y);
    const expected_g_type = HomTerm(Var("C4"), y, z);

    if (!areEqual(getTermRef(f_type), expected_f_type, baseCtx)) throw new Error(`Test 4.1: ?f_xy type mismatch. Got ${printTerm(getTermRef(f_type))}, expected ${printTerm(expected_f_type)}`);
    if (!areEqual(getTermRef(g_type), expected_g_type, baseCtx)) throw new Error(`Test 4.1: ?g_yz type mismatch. Got ${printTerm(getTermRef(g_type))}, expected ${printTerm(expected_g_type)}`);
    
    console.log("Test 4 Passed.");

    console.log("\n--- Test 5: Rewrite rule comp (g (id X)) ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules(); // Rules are added here
    const C5_const = MkCat_(NatObjRepr, H_repr_Nat, C_impl_Nat_dummy);
    defineGlobal("C5_cat", CatTerm(), C5_const, true);
    
    defineGlobal("x5_obj", ObjTerm(Var("C5_cat"))); 
    defineGlobal("y5_obj", ObjTerm(Var("C5_cat")));
    const X5_term = Var("x5_obj"); 
    const Y5_term = Var("y5_obj");
    
    // g: Hom C5_cat Y5_term X5_term (Note: G takes Y to X in pattern G o id_X)
    defineGlobal("concrete_g_yx", HomTerm(Var("C5_cat"), Y5_term, X5_term)); 
    const concrete_g_yx_term = Var("concrete_g_yx");

    const id_X5_term = IdentityMorph(X5_term, Var("C5_cat"));
    // Test G o id_X, where G is concrete_g_yx, id_X is id_X5_term.
    // ComposeMorph(G, id_X, Cat, Cod(G), Dom(G), Dom(id_X))
    // cat = C5_cat
    // G = concrete_g_yx (Hom C5_cat Y5_term X5_term)
    // id_X = id_X5_term (Hom C5_cat X5_term X5_term)
    // Implicit objX_IMPLICIT (dom of id) = X5_term
    // Implicit objY_IMPLICIT (cod of id / dom of G) = X5_term
    // Implicit objZ_IMPLICIT (cod of G) = Y5_term (Mistake in my pattern above, Y should be cod G)
    // My rule was: ComposeMorph(Var("G"), IdentityMorph(Var("X_obj"), Var("CAT")), Var("CAT"), Var("Y"), Var("X_obj"), Var("X_obj")) -> Var("G")
    // Here Y is codomain of G. X_obj is domain of G.
    // So G: Hom CAT X_obj Y. The result is Hom CAT X_obj Y.
    // Test term: concrete_g_yx o id_Y5 -- this doesn't match "g o id_X" where X is dom(g)
    // Let's redefine g to match the pattern structure: g: Hom C5 X Y. Test g o id_X.
    defineGlobal("concrete_g_xy", HomTerm(Var("C5_cat"), X5_term, Y5_term));
    const concrete_g_xy_term = Var("concrete_g_xy");

    // Test: concrete_g_xy o id_X5_term
    // Expected result: concrete_g_xy
    // ComposeMorph(concrete_g_xy, id_X5_term, cat=C5_cat, X=X5, Y=X5, Z=Y5)
    // LHS pattern: ComposeMorph(Var("G"), IdentityMorph(Var("X_obj"), Var("CAT")), Var("CAT"), Var("Y"), Var("X_obj"), Var("X_obj"))
    //  Var("G") matches concrete_g_xy (type Hom C5 X5 Y5)
    //  IdentityMorph(Var("X_obj"), Var("CAT")) matches id_X5_term (IdentityMorph(X5_term, C5_cat))
    //    Var("X_obj") matches X5_term
    //    Var("CAT") matches C5_cat
    //  Implicit cat matches C5_cat
    //  Implicit Y (cod G) matches Y5_term
    //  Implicit X (dom G / cod id) matches X5_term
    //  Implicit X (dom id) matches X5_term
    // This looks like it should match.
    const test_comp_concrete_g_id = ComposeMorph(concrete_g_xy_term, id_X5_term, Var("C5_cat"), X5_term, X5_term, Y5_term);

    elabRes = elaborate(test_comp_concrete_g_id, undefined, baseCtx);
    console.log(`Term (g o id): ${printTerm(elabRes.term)}`);
    console.log(`Type (g o id): ${printTerm(elabRes.type)}`);

    if (!areEqual(elabRes.term, concrete_g_xy_term, baseCtx)) {
        throw new Error(`Test 5 failed: g o id did not reduce to g. Got ${printTerm(elabRes.term)}, expected ${printTerm(concrete_g_xy_term)}`);
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

function resetMyLambdaPi_Emdash() { // Renamed for clarity
    resetMyLambdaPi(); 
}