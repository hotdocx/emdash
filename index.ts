// --- MyLambdaPi with Emdash Phase 1: Core Categories (Attempt 3) ---

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
    if (isConstantSymbol && value !== undefined) { // Corrected check
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
            // Only unfold if it has a value AND is NOT a declared constant symbol
            if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol) { 
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
                    const objX_val = getTermRef(comp.objX_IMPLICIT);
                    const objY_val = getTermRef(comp.objY_IMPLICIT);
                    const objZ_val = getTermRef(comp.objZ_IMPLICIT);
                    termAfterEmdashRules = App(App(App(App(App(C_impl, objX_val), objY_val), objZ_val), comp.g), comp.f);
                }
            }
        }
        
        if (termAfterEmdashRules !== termAfterDelta) {
            current = termAfterEmdashRules;
            changedInThisIteration = true;
        }

        const termBeforeUserRules = current;
        // Check if current head is a constant symbol (either Emdash primitive or global Var marked as such)
        const headIsConstant = isEmdashConstantSymbolTag(current.tag) || 
                               (current.tag === 'Var' && globalDefs.get(current.name)?.isConstantSymbol);

        if (!headIsConstant) {
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
            if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol) {
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
                if (comp.objX_IMPLICIT && comp.objY_IMPLICIT && comp.objZ_IMPLICIT) { 
                     const objX_val = getTermRef(comp.objX_IMPLICIT);
                     const objY_val = getTermRef(comp.objY_IMPLICIT);
                     const objZ_val = getTermRef(comp.objZ_IMPLICIT);
                     termAfterEmdashRules = App(App(App(App(App(catVal.composeImplementation, objX_val), objY_val), objZ_val), comp.g), comp.f);
                }
            }
        }
        if (termAfterEmdashRules !== termAfterDelta) {
            current = termAfterEmdashRules; changedInThisIteration = true;
        }
        
        const termBeforeUserRules = current;
        const headIsConstant = isEmdashConstantSymbolTag(current.tag) || 
                               (current.tag === 'Var' && globalDefs.get(current.name)?.isConstantSymbol);
        if (!headIsConstant) {
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
            if ((headReducedCompose as BaseTerm).tag === 'App') { // Use BaseTerm for cast
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
        case 'Type': case 'CatTerm': return rt2.tag === rt1.tag; // Ensure same tag
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
            const cat1_eq = rt1.cat_IMPLICIT ? getTermRef(rt1.cat_IMPLICIT) : Hole('_'); 
            const cat2_eq = id2.cat_IMPLICIT ? getTermRef(id2.cat_IMPLICIT) : Hole('_');
            if ((cat1_eq.tag !== 'Hole' || cat1_eq.id !== '_') && (cat2_eq.tag !== 'Hole' || cat2_eq.id !== '_') && !areEqual(cat1_eq, cat2_eq, ctx, depth + 1)) return false;
            return areEqual(rt1.obj, id2.obj, ctx, depth + 1);
        case 'ComposeMorph': 
            const comp2 = rt2 as Term & {tag:'ComposeMorph'};
            const comp_cat1_eq = rt1.cat_IMPLICIT ? getTermRef(rt1.cat_IMPLICIT) : Hole('_');
            const comp_cat2_eq = comp2.cat_IMPLICIT ? getTermRef(comp2.cat_IMPLICIT) : Hole('_');
            if ((comp_cat1_eq.tag !== 'Hole' || comp_cat1_eq.id !== '_') && (comp_cat2_eq.tag !== 'Hole' || comp_cat2_eq.id !== '_') && !areEqual(comp_cat1_eq, comp_cat2_eq, ctx, depth+1)) return false;
            // For ComposeMorph, after whnf, if they are still ComposeMorph tags, their explicit parts must be equal.
            // Implicits are mainly for type checking and enabling reductions; for structural equality of already-reduced terms, they might not be compared if one is a hole.
            return areEqual(rt1.g, comp2.g, ctx, depth + 1) &&
                   areEqual(rt1.f, comp2.f, ctx, depth + 1);
    }
}

function termContainsHole(term: Term, holeId: string, visited: Set<string>, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH) {
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
    let allSubSolved = true;
    for (let i = 0; i < args1.length; i++) {
        const t1_arg = args1[i];
        const t2_arg = args2[i];

        if (t1_arg === undefined && t2_arg === undefined) continue;
        if (!t1_arg || !t2_arg) { // One is undefined, the other is not. If not a hole, this is a structural mismatch.
            if ((t1_arg && t1_arg.tag !== 'Hole') || (t2_arg && t2_arg.tag !== 'Hole')) return UnifyResult.Failed;
            // If one is undef and other is hole, unify hole with a conceptual "absent" or specific marker (or fail).
            // For now, if shapes differ for injective, it's fail.
            if(t1_arg !== t2_arg) return UnifyResult.Failed; // e.g. undef vs hole
            continue;
        }

        const argStatus = unify(t1_arg, t2_arg, ctx, depth + 1);
        if (argStatus === UnifyResult.Failed) return UnifyResult.Failed;
        if (argStatus === UnifyResult.RewrittenByRule || argStatus === UnifyResult.Progress) {
            madeProgress = true;
            allSubSolved = false;
        } else if (argStatus !== UnifyResult.Solved) { // Should not happen if Failed/Rewritten/Progress handled
            allSubSolved = false;
        }
    }
    
    if (madeProgress) return UnifyResult.Progress; // If any sub-problem made progress, the whole is Progress.
    
    // If allSubSolved is true, it means all unify calls on args returned Solved.
    // Then check if the parent terms are actually equal.
    if (allSubSolved) {
        if (areEqual(parentRt1, parentRt2, ctx, depth + 1)) return UnifyResult.Solved;
        // All args "solved", but parents not equal. This means the structure itself is problematic.
        // This path (injective unification where args are fine but whole is not) should then try rules.
        // However, the `isEmdashUnificationInjectiveTag` path in `unify` returns if this `unifyArgs` fails.
        // So if we reach here and `areEqual` is false, it's likely `Progress` still.
        return UnifyResult.Progress; 
    }
    
    return UnifyResult.Progress; // Default if not all solved but no failure.
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
                // This means a tag was in EMDASH_CONSTANT_SYMBOLS but not handled here specifically
                // or logic error in isEmdashUnificationInjectiveTag.
                // For constant symbols that are not IdentityMorph, their equality is structural.
                // areEqual should have handled them if they were truly equal.
                // If they are not areEqual, but have same constant tag, try rules.
                return tryUnificationRules(rt1, rt2, ctx, depth + 1);
        }
        const argStatus = unifyArgs(args1, args2, ctx, depth, rt1, rt2);
        // If injective path fails, it means args didn't unify. Don't try rules for the S===S problem here,
        // as injectivity means S t1 = S t2 <=> t1=t2. If t1!=t2, then S t1 != S t2.
        // This is different from non-injective where S t1 = S t2 might hold by a rule even if t1!=t2.
        return argStatus; // Failed, Progress, or Solved.
    }

    switch (rt1.tag) {
        case 'Type': return UnifyResult.Solved; 
        case 'Var': return tryUnificationRules(rt1, rt2, ctx, depth + 1);
        case 'App': { 
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
        case 'Lam': { 
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
        case 'Pi': { 
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
            const c_t1_current_ref = getTermRef(constraint.t1);
            const c_t2_current_ref = getTermRef(constraint.t2);

            if (areEqual(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1)) {
                constraints.splice(currentConstraintIdx, 1); 
                changedInOuterLoop = true; 
                continue; 
            }

            try {
                const unifyResult = unify(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1);
                
                if (unifyResult === UnifyResult.Solved) {
                    changedInOuterLoop = true; 
                    currentConstraintIdx++; 
                } else if (unifyResult === UnifyResult.RewrittenByRule) {
                    constraints.splice(currentConstraintIdx, 1); 
                    changedInOuterLoop = true;
                } else if (unifyResult === UnifyResult.Progress) {
                    changedInOuterLoop = true;
                    currentConstraintIdx++; 
                } else { 
                    return false; 
                }
            } catch (e) {
                return false; 
            }
        }
    }

    if (iterations >= maxIterations && changedInOuterLoop && constraints.length > 0) { 
        // console.warn("Constraint solving reached max iterations and was still making changes. Constraints list size: " + constraints.length);
    }
    for (const constraint of constraints) { 
        if (!areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
            return false;
        }
    }
    return constraints.length === 0;
}


function ensureImplicitsAsHoles(term: Term): Term {
    const t = term; 
    if (t.tag === 'IdentityMorph' && t.cat_IMPLICIT === undefined) {
        t.cat_IMPLICIT = Hole(freshHoleName() + "_cat_of_" + printTerm(t.obj).replace(/\W/g, '').slice(0,10));
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

    if (current.tag === 'Var') {
        const gdef = globalDefs.get(current.name);
        if (gdef) return gdef.type;
        const binding = lookupCtx(ctx, current.name);
        if (!binding) throw new Error(`Unbound variable: ${current.name}`);
        return binding.type;
    }

    switch (current.tag) {
        case 'Type': return Type();
        case 'Hole': {
            if (current.elaboratedType) return getTermRef(current.elaboratedType);
            const newTypeForHole = Hole(freshHoleName() + "_type_of_" + current.id.replace("?","")); 
            current.elaboratedType = newTypeForHole;
            return newTypeForHole;
        }
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
        case 'CatTerm': return Type();
        case 'ObjTerm':
            check(ctx, current.cat, CatTerm(), stackDepth + 1);
            return Type();
        case 'HomTerm': {
            check(ctx, current.cat, CatTerm(), stackDepth + 1);
            const catForHom = getTermRef(current.cat); 
            // We must use the *resolved* category `catForHom` when checking dom and cod
            check(ctx, current.dom, ObjTerm(catForHom), stackDepth + 1);
            check(ctx, current.cod, ObjTerm(catForHom), stackDepth + 1);
            return Type();
        }
        case 'MkCat_': {
            check(ctx, current.objRepresentation, Type(), stackDepth + 1);
            const O_repr = getTermRef(current.objRepresentation);
            
            const expected_H_type = Pi("X", O_repr, _X => Pi("Y", O_repr, _Y => Type()));
            check(ctx, current.homRepresentation, expected_H_type, stackDepth + 1);
            const H_repr_func = getTermRef(current.homRepresentation); 

            const type_of_hom_X_Y = (X_val: Term, Y_val: Term) => App(App(H_repr_func, X_val), Y_val);

            // The composeImplementation takes explicit X,Y,Z objects, then g, then f
            const expected_C_type = 
                Pi("Xobj", O_repr, Xobj_term =>
                Pi("Yobj", O_repr, Yobj_term =>
                Pi("Zobj", O_repr, Zobj_term =>
                Pi("gmorph", type_of_hom_X_Y(Yobj_term, Zobj_term), _gmorph_term =>
                Pi("fmorph", type_of_hom_X_Y(Xobj_term, Yobj_term), _fmorph_term =>
                type_of_hom_X_Y(Xobj_term, Zobj_term)
                )))));
            check(ctx, current.composeImplementation, expected_C_type, stackDepth + 1);
            return CatTerm();
        }
        case 'IdentityMorph': {
            // After ensureImplicitsAsHoles, cat_IMPLICIT is a Hole if it was undefined.
            const catHole = current.cat_IMPLICIT!; // Should be a Hole if not provided
            const objType = infer(ctx, current.obj, stackDepth + 1); 
            addConstraint(objType, ObjTerm(catHole), `Object ${printTerm(current.obj)} of id must be in cat ${printTerm(catHole)}`);
            return HomTerm(catHole, current.obj, current.obj);
        }
        case 'ComposeMorph': {
            const catHole = current.cat_IMPLICIT!;
            const XHole = current.objX_IMPLICIT!;
            const YHole = current.objY_IMPLICIT!;
            const ZHole = current.objZ_IMPLICIT!;

            const type_f = infer(ctx, current.f, stackDepth + 1);
            const type_g = infer(ctx, current.g, stackDepth + 1);

            addConstraint(type_f, HomTerm(catHole, XHole, YHole), `Arg f of Compose`);
            addConstraint(type_g, HomTerm(catHole, YHole, ZHole), `Arg g of Compose`);
            
            return HomTerm(catHole, XHole, ZHole);
        }
    }
}

function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0): void {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Check stack depth exceeded (depth: ${stackDepth}, term ${printTerm(term)}, expType ${printTerm(expectedType)})`);
    
    const current = ensureImplicitsAsHoles(getTermRef(term)); 
    const normExpectedType = whnf(expectedType, ctx, stackDepth + 1); 

    if (current.tag === 'Lam' && !current._isAnnotated && normExpectedType.tag === 'Pi') {
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
        // cat_IMPLICIT is already a hole if it was undefined
        addConstraint(idTerm.cat_IMPLICIT!, expHom.cat, `id.cat vs expected hom.cat`);
        addConstraint(idTerm.obj, expHom.dom, `id.obj vs expected hom.dom`);
        addConstraint(idTerm.obj, expHom.cod, `id.obj vs expected hom.cod`);
        
        // Crucially, check that idTerm.obj is an object of the (now constrained) idTerm.cat_IMPLICIT!
        const objTypeForId = infer(ctx, idTerm.obj, stackDepth + 1); // This might create new constraints if obj is complex
        addConstraint(objTypeForId, ObjTerm(idTerm.cat_IMPLICIT!), `id.obj actual type check for ${printTerm(idTerm.obj)} in cat ${printTerm(idTerm.cat_IMPLICIT!)}`);
        return;
    }
    
    if (current.tag === 'ComposeMorph' && normExpectedType.tag === 'HomTerm') {
        const compTerm = current;
        const expHom = normExpectedType;
        // Implicits are already holes
        addConstraint(compTerm.cat_IMPLICIT!, expHom.cat, `comp.cat vs expected hom.cat`);
        addConstraint(compTerm.objX_IMPLICIT!, expHom.dom, `comp.X vs expected hom.dom`);
        addConstraint(compTerm.objZ_IMPLICIT!, expHom.cod, `comp.Z vs expected hom.cod`);

        // Additional constraints from inferring f and g, using the now-constrained implicits from compTerm
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
        if (e instanceof Error && (e.message.startsWith("Type error:") || e.message.startsWith("Unbound variable:") || e.message.startsWith("Cannot apply non-function:") || e.message.startsWith("Constant symbol"))) {
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
        if (pvarName === '_') return subst; 
        const existing = subst.get(pvarName);
        if (existing) {
            return areEqual(currentTermStruct, existing, ctx, stackDepth + 1) ? subst : null;
        }
        subst.set(pvarName, currentTermStruct); 
        return subst;
    }
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
        case 'ObjTerm': {
            return matchPattern(rtPattern.cat, (currentTermStruct as Term & {tag:'ObjTerm'}).cat, ctx, patternVarDecls, subst, stackDepth + 1);
        }
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
            const idPcat_IMPLICIT = idP.cat_IMPLICIT; // To help TypeScript narrow type
            if (idPcat_IMPLICIT) { 
                if (!idT.cat_IMPLICIT && idPcat_IMPLICIT.tag !== 'Hole' && !(idPcat_IMPLICIT.tag === 'Var' && idPcat_IMPLICIT.name === '_')) return null;
                if (idT.cat_IMPLICIT) { 
                     s = matchPattern(idPcat_IMPLICIT, idT.cat_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1);
                     if(!s) return null;
                } else if (idPcat_IMPLICIT.tag !== 'Hole' && !(idPcat_IMPLICIT.tag === 'Var' && idPcat_IMPLICIT.name === '_')) {
                    return null; 
                }
            } 
            return matchPattern(idP.obj, idT.obj, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'ComposeMorph': {
            const compP = rtPattern as Term & {tag:'ComposeMorph'};
            const compT = currentTermStruct as Term & {tag:'ComposeMorph'};
            let s = subst;
            const compPcat_IMPLICIT = compP.cat_IMPLICIT;
            if (compPcat_IMPLICIT) {
                if (!compT.cat_IMPLICIT && compPcat_IMPLICIT.tag !== 'Hole' && !(compPcat_IMPLICIT.tag === 'Var' && compPcat_IMPLICIT.name === '_')) return null;
                if (compT.cat_IMPLICIT) { s = matchPattern(compPcat_IMPLICIT, compT.cat_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null; }
                else if (compPcat_IMPLICIT.tag !== 'Hole' && !(compPcat_IMPLICIT.tag === 'Var' && compPcat_IMPLICIT.name === '_')) return null;
            }
            const compPobjX_IMPLICIT = compP.objX_IMPLICIT;
            if (compPobjX_IMPLICIT) {
                if (!compT.objX_IMPLICIT && compPobjX_IMPLICIT.tag !== 'Hole' && !(compPobjX_IMPLICIT.tag === 'Var' && compPobjX_IMPLICIT.name === '_')) return null;
                if (compT.objX_IMPLICIT) { s = matchPattern(compPobjX_IMPLICIT, compT.objX_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null; }
                else if (compPobjX_IMPLICIT.tag !== 'Hole' && !(compPobjX_IMPLICIT.tag === 'Var' && compPobjX_IMPLICIT.name === '_')) return null;
            }
            const compPobjY_IMPLICIT = compP.objY_IMPLICIT;
            if (compPobjY_IMPLICIT) {
                if (!compT.objY_IMPLICIT && compPobjY_IMPLICIT.tag !== 'Hole' && !(compPobjY_IMPLICIT.tag === 'Var' && compPobjY_IMPLICIT.name === '_')) return null;
                if (compT.objY_IMPLICIT) { s = matchPattern(compPobjY_IMPLICIT, compT.objY_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null; }
                else if (compPobjY_IMPLICIT.tag !== 'Hole' && !(compPobjY_IMPLICIT.tag === 'Var' && compPobjY_IMPLICIT.name === '_')) return null;
            }
            const compPobjZ_IMPLICIT = compP.objZ_IMPLICIT;
            if (compPobjZ_IMPLICIT) {
                if (!compT.objZ_IMPLICIT && compPobjZ_IMPLICIT.tag !== 'Hole' && !(compPobjZ_IMPLICIT.tag === 'Var' && compPobjZ_IMPLICIT.name === '_')) return null;
                if (compT.objZ_IMPLICIT) { s = matchPattern(compPobjZ_IMPLICIT, compT.objZ_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1); if (!s) return null; }
                else if (compPobjZ_IMPLICIT.tag !== 'Hole' && !(compPobjZ_IMPLICIT.tag === 'Var' && compPobjZ_IMPLICIT.name === '_')) return null;
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
        case 'CatTerm': return 'Cat';
        case 'ObjTerm': return `(Obj ${printTerm(current.cat, boundVars, stackDepth + 1)})`;
        case 'HomTerm':
            return `(Hom ${printTerm(current.cat, boundVars, stackDepth + 1)} ${printTerm(current.dom, boundVars, stackDepth + 1)} ${printTerm(current.cod, boundVars, stackDepth + 1)})`;
        case 'MkCat_':
            return `(mkCat_ {O=${printTerm(current.objRepresentation, boundVars, stackDepth + 1)}, H=${printTerm(current.homRepresentation, boundVars, stackDepth + 1)}, C=${printTerm(current.composeImplementation, boundVars, stackDepth + 1)}})`;
        case 'IdentityMorph': {
            let catIdStr = "";
            if (current.cat_IMPLICIT && getTermRef(current.cat_IMPLICIT).tag !== 'Hole') { 
                 catIdStr = ` [cat=${printTerm(current.cat_IMPLICIT, boundVars, stackDepth + 1)}]`;
            }
            return `(id${catIdStr} ${printTerm(current.obj, boundVars, stackDepth + 1)})`;
        }
        case 'ComposeMorph': {
            let catCompStr = "";
            if (current.cat_IMPLICIT && getTermRef(current.cat_IMPLICIT).tag !== 'Hole') {
                 catCompStr = ` [cat=${printTerm(current.cat_IMPLICIT, boundVars, stackDepth + 1)}]`;
            }
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

console.log("--- MyLambdaPi with Emdash Phase 1: Core Categories (Attempt 3) ---");

function setupPhase1GlobalsAndRules() {
    defineGlobal("NatType", Type(), undefined, true); 
    defineGlobal("BoolType", Type(), undefined, true);

    const pvarCat = { name: "CAT_pv", type: CatTerm() }; // Changed name to avoid clash
    const pvarX_obj = { name: "X_obj_pv", type: ObjTerm(Var("CAT_pv")) }; 
    const pvarY_obj = { name: "Y_obj_pv", type: ObjTerm(Var("CAT_pv")) }; 
    // const pvarZ_obj = { name: "Z_obj_pv", type: ObjTerm(Var("CAT_pv")) }; // Not used in current rules

    const pvarF_morph = { name: "f_morph_pv", type: HomTerm(Var("CAT_pv"), Var("X_obj_pv"), Var("Y_obj_pv")) }; 
    const pvarG_morph = { name: "g_morph_pv", type: HomTerm(Var("CAT_pv"), Var("Y_obj_pv"), Var("X_obj_pv")) }; // g: Y -> X for g o id_X

    // Rule: g o id_X = g where g : Hom CAT Y X, id_X : Hom CAT X X
    // lhs: ComposeMorph(g_morph_pv, IdentityMorph(X_obj_pv, CAT_pv), CAT_pv, Y_obj_pv (cod g), X_obj_pv (dom g & cod id), X_obj_pv (dom id))
    addRewriteRule({
        name: "comp_g_idX",
        patternVars: [pvarCat, pvarX_obj, pvarY_obj, pvarG_morph],
        lhs: ComposeMorph(Var("g_morph_pv"), IdentityMorph(Var("X_obj_pv"), Var("CAT_pv")), 
                         Var("CAT_pv"), Var("Y_obj_pv"), Var("X_obj_pv"), Var("X_obj_pv")),
        rhs: Var("g_morph_pv")
    });

    // Rule: id_Y o f = f where f : Hom CAT X Y, id_Y : Hom CAT Y Y
    // lhs: ComposeMorph(IdentityMorph(Y_obj_pv, CAT_pv), f_morph_pv, CAT_pv, Y_obj_pv (cod id & cod f), Y_obj_pv (dom id), X_obj_pv (dom f))
    addRewriteRule({
        name: "comp_idY_f",
        patternVars: [pvarCat, pvarX_obj, pvarY_obj, pvarF_morph], 
        lhs: ComposeMorph(IdentityMorph(Var("Y_obj_pv"), Var("CAT_pv")), Var("f_morph_pv"),
                         Var("CAT_pv"), Var("Y_obj_pv"), Var("Y_obj_pv"), Var("X_obj_pv")),
        rhs: Var("f_morph_pv")
    });
}


function runPhase1Tests() {
    const baseCtx = emptyCtx;
    const NatObjRepr = Var("NatType"); 
    // const BoolObjRepr = Var("BoolType"); // Not used in phase 1 tests

    console.log("\n--- Test 1: Basic Cat/Obj/Hom Types ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    let testTerm : Term;
    testTerm = CatTerm();
    let elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.1 failed: Cat is not Type");

    const someCatHole = Hole("?MyCat"); 
    const type_of_someCatHole = infer(baseCtx, someCatHole); // This sets someCatHole.elaboratedType = ?h_type_of_MyCat
    addConstraint(type_of_someCatHole, CatTerm(), "Constraint: type of ?MyCat is Cat");
    if(!solveConstraints(baseCtx)) throw new Error("Test 1.2 setup failed: ?MyCat not typable as Cat");
    // After solving, someCatHole.elaboratedType.ref should be CatTerm()
    
    testTerm = ObjTerm(someCatHole);
    elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.2 failed: Obj ?MyCat is not Type");
    
    const objXHole = Hole("?X"); 
    const objYHole = Hole("?Y");
    // To correctly type ?X and ?Y as objects of ?MyCat, we infer their types and constrain them.
    const type_of_objXHole = infer(baseCtx, objXHole);
    const type_of_objYHole = infer(baseCtx, objYHole);
    addConstraint(type_of_objXHole, ObjTerm(someCatHole), "Constraint: type of ?X is Obj ?MyCat");
    addConstraint(type_of_objYHole, ObjTerm(someCatHole), "Constraint: type of ?Y is Obj ?MyCat");
    if(!solveConstraints(baseCtx)) throw new Error("Test 1.3 setup failed: ?X or ?Y not typable as Obj ?MyCat");

    testTerm = HomTerm(someCatHole, objXHole, objYHole);
    elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.3 failed: Hom ?MyCat ?X ?Y is not Type");
    console.log("Test 1 Passed.");

    console.log("\n--- Test 2: MkCat_ and Projections ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    const H_repr_Nat = Lam("X", Var("NatType"), _X => Lam("Y", Var("NatType"), _Y => Type())); 
    const C_impl_Nat_dummy = Lam("Xobj", Var("NatType"), _Xobj => Lam("Yobj", Var("NatType"), _Yobj => Lam("Zobj", Var("NatType"), _Zobj => Lam("gmorph", App(App(H_repr_Nat,Var("Yobj")),Var("Zobj")), _gmorph => Lam("fmorph", App(App(H_repr_Nat,Var("Xobj")),Var("Yobj")),_fmorph => Hole("comp_res_dummy"))))));
    
    const NatCategoryTermVal = MkCat_(NatObjRepr, H_repr_Nat, C_impl_Nat_dummy);
    elabRes = elaborate(NatCategoryTermVal, undefined, baseCtx); 
    console.log(`NatCategoryTermVal Term: ${printTerm(elabRes.term)}`);
    console.log(`NatCategoryTermVal Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'CatTerm') throw new Error("Test 2.1 failed: MkCat_ type is not Cat");

    const ObjOfNatCat = ObjTerm(NatCategoryTermVal);
    elabRes = elaborate(ObjOfNatCat, undefined, baseCtx); 
    console.log(`Obj(NatCategoryTermVal) Term (norm): ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if (!areEqual(elabRes.term, NatObjRepr, baseCtx)) throw new Error(`Test 2.2 failed: Obj(NatCategoryTerm) did not reduce to NatType. Got ${printTerm(elabRes.term)}`);

    defineGlobal("nat_val1", NatObjRepr); 
    defineGlobal("nat_val2", NatObjRepr); 
    const X_in_NatCat = Var("nat_val1"); 
    const Y_in_NatCat = Var("nat_val2"); 
    const HomInNatCat = HomTerm(NatCategoryTermVal, X_in_NatCat, Y_in_NatCat);
    elabRes = elaborate(HomInNatCat, undefined, baseCtx);
    console.log(`Hom(NatCat,X,Y) Term (norm): ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    const expectedHomReduced = App(App(H_repr_Nat, X_in_NatCat), Y_in_NatCat); 
    if (!areEqual(elabRes.term, normalize(expectedHomReduced, baseCtx), baseCtx)) throw new Error(`Test 2.3 failed: Hom(NatCat,X,Y) did not reduce correctly. Expected ${printTerm(normalize(expectedHomReduced,baseCtx))} Got ${printTerm(elabRes.term)}`);
    console.log("Test 2 Passed.");

    console.log("\n--- Test 3: IdentityMorph ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    const MyNatCat3_val = MkCat_(NatObjRepr, H_repr_Nat, C_impl_Nat_dummy);
    // Define MyNatCat3_Global as a *value*, not a primitive constant symbol
    defineGlobal("MyNatCat3_Global", CatTerm(), MyNatCat3_val, false); 

    // x_obj_for_id must be a term whose type is Obj(MyNatCat3_Global)
    // Obj(MyNatCat3_Global) normalizes to NatObjRepr (i.e. NatType)
    defineGlobal("x_obj_term", NatObjRepr); // x_obj_term : NatType
    const anObjX = Var("x_obj_term"); 

    const id_x = IdentityMorph(anObjX); 
    // We expect id_x to have type Hom MyNatCat3_Global anObjX anObjX
    const expected_id_x_type = HomTerm(Var("MyNatCat3_Global"), anObjX, anObjX);
    elabRes = elaborate(id_x, expected_id_x_type, baseCtx);

    console.log(`Term id_x: ${printTerm(elabRes.term)}`);
    console.log(`Type id_x: ${printTerm(elabRes.type)}`); // Should be normalized version of expected_id_x_type
    
    const idTermSolved = getTermRef(elabRes.term) as Term & {tag:"IdentityMorph"};
    if (!idTermSolved.cat_IMPLICIT) throw new Error("Test 3.1 failed: id_x cat_IMPLICIT not filled.");
    // After elaboration against expected_id_x_type, cat_IMPLICIT should be MyNatCat3_Global
    if (!areEqual(getTermRef(idTermSolved.cat_IMPLICIT), Var("MyNatCat3_Global"), baseCtx)) {
        throw new Error(`Test 3.1 failed: id_x.cat_IMPLICIT not resolved to MyNatCat3_Global. Got: ${printTerm(getTermRef(idTermSolved.cat_IMPLICIT))}`);
    }
    if (!areEqual(elabRes.type, expected_id_x_type, baseCtx)) {
         throw new Error(`Test 3.2 failed: id_x type mismatch. Expected ${printTerm(expected_id_x_type)}, Got ${printTerm(elabRes.type)}`)
    }
    console.log("Test 3 Passed.");

    console.log("\n--- Test 4: ComposeMorph Inference ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    const MyNatCat4_val = MkCat_(NatObjRepr, H_repr_Nat, C_impl_Nat_dummy);
    defineGlobal("C4_Global", CatTerm(), MyNatCat4_val, false); // C4_Global is MyNatCat4_val

    // Define object terms of type Obj(C4_Global), which is NatObjRepr (i.e. NatType)
    defineGlobal("obj_x_term", NatObjRepr); 
    defineGlobal("obj_y_term", NatObjRepr); 
    defineGlobal("obj_z_term", NatObjRepr);
    const x_term = Var("obj_x_term"); 
    const y_term = Var("obj_y_term"); 
    const z_term = Var("obj_z_term");

    const f_morph_hole = Hole("?f_xy"); 
    const g_morph_hole = Hole("?g_yz"); 
    
    const comp_gf = ComposeMorph(g_morph_hole, f_morph_hole); 
    const expectedCompType = HomTerm(Var("C4_Global"), x_term, z_term);
    elabRes = elaborate(comp_gf, expectedCompType, baseCtx);

    console.log(`Term comp_gf: ${printTerm(elabRes.term)}`);
    console.log(`Type comp_gf: ${printTerm(elabRes.type)}`); 
    if(!areEqual(elabRes.type, expectedCompType, baseCtx)) throw new Error(`Test 4.0 Failed: comp_gf type not as expected. Got ${printTerm(elabRes.type)}, Expected ${printTerm(expectedCompType)}`);
    
    const compTermSolved = getTermRef(elabRes.term) as Term & {tag:"ComposeMorph"};
    if (!compTermSolved.cat_IMPLICIT || !compTermSolved.objX_IMPLICIT || !compTermSolved.objY_IMPLICIT || !compTermSolved.objZ_IMPLICIT) {
        throw new Error("Test 4.1 failed: ComposeMorph implicits not filled.");
    }
    if(!areEqual(getTermRef(compTermSolved.cat_IMPLICIT), Var("C4_Global"), baseCtx)) throw new Error("Test 4.1 Failed: comp.cat not C4_Global");
    if(!areEqual(getTermRef(compTermSolved.objX_IMPLICIT), x_term, baseCtx)) throw new Error("Test 4.1 Failed: comp.X not obj_x_term");
    if(!areEqual(getTermRef(compTermSolved.objY_IMPLICIT), y_term, baseCtx)) throw new Error("Test 4.1 Failed: comp.Y not obj_y_term");
    if(!areEqual(getTermRef(compTermSolved.objZ_IMPLICIT), z_term, baseCtx)) throw new Error("Test 4.1 Failed: comp.Z not obj_z_term");
        
    const f_type = (f_morph_hole as Term & {tag:"Hole"}).elaboratedType;
    const g_type = (g_morph_hole as Term & {tag:"Hole"}).elaboratedType;
    if (!f_type || !g_type) throw new Error("Test 4.1: f or g did not get elaborated types.");

    const expected_f_type = HomTerm(Var("C4_Global"), x_term, y_term);
    const expected_g_type = HomTerm(Var("C4_Global"), y_term, z_term);

    if (!areEqual(getTermRef(f_type), expected_f_type, baseCtx)) throw new Error(`Test 4.1: ?f_xy type mismatch. Got ${printTerm(getTermRef(f_type))}, expected ${printTerm(expected_f_type)}`);
    if (!areEqual(getTermRef(g_type), expected_g_type, baseCtx)) throw new Error(`Test 4.1: ?g_yz type mismatch. Got ${printTerm(getTermRef(g_type))}, expected ${printTerm(expected_g_type)}`);
    
    console.log("Test 4 Passed.");

    console.log("\n--- Test 5: Rewrite rule comp (g (id X)) ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules(); 
    const C5_val = MkCat_(NatObjRepr, H_repr_Nat, C_impl_Nat_dummy);
    defineGlobal("C5_cat_global", CatTerm(), C5_val, false);
    
    defineGlobal("x5_obj_term", NatObjRepr); 
    defineGlobal("y5_obj_term", NatObjRepr);
    const X5_term = Var("x5_obj_term"); 
    const Y5_term = Var("y5_obj_term");
    
    // g: Hom C5_cat_global X5_term Y5_term (for rule g o id_X where X is dom(g))
    defineGlobal("concrete_g_xy", HomTerm(Var("C5_cat_global"), X5_term, Y5_term)); 
    const concrete_g_xy_term = Var("concrete_g_xy");

    const id_X5_term = IdentityMorph(X5_term, Var("C5_cat_global")); // id_{X5_term} in C5_cat_global
    // Test: concrete_g_xy o id_X5_term
    // ComposeMorph(concrete_g_xy, id_X5_term, cat=C5_cat_global, X=X5_term, Y=X5_term, Z=Y5_term)
    const test_comp_concrete_g_id = ComposeMorph(concrete_g_xy_term, id_X5_term, 
                                                Var("C5_cat_global"), X5_term, X5_term, Y5_term);

    elabRes = elaborate(test_comp_concrete_g_id, undefined, baseCtx);
    console.log(`Term (g o id): ${printTerm(elabRes.term)}`);
    console.log(`Type (g o id): ${printTerm(elabRes.type)}`);

    if (!areEqual(elabRes.term, concrete_g_xy_term, baseCtx)) {
        throw new Error(`Test 5 failed: g o id did not reduce to g. Got ${printTerm(elabRes.term)}, expected ${printTerm(concrete_g_xy_term)}`);
    }
    console.log("Test 5 Passed.");

}

try {
    runPhase1Tests();
    console.log("\nAll Phase 1 Emdash tests passed successfully!");
} catch (e) {
    console.error("\n*** PHASE 1 EMdash TEST SCENARIO FAILED ***");
    console.error((e as Error).message);
    console.error((e as Error).stack);
}

function resetMyLambdaPi_Emdash() { 
    resetMyLambdaPi(); 
}