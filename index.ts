// --- MyLambdaPi with Emdash Phase 1: Core Categories (Attempt 5) ---

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
const Lam = (paramName: string, paramTypeOrBody: Term | ((v: Term) => Term), bodyOrNothing?: (v: Term) => Term): Term & { tag: 'Lam' } => {
    if (typeof paramTypeOrBody === 'function' && bodyOrNothing === undefined) { 
        return { tag: 'Lam', paramName, paramType: undefined, body: paramTypeOrBody, _isAnnotated: false };
    } else if (paramTypeOrBody && typeof bodyOrNothing === 'function') { 
        return { tag: 'Lam', paramName, paramType: paramTypeOrBody as Term, body: bodyOrNothing, _isAnnotated: true };
    }
    throw new Error("Invalid Lam arguments");
}
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
// IdentityMorph is unification injective, but not a "constant symbol" in the sense of disallowing rewrite rules with it at the head.
const EMDASH_UNIFICATION_INJECTIVE_SYMBOLS = new Set<string>(['IdentityMorph']); 

function isEmdashConstantSymbolTag(tag: string): boolean {
    return EMDASH_CONSTANT_SYMBOLS.has(tag);
}
function isEmdashUnificationInjectiveStructurally(tag: string): boolean {
    // Constant symbols are structurally injective by definition of their comparison.
    // Plus explicitly marked ones.
    return EMDASH_CONSTANT_SYMBOLS.has(tag) || EMDASH_UNIFICATION_INJECTIVE_SYMBOLS.has(tag);
}

function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`WHNF stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    let current = getTermRef(term);

    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        let changedInThisPass = false;
        const termAtStartOfPass = current;

        // 1. Delta Reduction (for Vars)
        if (current.tag === 'Var') {
            const gdef = globalDefs.get(current.name);
            if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol) { 
                const valRef = getTermRef(gdef.value);
                if (valRef !== current) {
                     current = valRef;
                     changedInThisPass = true;
                }
            }
        }
        
        // 2. Emdash Specific Unfolding/Structural Reductions (Higher Priority)
        // These are definitional for Emdash constructors.
        const termAfterDelta = current;
        let termAfterEmdashRules = termAfterDelta;

        if (termAfterEmdashRules.tag === 'ObjTerm') {
            const resolvedCat = whnf(termAfterEmdashRules.cat, ctx, stackDepth + 1); // Crucial: WHNF cat first
            if (getTermRef(resolvedCat).tag === 'MkCat_') {
                const mkCatTerm = getTermRef(resolvedCat) as Term & {tag: 'MkCat_'};
                termAfterEmdashRules = mkCatTerm.objRepresentation;
            }
        } else if (termAfterEmdashRules.tag === 'HomTerm') {
            const resolvedCat = whnf(termAfterEmdashRules.cat, ctx, stackDepth + 1); 
            if (getTermRef(resolvedCat).tag === 'MkCat_') {
                const mkCatTerm = getTermRef(resolvedCat) as Term & {tag: 'MkCat_'};
                const H_repr = mkCatTerm.homRepresentation;
                // Args dom/cod are passed as is; App reduction will handle them if H_repr is Lam.
                termAfterEmdashRules = App(App(H_repr, termAfterEmdashRules.dom), termAfterEmdashRules.cod);
            }
        } else if (termAfterEmdashRules.tag === 'ComposeMorph') {
            const comp = termAfterEmdashRules;
            if (comp.cat_IMPLICIT) { 
                const resolvedCat = whnf(comp.cat_IMPLICIT, ctx, stackDepth + 1);
                if (getTermRef(resolvedCat).tag === 'MkCat_') {
                    const mkCatTerm = getTermRef(resolvedCat) as Term & {tag: 'MkCat_'};
                    const C_impl = mkCatTerm.composeImplementation;
                    // Implicits objX, Y, Z must be resolved (i.e., not undefined and not just fresh holes without refs)
                    // Type checking ensures they are filled or become constrained holes.
                    // WHNFing them here ensures they are values if they were complex terms.
                    if (comp.objX_IMPLICIT && comp.objY_IMPLICIT && comp.objZ_IMPLICIT) {
                        const objX_val = whnf(comp.objX_IMPLICIT, ctx, stackDepth + 1); 
                        const objY_val = whnf(comp.objY_IMPLICIT, ctx, stackDepth + 1);
                        const objZ_val = whnf(comp.objZ_IMPLICIT, ctx, stackDepth + 1);
                        // g and f are also whnf'd before application
                        const g_val = whnf(comp.g, ctx, stackDepth+1);
                        const f_val = whnf(comp.f, ctx, stackDepth+1);
                        termAfterEmdashRules = App(App(App(App(App(C_impl, objX_val), objY_val), objZ_val), g_val), f_val);
                    }
                }
            }
        }
        
        if (termAfterEmdashRules !== termAfterDelta) {
            current = termAfterEmdashRules;
            changedInThisPass = true;
            continue; // Restart WHNF loop for the new `current` term
        }

        // 3. User-Defined Rewrite Rules
        const termBeforeUserRules = current; // `current` might have changed from delta
        const headIsConstantForUserRules = isEmdashConstantSymbolTag(current.tag) || 
                               (current.tag === 'Var' && globalDefs.get(current.name)?.isConstantSymbol);
        if (!headIsConstantForUserRules) {
            for (const rule of userRewriteRules) {
                const subst = matchPattern(rule.lhs, termBeforeUserRules, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    const rhsApplied = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                    if (rhsApplied !== termBeforeUserRules) {
                        current = rhsApplied;
                        changedInThisPass = true;
                    }
                    if (changedInThisPass) continue; // Restart WHNF loop if rule fired
                }
            }
        }
        
        current = getTermRef(current); // Re-resolve after all potential changes in this pass

        if (!changedInThisPass && current === termAtStartOfPass) { // Check if term reference itself changed
            break; 
        }
        if (i === MAX_RECURSION_DEPTH - 1 && (changedInThisPass || current !== termAtStartOfPass) ) {
            // console.warn(`WHNF reached max iterations for delta/rules on: ${printTerm(term)} -> ${printTerm(current)}`);
        }
    }

    // Beta Reduction (last step in WHNF if head is App(Lam...))
    if (current.tag === 'App') {
        const funcNorm = whnf(current.func, ctx, stackDepth + 1); // WHNF the function part
        if (funcNorm.tag === 'Lam') {
            return whnf(funcNorm.body(current.arg), ctx, stackDepth + 1); // Beta reduce and WHNF result
        }
        if (funcNorm !== getTermRef(current.func)) return App(funcNorm, current.arg); // Reconstruct if func changed
        return current; 
    }
    return current;
}

function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Normalize stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    
    let current = getTermRef(term); 
    // Head reduction loop (similar to whnf, but separated for clarity for normalize)
    for (let i = 0; i < MAX_RECURSION_DEPTH; i++) {
        let changedInThisHeadPass = false;
        const termAtStartOfHeadPass = current;

        // Delta
        if (current.tag === 'Var') {
            const gdef = globalDefs.get(current.name);
            if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol) {
                const valRef = getTermRef(gdef.value);
                if (valRef !== current) { current = valRef; changedInThisHeadPass = true; }
            }
        }
        
        // Emdash structural reductions (higher priority)
        const termAfterHeadDelta = current;
        let termAfterHeadEmdash = termAfterHeadDelta;
        if (termAfterHeadEmdash.tag === 'ObjTerm') {
            const resolvedCat = whnf(termAfterHeadEmdash.cat, ctx, stackDepth + 1);
            if (getTermRef(resolvedCat).tag === 'MkCat_') {
                termAfterHeadEmdash = (getTermRef(resolvedCat) as Term & {tag: 'MkCat_'}).objRepresentation;
            }
        } else if (termAfterHeadEmdash.tag === 'HomTerm') {
            const resolvedCat = whnf(termAfterHeadEmdash.cat, ctx, stackDepth + 1);
            if (getTermRef(resolvedCat).tag === 'MkCat_') {
                const mkCatTerm = getTermRef(resolvedCat) as Term & {tag: 'MkCat_'};
                termAfterHeadEmdash = App(App(mkCatTerm.homRepresentation, termAfterHeadEmdash.dom), termAfterHeadEmdash.cod);
            }
        } else if (termAfterHeadEmdash.tag === 'ComposeMorph') {
            const comp = termAfterHeadEmdash;
            if (comp.cat_IMPLICIT) {
                const resolvedCat = whnf(comp.cat_IMPLICIT, ctx, stackDepth + 1);
                if (getTermRef(resolvedCat).tag === 'MkCat_') {
                    const mkCatTerm = getTermRef(resolvedCat) as Term & {tag: 'MkCat_'};
                    if (comp.objX_IMPLICIT && comp.objY_IMPLICIT && comp.objZ_IMPLICIT) { 
                         const objX_val = whnf(comp.objX_IMPLICIT, ctx, stackDepth+1);
                         const objY_val = whnf(comp.objY_IMPLICIT, ctx, stackDepth+1);
                         const objZ_val = whnf(comp.objZ_IMPLICIT, ctx, stackDepth+1);
                         const g_val = whnf(comp.g, ctx, stackDepth+1);
                         const f_val = whnf(comp.f, ctx, stackDepth+1);
                         termAfterHeadEmdash = App(App(App(App(App(mkCatTerm.composeImplementation, objX_val), objY_val), objZ_val), g_val), f_val);
                    }
                }
            }
        }
        if (termAfterHeadEmdash !== termAfterHeadDelta) {
            current = termAfterHeadEmdash; changedInThisHeadPass = true;
            continue; // Restart head reduction loop
        }
        
        // User Rewrite Rules
        const termBeforeHeadUserRules = current;
        const headIsConstant = isEmdashConstantSymbolTag(current.tag) || 
                               (current.tag === 'Var' && globalDefs.get(current.name)?.isConstantSymbol);
        if (!headIsConstant) {
            for (const rule of userRewriteRules) {
                const subst = matchPattern(rule.lhs, termBeforeHeadUserRules, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    const rhsApplied = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                    if (rhsApplied !== termBeforeHeadUserRules) { current = rhsApplied; changedInThisHeadPass = true; }
                    if (changedInThisHeadPass) continue; // Restart head reduction loop
                }
            }
        }
        
        current = getTermRef(current);
        if (!changedInThisHeadPass && current === termAtStartOfHeadPass) break; // Head is stable
        if (i === MAX_RECURSION_DEPTH -1 && (changedInThisHeadPass || current !== termAtStartOfHeadPass)) {
            // console.warn(`Normalize (head) reached max iterations: ${printTerm(term)} -> ${printTerm(current)}`);
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
            // If ComposeMorph's head reduction resulted in Apps (from C_impl), it will be an App tag.
            // Otherwise, it's still a ComposeMorph tag, normalize its arguments.
            if ((current as Term).tag === 'App') return normalize(current, ctx, stackDepth + 1); // Should have been handled by the loop if it became App(Lam...)
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
            const newLam = Lam(currentLam.paramName, normLamParamType,
                (v_arg: Term) => {
                    const paramTypeForBodyCtx = normLamParamType || 
                        (currentLam._isAnnotated && currentLam.paramType ? getTermRef(currentLam.paramType) : Hole());
                    let bodyCtx = ctx;
                    if (v_arg.tag === 'Var') { bodyCtx = extendCtx(ctx, v_arg.name, paramTypeForBodyCtx); }
                    return normalize(currentLam.body(v_arg), bodyCtx, stackDepth + 1);
                });
            newLam._isAnnotated = currentLam._isAnnotated;
            return newLam;
        }
        case 'App': // This case is after head-reduction loop.
            const normFunc = normalize(current.func, ctx, stackDepth + 1);
            const normArg = normalize(current.arg, ctx, stackDepth + 1);
            const finalNormFunc = getTermRef(normFunc); 
            if (finalNormFunc.tag === 'Lam') { // Final beta reduction check
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
        case 'Type': case 'CatTerm': return rt2.tag === rt1.tag;
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
            
            const comp_objX1_eq = rt1.objX_IMPLICIT ? getTermRef(rt1.objX_IMPLICIT) : Hole('_');
            const comp_objX2_eq = comp2.objX_IMPLICIT ? getTermRef(comp2.objX_IMPLICIT) : Hole('_');
            if ((comp_objX1_eq.tag !== 'Hole' || comp_objX1_eq.id !== '_') && (comp_objX2_eq.tag !== 'Hole' || comp_objX2_eq.id !== '_') && !areEqual(comp_objX1_eq, comp_objX2_eq, ctx, depth+1)) return false;

            const comp_objY1_eq = rt1.objY_IMPLICIT ? getTermRef(rt1.objY_IMPLICIT) : Hole('_');
            const comp_objY2_eq = comp2.objY_IMPLICIT ? getTermRef(comp2.objY_IMPLICIT) : Hole('_');
            if ((comp_objY1_eq.tag !== 'Hole' || comp_objY1_eq.id !== '_') && (comp_objY2_eq.tag !== 'Hole' || comp_objY2_eq.id !== '_') && !areEqual(comp_objY1_eq, comp_objY2_eq, ctx, depth+1)) return false;

            const comp_objZ1_eq = rt1.objZ_IMPLICIT ? getTermRef(rt1.objZ_IMPLICIT) : Hole('_');
            const comp_objZ2_eq = comp2.objZ_IMPLICIT ? getTermRef(comp2.objZ_IMPLICIT) : Hole('_');
            if ((comp_objZ1_eq.tag !== 'Hole' || comp_objZ1_eq.id !== '_') && (comp_objZ2_eq.tag !== 'Hole' || comp_objZ2_eq.id !== '_') && !areEqual(comp_objZ1_eq, comp_objZ2_eq, ctx, depth+1)) return false;

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
        if (!t1_arg || !t2_arg) { 
            if ((t1_arg && t1_arg.tag !== 'Hole') || (t2_arg && t2_arg.tag !== 'Hole')) return UnifyResult.Failed;
            if(t1_arg !== t2_arg) return UnifyResult.Failed; 
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
    
    if (madeProgress) return UnifyResult.Progress; 
    
    if (allSubSolved) {
        if (areEqual(parentRt1, parentRt2, ctx, depth + 1)) return UnifyResult.Solved;
        return UnifyResult.Progress; 
    }
    
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

    if (isEmdashUnificationInjectiveStructurally(rt1.tag)) { // Renamed for clarity
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
            default: // Should not be reached if tag list is correct
                return tryUnificationRules(rt1, rt2, ctx, depth + 1);
        }
        const argStatus = unifyArgs(args1, args2, ctx, depth, rt1, rt2);
        if (argStatus === UnifyResult.Failed) return UnifyResult.Failed; 
        return argStatus; 
    }

    // Non-injective cases or fall-through
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
            // ComposeMorph is not unification-injective for g and f.
            // Its equality relies on reductions or specific unif rules.
            return tryUnificationRules(rt1, rt2, ctx, depth + 1);
        default: 
            // This includes ObjTerm, HomTerm, MkCat_ if not caught by isEmdashUnificationInjectiveTag (which they are)
            // Or any other future same-tag terms.
            return tryUnificationRules(rt1, rt2, ctx, depth + 1);
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
            break;
        case 'Pi':
            collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            break;
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
    collectPatternVars(rule.lhsPattern1, rule.patternVars, lhsVars, new Set<Term>());
    collectPatternVars(rule.lhsPattern2, rule.patternVars, lhsVars, new Set<Term>());

    const finalSubst = new Map(subst); 

    for (const pVarDecl of rule.patternVars) {
        const pVarName = pVarDecl.name;
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
            if (!finalSubst.has(pVarName)) {
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
        let subst1 = matchPattern(rule.lhsPattern1, t1, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t2, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) {
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }

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

function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("solveConstraints stack depth exceeded");
    let changedInOuterLoop = true;
    let iterations = 0;
    // Increased maxIterations slightly more, constraint solving can be tricky with new rules
    const maxIterations = (constraints.length + userUnificationRules.length + 30) * 40 + 150; 

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
                    // Even if unify says Solved (e.g. hole assignment), we don't remove the constraint here.
                    // We let the areEqual check at the start of the next iteration (or this one if it loops) remove it.
                    // This ensures that the equality holds after all effects of the unification are propagated.
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
            const catHoleOrTerm = current.cat_IMPLICIT!; 
            const objType = infer(ctx, current.obj, stackDepth + 1); 
            addConstraint(objType, ObjTerm(catHoleOrTerm), `Object ${printTerm(current.obj)} of id must be in cat ${printTerm(catHoleOrTerm)}`);
            return HomTerm(catHoleOrTerm, current.obj, current.obj);
        }
        case 'ComposeMorph': {
            const catHoleOrTerm = current.cat_IMPLICIT!;
            const XHoleOrTerm = current.objX_IMPLICIT!;
            const YHoleOrTerm = current.objY_IMPLICIT!;
            const ZHoleOrTerm = current.objZ_IMPLICIT!;

            const type_f = infer(ctx, current.f, stackDepth + 1);
            const type_g = infer(ctx, current.g, stackDepth + 1);

            addConstraint(type_f, HomTerm(catHoleOrTerm, XHoleOrTerm, YHoleOrTerm), `Arg f of Compose`);
            addConstraint(type_g, HomTerm(catHoleOrTerm, YHoleOrTerm, ZHoleOrTerm), `Arg g of Compose`);
            
            return HomTerm(catHoleOrTerm, XHoleOrTerm, ZHoleOrTerm);
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
    
    if (current.tag === 'Hole') {
        if (!current.elaboratedType) {
             current.elaboratedType = normExpectedType; 
        }
        const inferredHoleType = infer(ctx, current, stackDepth + 1); 
        addConstraint(inferredHoleType, normExpectedType, `Hole ${current.id} checked against ${printTerm(normExpectedType)}`);
        return;
    }

    // Default: infer type of `current` and add constraint `inferred === expected`.
    // The infer function for Emdash terms (IdentityMorph, ComposeMorph) already sets up
    // constraints for their implicits based on their arguments.
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

    if (rtPattern.tag === 'Hole') { 
        if (rtPattern.id === '_') return subst; 
        if (currentTermStruct.tag === 'Hole') { 
            return rtPattern.id === currentTermStruct.id ? subst : null;
        } else { 
            return null;
        }
    } else if (currentTermStruct.tag === 'Hole') { 
        return null;
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
            const idPcat_IMPLICIT = idP.cat_IMPLICIT; 
            if (idPcat_IMPLICIT) { 
                const isPatWildcard = (idPcat_IMPLICIT.tag === 'Hole' && idPcat_IMPLICIT.id === '_') || (idPcat_IMPLICIT.tag === 'Var' && isPatternVarName(idPcat_IMPLICIT.name, patternVarDecls) && idPcat_IMPLICIT.name === '_');
                if (!idT.cat_IMPLICIT && !isPatWildcard) return null;
                if (idT.cat_IMPLICIT) { 
                     s = matchPattern(idPcat_IMPLICIT, idT.cat_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1);
                     if(!s) return null;
                } else if (!isPatWildcard) {
                    return null; 
                }
            } 
            return matchPattern(idP.obj, idT.obj, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'ComposeMorph': {
            const compP = rtPattern as Term & {tag:'ComposeMorph'};
            const compT = currentTermStruct as Term & {tag:'ComposeMorph'};
            let s = subst;
            const matchOptImplicit = (patArg?: Term, termArg?: Term): Substitution | null => {
                if (patArg) {
                    const isPatWildcard = (patArg.tag === 'Hole' && patArg.id === '_') || (patArg.tag === 'Var' && isPatternVarName(patArg.name, patternVarDecls) && patArg.name === '_');
                    if (!termArg && !isPatWildcard) return null;
                    if (termArg) {
                        const res = matchPattern(patArg, termArg, ctx, patternVarDecls, s, stackDepth + 1);
                        if (!res) return null;
                        s = res;
                    } else if (!isPatWildcard) {
                        return null;
                    }
                } 
                return s;
            };

            s = matchOptImplicit(compP.cat_IMPLICIT, compT.cat_IMPLICIT); if (!s) return null;
            s = matchOptImplicit(compP.objX_IMPLICIT, compT.objX_IMPLICIT); if (!s) return null;
            s = matchOptImplicit(compP.objY_IMPLICIT, compT.objY_IMPLICIT); if (!s) return null;
            s = matchOptImplicit(compP.objZ_IMPLICIT, compT.objZ_IMPLICIT); if (!s) return null;
            
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
            const newLam = Lam(lam.paramName, lamParamType, 
                (v_arg: Term) => applySubst(lam.body(v_arg), subst, patternVarDecls));
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

console.log("--- MyLambdaPi with Emdash Phase 1: Core Categories (Attempt 5) ---");

function setupPhase1GlobalsAndRules() {
    defineGlobal("NatType", Type(), undefined, true); 
    defineGlobal("BoolType", Type(), undefined, true);

    const pvarCat = { name: "CAT_pv", type: CatTerm() };
    const pvarX_obj = { name: "X_obj_pv", type: ObjTerm(Var("CAT_pv")) }; 
    const pvarY_obj = { name: "Y_obj_pv", type: ObjTerm(Var("CAT_pv")) }; 
    const pvarZ_obj = { name: "Z_obj_pv", type: ObjTerm(Var("CAT_pv")) };

    const pvarG_for_g_id = { name: "g_param_gid", type: HomTerm(Var("CAT_pv"), Var("Y_obj_pv"), Var("X_obj_pv")) }; // g: Y -> X
    addRewriteRule({
        name: "comp_g_idX", 
        patternVars: [pvarCat, pvarX_obj, pvarY_obj, pvarG_for_g_id],
        // ComposeMorph(g, id_X, cat, cod(g), dom(g)=X, dom(id)=X)
        lhs: ComposeMorph(Var("g_param_gid"), IdentityMorph(Var("X_obj_pv"), Var("CAT_pv")), 
                         Var("CAT_pv"), Var("Y_obj_pv"), Var("X_obj_pv"), Var("X_obj_pv")),
        rhs: Var("g_param_gid")
    });
    
    const pvarF_for_id_f = { name: "f_param_idf", type: HomTerm(Var("CAT_pv"), Var("X_obj_pv"), Var("Y_obj_pv")) }; // f: X -> Y
    addRewriteRule({
        name: "comp_idY_f",
        patternVars: [pvarCat, pvarX_obj, pvarY_obj, pvarF_for_id_f], 
        // ComposeMorph(id_Y, f, cat, cod(id)=Y, dom(id)=Y, dom(f)=X )
        lhs: ComposeMorph(IdentityMorph(Var("Y_obj_pv"), Var("CAT_pv")), Var("f_param_idf"),
                         Var("CAT_pv"), Var("Y_obj_pv"), Var("Y_obj_pv"), Var("X_obj_pv")),
        rhs: Var("f_param_idf")
    });
}


function runPhase1Tests() {
    const baseCtx = emptyCtx;
    const NatObjRepr = Var("NatType"); 

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
    
    testTerm = ObjTerm(someCatHole);
    elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.2 failed: Obj ?MyCat is not Type");
    
    const objXHole = Hole("?X"); 
    const objYHole = Hole("?Y");
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
    const H_repr_Nat = Lam("X", NatObjRepr, _X => Lam("Y", NatObjRepr, _Y => Type())); 
    const C_impl_Nat_dummy = Lam("Xobj", NatObjRepr, Xobj_term => 
                              Lam("Yobj", NatObjRepr, Yobj_term => 
                              Lam("Zobj", NatObjRepr, Zobj_term => 
                              Lam("gmorph", App(App(H_repr_Nat,Yobj_term),Zobj_term), _gmorph_term => 
                              Lam("fmorph", App(App(H_repr_Nat,Xobj_term),Yobj_term),_fmorph_term => 
                              Hole("comp_res_dummy"))))));
    
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
    defineGlobal("MyNatCat3_Global", CatTerm(), MyNatCat3_val, false); 

    defineGlobal("x_obj_val_t3", ObjTerm(Var("MyNatCat3_Global"))); 
    const anObjX_term = Var("x_obj_val_t3"); 

    const id_x = IdentityMorph(anObjX_term); 
    const expected_id_x_type = HomTerm(Var("MyNatCat3_Global"), anObjX_term, anObjX_term);
    elabRes = elaborate(id_x, expected_id_x_type, baseCtx);

    console.log(`Term id_x: ${printTerm(elabRes.term)}`);
    console.log(`Type id_x: ${printTerm(elabRes.type)}`);
    
    const idTermSolved = getTermRef(elabRes.term) as Term & {tag:"IdentityMorph"};
    if (!idTermSolved.cat_IMPLICIT) throw new Error("Test 3.1 failed: id_x cat_IMPLICIT not filled.");
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
    defineGlobal("C4_Global", CatTerm(), undefined, true); 

    defineGlobal("obj_x_val_t4", NatObjRepr); 
    defineGlobal("obj_y_val_t4", NatObjRepr); 
    defineGlobal("obj_z_val_t4", NatObjRepr);
    const x_term = Var("obj_x_val_t4"); 
    const y_term = Var("obj_y_val_t4"); 
    const z_term = Var("obj_z_val_t4");

    const f_morph_hole = Hole("?f_xy"); 
    const g_morph_hole = Hole("?g_yz"); 

    const y_hole = Hole("?y_hole"); 
    
    const comp_gf = ComposeMorph(g_morph_hole, f_morph_hole,Var("C4_Global"), undefined, y_hole, undefined); 
    const expectedCompType = HomTerm(Var("C4_Global"), x_term, z_term);
    elabRes = elaborate(comp_gf, expectedCompType, baseCtx);

    console.log(`Term comp_gf: ${printTerm(elabRes.term)}`);
    console.log(`Type comp_gf: ${printTerm(elabRes.type)}`); 
    if(!areEqual(elabRes.type, expectedCompType, baseCtx)) throw new Error(`Test 4.0 Failed: comp_gf type not as expected. Got ${printTerm(elabRes.type)}, Expected ${printTerm(expectedCompType)}`);
    
    const compTermSolved = getTermRef(elabRes.term) as Term & {tag:"ComposeMorph"};
    if (!compTermSolved.cat_IMPLICIT || !compTermSolved.objX_IMPLICIT  || !compTermSolved.objZ_IMPLICIT) {
        throw new Error("Test 4.1 failed: ComposeMorph implicits not filled.");
    }
    if(!areEqual(getTermRef(compTermSolved.cat_IMPLICIT), Var("C4_Global"), baseCtx)) throw new Error("Test 4.1 Failed: comp.cat not C4_Global");
    if(!areEqual(getTermRef(compTermSolved.objX_IMPLICIT), x_term, baseCtx)) throw new Error("Test 4.1 Failed: comp.X not obj_x_val_t4");
    if(!areEqual(getTermRef(compTermSolved.objY_IMPLICIT), y_hole, baseCtx)) throw new Error("Test 4.1 Failed: comp.Y not y_hole");
    if(!areEqual(getTermRef(compTermSolved.objZ_IMPLICIT), z_term, baseCtx)) throw new Error("Test 4.1 Failed: comp.Z not obj_z_val_t4");
        
    const f_type = (f_morph_hole as Term & {tag:"Hole"}).elaboratedType;
    const g_type = (g_morph_hole as Term & {tag:"Hole"}).elaboratedType;
    if (!f_type || !g_type) throw new Error("Test 4.1: f or g did not get elaborated types.");

    const expected_f_type = HomTerm(Var("C4_Global"), x_term, y_hole);
    const expected_g_type = HomTerm(Var("C4_Global"), y_hole, z_term);

    if (!areEqual(getTermRef(f_type), expected_f_type, baseCtx)) throw new Error(`Test 4.1: ?f_xy type mismatch. Got ${printTerm(getTermRef(f_type))}, expected ${printTerm(expected_f_type)}`);
    if (!areEqual(getTermRef(g_type), expected_g_type, baseCtx)) throw new Error(`Test 4.1: ?g_yz type mismatch. Got ${printTerm(getTermRef(g_type))}, expected ${printTerm(expected_g_type)}`);
    
    console.log("Test 4 Passed.");

    console.log("\n--- Test 5: Rewrite rule comp (g (id X)) ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules(); 
    const C5_val = MkCat_(NatObjRepr, H_repr_Nat, C_impl_Nat_dummy);
    defineGlobal("C5_cat_global", CatTerm(), undefined, true);
    
    defineGlobal("x5_val_t5", ObjTerm(Var("C5_cat_global"))); 
    defineGlobal("y5_val_t5", ObjTerm(Var("C5_cat_global")));
    const X5_term = Var("x5_val_t5"); 
    const Y5_term = Var("y5_val_t5");
    
    // For rule comp_g_idX: g: Hom C Y X.
    // Our g_param for the rule is typed Hom CAT Y X.
    // So, concrete_g should be Hom C5_cat_global Y5_term X5_term
    defineGlobal("concrete_g_yx_val", HomTerm(Var("C5_cat_global"), Y5_term, X5_term)); 
    const concrete_g_yx_term = Var("concrete_g_yx_val");

    const id_X5_term = IdentityMorph(X5_term, Var("C5_cat_global")); 
    // Test: concrete_g_yx_term o id_X5_term
    // ComposeMorph(g, f, cat, cod(g), dom(g)=cod(f), dom(f))
    // g = concrete_g_yx_term (Hom C5 Y5 X5)
    // f = id_X5_term        (Hom C5 X5 X5)
    // cat = C5_cat_global
    // dom(f) = X5_term
    // cod(f)/dom(g) = X5_term
    // cod(g) = Y5_term -- This was the corrected understanding for the implicit objZ of ComposeMorph
    const test_comp_g_id_term = ComposeMorph(concrete_g_yx_term, id_X5_term, 
                                                Var("C5_cat_global"), X5_term, X5_term, Y5_term);
                                                // objX=dom(f), objY=cod(f)=dom(g), objZ=cod(g)
                                                // dom(id_X5_term) = X5_term (correct for objX)
                                                // cod(id_X5_term) = X5_term (correct for objY)
                                                // dom(concrete_g_yx_term) = Y5_term. This should match objY.
                                                // My test_comp_g_id_term has objY = X5_term.
                                                // This means concrete_g_yx_term should be Hom C5 X5 Y5 for g o id_X to be typed with this configuration.
                                                // Let's make g : Hom C5 X5 Y5 as in the previous test.
    defineGlobal("concrete_g_xy_val_t5", HomTerm(Var("C5_cat_global"), X5_term, Y5_term));
    const concrete_g_xy_term_t5 = Var("concrete_g_xy_val_t5");
    const test_comp_concrete_g_id_corrected = ComposeMorph(concrete_g_xy_term_t5, id_X5_term, 
                                                Var("C5_cat_global"), X5_term, X5_term, Y5_term);

    elabRes = elaborate(test_comp_concrete_g_id_corrected, undefined, baseCtx);
    console.log(`Term (g o id): ${printTerm(elabRes.term)}`);
    console.log(`Type (g o id): ${printTerm(elabRes.type)}`);

    // Expected term is concrete_g_xy_term_t5
    // Expected type is HomTerm(Var("C5_cat_global"), X5_term, Y5_term)
    if (!areEqual(elabRes.term, concrete_g_xy_term_t5, baseCtx)) {
        throw new Error(`Test 5 failed: g o id did not reduce to g. Got ${printTerm(elabRes.term)}, expected ${printTerm(concrete_g_xy_term_t5)}`);
    }
    const expectedTypeT5 = HomTerm(Var("C5_cat_global"), X5_term, Y5_term);
    if (!areEqual(elabRes.type, expectedTypeT5, baseCtx)) {
        throw new Error(`Test 5 type failed. Got ${printTerm(elabRes.type)}, expected ${printTerm(expectedTypeT5)}`);
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