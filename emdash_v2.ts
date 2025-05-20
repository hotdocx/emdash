// --- MyLambdaPi with Emdash Phase 1: Core Categories (Attempt 7 - Applying Revisions) ---

export let nextVarId = 0;
export const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarId++}`;

export let nextHoleId = 0;
export const freshHoleName = (): string => `?h${nextHoleId++}`;

// --- Term Definition ---
export type BaseTerm =
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

export type Term = BaseTerm;
export type PatternVarDecl = { name: string, type: Term };

export const Type = (): Term => ({ tag: 'Type' });
export const Var = (name: string): Term & { tag: 'Var' } => ({ tag: 'Var', name });
export const Lam = (paramName: string, paramTypeOrBody: Term | ((v: Term) => Term), bodyOrNothing?: (v: Term) => Term): Term & { tag: 'Lam' } => {
    if (typeof paramTypeOrBody === 'function' && bodyOrNothing === undefined) {
        return { tag: 'Lam', paramName, paramType: undefined, body: paramTypeOrBody, _isAnnotated: false };
    } else if (bodyOrNothing && typeof bodyOrNothing === 'function' && paramTypeOrBody) {
        return { tag: 'Lam', paramName, paramType: paramTypeOrBody as Term, body: bodyOrNothing, _isAnnotated: true };
    }
    throw new Error(`Invalid Lam arguments: ${paramName}, ${paramTypeOrBody}, ${bodyOrNothing}`);
}
export const App = (func: Term, arg: Term): Term => ({ tag: 'App', func, arg });
export const Pi = (paramName: string, paramType: Term, bodyType: (v: Term) => Term): Term =>
    ({ tag: 'Pi', paramName, paramType, bodyType });
export const Hole = (id?: string): Term & { tag: 'Hole' } => {
    const holeId = id || freshHoleName();
    return { tag: 'Hole', id: holeId, ref: undefined, elaboratedType: undefined };
};

export const CatTerm = (): Term & { tag: 'CatTerm' } => ({ tag: 'CatTerm' });
export const ObjTerm = (cat: Term): Term & { tag: 'ObjTerm' } => ({ tag: 'ObjTerm', cat });
export const HomTerm = (cat: Term, dom: Term, cod: Term): Term & { tag: 'HomTerm' } => ({ tag: 'HomTerm', cat, dom, cod });
export const MkCat_ = (objRepresentation: Term, homRepresentation: Term, composeImplementation: Term): Term & { tag: 'MkCat_' } =>
    ({ tag: 'MkCat_', objRepresentation, homRepresentation, composeImplementation });
export const IdentityMorph = (obj: Term, cat_IMPLICIT?: Term): Term & { tag: 'IdentityMorph' } =>
    ({ tag: 'IdentityMorph', obj, cat_IMPLICIT });
export const ComposeMorph = (g: Term, f: Term, cat_IMPLICIT?: Term, objX_IMPLICIT?: Term, objY_IMPLICIT?: Term, objZ_IMPLICIT?: Term): Term & { tag: 'ComposeMorph' } =>
    ({ tag: 'ComposeMorph', g, f, cat_IMPLICIT, objX_IMPLICIT, objY_IMPLICIT, objZ_IMPLICIT });

export type Binding = { name: string, type: Term };
export type Context = Binding[];
export const emptyCtx: Context = [];
export const extendCtx = (ctx: Context, name: string, type: Term): Context => [{ name, type }, ...ctx];
export const lookupCtx = (ctx: Context, name: string): Binding | undefined => ctx.find(b => b.name === name);

export interface GlobalDef {
    name: string;
    type: Term;
    value?: Term;
    isConstantSymbol?: boolean;
}
export let globalDefs: Map<string, GlobalDef> = new Map();

export function defineGlobal(name: string, type: Term, value?: Term, isConstantSymbol: boolean = false) {
    if (globalDefs.has(name)) console.warn(`Warning: Redefining global ${name}`);
    if (isConstantSymbol && value !== undefined) {
        throw new Error(`Constant symbol ${name} cannot have a definition/value.`);
    }
    globalDefs.set(name, { name, type, value, isConstantSymbol });
}

export interface RewriteRule { name: string; patternVars: PatternVarDecl[]; lhs: Term; rhs: Term; }
export let userRewriteRules: RewriteRule[] = [];
export function addRewriteRule(rule: RewriteRule) {
    userRewriteRules.push(rule);
}

export interface UnificationRule {
    name: string;
    patternVars: PatternVarDecl[];
    lhsPattern1: Term;
    lhsPattern2: Term;
    rhsNewConstraints: Array<{ t1: Term, t2: Term }>;
}
export let userUnificationRules: UnificationRule[] = [];
export function addUnificationRule(rule: UnificationRule) {
    userUnificationRules.push(rule);
}

export type Substitution = Map<string, Term>;
export interface Constraint { t1: Term; t2: Term; origin?: string; }
export let constraints: Constraint[] = [];

export function addConstraint(t1: Term, t2: Term, origin?: string) { constraints.push({ t1, t2, origin }); }
export function getTermRef(term: Term): Term {
    if (term.tag === 'Hole' && term.ref) return getTermRef(term.ref);
    return term;
}

export const MAX_WHNF_ITERATIONS = 1000; // Max iterations for whnf reduction loop
let whnfIterationCount = 0;

export const MAX_STACK_DEPTH = 200; // General recursion depth limit

export let DEBUG_VERBOSE = false;

// Metadata for Emdash symbols
// UPDATED: ObjTerm and HomTerm are NOT constant symbols for rewrite head blocking
export const EMDASH_CONSTANT_SYMBOLS_TAGS = new Set<string>(['CatTerm', 'MkCat_']);
export const EMDASH_UNIFICATION_INJECTIVE_TAGS = new Set<string>(['IdentityMorph', 'CatTerm', 'ObjTerm', 'HomTerm', 'MkCat_']);

export function isKernelConstantSymbolStructurally(term: Term): boolean {
    const t = getTermRef(term);
    if (EMDASH_CONSTANT_SYMBOLS_TAGS.has(t.tag)) return true;
    // Check for global Vars marked as isConstantSymbol
    if (t.tag === 'Var' && globalDefs.get(t.name)?.isConstantSymbol) return true;
    return false;
}

export function isEmdashUnificationInjectiveStructurally(tag: string): boolean {
    return EMDASH_UNIFICATION_INJECTIVE_TAGS.has(tag);
}

export function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    consoleLog(`[TRACE whnf (${stackDepth})] Enter: term = ${printTerm(term)}`);
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`WHNF stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    
    let current = term;

    for (let i = 0; i < MAX_WHNF_ITERATIONS; i++) {
        consoleLog(`[TRACE whnf (${stackDepth})] Iteration ${i}, current = ${printTerm(current)}`);
        let changedInThisPass = false;
        const termAtStartOfOuterPass = current; // For detecting overall progress in one whnf call if no specific rule restarts

        // 1. Resolve solved Holes (most fundamental step)
        const dereffedCurrent = getTermRef(current);
        if (dereffedCurrent !== current) {
            consoleLog(`[TRACE whnf (${stackDepth})] Hole dereferenced: ${printTerm(current)} -> ${printTerm(dereffedCurrent)}`);
            current = dereffedCurrent;
            changedInThisPass = true; 
        }
        
        const termBeforeInnerReductions = current;


        // 2. User-Defined Rewrite Rules
        consoleLog(`[TRACE whnf (${stackDepth})] Checking user rewrite rules for: ${printTerm(current)} (isKernelConstant: ${isKernelConstantSymbolStructurally(current)})`);
        if (!isKernelConstantSymbolStructurally(current)) {
            for (const rule of userRewriteRules) {
                consoleLog(`[TRACE whnf (${stackDepth})] Trying rule: ${rule.name} on ${printTerm(current)}`);
                const termBeforeThisRuleAttempt = current; // Save the term state before this specific rule match
                const subst = matchPattern(rule.lhs, termBeforeThisRuleAttempt, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    consoleLog(`[TRACE whnf (${stackDepth})] Rule ${rule.name} matched against ${printTerm(termBeforeThisRuleAttempt)}.`);
                    const rhsApplied = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                    consoleLog(`[TRACE whnf (${stackDepth})] RHS after subst for rule ${rule.name}: ${printTerm(rhsApplied)}.`);

                    // Check if the rule application resulted in a structural change.
                    if (areStructurallyEqualNoWhnf(rhsApplied, termBeforeThisRuleAttempt, ctx, stackDepth + 1)) {
                        consoleLog(`[TRACE whnf (${stackDepth})] Rule ${rule.name} result is structurally identical to matched term. No change by this specific rule. Matched: ${printTerm(termBeforeThisRuleAttempt)}, RHS: ${printTerm(rhsApplied)}.`);
                        // No change from this rule, so continue to the next rule in the userRewriteRules loop.
                    } else {
                        // Structurally different, this is progress from this rule.
                        consoleLog(`[TRACE whnf (${stackDepth})] Rule ${rule.name} resulted in structural change: ${printTerm(termBeforeThisRuleAttempt)} -> ${printTerm(rhsApplied)}.`);
                        current = rhsApplied; // Update the main 'current' term for whnf.
                        changedInThisPass = true;
                        break; // Rule applied and caused change, break from userRewriteRules loop.
                    }
                }
            }
            if (changedInThisPass) {
                consoleLog(`[TRACE whnf (${stackDepth})] A user rule caused structural change. Continuing whnf loop's next iteration. New current for whnf: ${printTerm(current)}`);
                continue; // Restart entire whnf loop from step 1 with the modified 'current'.
            }
        }

        // 3. Head-Specific Reductions (Standard Beta, Categorical Beta, Delta)
        const headSpecificReductionTerm = current; 
        let reducedInThisBlock = false;
        consoleLog(`[TRACE whnf (${stackDepth})] Checking head-specific reductions for: ${printTerm(current)} (tag: ${current.tag})`);

        switch (current.tag) {
            case 'App': { 
                const func = current.func;
                const func_whnf = whnf(func, ctx, stackDepth + 1); 
                const func_whnf_ref = getTermRef(func_whnf);
                consoleLog(`[TRACE whnf (${stackDepth})] App: func_whnf_ref = ${printTerm(func_whnf_ref)}`);

                if (func_whnf_ref.tag === 'Lam') {
                    consoleLog(`[TRACE whnf (${stackDepth})] App: Beta reducing with arg ${printTerm(current.arg)}`);
                    current = func_whnf_ref.body(current.arg); 
                    reducedInThisBlock = true;
                } else if (func_whnf !== func) { 
                    consoleLog(`[TRACE whnf (${stackDepth})] App: func part changed to ${printTerm(func_whnf)}, reconstructing App.`);
                    current = App(func_whnf, current.arg);
                    reducedInThisBlock = true; 
                }
                break;
            }
            case 'ObjTerm': { 
                const cat = current.cat;
                const cat_whnf = whnf(cat, ctx, stackDepth + 1);
                const cat_whnf_ref = getTermRef(cat_whnf);
                consoleLog(`[TRACE whnf (${stackDepth})] ObjTerm: cat_whnf_ref = ${printTerm(cat_whnf_ref)}`);

                if (cat_whnf_ref.tag === 'MkCat_') {
                    consoleLog(`[TRACE whnf (${stackDepth})] ObjTerm: Categorical Beta to ${printTerm(cat_whnf_ref.objRepresentation)}`);
                    current = cat_whnf_ref.objRepresentation; 
                    reducedInThisBlock = true;
                } else if (cat_whnf !== cat) {
                    consoleLog(`[TRACE whnf (${stackDepth})] ObjTerm: cat part changed to ${printTerm(cat_whnf)}, reconstructing ObjTerm.`);
                    current = ObjTerm(cat_whnf);
                    reducedInThisBlock = true;
                }
                break;
            }
            case 'HomTerm': { 
                const cat = current.cat;
                const cat_whnf = whnf(cat, ctx, stackDepth + 1);
                const cat_whnf_ref = getTermRef(cat_whnf);
                consoleLog(`[TRACE whnf (${stackDepth})] HomTerm: cat_whnf_ref = ${printTerm(cat_whnf_ref)}`);

                if (cat_whnf_ref.tag === 'MkCat_') {
                    const newTerm = App(App(cat_whnf_ref.homRepresentation, current.dom), current.cod);
                    consoleLog(`[TRACE whnf (${stackDepth})] HomTerm: Categorical Beta to ${printTerm(newTerm)}`);
                    current = newTerm;
                    reducedInThisBlock = true;
                } else if (cat_whnf !== cat) {
                    consoleLog(`[TRACE whnf (${stackDepth})] HomTerm: cat part changed to ${printTerm(cat_whnf)}, reconstructing HomTerm.`);
                    current = HomTerm(cat_whnf, current.dom, current.cod);
                    reducedInThisBlock = true;
                }
                break;
            }
            case 'ComposeMorph': { 
                consoleLog(`[TRACE whnf (${stackDepth})] ComposeMorph: cat_IMPLICIT = ${current.cat_IMPLICIT ? printTerm(current.cat_IMPLICIT) : 'undef'}`);
                if (current.cat_IMPLICIT && current.objX_IMPLICIT && current.objY_IMPLICIT && current.objZ_IMPLICIT) {
                    const cat = current.cat_IMPLICIT;
                    const cat_whnf = whnf(cat, ctx, stackDepth + 1);
                    const cat_whnf_ref = getTermRef(cat_whnf);
                    consoleLog(`[TRACE whnf (${stackDepth})] ComposeMorph: cat_whnf_ref = ${printTerm(cat_whnf_ref)}`);

                    if (cat_whnf_ref.tag === 'MkCat_') {
                        const newTerm = App(App(App(App(App(cat_whnf_ref.composeImplementation, current.objX_IMPLICIT), current.objY_IMPLICIT), current.objZ_IMPLICIT), current.g), current.f);
                        consoleLog(`[TRACE whnf (${stackDepth})] ComposeMorph: Categorical Beta to ${printTerm(newTerm)}`);
                        current = newTerm;
                        reducedInThisBlock = true;
                    } 
                }
                break;
            }
            case 'Var': { 
                const gdef = globalDefs.get(current.name);
                if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol) {
                    consoleLog(`[TRACE whnf (${stackDepth})] Var: Delta reducing ${current.name} to ${printTerm(gdef.value)}`);
                    current = gdef.value;
                    reducedInThisBlock = true;
                }
                break;
            }
        }
        
        if (reducedInThisBlock) {
             consoleLog(`[TRACE whnf (${stackDepth})] Head-specific reduction occurred, continuing to next iteration. New current = ${printTerm(current)}`);
             changedInThisPass = true;
             continue; 
        }

        consoleLog(`[TRACE whnf (${stackDepth})] Before final progress check: current = ${printTerm(current)}, termBeforeInnerReductions = ${printTerm(termBeforeInnerReductions)}, changedInThisPass = ${changedInThisPass}`);
        const currentAfterSubPartsReduced = getTermRef(current); 
        if (currentAfterSubPartsReduced !== termBeforeInnerReductions) { 
            consoleLog(`[TRACE whnf (${stackDepth})] Structural change in sub-parts detected: ${printTerm(termBeforeInnerReductions)} -> ${printTerm(currentAfterSubPartsReduced)}`);
            current = currentAfterSubPartsReduced; 
            changedInThisPass = true; 
        }
        
        if (!changedInThisPass) {
            consoleLog(`[TRACE whnf (${stackDepth})] No change in this pass, breaking loop. Current = ${printTerm(current)}`);
            break; 
        }
        
        consoleLog(`[TRACE whnf (${stackDepth})] End of iteration ${i}. Current = ${printTerm(current)}, termAtStartOfOuterPass = ${printTerm(termAtStartOfOuterPass)}, changedInThisPass = ${changedInThisPass}`);
        if (current === termAtStartOfOuterPass && !changedInThisPass && i > 0) { 
             consoleLog(`[TRACE whnf (${stackDepth})] Term stabilized, breaking loop.`);
             break;
        }
         if (i === MAX_WHNF_ITERATIONS - 1 ) {
             if(changedInThisPass || current !== termAtStartOfOuterPass) {
                console.warn(`[TRACE whnf (${stackDepth})] WHNF reached max iterations for: ${printTerm(term)} -> ${printTerm(current)}`);
             }
        }
    }
    consoleLog(`[TRACE whnf (${stackDepth})] Exit: returning ${printTerm(current)} for original ${printTerm(term)}`);
    return current;
}

export function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Normalize stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    
    const headReduced = whnf(term, ctx, stackDepth + 1);
    // Must use getTermRef here as whnf might return a hole that got solved during its sub-calls.
    const current = getTermRef(headReduced); 

    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': case 'CatTerm':
            return current; // Vars are returned as is; if they were delta-reducible, whnf would have done it.
        case 'ObjTerm':
            // If whnf turned ObjTerm(MkCat_...) into its representation, current would be that representation.
            // So, if it's still ObjTerm, its category is abstract or a hole.
            return ObjTerm(normalize(current.cat, ctx, stackDepth + 1));
        case 'HomTerm':
            return HomTerm(
                normalize(current.cat, ctx, stackDepth + 1),
                normalize(current.dom, ctx, stackDepth + 1),
                normalize(current.cod, ctx, stackDepth + 1)
            );
        case 'MkCat_': // Arguments of MkCat_ are types or term formers, normalize them.
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
             // If whnf turned it into Apps (due to MkCat_ cat unfolding), normalize that App structure.
            if (current.tag !== 'ComposeMorph') return normalize(current, ctx, stackDepth + 1);
            // Otherwise, it's an abstract composition, normalize its components.
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
            // Normalize paramType if it exists and is annotated
            const normLamParamType = (currentLam._isAnnotated && currentLam.paramType) 
                                     ? normalize(currentLam.paramType, ctx, stackDepth + 1) 
                                     : undefined; // If not annotated, paramType is for inference, not structural part of norm form yet

            const newLam = Lam(currentLam.paramName, normLamParamType, 
                (v_arg: Term) => {
                    // Use the potentially normalized param type for context if available, otherwise rely on original hole / type.
                    const paramTypeForBodyCtx = normLamParamType || 
                                                (currentLam.paramType ? getTermRef(currentLam.paramType) : Hole(freshHoleName()+"_norm_lam_body"));
                    let bodyCtx = ctx;
                    if (v_arg.tag === 'Var') { bodyCtx = extendCtx(ctx, v_arg.name, paramTypeForBodyCtx); }
                    return normalize(currentLam.body(v_arg), bodyCtx, stackDepth + 1);
                });
            (newLam as Term & {tag:'Lam'})._isAnnotated = currentLam._isAnnotated; // Preserve annotation status
            if(normLamParamType) (newLam as Term & {tag:'Lam'}).paramType = normLamParamType; // Ensure normalized type is set
            return newLam;
        }
        case 'App': // If whnf didn't beta-reduce it, normalize func and arg.
            const normFunc = normalize(current.func, ctx, stackDepth + 1);
            const normArg = normalize(current.arg, ctx, stackDepth + 1);
            const finalNormFunc = getTermRef(normFunc); // It might have normalized to a hole that got solved
            // Check for beta-reduction again after normalizing func and arg, as they might have changed
            if (finalNormFunc.tag === 'Lam') {
                return normalize(finalNormFunc.body(normArg), ctx, stackDepth + 1); // Re-normalize the result
            }
            return App(normFunc, normArg);
        case 'Pi': {
            const currentPi = current;
            const normPiParamType = normalize(currentPi.paramType, ctx, stackDepth + 1);
            return Pi(currentPi.paramName, normPiParamType, (v_arg: Term) => {
                let bodyTypeCtx = ctx;
                // Use the normalized parameter type for the context of the body type
                if (v_arg.tag === 'Var') { bodyTypeCtx = extendCtx(ctx, v_arg.name, normPiParamType); }
                return normalize(currentPi.bodyType(v_arg), bodyTypeCtx, stackDepth + 1);
            });
        }
    }
}

export function areEqual(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    consoleLog(`[TRACE areEqual (${depth})] Enter: t1 = ${printTerm(t1)}, t2 = ${printTerm(t2)}`);
    if (depth > MAX_STACK_DEPTH) throw new Error(`Equality check depth exceeded (areEqual depth: ${depth})`);
    const normT1 = whnf(t1, ctx, depth + 1);
    const normT2 = whnf(t2, ctx, depth + 1);
    const rt1 = getTermRef(normT1);
    const rt2 = getTermRef(normT2);
    consoleLog(`[TRACE areEqual (${depth})] normT1 = ${printTerm(normT1)}, normT2 = ${printTerm(normT2)} => rt1 = ${printTerm(rt1)}, rt2 = ${printTerm(rt2)}`);

    if (rt1.tag === 'Hole' && rt2.tag === 'Hole') {
        const result = rt1.id === rt2.id;
        consoleLog(`[TRACE areEqual (${depth})] Holes: ${rt1.id} === ${rt2.id} is ${result}`);
        return result;
    }
    if (rt1.tag === 'Hole' || rt2.tag === 'Hole') {
        consoleLog(`[TRACE areEqual (${depth})] One is hole, other is not. Returning false.`);
        return false; 
    }
    if (rt1.tag !== rt2.tag) {
        consoleLog(`[TRACE areEqual (${depth})] Tags differ: ${rt1.tag} vs ${rt2.tag}. Returning false.`);
        return false;
    }

    let result = false;
    switch (rt1.tag) {
        case 'Type': case 'CatTerm': 
            result = (rt2.tag === rt1.tag);
            consoleLog(`[TRACE areEqual (${depth})] Type/CatTerm: result = ${result}`);
            break;
        case 'Var': 
            result = rt1.name === (rt2 as Term & {tag:'Var'}).name;
            consoleLog(`[TRACE areEqual (${depth})] Var: ${rt1.name} === ${(rt2 as Term & {tag:'Var'}).name} is ${result}`);
            break;
        case 'App': {
            const app2 = rt2 as Term & {tag:'App'};
            consoleLog(`[TRACE areEqual (${depth})] App: comparing func and arg recursively.`);
            result = areEqual(rt1.func, app2.func, ctx, depth + 1) &&
                   areEqual(rt1.arg, app2.arg, ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] App: recursive result = ${result}`);
            break;
        }
        case 'Lam': {
            const lam2 = rt2 as Term & {tag:'Lam'};
            consoleLog(`[TRACE areEqual (${depth})] Lam: annotated1=${rt1._isAnnotated}, annotated2=${lam2._isAnnotated}`);
            if (rt1._isAnnotated !== lam2._isAnnotated) { result = false; break; }
            if (rt1._isAnnotated) { 
                if (!rt1.paramType || !lam2.paramType || !areEqual(rt1.paramType, lam2.paramType, ctx, depth + 1)) {
                    consoleLog(`[TRACE areEqual (${depth})] Lam: annotated param types not equal.`);
                    result = false; break;
                }
                consoleLog(`[TRACE areEqual (${depth})] Lam: annotated param types are equal.`);
            }
            const freshVName = freshVarName(rt1.paramName);
            const freshV = Var(freshVName);
            consoleLog(`[TRACE areEqual (${depth})] Lam: comparing bodies with fresh var ${freshVName}.`);
            result = areEqual(rt1.body(freshV), lam2.body(freshV), ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] Lam: bodies comparison result = ${result}`);
            break;
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            consoleLog(`[TRACE areEqual (${depth})] Pi: comparing param types.`);
            if (!areEqual(rt1.paramType, pi2.paramType, ctx, depth + 1)) {
                consoleLog(`[TRACE areEqual (${depth})] Pi: param types not equal.`);
                result = false; break;
            }
            consoleLog(`[TRACE areEqual (${depth})] Pi: param types equal. Comparing body types.`);
            const freshVName = freshVarName(rt1.paramName);
            const freshV = Var(freshVName);
            result = areEqual(rt1.bodyType(freshV), pi2.bodyType(freshV), ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] Pi: body types comparison result = ${result}`);
            break;
        }
        case 'ObjTerm':
            consoleLog(`[TRACE areEqual (${depth})] ObjTerm: comparing categories.`);
            result = areEqual(rt1.cat, (rt2 as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] ObjTerm: categories comparison result = ${result}`);
            break;
        case 'HomTerm':
            const hom2 = rt2 as Term & {tag:'HomTerm'};
            consoleLog(`[TRACE areEqual (${depth})] HomTerm: comparing cat, dom, cod.`);
            result = areEqual(rt1.cat, hom2.cat, ctx, depth + 1) &&
                   areEqual(rt1.dom, hom2.dom, ctx, depth + 1) &&
                   areEqual(rt1.cod, hom2.cod, ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] HomTerm: comparison result = ${result}`);
            break;
        case 'MkCat_':
            const mkcat2 = rt2 as Term & {tag:'MkCat_'};
            consoleLog(`[TRACE areEqual (${depth})] MkCat_: comparing obj, hom, compose impls.`);
            result = areEqual(rt1.objRepresentation, mkcat2.objRepresentation, ctx, depth + 1) &&
                   areEqual(rt1.homRepresentation, mkcat2.homRepresentation, ctx, depth + 1) &&
                   areEqual(rt1.composeImplementation, mkcat2.composeImplementation, ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] MkCat_: comparison result = ${result}`);
            break;
        case 'IdentityMorph':
            const id2 = rt2 as Term & {tag:'IdentityMorph'};
            consoleLog(`[TRACE areEqual (${depth})] IdentityMorph: comparing implicits and obj.`);
            const cat1_eq = rt1.cat_IMPLICIT ? getTermRef(rt1.cat_IMPLICIT) : undefined;
            const cat2_eq = id2.cat_IMPLICIT ? getTermRef(id2.cat_IMPLICIT) : undefined;
            let implicitsResult = true;
            if (cat1_eq && cat2_eq) {
                 if (!areEqual(cat1_eq, cat2_eq, ctx, depth + 1)) implicitsResult = false;
            } else if (cat1_eq !== cat2_eq) { 
                 implicitsResult = false;
            }
            if (!implicitsResult) { result = false; consoleLog(`[TRACE areEqual (${depth})] IdentityMorph: cat_IMPLICITs not equal.`); break; }
            consoleLog(`[TRACE areEqual (${depth})] IdentityMorph: cat_IMPLICITs equal or both absent. Comparing obj.`);
            result = areEqual(rt1.obj, id2.obj, ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] IdentityMorph: obj comparison result = ${result}`);
            break;
        case 'ComposeMorph': { 
            const comp2 = rt2 as Term & {tag:'ComposeMorph'};
            consoleLog(`[TRACE areEqual (${depth})] ComposeMorph: comparing implicits, g, and f.`);
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areEqual(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2; 
            };
            if (!implicitsMatch(rt1.cat_IMPLICIT, comp2.cat_IMPLICIT)) { result = false; console.log('[TRACE areEqual (${depth})] ComposeMorph: cat_IMPLICITs not equal.'); break; }
            if (!implicitsMatch(rt1.objX_IMPLICIT, comp2.objX_IMPLICIT)) { result = false; console.log('[TRACE areEqual (${depth})] ComposeMorph: objX_IMPLICITs not equal.'); break; }
            if (!implicitsMatch(rt1.objY_IMPLICIT, comp2.objY_IMPLICIT)) { result = false; console.log('[TRACE areEqual (${depth})] ComposeMorph: objY_IMPLICITs not equal.'); break; }
            if (!implicitsMatch(rt1.objZ_IMPLICIT, comp2.objZ_IMPLICIT)) { result = false; console.log('[TRACE areEqual (${depth})] ComposeMorph: objZ_IMPLICITs not equal.'); break; }
            consoleLog(`[TRACE areEqual (${depth})] ComposeMorph: All implicits match. Comparing g and f.`);

            result = areEqual(rt1.g, comp2.g, ctx, depth + 1) &&
                   areEqual(rt1.f, comp2.f, ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] ComposeMorph: g and f comparison result = ${result}`);
            break;
        }
    }
    consoleLog(`[TRACE areEqual (${depth})] Exit: returning ${result} for t1 = ${printTerm(t1)}, t2 = ${printTerm(t2)}`);
    return result;
}

export function termContainsHole(term: Term, holeId: string, visited: Set<string>, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH * 2) { // Increased depth for occurs check, can be deeper than other ops
        console.warn(`termContainsHole depth exceeded for hole ${holeId} in ${printTerm(term)}`);
        return true; // Fail safe: assume it contains if too deep
    }
    const current = getTermRef(term);

    switch (current.tag) {
        case 'Hole': return current.id === holeId;
        case 'Type': case 'Var': case 'CatTerm': return false;
        default: {
            // For HOAS terms, if we generate a string key, it might be different each time due to fresh var names.
            // For non-HOAS terms, visited set based on printTerm can be an optimization.
            // A more robust visited set for general terms would involve structural hashing or a Set<Term> if refs are stable.
            // Given HOAS, let's be careful with `printTerm` based visited set.
            // For now, let's remove it to ensure correctness for HOAS, accepting potential performance hit.
            // const termStrKey = printTerm(current); // This can be problematic with fresh names in HOAS.
            // if (visited.has(termStrKey)) return false;
            // visited.add(termStrKey);

            if (current.tag === 'App') {
                return termContainsHole(current.func, holeId, visited, depth + 1) ||
                       termContainsHole(current.arg, holeId, visited, depth + 1);
            } else if (current.tag === 'Lam') {
                // Check paramType if it exists
                if (current.paramType && termContainsHole(current.paramType, holeId, visited, depth + 1)) return true;
                // Check body by instantiating with a fresh variable
                const freshV = Var(freshVarName("_occ_check")); // Unique name for this check
                return termContainsHole(current.body(freshV), holeId, visited, depth + 1);
            } else if (current.tag === 'Pi') {
                if (termContainsHole(current.paramType, holeId, visited, depth + 1)) return true;
                const freshV = Var(freshVarName("_occ_check"));
                return termContainsHole(current.bodyType(freshV), holeId, visited, depth + 1);
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
            return false; // Should not be reached for defined tags
        }
    }
}

export enum UnifyResult { Solved, Failed, RewrittenByRule, Progress }

export function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
    const normTerm = getTermRef(term); // Dereference term before occurs check
    if (normTerm.tag === 'Hole') {
        if (hole.id === normTerm.id) return true; // Unifying hole with itself is success
        // Consistent ordering for hole unification to avoid chains like ?a := ?b, ?b := ?a
        if (hole.id < normTerm.id) (normTerm as Term & {tag:'Hole'}).ref = hole;
        else hole.ref = normTerm;
        return true;
    }
    // Pass a new Set for visited each time to avoid cross-contamination between different unifyHole calls in a unification problem
    if (termContainsHole(normTerm, hole.id, new Set(), depth + 1)) {
        // console.warn(`Occurs check failed: cannot unify ${hole.id} with ${printTerm(normTerm)}`);
        return false;
    }
    hole.ref = normTerm;
    return true;
}

export function unifyArgs(args1: (Term | undefined)[], args2: (Term | undefined)[], ctx: Context, depth: number, parentRt1: Term, parentRt2: Term): UnifyResult {
    if (args1.length !== args2.length) return UnifyResult.Failed;

    let madeProgress = false;
    let allSubSolved = true;
    for (let i = 0; i < args1.length; i++) {
        const t1_arg = args1[i];
        const t2_arg = args2[i];

        if (t1_arg === undefined && t2_arg === undefined) continue;
        if ((t1_arg === undefined && t2_arg && getTermRef(t2_arg).tag !== 'Hole') ||
            (t2_arg === undefined && t1_arg && getTermRef(t1_arg).tag !== 'Hole')) {
            return UnifyResult.Failed;
        }
        
        const arg1ToUnify = t1_arg === undefined ? Hole(freshHoleName() + "_undef_arg_lhs_" + i) : t1_arg;
        const arg2ToUnify = t2_arg === undefined ? Hole(freshHoleName() + "_undef_arg_rhs_" + i) : t2_arg;

        const argStatus = unify(arg1ToUnify, arg2ToUnify, ctx, depth + 1);

        if (argStatus === UnifyResult.Failed) return UnifyResult.Failed;
        if (argStatus === UnifyResult.RewrittenByRule || argStatus === UnifyResult.Progress) {
            madeProgress = true; // If any sub-unification makes progress or rewrites
        }
        if (argStatus !== UnifyResult.Solved) {
            allSubSolved = false; // If any sub-unification isn't fully Solved yet
        }
    }

    if (allSubSolved) {
        // If all args solved and no progress/rewrite, check if parent structures are now equal.
        // This is particularly important if hole fillings in args made parents equal.
        if(areEqual(parentRt1, parentRt2, ctx, depth +1)) return UnifyResult.Solved;
        // If args solved but parents still not equal (e.g. due to different Var names not involved in unification),
        // it's not Failed, but Progress, as the arguments are resolved.
        // The overall unification of parentRt1 and parentRt2 might fail later if these non-unifiable parts persist.
        return UnifyResult.Progress; 
    }
    
    if (madeProgress) return UnifyResult.Progress; // Some arg made progress but not all solved
    
    // If !allSubSolved and !madeProgress, means some args are stuck (not Failed, but not Solved/Progress/Rewritten)
    // This implies the overall unification is also stuck, so Progress.
    return UnifyResult.Progress;
}

export function unify(t1: Term, t2: Term, ctx: Context, depth = 0): UnifyResult {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Unification stack depth exceeded (Unify depth: ${depth}, ${printTerm(t1)} vs ${printTerm(t2)})`);
    
    const rt1_orig = getTermRef(t1);
    const rt2_orig = getTermRef(t2);

    // Optimization: if terms are physically identical and not holes, they are Solved.
    if (rt1_orig === rt2_orig && rt1_orig.tag !== 'Hole') return UnifyResult.Solved;

    // 1. Handle hole cases first.
    // A hole is unified with the whnf'd version of the other term.
    if (rt1_orig.tag === 'Hole') {
        if (unifyHole(rt1_orig, whnf(rt2_orig, ctx, depth + 1), ctx, depth + 1)) return UnifyResult.Solved;
        // If unifyHole fails (e.g. occurs check), try rules with original forms.
        return tryUnificationRules(rt1_orig, rt2_orig, ctx, depth + 1);
    }
    if (rt2_orig.tag === 'Hole') {
        if (unifyHole(rt2_orig, whnf(rt1_orig, ctx, depth + 1), ctx, depth + 1)) return UnifyResult.Solved;
        return tryUnificationRules(rt1_orig, rt2_orig, ctx, depth + 1);
    }

    // 2. Try structural unification for injective constructors *before* full whnf of parents.
    // Applicable if neither rt1_orig nor rt2_orig is a hole at this point.
    if (rt1_orig.tag === rt2_orig.tag && isEmdashUnificationInjectiveStructurally(rt1_orig.tag)) {
        let args1: (Term|undefined)[] = [];
        let args2: (Term|undefined)[] = [];
        switch (rt1_orig.tag) {
            case 'CatTerm': return UnifyResult.Solved;
            case 'ObjTerm':
                args1 = [rt1_orig.cat]; args2 = [(rt2_orig as Term & {tag:'ObjTerm'}).cat];
                break;
            case 'HomTerm':
                const hom1 = rt1_orig as Term & {tag:'HomTerm'}; const hom2 = rt2_orig as Term & {tag:'HomTerm'};
                args1 = [hom1.cat, hom1.dom, hom1.cod]; args2 = [hom2.cat, hom2.dom, hom2.cod];
                break;
            case 'MkCat_':
                const mk1 = rt1_orig as Term & {tag:'MkCat_'}; const mk2 = rt2_orig as Term & {tag:'MkCat_'};
                args1 = [mk1.objRepresentation, mk1.homRepresentation, mk1.composeImplementation];
                args2 = [mk2.objRepresentation, mk2.homRepresentation, mk2.composeImplementation];
                break;
            case 'IdentityMorph':
                const id1 = rt1_orig as Term & {tag:'IdentityMorph'}; const id2 = rt2_orig as Term & {tag:'IdentityMorph'};
                args1 = [id1.cat_IMPLICIT, id1.obj]; args2 = [id2.cat_IMPLICIT, id2.obj];
                break;
            // Default case for this switch should not be hit if tag is in EMDASH_UNIFICATION_INJECTIVE_TAGS
        }
        // Pass rt1_orig, rt2_orig as parent terms for the areEqual check within unifyArgs
        const argStatus = unifyArgs(args1, args2, ctx, depth, rt1_orig, rt2_orig);
        
        // If args unified successfully (Solved) or made Progress, return that result.
        // If args Failed, we fall through to the general whnf path below.
        if (argStatus === UnifyResult.Solved || argStatus === UnifyResult.Progress) {
            return argStatus;
        }
        // Fall-through if argStatus === UnifyResult.Failed
    }

    // 3. General case: whnf both terms and proceed with unification.
    const rt1_whnf = whnf(rt1_orig, ctx, depth + 1);
    const rt2_whnf = whnf(rt2_orig, ctx, depth + 1);
    
    // Re-check equality after whnf, as they might have become equal.
    if (rt1_whnf === rt2_whnf && rt1_whnf.tag !== 'Hole') return UnifyResult.Solved; // Physical equality of non-holes after whnf
    if (areEqual(rt1_whnf, rt2_whnf, ctx, depth + 1)) return UnifyResult.Solved;

    // Handle holes that might have been exposed by whnf (e.g., a variable defined as a hole).
    // getTermRef again after whnf.
    const rt1_final = getTermRef(rt1_whnf);
    const rt2_final = getTermRef(rt2_whnf);

    if (rt1_final.tag === 'Hole') {
        // rt2_final is already whnf'd here.
        if (unifyHole(rt1_final, rt2_final, ctx, depth + 1)) return UnifyResult.Solved;
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }
    if (rt2_final.tag === 'Hole') {
        if (unifyHole(rt2_final, rt1_final, ctx, depth + 1)) return UnifyResult.Solved;
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }

    // Tags differ after whnf, and neither is a hole. Try rules.
    if (rt1_final.tag !== rt2_final.tag) {
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }

    // Tags are the same (rt1_final.tag === rt2_final.tag), neither is a hole.
    // This is the path for:
    // a) Injective constructors whose arguments failed to unify in the pre-whnf path (step 2).
    // b) Non-injective constructors (e.g., App, Lam, Pi, ComposeMorph).
    // c) Simple terms like Type, Var.

    if (isEmdashUnificationInjectiveStructurally(rt1_final.tag)) {
        // This means the pre-whnf path (step 2) for this injective tag resulted in UnifyResult.Failed for its arguments.
        // We now retry unifying the arguments, but this time the arguments are from the whnf'd parent terms.
        let args1_w: (Term|undefined)[] = [];
        let args2_w: (Term|undefined)[] = [];
        switch (rt1_final.tag) {
            case 'CatTerm': return UnifyResult.Solved; // Already known tags are equal
            case 'ObjTerm':
                args1_w = [rt1_final.cat]; args2_w = [(rt2_final as Term & {tag:'ObjTerm'}).cat];
                break;
            case 'HomTerm':
                const hom1_w = rt1_final as Term & {tag:'HomTerm'}; const hom2_w = rt2_final as Term & {tag:'HomTerm'};
                args1_w = [hom1_w.cat, hom1_w.dom, hom1_w.cod]; args2_w = [hom2_w.cat, hom2_w.dom, hom2_w.cod];
                break;
            case 'MkCat_':
                const mk1_w = rt1_final as Term & {tag:'MkCat_'}; const mk2_w = rt2_final as Term & {tag:'MkCat_'};
                args1_w = [mk1_w.objRepresentation, mk1_w.homRepresentation, mk1_w.composeImplementation];
                args2_w = [mk2_w.objRepresentation, mk2_w.homRepresentation, mk2_w.composeImplementation];
                break;
            case 'IdentityMorph':
                const id1_w = rt1_final as Term & {tag:'IdentityMorph'}; const id2_w = rt2_final as Term & {tag:'IdentityMorph'};
                args1_w = [id1_w.cat_IMPLICIT, id1_w.obj]; args2_w = [id2_w.cat_IMPLICIT, id2_w.obj];
                break;
            default: // Should not be reached if tag is in EMDASH_UNIFICATION_INJECTIVE_TAGS
                 return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        }
        // Pass rt1_final, rt2_final as parents to unifyArgs
        const argStatus_w = unifyArgs(args1_w, args2_w, ctx, depth, rt1_final, rt2_final);
        if (argStatus_w === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        return argStatus_w; // Solved or Progress
    }

    // Non-injective cases or general structural unification for core terms (using whnf'd, non-hole terms)
    switch (rt1_final.tag) {
        case 'Type': return UnifyResult.Solved; // Tags are 'Type', so Solved.
        case 'Var': // Vars are equal if names are same. If not, they are distinct rigid terms.
            return rt1_final.name === (rt2_final as Term & {tag:'Var'}).name ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        case 'App': {
            const app2_final = rt2_final as Term & {tag:'App'};
            // Unify functions then arguments. If any fails, try rules for the App terms.
            const funcUnifyStatus = unify(rt1_final.func, app2_final.func, ctx, depth + 1);
            if (funcUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            const argUnifyStatus = unify(rt1_final.arg, app2_final.arg, ctx, depth + 1);
            if (argUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            if (funcUnifyStatus === UnifyResult.Solved && argUnifyStatus === UnifyResult.Solved) {
                if (areEqual(rt1_final, rt2_final, ctx, depth + 1)) return UnifyResult.Solved;
                // Sub-parts solved but term not overall equal yet (e.g. due to other constraints needed)
                // or they might become equal later. Try rules if not directly equal now.
                return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1); 
            }
            return UnifyResult.Progress; // If any sub-part made progress or was rewritten
        }
        case 'Lam': { 
            const lam2_final = rt2_final as Term & {tag:'Lam'};
            if (rt1_final._isAnnotated !== lam2_final._isAnnotated) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            
            let paramTypeStatus = UnifyResult.Solved;
            if (rt1_final._isAnnotated) { 
                if(!rt1_final.paramType || !lam2_final.paramType) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1); 
                paramTypeStatus = unify(rt1_final.paramType, lam2_final.paramType, ctx, depth + 1);
                if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }

            const freshV = Var(freshVarName(rt1_final.paramName));
            const CtxParamType = rt1_final._isAnnotated && rt1_final.paramType ? getTermRef(rt1_final.paramType) : Hole(freshHoleName() + "_unif_lam_ctx");
            const extendedCtx = extendCtx(ctx, freshV.name, CtxParamType);
            const bodyStatus = unify(rt1_final.body(freshV), lam2_final.body(freshV), extendedCtx, depth + 1);

            if(bodyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            if(paramTypeStatus === UnifyResult.Solved && bodyStatus === UnifyResult.Solved) {
                if(areEqual(rt1_final, rt2_final, ctx, depth+1)) return UnifyResult.Solved;
                 return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }
            return UnifyResult.Progress;
        }
        case 'Pi': { 
            const pi2_final = rt2_final as Term & {tag:'Pi'};
            const paramTypeStatus = unify(rt1_final.paramType, pi2_final.paramType, ctx, depth + 1);
            if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            const freshV = Var(freshVarName(rt1_final.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(rt1_final.paramType));
            const bodyTypeStatus = unify(rt1_final.bodyType(freshV), pi2_final.bodyType(freshV), extendedCtx, depth + 1);
            if(bodyTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            if(paramTypeStatus === UnifyResult.Solved && bodyTypeStatus === UnifyResult.Solved) {
                if(areEqual(rt1_final, rt2_final, ctx, depth+1)) return UnifyResult.Solved;
                return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }
            return UnifyResult.Progress;
        }
        case 'ComposeMorph': 
            const cm1_final = rt1_final; const cm2_final = rt2_final as Term & {tag: 'ComposeMorph'};
            let implicitsOk = true;
            const implicitsToUnify: [Term|undefined, Term|undefined][] = [
                [cm1_final.cat_IMPLICIT, cm2_final.cat_IMPLICIT],
                [cm1_final.objX_IMPLICIT, cm2_final.objX_IMPLICIT],
                [cm1_final.objY_IMPLICIT, cm2_final.objY_IMPLICIT],
                [cm1_final.objZ_IMPLICIT, cm2_final.objZ_IMPLICIT],
            ];
            let madeProgressOnImplicits = false;
            for(const [imp1, imp2] of implicitsToUnify) {
                const arg1ToUnify = imp1 === undefined ? Hole(freshHoleName() + "_undef_imp_lhs") : imp1;
                const arg2ToUnify = imp2 === undefined ? Hole(freshHoleName() + "_undef_imp_rhs") : imp2;
                const impStatus = unify(arg1ToUnify, arg2ToUnify, ctx, depth + 1);
                if (impStatus === UnifyResult.Failed) { implicitsOk = false; break; }
                if (impStatus !== UnifyResult.Solved) madeProgressOnImplicits = true;
            }
            if (!implicitsOk) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            const gStatus = unify(cm1_final.g, cm2_final.g, ctx, depth + 1);
            if (gStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const fStatus = unify(cm1_final.f, cm2_final.f, ctx, depth + 1);
            if (fStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            if (!madeProgressOnImplicits && gStatus === UnifyResult.Solved && fStatus === UnifyResult.Solved) {
                 if(areEqual(rt1_final, rt2_final, ctx, depth+1)) return UnifyResult.Solved;
                 return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }
            return UnifyResult.Progress; 

        default:
            console.warn(`Unify: Unhandled same-tag case during structural unification: ${rt1_final.tag}`);
            return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }
}

// --- Functions for Unification Rules ---
export function collectPatternVars(term: Term, patternVarDecls: PatternVarDecl[], collectedVars: Set<string>, visited: Set<Term> = new Set()): void {
    const current = getTermRef(term);
    if (visited.has(current) && current.tag !== 'Var' && current.tag !== 'Hole') return; 
    visited.add(current);

    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        collectedVars.add(current.name);
    } else if (current.tag === 'Hole' && isPatternVarName(current.id, patternVarDecls)) { // Pattern Holes can be variables too
        collectedVars.add(current.id);
    }

    switch (current.tag) {
        case 'App':
            collectPatternVars(current.func, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.arg, patternVarDecls, collectedVars, visited);
            break;
        case 'Lam':
            if (current.paramType) collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            // For HOAS Lam/Pi in patterns, we can't easily collect free pattern vars from the body function itself
            // without applying it. Assumed pattern variables are not bound *within* the pattern's HOAS body.
            // If a HOAS body is part of a pattern (e.g. rule LHS is `Lam("x", Var("T"), bodyFunc)`),
            // `bodyFunc` would be a JS function, not a term containing more pattern vars.
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
        // Other tags don't have sub-terms with pattern vars (Type, Var, Hole (non-pattern var), CatTerm)
    }
}

export function applyAndAddRuleConstraints(rule: UnificationRule, subst: Substitution, ctx: Context): void {
    const lhsVars = new Set<string>();
    collectPatternVars(rule.lhsPattern1, rule.patternVars, lhsVars, new Set<Term>());
    collectPatternVars(rule.lhsPattern2, rule.patternVars, lhsVars, new Set<Term>());

    const finalSubst = new Map(subst); // Copy initial substitution

    // Ensure all pattern variables used in RHS are either bound by LHS or explicitly made fresh holes
    for (const pVarDecl of rule.patternVars) {
        const pVarName = pVarDecl.name;
        if (pVarName === '_') continue; // Wildcard

        let usedInRhs = false;
        for(const {t1: rhs_t1, t2: rhs_t2} of rule.rhsNewConstraints) {
            const rhsConstraintVars = new Set<string>();
            collectPatternVars(rhs_t1, rule.patternVars, rhsConstraintVars, new Set<Term>());
            collectPatternVars(rhs_t2, rule.patternVars, rhsConstraintVars, new Set<Term>());
            if (rhsConstraintVars.has(pVarName)) {
                usedInRhs = true;
                break;
            }
        }
        // If a pVar is used in RHS, but not in LHS and not already in subst (e.g. from matching one side of rule)
        // then it must be a fresh variable introduced by the rule. Instantiate as a fresh hole.
        if (usedInRhs && !lhsVars.has(pVarName) && !finalSubst.has(pVarName)) {
             finalSubst.set(pVarName, Hole(freshHoleName() + "_unifRuleRHS_" + pVarName));
        }
    }

    for (const constrPair of rule.rhsNewConstraints) {
        const newT1 = applySubst(constrPair.t1, finalSubst, rule.patternVars);
        const newT2 = applySubst(constrPair.t2, finalSubst, rule.patternVars);
        addConstraint(newT1, newT2, `UnifRule ${rule.name}`);
    }
}

export function tryUnificationRules(t1: Term, t2: Term, ctx: Context, depth: number): UnifyResult {
    for (const rule of userUnificationRules) {
        // Attempt: rule.lhsPattern1 vs t1, rule.lhsPattern2 vs t2
        let subst1 = matchPattern(rule.lhsPattern1, t1, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t2, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) {
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }

        // Attempt: rule.lhsPattern1 vs t2, rule.lhsPattern2 vs t1 (commuted)
        subst1 = matchPattern(rule.lhsPattern1, t2, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t1, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) {
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }
    }
    return UnifyResult.Failed; // No rule applied
}
// --- End functions for Unification Rules ---

export function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("solveConstraints stack depth exceeded");
    let changedInOuterLoop = true;
    let iterations = 0;
    // Max iterations can be high for complex unifications with many rules/holes.
    const maxIterations = (constraints.length * constraints.length + userUnificationRules.length * 2 + 50) * 50 + 200;


    while (changedInOuterLoop && iterations < maxIterations) {
        changedInOuterLoop = false;
        iterations++;
        if(iterations > maxIterations / 2 && iterations % 100 === 0) {
            // console.warn(`solveConstraints reaching high iteration count: ${iterations}/${maxIterations}, constraints left: ${constraints.length}`);
        }


        let currentConstraintIdx = 0;
        while(currentConstraintIdx < constraints.length) {
            const constraint = constraints[currentConstraintIdx];
            const c_t1_current_ref = getTermRef(constraint.t1);
            const c_t2_current_ref = getTermRef(constraint.t2);

            // Optimization: if terms are already equal (after dereferencing), remove constraint.
            // areEqual calls whnf internally.
            if (areEqual(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1)) {
                constraints.splice(currentConstraintIdx, 1);
                changedInOuterLoop = true;
                // Don't increment currentConstraintIdx, as the list shifted. Restart inner loop scan.
                continue; 
            }

            try {
                const unifyResult = unify(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1);

                if (unifyResult === UnifyResult.Solved) {
                    changedInOuterLoop = true;
                    // If solved, the areEqual check at the start of the *next* outer loop iteration (or current if it continues)
                    // should remove it. Or, if a hole was assigned, getTermRef will reflect it.
                    // We still increment currentConstraintIdx to move to the next constraint in *this* pass.
                    currentConstraintIdx++;
                } else if (unifyResult === UnifyResult.RewrittenByRule) {
                    constraints.splice(currentConstraintIdx, 1); // Original constraint removed, new ones added by rule
                    changedInOuterLoop = true;
                    // Don't increment, list shifted, new constraints are at end. Restart scan of constraints.
                    // This ensures new constraints from rules are processed promptly.
                    // However, to avoid infinite loops if a rule doesn't simplify, consider carefully.
                    // For now, assume rules are reductive or add solvable constraints.
                } else if (unifyResult === UnifyResult.Progress) {
                    // Progress means some change happened (e.g. sub-hole solved, or sub-part made progress)
                    // but the top-level constraint isn't fully Solved yet.
                    changedInOuterLoop = true;
                    currentConstraintIdx++;
                } else { // UnifyResult.Failed
                    console.warn(`Unification failed permanently for: ${printTerm(c_t1_current_ref)} === ${printTerm(c_t2_current_ref)} (orig: ${constraint.origin || 'unknown'})`);
                    // console.warn(`Context at failure: ${ctx.map(b => `${b.name}:${printTerm(b.type)}`).join(', ')}`);
                    // console.warn(`Global defs: ${Array.from(globalDefs.keys()).join(', ')}`);
                    return false; // Permanent failure
                }
            } catch (e) {
                console.error(`Error during unification of ${printTerm(c_t1_current_ref)} and ${printTerm(c_t2_current_ref)} (origin: ${constraint.origin || 'unknown'}): ${(e as Error).message}`);
                console.error((e as Error).stack);
                return false;
            }
        }
    }

    if (iterations >= maxIterations && changedInOuterLoop && constraints.length > 0) {
        console.warn("Constraint solving reached max iterations and was still making changes. Constraints left: " + constraints.length);
        // constraints.forEach(c => console.warn(` - ${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))}`));
    }
    
    // Final check: all remaining constraints must be true
    for (const constraint of constraints) {
        if (!areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
            console.warn(`Final check failed for constraint: ${printTerm(getTermRef(constraint.t1))} === ${printTerm(getTermRef(constraint.t2))} (orig: ${constraint.origin || 'unknown'})`);
            return false;
        }
    }
    return constraints.length === 0;
}

// ADDING NEW FUNCTION HERE
export function areStructurallyEqualNoWhnf(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Enter: t1 = ${printTerm(t1)}, t2 = ${printTerm(t2)}`);
    if (depth > MAX_STACK_DEPTH) throw new Error(`Structural Equality check depth exceeded (areStructurallyEqualNoWhnf depth: ${depth})`);
    // DO NOT CALL WHNF HERE
    const rt1 = getTermRef(t1);
    const rt2 = getTermRef(t2);
    consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] rt1 = ${printTerm(rt1)}, rt2 = ${printTerm(rt2)}`);

    if (rt1.tag === 'Hole' && rt2.tag === 'Hole') {
        const result = rt1.id === rt2.id;
        consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Holes: ${rt1.id} === ${rt2.id} is ${result}`);
        return result;
    }
    if (rt1.tag === 'Hole' || rt2.tag === 'Hole') {
        consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] One is hole, other is not. Returning false.`);
        return false; 
    }
    if (rt1.tag !== rt2.tag) {
        consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Tags differ: ${rt1.tag} vs ${rt2.tag}. Returning false.`);
        return false;
    }

    let result = false;
    switch (rt1.tag) {
        case 'Type': case 'CatTerm': 
            result = (rt2.tag === rt1.tag);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Type/CatTerm: result = ${result}`);
            break;
        case 'Var': 
            result = rt1.name === (rt2 as Term & {tag:'Var'}).name;
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Var: ${rt1.name} === ${(rt2 as Term & {tag:'Var'}).name} is ${result}`);
            break;
        case 'App': {
            const app2 = rt2 as Term & {tag:'App'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] App: comparing func and arg recursively.`);
            result = areStructurallyEqualNoWhnf(rt1.func, app2.func, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.arg, app2.arg, ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] App: recursive result = ${result}`);
            break;
        }
        case 'Lam': {
            const lam2 = rt2 as Term & {tag:'Lam'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: annotated1=${rt1._isAnnotated}, annotated2=${lam2._isAnnotated}`);
            if (rt1._isAnnotated !== lam2._isAnnotated) { result = false; break; }
            if (rt1._isAnnotated) { 
                if (!rt1.paramType || !lam2.paramType || !areStructurallyEqualNoWhnf(rt1.paramType, lam2.paramType, ctx, depth + 1)) {
                    consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: annotated param types not equal.`);
                    result = false; break;
                }
                consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: annotated param types are equal.`);
            }
            const freshVName = freshVarName(rt1.paramName);
            const freshV = Var(freshVName);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: comparing bodies with fresh var ${freshVName}.`);
            result = areStructurallyEqualNoWhnf(rt1.body(freshV), lam2.body(freshV), ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: bodies comparison result = ${result}`);
            break;
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Pi: comparing param types.`);
            if (!areStructurallyEqualNoWhnf(rt1.paramType, pi2.paramType, ctx, depth + 1)) {
                consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Pi: param types not equal.`);
                result = false; break;
            }
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Pi: param types equal. Comparing body types.`);
            const freshVName = freshVarName(rt1.paramName);
            const freshV = Var(freshVName);
            result = areStructurallyEqualNoWhnf(rt1.bodyType(freshV), pi2.bodyType(freshV), ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Pi: body types comparison result = ${result}`);
            break;
        }
        case 'ObjTerm':
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] ObjTerm: comparing categories.`);
            result = areStructurallyEqualNoWhnf(rt1.cat, (rt2 as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] ObjTerm: categories comparison result = ${result}`);
            break;
        case 'HomTerm':
            const hom2 = rt2 as Term & {tag:'HomTerm'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] HomTerm: comparing cat, dom, cod.`);
            result = areStructurallyEqualNoWhnf(rt1.cat, hom2.cat, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.dom, hom2.dom, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.cod, hom2.cod, ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] HomTerm: comparison result = ${result}`);
            break;
        case 'MkCat_':
            const mkcat2 = rt2 as Term & {tag:'MkCat_'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] MkCat_: comparing obj, hom, compose impls.`);
            result = areStructurallyEqualNoWhnf(rt1.objRepresentation, mkcat2.objRepresentation, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.homRepresentation, mkcat2.homRepresentation, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.composeImplementation, mkcat2.composeImplementation, ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] MkCat_: comparison result = ${result}`);
            break;
        case 'IdentityMorph':
            const id2 = rt2 as Term & {tag:'IdentityMorph'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] IdentityMorph: comparing implicits and obj.`);
            const cat1_eq = rt1.cat_IMPLICIT ? getTermRef(rt1.cat_IMPLICIT) : undefined;
            const cat2_eq = id2.cat_IMPLICIT ? getTermRef(id2.cat_IMPLICIT) : undefined;
            let implicitsResult = true;
            if (cat1_eq && cat2_eq) {
                 if (!areStructurallyEqualNoWhnf(cat1_eq, cat2_eq, ctx, depth + 1)) implicitsResult = false;
            } else if (cat1_eq !== cat2_eq) { 
                 implicitsResult = false;
            }
            if (!implicitsResult) { result = false; consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] IdentityMorph: cat_IMPLICITs not equal.`); break; }
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] IdentityMorph: cat_IMPLICITs equal or both absent. Comparing obj.`);
            result = areStructurallyEqualNoWhnf(rt1.obj, id2.obj, ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] IdentityMorph: obj comparison result = ${result}`);
            break;
        case 'ComposeMorph': {
            const comp2 = rt2 as Term & {tag:'ComposeMorph'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: comparing implicits, g, and f.`);
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areStructurallyEqualNoWhnf(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2; 
            };
            if (!implicitsMatch(rt1.cat_IMPLICIT, comp2.cat_IMPLICIT)) { result = false; console.log('[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: cat_IMPLICITs not equal.'); break; }
            if (!implicitsMatch(rt1.objX_IMPLICIT, comp2.objX_IMPLICIT)) { result = false; console.log('[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: objX_IMPLICITs not equal.'); break; }
            if (!implicitsMatch(rt1.objY_IMPLICIT, comp2.objY_IMPLICIT)) { result = false; console.log('[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: objY_IMPLICITs not equal.'); break; }
            if (!implicitsMatch(rt1.objZ_IMPLICIT, comp2.objZ_IMPLICIT)) { result = false; console.log('[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: objZ_IMPLICITs not equal.'); break; }
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: All implicits match. Comparing g and f.`);

            result = areStructurallyEqualNoWhnf(rt1.g, comp2.g, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.f, comp2.f, ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: g and f comparison result = ${result}`);
            break;
        }
    }
    consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Exit: returning ${result} for t1 = ${printTerm(t1)}, t2 = ${printTerm(t2)}`);
    return result;
}

export function ensureImplicitsAsHoles(term: Term): Term {
    // This function is called at the start of infer/check, before getTermRef on the input term.
    // It can mutate the term directly.
    if (term.tag === 'IdentityMorph') {
        if (term.cat_IMPLICIT === undefined) {
            // Try to make hole names more informative based on context if possible, e.g. obj name.
            let objHint = "obj";
            if (term.obj.tag === 'Var') objHint = term.obj.name;
            else if (term.obj.tag === 'Hole') objHint = term.obj.id.replace("?","");
            term.cat_IMPLICIT = Hole(freshHoleName() + "_cat_of_" + objHint);
        }
    }
    if (term.tag === 'ComposeMorph') {
        if (term.cat_IMPLICIT === undefined) term.cat_IMPLICIT = Hole(freshHoleName() + "_comp_cat");
        if (term.objX_IMPLICIT === undefined) term.objX_IMPLICIT = Hole(freshHoleName() + "_comp_X");
        if (term.objY_IMPLICIT === undefined) term.objY_IMPLICIT = Hole(freshHoleName() + "_comp_Y");
        if (term.objZ_IMPLICIT === undefined) term.objZ_IMPLICIT = Hole(freshHoleName() + "_comp_Z");
    }
    return term;
}

export function infer(ctx: Context, term: Term, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Infer stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);

    // Ensure implicits are holes *before* getTermRef, as getTermRef might return a solved hole's content.
    const termWithImplicits = ensureImplicitsAsHoles(term);
    const current = getTermRef(termWithImplicits);


    if (current.tag === 'Var') {
        const gdef = globalDefs.get(current.name);
        if (gdef) return gdef.type;
        const binding = lookupCtx(ctx, current.name);
        if (!binding) throw new Error(`Unbound variable: ${current.name} in context [${ctx.map(b => b.name).join(', ')}]`);
        return binding.type;
    }

    switch (current.tag) {
        case 'Type': return Type(); // Type : Type
        case 'Hole': {
            if (current.elaboratedType) return getTermRef(current.elaboratedType); // Return existing, possibly solved type
            const newTypeForHole = Hole(freshHoleName() + "_type_of_" + current.id.replace("?","h"));
            current.elaboratedType = newTypeForHole; // Assign a new hole type
            return newTypeForHole;
        }
        case 'App': {
            const funcType = infer(ctx, current.func, stackDepth + 1);
            // whnf the function's type to expose Pi, or a Hole that needs to become a Pi
            const normFuncType = whnf(funcType, ctx, stackDepth + 1); 
            
            if (normFuncType.tag === 'Hole') {
                // If func's type is a Hole, constrain it to be a Pi type
                const argTypeHole = Hole(freshHoleName() + "_app_argT_of_" + (current.arg.tag === 'Hole' ? current.arg.id.replace("?","h") : "arg"));
                const resultTypeHole = Hole(freshHoleName() + "_app_resT");
                const freshPN = freshVarName("appArgInfer");
                // The hole normFuncType must be equal to Pi(freshPN, argTypeHole, _ => resultTypeHole)
                addConstraint(normFuncType, Pi(freshPN, argTypeHole, _ => resultTypeHole), `App func type ${printTerm(normFuncType)} for ${printTerm(current.func)}`);
                check(ctx, current.arg, argTypeHole, stackDepth + 1); // Check arg against the new hole for argType
                return resultTypeHole;
            }
            if (normFuncType.tag !== 'Pi') throw new Error(`Cannot apply non-function: ${printTerm(current.func)} of type ${printTerm(normFuncType)} (original type: ${printTerm(funcType)})`);
            
            check(ctx, current.arg, normFuncType.paramType, stackDepth + 1);
            // Apply arg to bodyType. Result might need normalization if bodyType contains computations.
            return normFuncType.bodyType(current.arg); 
        }
        case 'Lam': {
            const lam = current; // current is already getTermRef'd
            const paramName = lam.paramName;

            if (lam._isAnnotated && lam.paramType) { // Annotated lambda
                check(ctx, lam.paramType, Type(), stackDepth + 1); // Check param type is a Type
                const extendedCtx = extendCtx(ctx, paramName, lam.paramType);
                const bodyTermInstance = lam.body(Var(paramName)); // Instantiate HOAS body
                const bodyType = infer(extendedCtx, bodyTermInstance, stackDepth + 1);
                return Pi(paramName, lam.paramType, _ => bodyType); // Return Pi type
            } else { // Unannotated lambda, infer parameter type
                const paramTypeHole = Hole(freshHoleName() + "_lam_" + paramName + "_paramT");
                
                // Bug Fix #1: Tentatively annotate the Lam term itself with the paramTypeHole
                // This allows solveConstraints to fill this hole, and normalize can then use the solved type.
                // This is a mutation but aligns with deep elaboration.
                // We need to ensure 'current' (which is a getTermRef result) can be mutated IF it was the original term.
                // If 'term' was the original un-dereferenced Lam, mutate that.
                if (term.tag === 'Lam' && !term._isAnnotated) { // ensure we are mutating the original term if it's a Lam
                    term.paramType = paramTypeHole;
                    term._isAnnotated = true; // Mark as "annotated" for normalization/equality purposes now
                } else if (current.tag === 'Lam' && !current._isAnnotated) { // If current is the actual Lam node
                     current.paramType = paramTypeHole;
                     current._isAnnotated = true;
                }
                // If current was a hole that dereferenced to a Lam, this mutation might be on a shared structure.
                // This part of the fix is tricky. The idea is the Lam term passed to 'elaborate' gets updated.
                // Let's assume `elaborate` will use the `term` given to it, which might have its `paramType` field
                // (if it's a Lam) updated by this infer call if that Lam was passed directly.

                const extendedCtx = extendCtx(ctx, paramName, paramTypeHole);
                const bodyTermInstance = lam.body(Var(paramName));
                const bodyType = infer(extendedCtx, bodyTermInstance, stackDepth + 1);
                return Pi(paramName, paramTypeHole, _ => bodyType);
            }
        }
        case 'Pi': { // (Π x : A . B) : Type
            const pi = current;
            check(ctx, pi.paramType, Type(), stackDepth + 1); // A : Type
            const paramName = pi.paramName;
            const extendedCtx = extendCtx(ctx, paramName, pi.paramType);
            const bodyTypeInstance = pi.bodyType(Var(paramName)); // B[x/x]
            check(extendedCtx, bodyTypeInstance, Type(), stackDepth + 1); // B[x/x] : Type
            return Type();
        }
        // Emdash Phase 1
        case 'CatTerm': return Type(); // Cat : Type
        case 'ObjTerm': // Obj C : Type, requires C : Cat
            check(ctx, current.cat, CatTerm(), stackDepth + 1);
            return Type();
        case 'HomTerm': { // Hom C X Y : Type, requires C:Cat, X:Obj C, Y:Obj C
            check(ctx, current.cat, CatTerm(), stackDepth + 1);
            const catForHom = getTermRef(current.cat); 
            check(ctx, current.dom, ObjTerm(catForHom), stackDepth + 1);
            check(ctx, current.cod, ObjTerm(catForHom), stackDepth + 1);
            return Type();
        }
        case 'MkCat_': { // MkCat O H C : Cat
            // O : Type
            check(ctx, current.objRepresentation, Type(), stackDepth + 1);
            const O_repr_norm = getTermRef(current.objRepresentation); // Use normalized for expected types

            // H : Π X:O . Π Y:O . Type
            const expected_H_type = Pi("X", O_repr_norm, _X => Pi("Y", O_repr_norm, _Y => Type()));
            check(ctx, current.homRepresentation, expected_H_type, stackDepth + 1);
            const H_repr_func_norm = getTermRef(current.homRepresentation);

            // C : Π X:O . Π Y:O . Π Z:O . Π g:(H Y Z) . Π f:(H X Y) . (H X Z)
            const type_of_hom_X_Y = (X_val: Term, Y_val: Term) => App(App(H_repr_func_norm, X_val), Y_val);

            const expected_C_type =
                Pi("Xobj", O_repr_norm, Xobj_term =>
                Pi("Yobj", O_repr_norm, Yobj_term =>
                Pi("Zobj", O_repr_norm, Zobj_term =>
                Pi("gmorph", type_of_hom_X_Y(Yobj_term, Zobj_term), _gmorph_term =>
                Pi("fmorph", type_of_hom_X_Y(Xobj_term, Yobj_term), _fmorph_term =>
                type_of_hom_X_Y(Xobj_term, Zobj_term)
                )))));
            check(ctx, current.composeImplementation, expected_C_type, stackDepth + 1);
            return CatTerm();
        }
        case 'IdentityMorph': { // id X : Hom C X X
            const idTerm = current; // implicits (cat_IMPLICIT) are now filled with holes if undefined
            const catArgHole = idTerm.cat_IMPLICIT!; // Should be a Hole if not provided by user
            
            // Infer type of obj: T_obj
            const objActualType = infer(ctx, idTerm.obj, stackDepth + 1);
            // Add constraint: T_obj === Obj(catArgHole)
            addConstraint(objActualType, ObjTerm(catArgHole), `Object ${printTerm(idTerm.obj)} in IdentityMorph must be of type Obj(${printTerm(catArgHole)})`);
            
            // Return Hom(catArgHole, obj, obj)
            return HomTerm(catArgHole, idTerm.obj, idTerm.obj);
        }
        case 'ComposeMorph': { // g ∘ f : Hom C X Z
            const compTerm = current; // implicits are filled with holes
            const catArgHole = compTerm.cat_IMPLICIT!;
            const XArgHole = compTerm.objX_IMPLICIT!;
            const YArgHole = compTerm.objY_IMPLICIT!;
            const ZArgHole = compTerm.objZ_IMPLICIT!;

            // These checks will generate constraints for f, g, and the hole implicits
            // f : Hom C X Y
            check(ctx, compTerm.f, HomTerm(catArgHole, XArgHole, YArgHole), stackDepth + 1);
            // g : Hom C Y Z
            check(ctx, compTerm.g, HomTerm(catArgHole, YArgHole, ZArgHole), stackDepth + 1);

            // Result type: Hom C X Z
            return HomTerm(catArgHole, XArgHole, ZArgHole);
        }
    }
}

export function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0): void {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Check stack depth exceeded (depth: ${stackDepth}, term ${printTerm(term)}, expType ${printTerm(expectedType)})`);

    const termWithImplicits = ensureImplicitsAsHoles(term); // Ensure implicits before getTermRef
    const current = getTermRef(termWithImplicits);
    const normExpectedType = whnf(expectedType, ctx, stackDepth + 1); // whnf expected type

    // Handling for unannotated Lam when expected type is Pi (bidirectional rule for lambda)
    if (current.tag === 'Lam' && !current._isAnnotated && normExpectedType.tag === 'Pi') {
        const lamTerm = current; // This is the getTermRef'd version.
        const expectedPi = normExpectedType;

        // Annotate the Lam term with the parameter type from Pi.
        // This mutation needs to affect the term that `elaborate` will eventually return/normalize.
        // If `current` is the actual Lam node (not a hole that resolved to it), mutate it.
        // The more robust way is if `elaborate` reconstructs after solving, or `infer`/`check` return elaborated terms.
        // For now, assume `term` (original argument to check) is the one to mutate if it's the Lam.
        let lamToAnnotate : Term & {tag: 'Lam'};
        if (term.tag === 'Lam' && !term._isAnnotated) {
            lamToAnnotate = term;
        } else if (current.tag === 'Lam' && !current._isAnnotated) { // Should be the same if term was not a hole
            lamToAnnotate = current;
        } else {
            // This case should ideally not happen if unannotated lambdas are directly passed.
            // If current is a Lam from a solved hole, it might already be annotated by infer.
            // Fall through to general infer and constrain if this path is complex.
            const inferredType = infer(ctx, current, stackDepth + 1);
            addConstraint(inferredType, normExpectedType, `Check Lam (unannotated, from hole?) ${printTerm(current)} against Pi ${printTerm(normExpectedType)}`);
            return;
        }

        lamToAnnotate.paramType = expectedPi.paramType;
        lamToAnnotate._isAnnotated = true;

        // Deep elaboration: replace body function with one that checks recursively.
        // This was described in "Difficulties Encountered" - Solution (Deep Elaboration)
        const originalBodyFn = lamToAnnotate.body;
        lamToAnnotate.body = (v_arg: Term): Term => {
            const freshInnerRawTerm = originalBodyFn(v_arg); // Get the body term
            let ctxForInnerBody = ctx;
            const currentLamParamType = lamToAnnotate.paramType!; // Now annotated
            if (v_arg.tag === 'Var') { // Extend context with the param type
                ctxForInnerBody = extendCtx(ctx, v_arg.name, currentLamParamType);
            }
            const expectedTypeForInnerBody = expectedPi.bodyType(v_arg); // Get expected body type
            check(ctxForInnerBody, freshInnerRawTerm, expectedTypeForInnerBody, stackDepth + 1); // Check it
            return freshInnerRawTerm; // Return original structure, side effects of check applied
        };
        
        // Check the original body structure once with the new annotation to ensure constraints are generated.
        // This call to `check` will use the *new* body function defined above, which performs the inner check.
        const tempVarForOriginalCheck = Var(lamToAnnotate.paramName);
        const extendedCtx = extendCtx(ctx, tempVarForOriginalCheck.name, lamToAnnotate.paramType);
        check(extendedCtx, lamToAnnotate.body(tempVarForOriginalCheck), expectedPi.bodyType(tempVarForOriginalCheck), stackDepth + 1);
        return;
    }

    if (current.tag === 'Hole') {
        if (!current.elaboratedType) {
            current.elaboratedType = normExpectedType; // Tentatively assign type to hole
        }
        // Whether elaboratedType was just set or existed, constrain its (inferred) type with expected.
        const inferredHoleType = infer(ctx, current, stackDepth + 1); // Infer will use/create elaboratedType
        addConstraint(inferredHoleType, normExpectedType, `Hole ${current.id} checked against ${printTerm(normExpectedType)}`);
        
        // Ensure the type assigned to/expected for the hole is itself a well-formed type.
        // This generates constraints for components of normExpectedType if it's complex.
        check(ctx, normExpectedType, Type(), stackDepth + 1);
        return;
    }

    // Specific check logic for IdentityMorph/ComposeMorph when expected is HomTerm
    // This aligns with "Difficulties Encountered" - Solution 5
    if (current.tag === 'IdentityMorph' && normExpectedType.tag === 'HomTerm') {
        const idTerm = current; // implicits are holes
        const expHom = normExpectedType;

        // Constrain cat_IMPLICIT with cat from expected HomTerm
        addConstraint(idTerm.cat_IMPLICIT!, expHom.cat, `IdentityMorph cat implicit ${printTerm(idTerm.cat_IMPLICIT!)} for ${printTerm(idTerm.obj)} vs expected Hom.cat ${printTerm(expHom.cat)}`);
        // Constrain obj with dom and cod from expected HomTerm
        addConstraint(idTerm.obj, expHom.dom, `IdentityMorph obj ${printTerm(idTerm.obj)} vs Hom.dom ${printTerm(expHom.dom)}`);
        addConstraint(idTerm.obj, expHom.cod, `IdentityMorph obj ${printTerm(idTerm.obj)} vs Hom.cod ${printTerm(expHom.cod)}`);
        
        // Also, the object itself must be of type Obj(cat_IMPLICIT)
        const objActualType = infer(ctx, idTerm.obj, stackDepth +1); // Infer type of object
        addConstraint(objActualType, ObjTerm(idTerm.cat_IMPLICIT!), `Object ${printTerm(idTerm.obj)} type check: ${printTerm(objActualType)} vs Obj(${printTerm(idTerm.cat_IMPLICIT!)})`);
        return; // Constraints are set, solver does the work.
    }

    if (current.tag === 'ComposeMorph' && normExpectedType.tag === 'HomTerm') {
        const compTerm = current; // implicits are holes
        const expHom = normExpectedType;

        addConstraint(compTerm.cat_IMPLICIT!, expHom.cat, `ComposeMorph cat implicit ${printTerm(compTerm.cat_IMPLICIT!)} vs Hom.cat ${printTerm(expHom.cat)}`);
        addConstraint(compTerm.objX_IMPLICIT!, expHom.dom, `ComposeMorph objX implicit ${printTerm(compTerm.objX_IMPLICIT!)} (dom of result) vs Hom.dom ${printTerm(expHom.dom)}`);
        addConstraint(compTerm.objZ_IMPLICIT!, expHom.cod, `ComposeMorph objZ implicit ${printTerm(compTerm.objZ_IMPLICIT!)} (cod of result) vs Hom.cod ${printTerm(expHom.cod)}`);
        
        // objY_IMPLICIT is the intermediate object.
        // Check f and g against HomTerms constructed with these (potentially hole) implicits.
        check(ctx, compTerm.f, HomTerm(compTerm.cat_IMPLICIT!, compTerm.objX_IMPLICIT!, compTerm.objY_IMPLICIT!), stackDepth + 1);
        check(ctx, compTerm.g, HomTerm(compTerm.cat_IMPLICIT!, compTerm.objY_IMPLICIT!, compTerm.objZ_IMPLICIT!), stackDepth + 1);
        return; // Constraints set.
    }

    // Default case: infer type of `current` and add constraint `inferred === expected`.
    const inferredType = infer(ctx, current, stackDepth + 1);
    addConstraint(inferredType, normExpectedType, `Check general: ${printTerm(inferredType)} vs ${printTerm(normExpectedType)} for term ${printTerm(current)}`);
}

export interface ElaborationResult { term: Term; type: Term; }
export function elaborate(term: Term, expectedType?: Term, initialCtx: Context = emptyCtx): ElaborationResult {
    constraints = []; // Reset global constraints
    // Reset fresh ID counters for each elaboration call for reproducible hole/var names in tests.
    // In a real system, these might be instance-based or managed differently.
    nextHoleId = 0; 
    nextVarId = 0; 
    
    let finalTypeToReport: Term;
    // The `term` passed to elaborate is the root of what we're working on.
    // Mutations by `infer` (for Lam unannotated) or `check` (Lam deep elab) should apply to this `term` instance
    // or its sub-objects if they are directly part of its structure.
    const termToElaborate = term; 

    try {
        if (expectedType) {
            check(initialCtx, termToElaborate, expectedType);
            // The expectedType itself might contain holes that get resolved.
            // So, use getTermRef on it for the final reported type.
            finalTypeToReport = getTermRef(expectedType); 
        } else {
            finalTypeToReport = infer(initialCtx, termToElaborate);
        }

        if (!solveConstraints(initialCtx)) {
            const fc = constraints.find(c => !areEqual(getTermRef(c.t1), getTermRef(c.t2), initialCtx));
            let fcMsg = "Unknown constraint";
            if (fc) {
                const fc_t1_print = printTerm(getTermRef(fc.t1));
                const fc_t2_print = printTerm(getTermRef(fc.t2));
                fcMsg = `${fc_t1_print} vs ${fc_t2_print} (orig: ${fc.origin || 'unspecified'})`;
            }
            console.error("Remaining constraints on failure during elaboration:");
            constraints.forEach(c => {
                 const c_t1_dbg = getTermRef(c.t1); const c_t2_dbg = getTermRef(c.t2);
                 console.error(`  ${printTerm(c_t1_dbg)} ${areEqual(c_t1_dbg, c_t2_dbg, initialCtx) ? "===" : "=/="} ${printTerm(c_t2_dbg)} (origin: ${c.origin})`);
            });
            throw new Error(`Type error: Could not solve constraints. Approx failing: ${fcMsg}`);
        }
    } catch (e) {
        // Filter known type system errors vs unexpected JS errors
        if (e instanceof Error && (e.message.startsWith("Type error:") || e.message.startsWith("Unbound variable:") || e.message.startsWith("Cannot apply non-function:") || e.message.startsWith("Constant symbol") || e.message.startsWith("WHNF stack depth") || e.message.startsWith("Normalize stack depth") || e.message.startsWith("Unification stack depth") || e.message.startsWith("Equality check depth") || e.message.startsWith("Infer stack depth") || e.message.startsWith("Check stack depth") || e.message.startsWith("matchPattern stack depth"))) {
            throw e;
        }
        // For other errors, provide more context
        throw new Error(`Elaboration internal error: ${(e as Error).message} on term ${printTerm(termToElaborate)}. Stack: ${(e as Error).stack}`);
    }

    // After solving, termToElaborate might have its holes filled or its structure changed by infer/check (e.g. Lam annotation).
    // Normalizing this termToElaborate structure should give the final elaborated term.
    const normalizedElaboratedTerm = normalize(termToElaborate, initialCtx);

    // The finalTypeToReport (from infer or expectedType) might also have had its holes solved.
    // Normalize it too.
    const normalizedReportedType = normalize(getTermRef(finalTypeToReport), initialCtx);
    
    return { term: normalizedElaboratedTerm, type: normalizedReportedType };
}

export function isPatternVarName(name: string, patternVarDecls: PatternVarDecl[]): boolean {
    return patternVarDecls.some(pvd => pvd.name === name);
}

export function matchPattern(
    pattern: Term, termToMatch: Term, ctx: Context,
    patternVarDecls: PatternVarDecl[],
    currentSubst?: Substitution, stackDepth = 0
): Substitution | null {
    consoleLog(`[TRACE matchPattern (${stackDepth})] Enter: pattern = ${printTerm(pattern)}, termToMatch = ${printTerm(termToMatch)}`);
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`matchPattern stack depth exceeded for pattern ${printTerm(pattern)} vs term ${printTerm(termToMatch)}`);
    
    const currentTermStruct = getTermRef(termToMatch);
    const rtPattern = getTermRef(pattern); 
    consoleLog(`[TRACE matchPattern (${stackDepth})] rtPattern = ${printTerm(rtPattern)}, currentTermStruct = ${printTerm(currentTermStruct)}`);

    const subst = currentSubst ? new Map(currentSubst) : new Map<string, Term>();

    // Pattern variable case (Var or Hole in pattern treated as pvar)
    if (rtPattern.tag === 'Var' && isPatternVarName(rtPattern.name, patternVarDecls)) {
        const pvarName = rtPattern.name;
        consoleLog(`[TRACE matchPattern (${stackDepth})] Pattern Var: ${pvarName}`);
        if (pvarName === '_') {
            consoleLog(`[TRACE matchPattern (${stackDepth})] Wildcard Var "_", returning current subst.`);
            return subst; 
        }
        const existing = subst.get(pvarName);
        if (existing) { 
            consoleLog(`[TRACE matchPattern (${stackDepth})] Pattern Var ${pvarName} already bound to ${printTerm(existing)}. Checking consistency with ${printTerm(currentTermStruct)}`);
            const consistent = areStructurallyEqualNoWhnf(currentTermStruct, getTermRef(existing), ctx, stackDepth + 1);
            consoleLog(`[TRACE matchPattern (${stackDepth})] Consistency check for ${pvarName}: ${consistent}`);
            return consistent ? subst : null;
        }
        consoleLog(`[TRACE matchPattern (${stackDepth})] Binding ${pvarName} to ${printTerm(currentTermStruct)}`);
        subst.set(pvarName, currentTermStruct); 
        return subst;
    }
    if (rtPattern.tag === 'Hole' && isPatternVarName(rtPattern.id, patternVarDecls)) { 
        const pvarId = rtPattern.id;
        consoleLog(`[TRACE matchPattern (${stackDepth})] Pattern Hole (as pvar): ${pvarId}`);
        if (pvarId === '_') {
            consoleLog(`[TRACE matchPattern (${stackDepth})] Wildcard Hole "_", returning current subst.`);
            return subst; 
        }
        const existing = subst.get(pvarId);
        if (existing) {
            consoleLog(`[TRACE matchPattern (${stackDepth})] Pattern Hole ${pvarId} already bound to ${printTerm(existing)}. Checking consistency with ${printTerm(currentTermStruct)}`);
            const consistent = areStructurallyEqualNoWhnf(currentTermStruct, getTermRef(existing), ctx, stackDepth + 1);
            consoleLog(`[TRACE matchPattern (${stackDepth})] Consistency check for ${pvarId}: ${consistent}`);
            return consistent ? subst : null;
        }
        consoleLog(`[TRACE matchPattern (${stackDepth})] Binding ${pvarId} to ${printTerm(currentTermStruct)}`);
        subst.set(pvarId, currentTermStruct);
        return subst;
    }

    if (rtPattern.tag === 'Hole') { 
        if (currentTermStruct.tag === 'Hole' && rtPattern.id === currentTermStruct.id) {
            consoleLog(`[TRACE matchPattern (${stackDepth})] Concrete Hole in pattern ${rtPattern.id} matches term Hole ${currentTermStruct.id}.`);
            return subst;
        }
        consoleLog(`[TRACE matchPattern (${stackDepth})] Concrete Hole in pattern ${rtPattern.id} does not match term ${printTerm(currentTermStruct)}. Returning null.`);
        return null; 
    }
    if (currentTermStruct.tag === 'Hole') {
        consoleLog(`[TRACE matchPattern (${stackDepth})] Term is Hole ${currentTermStruct.id} but pattern is not pvar/concrete matching hole. Returning null.`);
        return null;
    }

    if (rtPattern.tag !== currentTermStruct.tag) {
        consoleLog(`[TRACE matchPattern (${stackDepth})] Tags differ: pattern ${rtPattern.tag} vs term ${currentTermStruct.tag}. Returning null.`);
        return null;
    }

    const matchOptImplicitArgPattern = (currentS: Substitution | null, patArg?: Term, termArg?: Term): Substitution | null => {
        if (!currentS) return null; // Previous match failed

        if (patArg) { // Pattern specifies this implicit argument
            const patArgRef = getTermRef(patArg);
            // If patArg is a wildcard var/hole, it matches anything (even absence if termArg is undef)
            // For pattern matching, wildcard means "don't care and don't bind".
            // If it's a pvar, it tries to bind.
            if ((patArgRef.tag === 'Var' && isPatternVarName(patArgRef.name, patternVarDecls) && patArgRef.name === '_') ||
                (patArgRef.tag === 'Hole' && patArgRef.id === '_')) {
                return currentS; // Wildcard matches presence or absence of termArg
            }

            if (!termArg) return null; // Pattern requires implicit, term doesn't have it (and pattern arg not wildcard)

            // Both pattern and term have the implicit arg, recursively match.
            return matchPattern(patArg, termArg, ctx, patternVarDecls, currentS, stackDepth + 1);

        }
        // If patArg is undefined, pattern doesn't care about this implicit.
        // It matches whether termArg is present or absent.
        return currentS;
    };

    // Structural comparison for each tag
    switch (rtPattern.tag) {
        case 'Type': case 'CatTerm': 
            consoleLog(`[TRACE matchPattern (${stackDepth})] Matched Type/CatTerm.`);
            return subst; 
        case 'Var': 
            const varNameMatch = rtPattern.name === (currentTermStruct as Term & {tag:'Var'}).name;
            consoleLog(`[TRACE matchPattern (${stackDepth})] Concrete Var in pattern: ${rtPattern.name} vs term Var ${(currentTermStruct as Term & {tag:'Var'}).name}. Match: ${varNameMatch}`);
            return varNameMatch ? subst : null;
        case 'App': {
            const termApp = currentTermStruct as Term & {tag:'App'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] App: matching func and arg recursively.`);
            const s1 = matchPattern(rtPattern.func, termApp.func, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s1) {
                consoleLog(`[TRACE matchPattern (${stackDepth})] App: func match failed. Returning null.`);
                return null;
            }
            consoleLog(`[TRACE matchPattern (${stackDepth})] App: func matched. Matching arg.`);
            const s2 = matchPattern(rtPattern.arg, termApp.arg, ctx, patternVarDecls, s1, stackDepth + 1);
            if(!s2) consoleLog(`[TRACE matchPattern (${stackDepth})] App: arg match failed. Returning null.`);
            return s2;
        }
        case 'Lam': { 
            const lamP = rtPattern as Term & {tag:'Lam'};
            const lamT = currentTermStruct as Term & {tag:'Lam'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: pattern annotated=${lamP._isAnnotated}, term annotated=${lamT._isAnnotated}`);
            if (lamP._isAnnotated !== lamT._isAnnotated) {
                consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: annotation mismatch. Returning null.`);
                return null;
            }
            
            let tempSubst = subst;
            if (lamP._isAnnotated) { 
                if (!lamP.paramType || !lamT.paramType) {
                     consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: annotated but one has no paramType. Returning null.`);
                     return null; 
                }
                consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: matching annotated param types.`);
                 const sType = matchPattern(lamP.paramType, lamT.paramType, ctx, patternVarDecls, tempSubst, stackDepth + 1);
                 if (!sType) {
                    consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: param type match failed. Returning null.`);
                    return null;
                 }
                 tempSubst = sType;
                 consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: param types matched.`);
            }
            const freshV = Var(freshVarName(lamP.paramName));
            const CtxTypeP = lamP.paramType ? getTermRef(lamP.paramType) : Hole(freshHoleName()+"_match_lam_ctx");
            const extendedCtx = extendCtx(ctx, freshV.name, CtxTypeP);
            consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: comparing bodies using areEqual with fresh var ${freshV.name}.`);
            const bodiesEqual = areEqual(lamP.body(freshV), lamT.body(freshV), extendedCtx, stackDepth + 1);
            consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: bodies areEqual result: ${bodiesEqual}`);
            return bodiesEqual ? tempSubst : null;
        }
        case 'Pi': { 
            const piP = rtPattern as Term & {tag:'Pi'};
            const piT = currentTermStruct as Term & {tag:'Pi'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] Pi: matching param types.`);
            const sType = matchPattern(piP.paramType, piT.paramType, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!sType) {
                consoleLog(`[TRACE matchPattern (${stackDepth})] Pi: param type match failed. Returning null.`);
                return null;
            }
            consoleLog(`[TRACE matchPattern (${stackDepth})] Pi: param types matched. Comparing body types using areEqual.`);
            const freshV = Var(freshVarName(piP.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(piP.paramType)); 
            const bodyTypesEqual = areEqual(piP.bodyType(freshV), piT.bodyType(freshV), extendedCtx, stackDepth + 1);
            consoleLog(`[TRACE matchPattern (${stackDepth})] Pi: body types areEqual result: ${bodyTypesEqual}`);
            return bodyTypesEqual ? sType : null;
        }
        case 'ObjTerm': {
            consoleLog(`[TRACE matchPattern (${stackDepth})] ObjTerm: matching categories.`);
            const catMatchResult = matchPattern(rtPattern.cat, (currentTermStruct as Term & {tag:'ObjTerm'}).cat, ctx, patternVarDecls, subst, stackDepth + 1);
            if(!catMatchResult) consoleLog(`[TRACE matchPattern (${stackDepth})] ObjTerm: category match failed.`);
            return catMatchResult;
        }
        case 'HomTerm': {
            const homP = rtPattern as Term & {tag:'HomTerm'};
            const homT = currentTermStruct as Term & {tag:'HomTerm'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] HomTerm: matching cat, dom, cod.`);
            let s = matchPattern(homP.cat, homT.cat, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] HomTerm: cat match failed.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] HomTerm: cat matched. Matching dom.`);
            s = matchPattern(homP.dom, homT.dom, ctx, patternVarDecls, s, stackDepth + 1);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] HomTerm: dom match failed.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] HomTerm: dom matched. Matching cod.`);
            const codMatchResult = matchPattern(homP.cod, homT.cod, ctx, patternVarDecls, s, stackDepth + 1);
            if(!codMatchResult) consoleLog(`[TRACE matchPattern (${stackDepth})] HomTerm: cod match failed.`);
            return codMatchResult;
        }
        case 'MkCat_': {
            const mkP = rtPattern as Term & {tag:'MkCat_'};
            const mkT = currentTermStruct as Term & {tag:'MkCat_'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] MkCat_: matching objRepresentation, homRepresentation, composeImplementation.`);
            let s = matchPattern(mkP.objRepresentation, mkT.objRepresentation, ctx, patternVarDecls, subst, stackDepth + 1);
            if(!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] MkCat_: objRepresentation match failed.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] MkCat_: objRepresentation matched. Matching homRepresentation.`);
            s = matchPattern(mkP.homRepresentation, mkT.homRepresentation, ctx, patternVarDecls, s, stackDepth + 1);
            if(!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] MkCat_: homRepresentation match failed.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] MkCat_: homRepresentation matched. Matching composeImplementation.`);
            const composeImplMatchResult = matchPattern(mkP.composeImplementation, mkT.composeImplementation, ctx, patternVarDecls, s, stackDepth + 1);
            if(!composeImplMatchResult) consoleLog(`[TRACE matchPattern (${stackDepth})] MkCat_: composeImplementation match failed.`);
            return composeImplMatchResult;
        }


        case 'IdentityMorph': {
            const idP = rtPattern as Term & {tag:'IdentityMorph'};
            const idT = currentTermStruct as Term & {tag:'IdentityMorph'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] IdentityMorph: matching cat_IMPLICIT and obj.`);
            let s: Substitution | null = subst;
            s = matchOptImplicitArgPattern(s, idP.cat_IMPLICIT, idT.cat_IMPLICIT);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] IdentityMorph: cat_IMPLICIT match failed via matchOptImplicitArgPattern.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] IdentityMorph: cat_IMPLICIT matched. Matching obj.`);
            const objMatchResult = matchPattern(idP.obj, idT.obj, ctx, patternVarDecls, s, stackDepth + 1);
            if(!objMatchResult) consoleLog(`[TRACE matchPattern (${stackDepth})] IdentityMorph: obj match failed.`);
            return objMatchResult;
        }
        case 'ComposeMorph': {
            const compP = rtPattern as Term & {tag:'ComposeMorph'};
            const compT = currentTermStruct as Term & {tag:'ComposeMorph'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: matching implicits, g, and f.`);
            let s: Substitution | null = subst;
            
            s = matchOptImplicitArgPattern(s, compP.cat_IMPLICIT, compT.cat_IMPLICIT);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: cat_IMPLICIT match failed.`); return null; }
            s = matchOptImplicitArgPattern(s, compP.objX_IMPLICIT, compT.objX_IMPLICIT);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: objX_IMPLICIT match failed.`); return null; }
            s = matchOptImplicitArgPattern(s, compP.objY_IMPLICIT, compT.objY_IMPLICIT);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: objY_IMPLICIT match failed.`); return null; }
            s = matchOptImplicitArgPattern(s, compP.objZ_IMPLICIT, compT.objZ_IMPLICIT);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: objZ_IMPLICIT match failed.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: All implicits matched. Matching g.`);

            s = matchPattern(compP.g, compT.g, ctx, patternVarDecls, s, stackDepth + 1); 
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: g match failed.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: g matched. Matching f.`);
            const fMatchResult = matchPattern(compP.f, compT.f, ctx, patternVarDecls, s, stackDepth + 1);
            if(!fMatchResult) consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: f match failed.`);
            return fMatchResult;
        }
    }
}

export function applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[]): Term {
    const current = getTermRef(term); // Dereference first

    // Check if current is a pattern variable (Var or Hole)
    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        if (current.name === '_') return Hole('_'); // Wildcard var "_" should remain Hole "_" if used in RHS
        const replacement = subst.get(current.name);
        if (!replacement) {
            console.warn(`applySubst: Unbound pattern variable Var "${current.name}" in RHS. This might be an issue with rule definition or fresh var generation in unif rules. Subst: ${Array.from(subst.keys())}`);
            return current; // Return original if no substitution found (should ideally not happen for well-formed rules)
        }
        return replacement;
    }
    if (current.tag === 'Hole' && isPatternVarName(current.id, patternVarDecls)) {
        if (current.id === '_') return Hole('_'); // Wildcard hole "_"
        const replacement = subst.get(current.id);
        if (!replacement) {
            console.warn(`applySubst: Unbound pattern variable Hole "${current.id}" in RHS. Subst: ${Array.from(subst.keys())}`);
            return current;
        }
        return replacement;
    }

    // Not a pattern variable, so recurse structurally.
    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': case 'CatTerm': return current; // Concrete terms, no pvars
        case 'App':
            return App(applySubst(current.func, subst, patternVarDecls), applySubst(current.arg, subst, patternVarDecls));
        case 'Lam': {
            const lam = current;
            const lamParamType = lam.paramType ? applySubst(lam.paramType, subst, patternVarDecls) : undefined;
            // Create new HOAS body; substitution applies *inside* the body when it's eventually called.
            // The new HOAS function captures the current `subst` and `patternVarDecls`.
            const newLam = Lam(lam.paramName, lamParamType,
                (v_arg: Term) => applySubst(lam.body(v_arg), subst, patternVarDecls));
            (newLam as Term & {tag:'Lam'})._isAnnotated = lam._isAnnotated;
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

// Print term with bound variables handling for HOAS
export function printTerm(term: Term, boundVarsMap: Map<string, string> = new Map(), stackDepth = 0): string {
    if (stackDepth > MAX_STACK_DEPTH * 2) return "<print_depth_exceeded>";
    if (!term) return "<null_term>";
    
    const current = getTermRef(term); // Always print the resolved term

    const getUniqueName = (baseName: string): string => {
        if (!boundVarsMap.has(baseName) && !globalDefs.has(baseName) && !Array.from(boundVarsMap.values()).includes(baseName)) {
            return baseName;
        }
        let uniqueName = baseName;
        let suffix = 1;
        while (globalDefs.has(uniqueName) || Array.from(boundVarsMap.values()).includes(uniqueName)) {
            uniqueName = `${baseName}_${suffix++}`;
        }
        return uniqueName;
    };

    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return boundVarsMap.get(current.name) || current.name;
        case 'Hole': {
            let typeInfo = "";
            if (current.elaboratedType) {
                const elabTypeRef = getTermRef(current.elaboratedType);
                // Avoid printing self-referential or trivial hole types like ?h : ?h or ?h : Type (if Type is obvious)
                if (!((elabTypeRef.tag === 'Hole' && elabTypeRef.id === current.id) || 
                      (elabTypeRef.tag === 'Type' && term.tag === 'Type'))) { // Check original term for Type:Type case
                    // Print elaborated type with current bound vars context
                    const elabTypePrint = printTerm(elabTypeRef, new Map(boundVarsMap), stackDepth + 1); 
                    if(!elabTypePrint.startsWith("?h") || elabTypePrint.length > current.id.length +3 ) { 
                        typeInfo = `(:${elabTypePrint})`;
                    }
                }
            }
            return (current.id === '_' ? '_' : (boundVarsMap.get(current.id) || current.id)) + typeInfo;
        }
        case 'Lam': {
            const paramDisplayName = getUniqueName(current.paramName);
            const newBoundVars = new Map(boundVarsMap);
            newBoundVars.set(current.paramName, paramDisplayName); // Map original name to display name

            const typeAnnotation = (current._isAnnotated && current.paramType) 
                ? ` : ${printTerm(current.paramType, new Map(boundVarsMap), stackDepth + 1)}` // Type printed in outer scope
                : '';
            // Instantiate body with a Var using the original paramName, let printTerm handle mapping to display name
            const bodyTerm = current.body(Var(current.paramName)); 
            return `(λ ${paramDisplayName}${typeAnnotation}. ${printTerm(bodyTerm, newBoundVars, stackDepth + 1)})`;
        }
        case 'App':
            return `(${printTerm(current.func, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.arg, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'Pi': {
            const paramDisplayName = getUniqueName(current.paramName);
            const newBoundVars = new Map(boundVarsMap);
            newBoundVars.set(current.paramName, paramDisplayName);

            const paramTypeStr = printTerm(current.paramType, new Map(boundVarsMap), stackDepth + 1); // Param type in outer scope
            const bodyTypeTerm = current.bodyType(Var(current.paramName)); // Instantiate with original name
            return `(Π ${paramDisplayName} : ${paramTypeStr}. ${printTerm(bodyTypeTerm, newBoundVars, stackDepth + 1)})`;
        }
        case 'CatTerm': return 'Cat';
        case 'ObjTerm': return `(Obj ${printTerm(current.cat, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'HomTerm':
            return `(Hom ${printTerm(current.cat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.dom, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.cod, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'MkCat_':
            return `(mkCat_ {O=${printTerm(current.objRepresentation, new Map(boundVarsMap), stackDepth + 1)}, H=${printTerm(current.homRepresentation, new Map(boundVarsMap), stackDepth + 1)}, C=${printTerm(current.composeImplementation, new Map(boundVarsMap), stackDepth + 1)}})`;
        case 'IdentityMorph': {
            let catIdStr = "";
            if (current.cat_IMPLICIT && getTermRef(current.cat_IMPLICIT).tag !== 'Hole') { 
                 catIdStr = ` [cat=${printTerm(current.cat_IMPLICIT, new Map(boundVarsMap), stackDepth + 1)}]`;
            }
            return `(id${catIdStr} ${printTerm(current.obj, new Map(boundVarsMap), stackDepth + 1)})`;
        }
        case 'ComposeMorph': {
            let catCompStr = "";
            if (current.cat_IMPLICIT && getTermRef(current.cat_IMPLICIT).tag !== 'Hole') {
                 catCompStr = ` [cat=${printTerm(current.cat_IMPLICIT, new Map(boundVarsMap), stackDepth + 1)}]`;
            }
            return `(${printTerm(current.g, new Map(boundVarsMap), stackDepth + 1)} ∘${catCompStr} ${printTerm(current.f, new Map(boundVarsMap), stackDepth + 1)})`;
        }
    }
}

export function consoleLog(message?: any, ...optionalParams: any[]): void {
    if (DEBUG_VERBOSE) {
        console.log(message, ...optionalParams);
    }
}

export function resetMyLambdaPi() {
    constraints = []; globalDefs.clear();
    userRewriteRules.length = 0;
    userUnificationRules.length = 0;
    nextVarId = 0; nextHoleId = 0;
}

// --- Test Suite ---
console.log("--- MyLambdaPi with Emdash Phase 1: Core Categories (Attempt 7) ---");

// SetupPhase1GlobalsAndRules and runPhase1Tests are unchanged from your provided "NEW TEST CODE"
// They will be used to test these modifications.
export function setupPhase1GlobalsAndRules() {
    defineGlobal("NatType", Type(), undefined, true); // NatType is a kernel constant Type
    defineGlobal("BoolType", Type(), undefined, true);

    // Pattern variables for rewrite rules
    // IMPORTANT: Pattern variable names should be distinct from any global/term variable names
    // if possible, or handled carefully by matching logic.
    // Our pattern variables are declared with types, but types aren't used yet in matching.
    const pvarCat = { name: "CAT_pv", type: CatTerm() };
    const pvarX_obj = { name: "X_obj_pv", type: ObjTerm(Var("CAT_pv")) }; // Type annotation for clarity
    const pvarY_obj = { name: "Y_obj_pv", type: ObjTerm(Var("CAT_pv")) };
    const pvarZ_obj = { name: "Z_obj_pv", type: ObjTerm(Var("CAT_pv")) };


    // Rule: g o id_X = g.
    // Pattern: ComposeMorph(g_param, IdentityMorph(X_obj_pv, CAT_pv), CAT_pv, X_obj_pv, X_obj_pv, Y_obj_pv)
    // g_param type: Hom CAT_pv Y_obj_pv X_obj_pv (as per original test, g: Y -> X)
    // This means id_X is on the RIGHT of g for the rule "g o id_X = g" as f o g (g then f)
    // Our ComposeMorph(g,f) means f then g. So rule should be for IdentityMorph(Y) o f = f
    // Let's stick to the rule names and adjust the structure if needed.
    // "comp_g_idX" suggests g is composed with id_X.
    // If g : Hom C Y X and id_X : Hom C X X, then g o id_X makes sense.
    // ComposeMorph(g, id_X, ...): id_X then g. This requires cod(id_X) = dom(g), so X = Y.
    // The rule `ComposeMorph(g, IdentityMorph(X, C), C, Z, X, X) ↪ g` (where `g : Hom C Z X`)
    // This means Z is objX_IMPLICIT, X is objY_IMPLICIT, X is objZ_IMPLICIT
    // So f = IdentityMorph(X,C) which has type Hom C X X.  objX_imp = X, objY_imp = X
    // And g has type Hom C X X. objY_imp = X, objZ_imp = X.
    // Wait, the rule from doc: `ComposeMorph(g, IdentityMorph(X_obj, CAT), CAT, obj_of_g_domain, X_obj, X_obj_cod_of_g) -> g`  (where `g : Hom CAT (obj_of_g_domain) (X_obj)`)
    // So f = IdentityMorph(X_obj, CAT) : Hom CAT X_obj X_obj
    // And g is the first argument to ComposeMorph.
    // Let's use the provided rule structures from Test 5 logic.
    // g_param_gid : Hom CAT_pv Y_obj_pv X_obj_pv
    // lhs: ComposeMorph(Var("g_param_gid"), IdentityMorph(Var("X_obj_pv"), Var("CAT_pv")), /* implicits */ )
    // Implicits for ComposeMorph(g,f): cat, dom(f), cod(f)=dom(g), cod(g)
    // f = IdentityMorph(X_obj_pv, CAT_pv) => dom(f)=X_obj_pv, cod(f)=X_obj_pv
    // g = g_param_gid => dom(g)=Y_obj_pv, cod(g)=X_obj_pv
    // For composition cod(f) = dom(g) => X_obj_pv = Y_obj_pv.
    // This means the pattern vars X_obj_pv and Y_obj_pv must match to the same object for this rule to apply as written.

    // Rule 1: g o id = g.  (Standard notation: f ; g, where f is id)
    // ComposeMorph(g, IdentityMorph(X,C))
    // IdentityMorph(X,C) has type Hom C X X.
    // g must have type Hom C X Y.
    // Result is Hom C X Y.
    // Implicits for ComposeMorph(g, id_X, C, X, X, Y)
    const pvar_g_XY = { name: "g_XY_pv", type: HomTerm(Var("CAT_pv"), Var("X_obj_pv"), Var("Y_obj_pv")) };
    addRewriteRule({
        name: "comp_g_idX_fwd", // g after id_X
        patternVars: [pvarCat, pvarX_obj, pvarY_obj, pvar_g_XY],
        lhs: ComposeMorph(
            Var("g_XY_pv"),                                     // g: X -> Y
            IdentityMorph(Var("X_obj_pv"), Var("CAT_pv")),      // id_X: X -> X
            Var("CAT_pv"),                                      // Implicit cat
            Var("X_obj_pv"),                                    // Implicit dom(id_X)
            Var("X_obj_pv"),                                    // Implicit cod(id_X) = dom(g_XY)
            Var("Y_obj_pv")                                     // Implicit cod(g_XY)
        ),
        rhs: Var("g_XY_pv")
    });


    // Rule 2: id o f = f. (Standard notation: f ; g, where g is id)
    // ComposeMorph(IdentityMorph(Y,C), f)
    // f has type Hom C X Y.
    // IdentityMorph(Y,C) has type Hom C Y Y.
    // Result is Hom C X Y.
    // Implicits for ComposeMorph(id_Y, f, C, X, Y, Y)
    const pvar_f_XY = { name: "f_XY_pv", type: HomTerm(Var("CAT_pv"), Var("X_obj_pv"), Var("Y_obj_pv")) };
    addRewriteRule({
        name: "comp_idY_f_fwd", // id_Y after f
        patternVars: [pvarCat, pvarX_obj, pvarY_obj, pvar_f_XY],
        lhs: ComposeMorph(
            IdentityMorph(Var("Y_obj_pv"), Var("CAT_pv")),      // id_Y: Y -> Y
            Var("f_XY_pv"),                                     // f: X -> Y
            Var("CAT_pv"),                                      // Implicit cat
            Var("X_obj_pv"),                                    // Implicit dom(f_XY)
            Var("Y_obj_pv"),                                    // Implicit cod(f_XY) = dom(id_Y)
            Var("Y_obj_pv")                                     // Implicit cod(id_Y)
        ),
        rhs: Var("f_XY_pv")
    });
}

export function resetMyLambdaPi_Emdash() { // If needed for more modular testing later
    resetMyLambdaPi();
}
