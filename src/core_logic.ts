import { Term, Context, PatternVarDecl, Substitution, UnifyResult, Hole, App, Lam, Pi, Var, ObjTerm, HomTerm, Type, CatTerm, MkCat_, IdentityMorph, ComposeMorph } from './core_types';
import { getTermRef, consoleLog, globalDefs, userRewriteRules, addConstraint, constraints, emptyCtx, extendCtx, isKernelConstantSymbolStructurally, isEmdashUnificationInjectiveStructurally, userUnificationRules, freshVarName, freshHoleName } from './core_context_globals';
// Removed forward import: import { matchPattern, applySubst } from './core_elaboration'; 

export const MAX_WHNF_ITERATIONS = 1000; 
export let whnfIterationCount = 0; 
export const MAX_STACK_DEPTH = 200; 

// Forward declaration for printTerm - it will be in core_elaboration
declare function printTerm(term: Term, boundVarsMap?: Map<string, string>, stackDepth?: number): string;
// Forward declaration for isPatternVarName - it will be in core_elaboration
declare function isPatternVarName(name: string, patternVarDecls: PatternVarDecl[]): boolean;
// Forward declaration for matchPattern and applySubst - they will be in core_elaboration
declare function matchPattern(
    pattern: Term, termToMatch: Term, ctx: Context,
    patternVarDecls: PatternVarDecl[],
    currentSubst?: Substitution, stackDepth?: number
): Substitution | null;
declare function applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[]): Term;


export function areStructurallyEqualNoWhnf(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Enter: t1 = ${printTerm(t1)}, t2 = ${printTerm(t2)}`);
    if (depth > MAX_STACK_DEPTH) throw new Error(`Structural Equality check depth exceeded (areStructurallyEqualNoWhnf depth: ${depth})`);
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
            
            let paramTypeForCtx_Lam_Struct: Term;
            if (rt1._isAnnotated) { 
                if (!rt1.paramType || !lam2.paramType || !areStructurallyEqualNoWhnf(rt1.paramType, lam2.paramType, ctx, depth + 1)) {
                    consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: annotated param types not equal.`);
                    result = false; break;
                }
                consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: annotated param types are equal.`);
                paramTypeForCtx_Lam_Struct = getTermRef(rt1.paramType!); 
            } else {
                paramTypeForCtx_Lam_Struct = rt1.paramType ? getTermRef(rt1.paramType) : Hole(freshHoleName()+"_structEq_unannot_lam_param");
            }

            const freshVName_Lam_Struct = rt1.paramName; 
            const freshV_Lam_Struct = Var(freshVName_Lam_Struct);
            const extendedCtx_Lam_Struct = extendCtx(ctx, freshVName_Lam_Struct, paramTypeForCtx_Lam_Struct);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: comparing bodies with var ${freshVName_Lam_Struct} in extended context.`);
            result = areStructurallyEqualNoWhnf(rt1.body(freshV_Lam_Struct), lam2.body(freshV_Lam_Struct), extendedCtx_Lam_Struct, depth + 1);
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
            const freshVName_Pi_Struct = rt1.paramName; 
            const freshV_Pi_Struct = Var(freshVName_Pi_Struct);
            const extendedCtx_Pi_Struct = extendCtx(ctx, freshVName_Pi_Struct, getTermRef(rt1.paramType)); 
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Pi: comparing body types with var ${freshVName_Pi_Struct} in extended context.`);
            result = areStructurallyEqualNoWhnf(rt1.bodyType(freshV_Pi_Struct), pi2.bodyType(freshV_Pi_Struct), extendedCtx_Pi_Struct, depth + 1);
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

export function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    consoleLog(`[TRACE whnf (${stackDepth})] Enter: term = ${printTerm(term)}`);
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`WHNF stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    
    let current = term;

    for (let i = 0; i < MAX_WHNF_ITERATIONS; i++) {
        consoleLog(`[TRACE whnf (${stackDepth})] Iteration ${i}, current = ${printTerm(current)}`);
        let changedInThisPass = false;
        const termAtStartOfOuterPass = current; 

        const dereffedCurrent = getTermRef(current);
        if (dereffedCurrent !== current) {
            consoleLog(`[TRACE whnf (${stackDepth})] Hole dereferenced: ${printTerm(current)} -> ${printTerm(dereffedCurrent)}`);
            current = dereffedCurrent;
            changedInThisPass = true; 
        }
        
        const termBeforeInnerReductions = current;

        consoleLog(`[TRACE whnf (${stackDepth})] Checking user rewrite rules for: ${printTerm(current)} (isKernelConstant: ${isKernelConstantSymbolStructurally(current)})`);
        if (!isKernelConstantSymbolStructurally(current)) {
            for (const rule of userRewriteRules) {
                consoleLog(`[TRACE whnf (${stackDepth})] Trying rule: ${rule.name} on ${printTerm(current)}`);
                const termBeforeThisRuleAttempt = current; 
                const subst = matchPattern(rule.lhs, termBeforeThisRuleAttempt, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    consoleLog(`[TRACE whnf (${stackDepth})] Rule ${rule.name} matched against ${printTerm(termBeforeThisRuleAttempt)}.`);
                    const rhsApplied = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                    consoleLog(`[TRACE whnf (${stackDepth})] RHS after subst for rule ${rule.name}: ${printTerm(rhsApplied)}.`);

                    if (areStructurallyEqualNoWhnf(rhsApplied, termBeforeThisRuleAttempt, ctx, stackDepth + 1)) {
                        consoleLog(`[TRACE whnf (${stackDepth})] Rule ${rule.name} result is structurally identical to matched term. No change by this specific rule. Matched: ${printTerm(termBeforeThisRuleAttempt)}, RHS: ${printTerm(rhsApplied)}.`);
                    } else {
                        consoleLog(`[TRACE whnf (${stackDepth})] Rule ${rule.name} resulted in structural change: ${printTerm(termBeforeThisRuleAttempt)} -> ${printTerm(rhsApplied)}.`);
                        current = rhsApplied; 
                        changedInThisPass = true;
                        break; 
                    }
                }
            }
            if (changedInThisPass) {
                consoleLog(`[TRACE whnf (${stackDepth})] A user rule caused structural change. Continuing whnf loop's next iteration. New current for whnf: ${printTerm(current)}`);
                continue; 
            }
        }

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
    const current = getTermRef(headReduced); 

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
            if (current.tag !== 'ComposeMorph') return normalize(current, ctx, stackDepth + 1);
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
            const normLamParamType = (currentLam._isAnnotated && currentLam.paramType) 
                                     ? normalize(currentLam.paramType, ctx, stackDepth + 1) 
                                     : undefined; 

            const newLam = Lam(currentLam.paramName, normLamParamType, 
                (v_arg: Term) => {
                    const paramTypeForBodyCtx = normLamParamType || 
                                                (currentLam.paramType ? getTermRef(currentLam.paramType) : Hole(freshHoleName()+"_norm_lam_body"));
                    let bodyCtx = ctx;
                    if (v_arg.tag === 'Var') { bodyCtx = extendCtx(ctx, v_arg.name, paramTypeForBodyCtx); }
                    return normalize(currentLam.body(v_arg), bodyCtx, stackDepth + 1);
                });
            (newLam as Term & {tag:'Lam'})._isAnnotated = currentLam._isAnnotated; 
            if(normLamParamType) (newLam as Term & {tag:'Lam'}).paramType = normLamParamType; 
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
            
            let paramTypeForCtx_Lam: Term;
            if (rt1._isAnnotated) { 
                if (!rt1.paramType || !lam2.paramType || !areEqual(rt1.paramType, lam2.paramType, ctx, depth + 1)) {
                    consoleLog(`[TRACE areEqual (${depth})] Lam: annotated param types not equal.`);
                    result = false; break;
                }
                consoleLog(`[TRACE areEqual (${depth})] Lam: annotated param types are equal.`);
                paramTypeForCtx_Lam = getTermRef(rt1.paramType!); 
            } else {
                paramTypeForCtx_Lam = rt1.paramType ? getTermRef(rt1.paramType) : Hole(freshHoleName()+"_areEqual_unannot_lam_param");
            }

            const freshVName_Lam = rt1.paramName; 
            const freshV_Lam = Var(freshVName_Lam);
            const extendedCtx_Lam = extendCtx(ctx, freshVName_Lam, paramTypeForCtx_Lam);
            consoleLog(`[TRACE areEqual (${depth})] Lam: comparing bodies with var ${freshVName_Lam} in extended context.`);
            result = areEqual(rt1.body(freshV_Lam), lam2.body(freshV_Lam), extendedCtx_Lam, depth + 1);
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
            const freshVName_Pi = rt1.paramName; 
            const freshV_Pi = Var(freshVName_Pi);
            const extendedCtx_Pi = extendCtx(ctx, freshVName_Pi, getTermRef(rt1.paramType)); 
            consoleLog(`[TRACE areEqual (${depth})] Pi: comparing body types with var ${freshVName_Pi} in extended context.`);
            result = areEqual(rt1.bodyType(freshV_Pi), pi2.bodyType(freshV_Pi), extendedCtx_Pi, depth + 1);
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
    if (depth > MAX_STACK_DEPTH * 2) { 
        console.warn(`termContainsHole depth exceeded for hole ${holeId} in ${printTerm(term)}`);
        return true; 
    }
    const current = getTermRef(term);

    switch (current.tag) {
        case 'Hole': return current.id === holeId;
        case 'Type': case 'Var': case 'CatTerm': return false;
        default: {
            if (current.tag === 'App') {
                return termContainsHole(current.func, holeId, visited, depth + 1) ||
                       termContainsHole(current.arg, holeId, visited, depth + 1);
            } else if (current.tag === 'Lam') {
                if (current.paramType && termContainsHole(current.paramType, holeId, visited, depth + 1)) return true;
                const freshV = Var(freshVarName("_occ_check")); 
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
            return false; 
        }
    }
}

export function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
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
            madeProgress = true; 
        }
        if (argStatus !== UnifyResult.Solved) {
            allSubSolved = false; 
        }
    }

    if (allSubSolved) {
        if(areEqual(parentRt1, parentRt2, ctx, depth +1)) return UnifyResult.Solved;
        return UnifyResult.Progress; 
    }
    
    if (madeProgress) return UnifyResult.Progress; 
    
    return UnifyResult.Progress;
}

export function unify(t1: Term, t2: Term, ctx: Context, depth = 0): UnifyResult {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Unification stack depth exceeded (Unify depth: ${depth}, ${printTerm(t1)} vs ${printTerm(t2)})`);
    
    const rt1_orig = getTermRef(t1);
    const rt2_orig = getTermRef(t2);

    if (rt1_orig === rt2_orig && rt1_orig.tag !== 'Hole') return UnifyResult.Solved;

    if (rt1_orig.tag === 'Hole') {
        if (unifyHole(rt1_orig, whnf(rt2_orig, ctx, depth + 1), ctx, depth + 1)) return UnifyResult.Solved;
        return tryUnificationRules(rt1_orig, rt2_orig, ctx, depth + 1);
    }
    if (rt2_orig.tag === 'Hole') {
        if (unifyHole(rt2_orig, whnf(rt1_orig, ctx, depth + 1), ctx, depth + 1)) return UnifyResult.Solved;
        return tryUnificationRules(rt1_orig, rt2_orig, ctx, depth + 1);
    }

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
        }
        const argStatus = unifyArgs(args1, args2, ctx, depth, rt1_orig, rt2_orig);
        
        if (argStatus === UnifyResult.Solved || argStatus === UnifyResult.Progress) {
            return argStatus;
        }
    }

    const rt1_whnf = whnf(rt1_orig, ctx, depth + 1);
    const rt2_whnf = whnf(rt2_orig, ctx, depth + 1);
    
    if (rt1_whnf === rt2_whnf && rt1_whnf.tag !== 'Hole') return UnifyResult.Solved; 
    if (areEqual(rt1_whnf, rt2_whnf, ctx, depth + 1)) return UnifyResult.Solved;

    const rt1_final = getTermRef(rt1_whnf);
    const rt2_final = getTermRef(rt2_whnf);

    if (rt1_final.tag === 'Hole') {
        if (unifyHole(rt1_final, rt2_final, ctx, depth + 1)) return UnifyResult.Solved;
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }
    if (rt2_final.tag === 'Hole') {
        if (unifyHole(rt2_final, rt1_final, ctx, depth + 1)) return UnifyResult.Solved;
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }

    if (rt1_final.tag !== rt2_final.tag) {
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }

    if (isEmdashUnificationInjectiveStructurally(rt1_final.tag)) {
        let args1_w: (Term|undefined)[] = [];
        let args2_w: (Term|undefined)[] = [];
        switch (rt1_final.tag) {
            case 'CatTerm': return UnifyResult.Solved; 
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
            default: 
                 return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        }
        const argStatus_w = unifyArgs(args1_w, args2_w, ctx, depth, rt1_final, rt2_final);
        if (argStatus_w === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        return argStatus_w; 
    }

    switch (rt1_final.tag) {
        case 'Type': return UnifyResult.Solved; 
        case 'Var': 
            return rt1_final.name === (rt2_final as Term & {tag:'Var'}).name ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        case 'App': {
            const app2_final = rt2_final as Term & {tag:'App'};
            const funcUnifyStatus = unify(rt1_final.func, app2_final.func, ctx, depth + 1);
            if (funcUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            const argUnifyStatus = unify(rt1_final.arg, app2_final.arg, ctx, depth + 1);
            if (argUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            if (funcUnifyStatus === UnifyResult.Solved && argUnifyStatus === UnifyResult.Solved) {
                if (areEqual(rt1_final, rt2_final, ctx, depth + 1)) return UnifyResult.Solved;
                return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1); 
            }
            return UnifyResult.Progress; 
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

export function collectPatternVars(term: Term, patternVarDecls: PatternVarDecl[], collectedVars: Set<string>, visited: Set<Term> = new Set()): void {
    const current = getTermRef(term);
    if (visited.has(current) && current.tag !== 'Var' && current.tag !== 'Hole') return; 
    visited.add(current);

    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        collectedVars.add(current.name);
    } else if (current.tag === 'Hole' && isPatternVarName(current.id, patternVarDecls)) { 
        collectedVars.add(current.id);
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

export function applyAndAddRuleConstraints(rule: {lhsPattern1: Term, lhsPattern2: Term, patternVars: PatternVarDecl[], rhsNewConstraints: Array<{t1:Term, t2:Term}>, name: string}, subst: Substitution, ctx: Context): void {
    const lhsVars = new Set<string>();
    collectPatternVars(rule.lhsPattern1, rule.patternVars, lhsVars, new Set<Term>());
    collectPatternVars(rule.lhsPattern2, rule.patternVars, lhsVars, new Set<Term>());

    const finalSubst = new Map(subst); 

    for (const pVarDecl of rule.patternVars) {
        const pVarName = pVarDecl.name;
        if (pVarName === '_') continue; 

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
        let subst1 = matchPattern(rule.lhsPattern1, t1, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t2, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) {
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }

        subst1 = matchPattern(rule.lhsPattern1, t2, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t1, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) {
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }
    }
    return UnifyResult.Failed; 
}

export function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("solveConstraints stack depth exceeded");
    let changedInOuterLoop = true;
    let iterations = 0;
    const maxIterations = (constraints.length * constraints.length + userUnificationRules.length * 2 + 50) * 50 + 200;


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
                    console.warn(`Unification failed permanently for: ${printTerm(c_t1_current_ref)} === ${printTerm(c_t2_current_ref)} (orig: ${constraint.origin || 'unknown'})`);
                    return false; 
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
    }
    
    for (const constraint of constraints) {
        if (!areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
            console.warn(`Final check failed for constraint: ${printTerm(getTermRef(constraint.t1))} === ${printTerm(getTermRef(constraint.t2))} (orig: ${constraint.origin || 'unknown'})`);
            return false;
        }
    }
    return constraints.length === 0;
} 