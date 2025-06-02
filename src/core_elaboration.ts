import {
    Term, Context, PatternVarDecl, Substitution, ElaborationResult, Icit, Binding,
    Hole, Var, App, Lam, Pi, Type, CatTerm, ObjTerm, HomTerm, MkCat_,
    IdentityMorph, ComposeMorph, FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm, NatTransComponentTerm,
    HomCovFunctorIdentity, SetTerm,
    BaseTerm
} from './core_types';
import {
    emptyCtx, extendCtx, lookupCtx, globalDefs, addConstraint, getTermRef,
    freshHoleName, freshVarName, consoleLog,
    resetHoleId,
    resetVarId,
    constraints,
    cloneTerm
} from './core_context_globals';
import { whnf, normalize, areEqual, solveConstraints, MAX_STACK_DEPTH } from './core_logic';
import { KERNEL_IMPLICIT_SPECS } from './core_kernel_metadata';

// Use Extract to get the specific type from the BaseTerm union for casting
type IdentityMorphType = Extract<BaseTerm, { tag: 'IdentityMorph' }>;
type ComposeMorphType = Extract<BaseTerm, { tag: 'ComposeMorph' }>;
// Emdash Phase 2: Functors and Natural Transformations
type FunctorCategoryTermType = Extract<BaseTerm, { tag: 'FunctorCategoryTerm' }>;
type FMap0TermType = Extract<BaseTerm, { tag: 'FMap0Term' }>;
type FMap1TermType = Extract<BaseTerm, { tag: 'FMap1Term' }>;
type NatTransTypeTermType = Extract<BaseTerm, { tag: 'NatTransTypeTerm' }>;
type NatTransComponentTermType = Extract<BaseTerm, { tag: 'NatTransComponentTerm' }>;

export interface ElaborationOptions {
    normalizeResultTerm?: boolean;
}

export function ensureKernelImplicitsPresent(term: Term): Term {
    const originalTermTag = term.tag;
    const specs = [...KERNEL_IMPLICIT_SPECS];

    for (const spec of specs) {
        if (originalTermTag === spec.tag) {
            const specificTerm = term as Term & { [key: string]: any };
            for (const fieldName of spec.fields as Array<keyof Term>) {
                if (specificTerm[fieldName as string] === undefined) {
                    let baseHint = spec.tag.toLowerCase().replace(/morph|term/g, '').replace(/_/g, '');
                    const fieldHint = (fieldName as string).replace('_IMPLICIT', '').toLowerCase();

                    let dynamicHintPart = "";
                    if (spec.tag === 'IdentityMorph' && specificTerm.obj) {
                        const idObj = getTermRef(specificTerm.obj);
                        if (idObj.tag === 'Var') dynamicHintPart = `_${idObj.name}`;
                        else if (idObj.tag === 'Hole') dynamicHintPart = `_${idObj.id.replace("?","h")}`;
                    }
                    // TODO: Could add similar hints for ComposeMorph based on g or f if simple and useful

                    specificTerm[fieldName as string] = Hole(freshHoleName() + `_k_${baseHint}${dynamicHintPart}_${fieldHint}`);
                }
            }
            break;
        }
    }
    return term;
}

// Result type for infer, to include the elaborated term
export interface InferResult {
    elaboratedTerm: Term;
    type: Term;
}

// Helper function to insert implicit applications
// Based on Haskell's insert' and parts of insert
function insertImplicitApps(ctx: Context, term: Term, type: Term, stackDepth: number, unConditional: boolean = false): { term: Term, type: Term, progress?: boolean } {
    let currentTerm = term;
    let currentType = whnf(type, ctx, stackDepth + 1);

    // Do not insert if the term itself is an implicit lambda
    // and we are not in unconditional mode
    const termRef = getTermRef(currentTerm);
    // if (termRef.tag === 'Lam' && termRef.icit === Icit.Impl && !unConditional) {
    //     return { term: currentTerm, type: currentType };
    // }

    let progress = false;
    while (currentType.tag === 'Pi' && currentType.icit === Icit.Impl) {
        //  console.log('insertImplicitApps>>', {unConditional}, printTerm(currentTerm), ' ::::: ', printTerm(currentType));

        const implHole = Hole(freshHoleName() + "_auto_inserted_impl_arg");
        if (currentType.paramType) {
            (implHole as Term & {tag:'Hole'}).elaboratedType = currentType.paramType;
        }
        currentTerm = App(currentTerm, implHole, Icit.Impl);
        currentType = whnf(currentType.bodyType(implHole), ctx, stackDepth + 1);
        progress = true;
        // console.log('insertImplicitApps<<', printTerm(currentTerm), ' ::::: ', printTerm(currentType));
    }
    return { term: currentTerm, type: currentType, progress };
}


export function infer(ctx: Context, term: Term, stackDepth: number = 0, isSubElaboration: boolean = false): InferResult {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Infer stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);

    const originalTerm = term;
    const termWithKernelImplicits = ensureKernelImplicitsPresent(originalTerm);
    let current = getTermRef(termWithKernelImplicits); // Use let for potential re-assignment



    if (current.tag === 'Var') {
        const localBinding = lookupCtx(ctx, current.name);
        if (localBinding) {
            if (localBinding.definition) {
                // console.log('INFER>>', current.name, localBinding.definition);
                return { elaboratedTerm: localBinding.definition, type: localBinding.type };
            } else {
                return { elaboratedTerm: current, type: localBinding.type };
            }
        }

        const gdef = globalDefs.get(current.name);
        if (gdef) return { elaboratedTerm: current, type: gdef.type };

        if (!localBinding) {
            if ((current.name.startsWith("_occ_check_") || current.name.startsWith("v_param_check"))) { // Check for occ_check or similar placeholders
                // These are special placeholders from termContainsHole or similar operations,
                // not meant for full inference that requires a context-defined type.
                // Give them a fresh hole type to avoid "Unbound variable" and allow structural checks to proceed.
                consoleLog(`[Infer Special Placeholder] Detected placeholder var: ${current.name}`);
                const placeholderType = Hole("_type_of_placeholder_" + current.name.replace(/[?$]/g, ""));
                (placeholderType as Term & {tag:'Hole'}).elaboratedType = Type(); // It's a type for some term
                return { elaboratedTerm: current, type: placeholderType };
            }
     
            throw new Error(`Unbound variable: ${current.name} in context [${ctx.map(b => b.name).join(', ')}]`);
        }
        return { elaboratedTerm: current, type: localBinding.type }; // Defensive
    }

    switch (current.tag) {
        case 'Type': return { elaboratedTerm: current, type: Type() };
        case 'Hole': {
            if (current.elaboratedType) return { elaboratedTerm: current, type: getTermRef(current.elaboratedType) };
            const newTypeForHole = Hole(freshHoleName() + "_type_of_" + current.id.replace("?", "h"));
            current.elaboratedType = newTypeForHole;
            return { elaboratedTerm: current, type: newTypeForHole };
        }
        case 'App': {
            const appNode = current;
            // Infer type of function part
            let { elaboratedTerm: inferredFuncElab, type: inferredFuncType } = infer(ctx, appNode.func, stackDepth + 1, isSubElaboration);

            // Insert implicit applications if the current application is explicit
            let funcAfterImplicits = inferredFuncElab;
            let typeFAfterImplicits = whnf(inferredFuncType, ctx, stackDepth + 1);
            let insertedProgressByOuter = false; 

            if (appNode.icit === Icit.Expl) {
                const inserted = insertImplicitApps(ctx, funcAfterImplicits, typeFAfterImplicits, stackDepth + 1, true);
                funcAfterImplicits = inserted.term;
                typeFAfterImplicits = inserted.type; 
                insertedProgressByOuter = inserted.progress || false;
            }
            
            let expectedParamTypeFromPi: Term;
            let bodyTypeFnFromPi: (argVal: Term) => Term;
            const applicationIcit = appNode.icit;

            const whnfOfFuncTypeAfterImplicits = whnf(typeFAfterImplicits, ctx, stackDepth + 1);
            let funcTypeWasRefinedToPi = false;

            if (whnfOfFuncTypeAfterImplicits.tag === 'Pi' && whnfOfFuncTypeAfterImplicits.icit === applicationIcit) {
                expectedParamTypeFromPi = whnfOfFuncTypeAfterImplicits.paramType;
                bodyTypeFnFromPi = whnfOfFuncTypeAfterImplicits.bodyType;
            } else if (whnfOfFuncTypeAfterImplicits.tag === 'Pi' && whnfOfFuncTypeAfterImplicits.icit !== applicationIcit) {
                throw new Error(`Type error in App (${applicationIcit === Icit.Expl ? "explicit" : "implicit"}): function ${printTerm(funcAfterImplicits)} of type ${printTerm(whnfOfFuncTypeAfterImplicits)} expects a ${whnfOfFuncTypeAfterImplicits.icit === Icit.Expl ? "explicit" : "implicit"} argument, but an ${applicationIcit === Icit.Expl ? "explicit" : "implicit"} one was provided for ${printTerm(appNode.arg)}.`);
            } else {
                funcTypeWasRefinedToPi = true; // Mark that we are refining the function type
                const freshPiParamName = freshVarName("pi_param_app");
                const paramTypeHole = Hole(freshHoleName() + "_app_paramT_infer");
                (paramTypeHole as Term & {tag:'Hole'}).elaboratedType = Type();
                const bodyTypeHole = Hole(freshHoleName() + "_app_bodyT_infer");
                (bodyTypeHole as Term & {tag:'Hole'}).elaboratedType = Type();
                const targetPiType = Pi(freshPiParamName, applicationIcit, paramTypeHole, (_arg: Term) => bodyTypeHole);
                
                addConstraint(typeFAfterImplicits, targetPiType, `App: func ${printTerm(funcAfterImplicits)} type needs to be Pi for arg ${printTerm(appNode.arg)}`);
                consoleLog(`INFER>>ADDCONSTRAINT_REFINE_HIGHER_ORDER_TYPE for App: ${printTerm(typeFAfterImplicits)} === ${printTerm(targetPiType)}`);
                solveConstraints(ctx, stackDepth + 1)

                expectedParamTypeFromPi = paramTypeHole;
                bodyTypeFnFromPi = (_argVal: Term) => bodyTypeHole; 
            }

            const elaboratedArg = check(ctx, appNode.arg, expectedParamTypeFromPi, stackDepth + 1, isSubElaboration);
            
            // if (true /*insertedProgressByOuter || funcTypeWasRefinedToPi*/) { // this condition is too restrictive and will allow errors
                // solveConstraints HERE was important to prevent error // could move it to end of `check` function, apparently not affecting perf
                // if (!solveConstraints(ctx, stackDepth + 1)) {
                //     const fc = constraints.find(c => !areEqual(getTermRef(c.t1), getTermRef(c.t2), ctx, 0));
                //     let fcMsg = "Unknown constraint";
                //     if (fc) {
                //         fcMsg = `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin || 'unspecified'})`;
                //     }
                //     console.error(`Type error during App inference: Could not solve constraints after checking argument. Approx failing: ${fcMsg}. Func: ${printTerm(funcAfterImplicits)}, Arg: ${printTerm(appNode.arg)}, Expected Param Type for Arg: ${printTerm(expectedParamTypeFromPi)}`);
                //     throw new Error(`Type error during App inference: Could not solve constraints after checking argument. Approx failing: ${fcMsg}.`);
                // }
            // }

            const finalFuncPart = getTermRef(funcAfterImplicits);
            const finalArgPart = getTermRef(elaboratedArg); 
            
            const finalAppTerm = App(finalFuncPart, finalArgPart, applicationIcit);
            const resultType = whnf(bodyTypeFnFromPi(finalArgPart), ctx, stackDepth + 1);

            return { elaboratedTerm: finalAppTerm, type: resultType };
        }
        case 'Lam': {
            const lamNode = current;
            let actualParamType: Term;
            let wasAnnotated = lamNode._isAnnotated;
            let originalParamType = lamNode.paramType;

            if (lamNode._isAnnotated && lamNode.paramType) {
                actualParamType = check(ctx, lamNode.paramType, Type(), stackDepth + 1, isSubElaboration);
            } else {
                actualParamType = Hole(freshHoleName() + "_lam_" + lamNode.paramName + "_paramT_infer_");
                (actualParamType as Term & {tag:'Hole'}).elaboratedType = Type();
                lamNode.paramType = actualParamType; // Temporarily annotate
                lamNode._isAnnotated = true;
            }
            
            const piType = Pi(
                lamNode.paramName,
                lamNode.icit,
                actualParamType,
                (pi_body_argument_term: Term): Term => {
                    const body_infer_ctx = extendCtx(ctx, lamNode.paramName, actualParamType, lamNode.icit, pi_body_argument_term);
                    const lambda_body_structure = lamNode.body(Var(lamNode.paramName, true)); 
                    
                    let { elaboratedTerm: inferredBodyElab, type: inferredBodyType } = infer(body_infer_ctx, lambda_body_structure, stackDepth + 1, true);
                    
                    const insertedBody = insertImplicitApps(body_infer_ctx, inferredBodyElab, inferredBodyType, stackDepth + 1);
                    
                    return insertedBody.type; 
                }
            );

            const elaboratedLam = Lam(
                lamNode.paramName,
                lamNode.icit,
                getTermRef(actualParamType),
                (v: Term) => {
                    const bodyInferCtx = extendCtx(ctx, lamNode.paramName, getTermRef(actualParamType), lamNode.icit, v);
                    const bodyTermRaw = lamNode.body(Var(lamNode.paramName, true));
                    let { elaboratedTerm: inferredBodyElab, type: inferredBodyType } = infer(bodyInferCtx, bodyTermRaw, stackDepth +1, true);
                    const insertedBody = insertImplicitApps(bodyInferCtx, inferredBodyElab, inferredBodyType, stackDepth + 1);
                    return insertedBody.term;
                }
            );
            (elaboratedLam as Term & {tag: 'Lam'})._isAnnotated = true;

            if (!wasAnnotated && originalTerm === lamNode && originalTerm.tag === 'Lam') {
                originalTerm.paramType = originalParamType; 
                originalTerm._isAnnotated = false;
            } else if (lamNode.tag === 'Lam' && !wasAnnotated) { // Current was mutated
                lamNode.paramType = originalParamType;
                lamNode._isAnnotated = false;
            }

            return { elaboratedTerm: elaboratedLam, type: piType };
        }
        case 'Pi': {
            const piNode = current;
            const elaboratedParamType = check(ctx, piNode.paramType, Type(), stackDepth + 1, isSubElaboration);
            const extendedCtx = extendCtx(ctx, piNode.paramName, elaboratedParamType, piNode.icit);
            const bodyTypeInstance = piNode.bodyType(Var(piNode.paramName, true));
            const elaboratedBodyTypeResult = check(extendedCtx, bodyTypeInstance, Type(), stackDepth + 1, true); 
            const finalPi = Pi(piNode.paramName, piNode.icit, elaboratedParamType, (v: Term) => {
                const bodyCtx = extendCtx(ctx, piNode.paramName, elaboratedParamType, piNode.icit, v);
                const piNodeBodyType = piNode.bodyType(Var(piNode.paramName, true));
                return check(bodyCtx, piNodeBodyType, Type(), stackDepth+1, true);
            });
            return { elaboratedTerm: finalPi, type: Type() };
        }
        case 'CatTerm': return { elaboratedTerm: current, type: Type() };
        case 'ObjTerm': {
            const elabCat = check(ctx, current.cat, CatTerm(), stackDepth + 1, isSubElaboration);
            return { elaboratedTerm: ObjTerm(elabCat), type: Type() };
        }
        case 'HomTerm': {
            const elabCat = check(ctx, current.cat, CatTerm(), stackDepth + 1, isSubElaboration);
            const catForHom = getTermRef(elabCat);
            const elabDom = check(ctx, current.dom, ObjTerm(catForHom), stackDepth + 1, isSubElaboration);
            const elabCod = check(ctx, current.cod, ObjTerm(catForHom), stackDepth + 1, isSubElaboration);
            return { elaboratedTerm: HomTerm(elabCat, elabDom, elabCod), type: Type() };
        }
        case 'MkCat_': {
            const elabObjR = check(ctx, current.objRepresentation, Type(), stackDepth + 1, isSubElaboration);
            const O_repr_norm = getTermRef(elabObjR);

            const expected_H_type = Pi("X", Icit.Expl, O_repr_norm, _X => Pi("Y", Icit.Expl, O_repr_norm, _Y => Type()));
            const elabHomR = check(ctx, current.homRepresentation, expected_H_type, stackDepth + 1, isSubElaboration);
            const H_repr_func_norm = getTermRef(elabHomR);

            const type_of_hom_X_Y = (X_val: Term, Y_val: Term) => App(App(H_repr_func_norm, X_val, Icit.Expl), Y_val, Icit.Expl);

            const expected_C_type =
                Pi("Xobj", Icit.Expl, O_repr_norm, Xobj_term =>
                Pi("Yobj", Icit.Expl, O_repr_norm, Yobj_term =>
                Pi("Zobj", Icit.Expl, O_repr_norm, Zobj_term =>
                Pi("gmorph", Icit.Expl, type_of_hom_X_Y(Yobj_term, Zobj_term), _gmorph_term =>
                Pi("fmorph", Icit.Expl, type_of_hom_X_Y(Xobj_term, Yobj_term), _fmorph_term =>
                type_of_hom_X_Y(Xobj_term, Zobj_term)
                )))));
            const elabCompI = check(ctx, current.composeImplementation, expected_C_type, stackDepth + 1, isSubElaboration);
            const finalMkCat = MkCat_(elabObjR, elabHomR, elabCompI);
            return { elaboratedTerm: finalMkCat, type: CatTerm() };
        }
        case 'IdentityMorph': {
            const idTerm = current as Term & IdentityMorphType;

            const elabCatImplicit = check(ctx, idTerm.cat_IMPLICIT!, CatTerm(), stackDepth + 1, isSubElaboration);

            const objInferResult = infer(ctx, idTerm.obj, stackDepth + 1, isSubElaboration);
            addConstraint(objInferResult.type, ObjTerm(elabCatImplicit), `Object ${printTerm(idTerm.obj)} in IdentityMorph must be of type Obj(${printTerm(elabCatImplicit)})`);
            
            if (!solveConstraints(ctx, stackDepth + 1)) {
                 console.warn(`[Infer IdentityMorph] Could not solve constraints after processing object and category for ${printTerm(idTerm)}`);
            }

            const finalIdMorph = IdentityMorph(objInferResult.elaboratedTerm, getTermRef(elabCatImplicit));
            return { elaboratedTerm: finalIdMorph, type: HomTerm(getTermRef(elabCatImplicit), objInferResult.elaboratedTerm, objInferResult.elaboratedTerm) };
        }
        case 'ComposeMorph': {
            const compTerm = current as Term & ComposeMorphType;

            const elabCatImplicit = check(ctx, compTerm.cat_IMPLICIT!, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabObjXImplicit = check(ctx, compTerm.objX_IMPLICIT!, ObjTerm(elabCatImplicit), stackDepth + 1, isSubElaboration);
            const elabObjYImplicit = check(ctx, compTerm.objY_IMPLICIT!, ObjTerm(elabCatImplicit), stackDepth + 1, isSubElaboration);
            const elabObjZImplicit = check(ctx, compTerm.objZ_IMPLICIT!, ObjTerm(elabCatImplicit), stackDepth + 1, isSubElaboration);
            
            if (!solveConstraints(ctx, stackDepth + 1)) {
                console.warn(`[Infer ComposeMorph] Could not solve constraints after processing implicits for ${printTerm(compTerm)}`);
            }

            const catArg = getTermRef(elabCatImplicit);
            const XArg = getTermRef(elabObjXImplicit);
            const YArg = getTermRef(elabObjYImplicit);
            const ZArg = getTermRef(elabObjZImplicit);

            const elabF = check(ctx, compTerm.f, HomTerm(catArg, XArg, YArg), stackDepth + 1, isSubElaboration);
            const elabG = check(ctx, compTerm.g, HomTerm(catArg, YArg, ZArg), stackDepth + 1, isSubElaboration);
            
            if (!solveConstraints(ctx, stackDepth + 1)) {
                console.warn(`[Infer ComposeMorph] Could not solve constraints after processing f and g for ${printTerm(compTerm)}`);
            }

            const finalComp = ComposeMorph(elabG, elabF, catArg, XArg, YArg, ZArg);
            return { elaboratedTerm: finalComp, type: HomTerm(catArg, XArg, ZArg) };
        }
        case 'FunctorCategoryTerm': {
            const fcTerm = current as Term & FunctorCategoryTermType;
            const elabDomainCat = check(ctx, fcTerm.domainCat, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabCodomainCat = check(ctx, fcTerm.codomainCat, CatTerm(), stackDepth + 1, isSubElaboration);
            return { elaboratedTerm: FunctorCategoryTerm(elabDomainCat, elabCodomainCat), type: CatTerm() };
        }
        case 'FMap0Term': {
            const fm0Term = current as Term & FMap0TermType;
            const elabCatA = check(ctx, fm0Term.catA_IMPLICIT!, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabCatB = check(ctx, fm0Term.catB_IMPLICIT!, CatTerm(), stackDepth + 1, isSubElaboration);
            
            const expectedFunctorType = ObjTerm(FunctorCategoryTerm(elabCatA, elabCatB));
            const elabFunctor = check(ctx, fm0Term.functor, expectedFunctorType, stackDepth + 1, isSubElaboration);
            
            const expectedObjectType = ObjTerm(elabCatA);
            const elabObjectX = check(ctx, fm0Term.objectX, expectedObjectType, stackDepth + 1, isSubElaboration);
            
            const finalFMap0 = FMap0Term(elabFunctor, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB));
            return { elaboratedTerm: finalFMap0, type: ObjTerm(getTermRef(elabCatB)) };
        }
        case 'FMap1Term': {
            const fm1Term = current as Term & FMap1TermType;
            const elabCatA = check(ctx, fm1Term.catA_IMPLICIT!, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabCatB = check(ctx, fm1Term.catB_IMPLICIT!, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabObjX_A = check(ctx, fm1Term.objX_A_IMPLICIT!, ObjTerm(elabCatA), stackDepth + 1, isSubElaboration);
            const elabObjY_A = check(ctx, fm1Term.objY_A_IMPLICIT!, ObjTerm(elabCatA), stackDepth + 1, isSubElaboration);

            const expectedFunctorType = ObjTerm(FunctorCategoryTerm(elabCatA, elabCatB));
            const elabFunctor = check(ctx, fm1Term.functor, expectedFunctorType, stackDepth + 1, isSubElaboration);

            const expectedMorphismType = HomTerm(elabCatA, elabObjX_A, elabObjY_A);
            const elabMorphism_a = check(ctx, fm1Term.morphism_a, expectedMorphismType, stackDepth + 1, isSubElaboration);

            // Result type: Hom B (FMap0 F X) (FMap0 F Y)
            // We need to construct FMap0 terms for domain and codomain of the resulting morphism
            const fmap0_X = FMap0Term(elabFunctor, elabObjX_A, getTermRef(elabCatA), getTermRef(elabCatB));
            const fmap0_Y = FMap0Term(elabFunctor, elabObjY_A, getTermRef(elabCatA), getTermRef(elabCatB));

            const finalFMap1 = FMap1Term(elabFunctor, elabMorphism_a, getTermRef(elabCatA), getTermRef(elabCatB), getTermRef(elabObjX_A), getTermRef(elabObjY_A));
            return { elaboratedTerm: finalFMap1, type: HomTerm(getTermRef(elabCatB), fmap0_X, fmap0_Y) };
        }
        case 'NatTransTypeTerm': {
            const ntTerm = current as Term & NatTransTypeTermType;
            const elabCatA = check(ctx, ntTerm.catA, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabCatB = check(ctx, ntTerm.catB, CatTerm(), stackDepth + 1, isSubElaboration);
            const expectedFunctorType = ObjTerm(FunctorCategoryTerm(elabCatA, elabCatB));
            const elabFunctorF = check(ctx, ntTerm.functorF, expectedFunctorType, stackDepth + 1, isSubElaboration);
            const elabFunctorG = check(ctx, ntTerm.functorG, expectedFunctorType, stackDepth + 1, isSubElaboration);

            const finalNatTransType = NatTransTypeTerm(elabCatA, elabCatB, elabFunctorF, elabFunctorG);
            return { elaboratedTerm: finalNatTransType, type: Type() };
        }
        case 'NatTransComponentTerm': {
            const ncTerm = current as Term & NatTransComponentTermType;
            const elabCatA = check(ctx, ncTerm.catA_IMPLICIT!, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabCatB = check(ctx, ncTerm.catB_IMPLICIT!, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabFunctorF = check(ctx, ncTerm.functorF_IMPLICIT!, ObjTerm(FunctorCategoryTerm(elabCatA, elabCatB)), stackDepth + 1, isSubElaboration);
            const elabFunctorG = check(ctx, ncTerm.functorG_IMPLICIT!, ObjTerm(FunctorCategoryTerm(elabCatA, elabCatB)), stackDepth + 1, isSubElaboration);

            const expectedTransformationType = NatTransTypeTerm(elabCatA, elabCatB, elabFunctorF, elabFunctorG);
            const elabTransformation = check(ctx, ncTerm.transformation, expectedTransformationType, stackDepth + 1, isSubElaboration);

            const expectedObjectType = ObjTerm(elabCatA);
            const elabObjectX = check(ctx, ncTerm.objectX, expectedObjectType, stackDepth + 1, isSubElaboration);

            // Result type: Hom catB (FMap0 F X) (FMap0 G X)
            const fmap0_F_X = FMap0Term(elabFunctorF, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB));
            const fmap0_G_X = FMap0Term(elabFunctorG, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB));

            const finalNatTransComp = NatTransComponentTerm(elabTransformation, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB), getTermRef(elabFunctorF), getTermRef(elabFunctorG));
            return { elaboratedTerm: finalNatTransComp, type: HomTerm(getTermRef(elabCatB), fmap0_F_X, fmap0_G_X) };
        }
        case 'HomCovFunctorIdentity': {
            const hciTerm = current as Term & {tag: 'HomCovFunctorIdentity'};
            // Elaborate components to ensure they are valid types/terms
            const elabDomainCat = check(ctx, hciTerm.domainCat, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabObjW = check(ctx, hciTerm.objW_InDomainCat, ObjTerm(elabDomainCat), stackDepth + 1, isSubElaboration);

            const setGlobal = globalDefs.get("Set");
            if (!setGlobal || !setGlobal.value) throw new Error("Global 'Set' category not defined for HomCovFunctorIdentity type inference.");
            const globalSetTerm = getTermRef(setGlobal.value);

            // Reconstruct with elaborated parts if necessary, though direct use is fine if they are already terms.
            const finalHCITerm = HomCovFunctorIdentity(elabDomainCat, elabObjW);
            return {
                elaboratedTerm: finalHCITerm,
                type: ObjTerm(FunctorCategoryTerm(elabDomainCat, globalSetTerm))
            };
        }
        case 'SetTerm': return { elaboratedTerm: current, type: CatTerm() };
        default:
            const exhaustiveCheck: never = current;
            throw new Error(`Infer: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
}

export function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0, isSubElaboration: boolean = false): Term {
    if (stackDepth > MAX_STACK_DEPTH) {
        throw new Error(`check: Max stack depth exceeded. Term: ${printTerm(term)}, Expected: ${printTerm(expectedType)}`);
    }

    const originalTerm = term;
    const termWithKernelImplicits = ensureKernelImplicitsPresent(originalTerm);
    let currentTerm = getTermRef(termWithKernelImplicits); 
    const currentExpectedType = getTermRef(expectedType);

    const expectedTypeWhnf = whnf(currentExpectedType, ctx, stackDepth + 1);

    // Rule for implicit lambda insertion (from Haskell: check LamAbsI)
    if (expectedTypeWhnf.tag === 'Pi' && expectedTypeWhnf.icit === Icit.Impl) {
        const termRef = getTermRef(currentTerm); // Re-evaluate currentTerm after potential modifications
        if (!(termRef.tag === 'Lam' && termRef.icit === Icit.Impl)) {
            const lamParamName = expectedTypeWhnf.paramName;
            const lamParamType = getTermRef(expectedTypeWhnf.paramType);
            
            const newLam = Lam(
                lamParamName,
                Icit.Impl,
                lamParamType,
                (v_actual_arg: Term) => {
                    const bodyCheckCtx = extendCtx(ctx, lamParamName, lamParamType, Icit.Impl, v_actual_arg);
                    const bodyExpectedTypeInner = whnf(expectedTypeWhnf.bodyType(v_actual_arg), bodyCheckCtx);
                    // Pass isSubElaboration = true for this internal check call
                    const bodyterm = check(bodyCheckCtx, termRef, bodyExpectedTypeInner, stackDepth + 1, true);
                    return bodyterm;
                }
            );
            return newLam;
        }
    }
    
    // Rule for annotated lambdas matching Pi types
    if (currentTerm.tag === 'Lam' && expectedTypeWhnf.tag === 'Pi' && currentTerm.icit === expectedTypeWhnf.icit) {
        const lamNode = currentTerm;
        const expectedPiNode = expectedTypeWhnf;
        let lamParamType = lamNode.paramType;

        if (!lamNode._isAnnotated) { 
            lamParamType = expectedPiNode.paramType;
            if (originalTerm === lamNode && originalTerm.tag === 'Lam' && !originalTerm._isAnnotated) {
                originalTerm.paramType = lamParamType; // Mutate original if it's the direct unannotated Lam
                originalTerm._isAnnotated = true;
            }
             // Also update currentTerm's view if it was the unannotated Lam
            lamNode.paramType = lamParamType;
            lamNode._isAnnotated = true;

        } else if (lamNode.paramType) { 
            const elabLamParamType = check(ctx, lamNode.paramType, Type(), stackDepth + 1, isSubElaboration);
            addConstraint(elabLamParamType, expectedPiNode.paramType, `Lam param type vs Pi param type for ${lamNode.paramName}`);
            // solveConstraints HERE was important to prevent error 
            // (until the addition of the final solveConstraints at the end of the function)
            // Now for efficientcy could erase this,
            solveConstraints(ctx, stackDepth + 1); // ALTERNATIVELY: attempt to solve only when lamNode.paramType is a hole
            lamParamType = elabLamParamType; 
        }
        if (!lamParamType) {
            throw new Error(`Lambda parameter type missing for ${lamNode.paramName} when checking against Pi`);
        }
        
        const finalLamParamType = lamParamType; // Capture for closure
        return Lam(lamNode.paramName, lamNode.icit, finalLamParamType,
            (v_arg: Term) => {
                const extendedCtx = extendCtx(ctx, lamNode.paramName, finalLamParamType, lamNode.icit, v_arg);
                const actualBodyTerm = lamNode.body(Var(lamNode.paramName, true));
                const expectedBodyPiType = whnf(expectedPiNode.bodyType(v_arg), extendedCtx);
                // Pass isSubElaboration = true for this internal check call
                return check(extendedCtx, actualBodyTerm, expectedBodyPiType, stackDepth + 1, true);
            }
        );
    }

    if (currentTerm.tag === 'Hole') {
        if (!currentTerm.elaboratedType) {
            currentTerm.elaboratedType = expectedTypeWhnf;
        } else {
            addConstraint(getTermRef(currentTerm.elaboratedType), expectedTypeWhnf, `check Hole ${currentTerm.id}: elaboratedType vs expectedType`);
            solveConstraints(ctx, stackDepth + 1);  // apparently not affecting perf
        }
        return currentTerm;
    }

    // Default case: infer type, insert implicits, then check against expected
    // This corresponds to `(t, inferred) <- insert cxt $ infer cxt t` in Haskell
    let { elaboratedTerm: inferredElabTerm, type: inferredType } = infer(ctx, currentTerm, stackDepth + 1, isSubElaboration);
    
    // Insert implicit applications based on the inferred type
    const afterInsert = insertImplicitApps(ctx, inferredElabTerm, inferredType, stackDepth + 1);
    
    addConstraint(whnf(afterInsert.type, ctx), expectedTypeWhnf, `check general: inferredType(${printTerm(afterInsert.term)}) vs expectedType(${printTerm(expectedTypeWhnf)})`);
    solveConstraints(ctx, stackDepth + 1);  // apparently not affecting perf regardless of alt position
    return afterInsert.term; // Return the term after implicit applications
}


export function elaborate(
    term: Term,
    expectedType?: Term,
    initialCtx: Context = emptyCtx,
    options: ElaborationOptions = { normalizeResultTerm: true }
): ElaborationResult {
    const originalConstraints = [...constraints];
    constraints.length = 0;

    let finalTermToReport: Term;
    let finalTypeToReport: Term;

    try {
        if (expectedType) {
            //TODO: should use elaborated expectedType instead of expectedType. DONE?
            const elaboratedExpectedType = check(initialCtx, expectedType, Type());

            finalTermToReport = check(initialCtx, term, elaboratedExpectedType);
            // After check, the type of finalTermToReport should match expectedType.
            // We use the (potentially refined by check) expectedType for the result.
            finalTypeToReport = elaboratedExpectedType; 
        } else {
            const inferResult = infer(initialCtx, term);
            // If no expected type, infer, then insert implicits.
            const afterInsert = insertImplicitApps(initialCtx, inferResult.elaboratedTerm, inferResult.type, 0);
            finalTermToReport = afterInsert.term;
            finalTypeToReport = afterInsert.type;
        }

        if (!solveConstraints(initialCtx)) {
            const fc = constraints.find(c => !areEqual(getTermRef(c.t1), getTermRef(c.t2), initialCtx, 0));
            let fcMsg = "Unknown constraint";
            if (fc) {
                fcMsg = `${printTerm(getTermRef(fc.t1))} vs ${printTerm(getTermRef(fc.t2))} (orig: ${fc.origin || 'unspecified'})`;
            }
            console.error("Remaining constraints on failure during elaboration:");
            constraints.forEach(c => {
                 const c_t1_dbg = getTermRef(c.t1); const c_t2_dbg = getTermRef(c.t2);
                 console.error(`  ${printTerm(c_t1_dbg)} ${areEqual(c_t1_dbg, c_t2_dbg, initialCtx,0) ? "===" : "=/="} ${printTerm(c_t2_dbg)} (origin: ${c.origin})`);
            });
            throw new Error(`Type error: Could not solve constraints. Approx failing: ${fcMsg}`);
        }
    } catch (e) {
        if (e instanceof Error && (e.message.startsWith("Type error:") || e.message.includes("Unbound variable:") || e.message.includes("Cannot apply non-function:") || e.message.includes("Constant symbol") || e.message.includes("stack depth exceeded"))) {
            constraints.splice(0, constraints.length, ...originalConstraints);
            throw e;
        }
        constraints.splice(0, constraints.length, ...originalConstraints);
        throw new Error(`Elaboration internal error: ${(e as Error).message} on term ${printTerm(term)}. Stack: ${(e as Error).stack}`);
    } finally {
        constraints.splice(0, constraints.length, ...originalConstraints);
    }

    const finalResultTerm = options.normalizeResultTerm ? normalize(finalTermToReport, initialCtx) : finalTermToReport;
    const finalResultType = whnf(getTermRef(finalTypeToReport), initialCtx); 

    return { term: finalResultTerm, type: finalResultType };
}


export function isPatternVarName(name: string, patternVarDecls: PatternVarDecl[]): boolean {
    return name.startsWith('$') && patternVarDecls.includes(name);
}

export function matchPattern(
    pattern: Term, 
    termToMatch: Term, 
    ctx: Context,
    patternVarDecls: PatternVarDecl[], 
    currentSubst?: Substitution,
    stackDepth = 0
): Substitution | null {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`matchPattern stack depth exceeded for pattern ${printTerm(pattern)} vs term ${printTerm(termToMatch)}`);

    const rtPattern = getTermRef(pattern); 
    const rtTermToMatch = getTermRef(termToMatch); 

    const subst = currentSubst ? new Map(currentSubst) : new Map<string, Term>();

    if (rtPattern.tag === 'Var' && isPatternVarName(rtPattern.name, patternVarDecls)) {
        const pvarName = rtPattern.name;
        if (pvarName === '_') return subst; 
        const existing = subst.get(pvarName);
        if (existing) {
            return areEqual(rtTermToMatch, getTermRef(existing), ctx, stackDepth + 1) ? subst : null;
        }
        subst.set(pvarName, rtTermToMatch);
        return subst;
    }

    if (rtPattern.tag === 'Hole') {
        if (rtPattern.id === '_') return subst; 
        if (isPatternVarName(rtPattern.id, patternVarDecls)) { 
            const pvarId = rtPattern.id;
            const existing = subst.get(pvarId);
            if (existing) {
                return areEqual(rtTermToMatch, getTermRef(existing), ctx, stackDepth + 1) ? subst : null;
            }
            subst.set(pvarId, rtTermToMatch);
            return subst;
        }
        if (rtTermToMatch.tag === 'Hole' && rtPattern.id === rtTermToMatch.id) return subst;
        return null;
    }


    if (rtTermToMatch.tag === 'Hole') return null; 
    if (rtPattern.tag !== rtTermToMatch.tag) return null;

    if ((rtPattern.tag === 'App' || rtPattern.tag === 'Lam' || rtPattern.tag === 'Pi') &&
        (rtTermToMatch.tag === rtPattern.tag) && rtPattern.icit !== rtTermToMatch.icit) {
        return null;
    }

    switch (rtPattern.tag) {
        case 'Type': case 'CatTerm': return subst;
        case 'Var': 
            return rtPattern.name === (rtTermToMatch as Term & {tag:'Var'}).name ? subst : null;
        case 'App': {
            const termApp = rtTermToMatch as Term & {tag:'App'};
            const s1 = matchPattern(rtPattern.func, termApp.func, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s1) return null;
            return matchPattern(rtPattern.arg, termApp.arg, ctx, patternVarDecls, s1, stackDepth + 1);
        }
        case 'Lam': { 
            const lamP = rtPattern; const lamT = rtTermToMatch as Term & {tag:'Lam'};
            if (lamP._isAnnotated !== lamT._isAnnotated) return null;
            let tempSubst = subst;
            if (lamP._isAnnotated) {
                if (!lamP.paramType || !lamT.paramType) return null; 
                 const sType = matchPattern(lamP.paramType, lamT.paramType, ctx, patternVarDecls, tempSubst, stackDepth + 1);
                 if (!sType) return null;
                 tempSubst = sType;
            }
            const freshV = Var(freshVarName(lamP.paramName), true); 
            const paramTypeForCtx = (lamP._isAnnotated && lamP.paramType) ? getTermRef(lamP.paramType) : Hole(freshHoleName() + "_match_lam_body_ctx");
            const extendedCtx = extendCtx(ctx, freshV.name, paramTypeForCtx, lamP.icit);
             return areEqual(lamP.body(freshV), lamT.body(freshV), extendedCtx, stackDepth + 1) ? tempSubst : null;
        }
        case 'Pi': { 
            const piP = rtPattern; const piT = rtTermToMatch as Term & {tag:'Pi'};
            const sType = matchPattern(piP.paramType, piT.paramType, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!sType) return null;
            const freshV = Var(freshVarName(piP.paramName), true);
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(piP.paramType), piP.icit);
            return areEqual(piP.bodyType(freshV), piT.bodyType(freshV), extendedCtx, stackDepth + 1) ? sType : null;
        }
        case 'ObjTerm':
            return matchPattern(rtPattern.cat, (rtTermToMatch as Term & {tag:'ObjTerm'}).cat, ctx, patternVarDecls, subst, stackDepth + 1);
        case 'HomTerm': {
            const homP = rtPattern; const homT = rtTermToMatch as Term & {tag:'HomTerm'};
            let s = matchPattern(homP.cat, homT.cat, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s) return null;
            s = matchPattern(homP.dom, homT.dom, ctx, patternVarDecls, s, stackDepth + 1);
            if (!s) return null;
            return matchPattern(homP.cod, homT.cod, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'MkCat_': {
            const mkP = rtPattern; const mkT = rtTermToMatch as Term & {tag:'MkCat_'};
            let s = matchPattern(mkP.objRepresentation, mkT.objRepresentation, ctx, patternVarDecls, subst, stackDepth + 1);
            if(!s) return null;
            s = matchPattern(mkP.homRepresentation, mkT.homRepresentation, ctx, patternVarDecls, s, stackDepth + 1);
            if(!s) return null;
            return matchPattern(mkP.composeImplementation, mkT.composeImplementation, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'IdentityMorph': {
            const idP = rtPattern; const idT = rtTermToMatch as Term & {tag:'IdentityMorph'};
            let s: Substitution | null = subst;
            if (idP.cat_IMPLICIT) { 
                if (!idT.cat_IMPLICIT) return null; 
                s = matchPattern(idP.cat_IMPLICIT, idT.cat_IMPLICIT, ctx, patternVarDecls, s, stackDepth +1);
                if (!s) return null;
            }  // If pattern has no cat_IMPLICIT, term can have one or not. It's like a wildcard for that field if absent in pattern.
            
            return matchPattern(idP.obj, idT.obj, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'ComposeMorph': {
            const compP = rtPattern; const compT = rtTermToMatch as Term & {tag:'ComposeMorph'};
            let s: Substitution | null = subst;
            const implicitsP = [compP.cat_IMPLICIT, compP.objX_IMPLICIT, compP.objY_IMPLICIT, compP.objZ_IMPLICIT];
            const implicitsT = [compT.cat_IMPLICIT, compT.objX_IMPLICIT, compT.objY_IMPLICIT, compT.objZ_IMPLICIT];
            for(let i=0; i<implicitsP.length; i++) {
                if (implicitsP[i]) { // If pattern specifies an implicit, term must have it and match
                    if (!implicitsT[i]) return null; 
                    s = matchPattern(implicitsP[i]!, implicitsT[i]!, ctx, patternVarDecls, s, stackDepth + 1);
                    if (!s) return null;
                } // If pattern omits an implicit, term's corresponding implicit is not checked here (acts as wildcard)
            }
            s = matchPattern(compP.g, compT.g, ctx, patternVarDecls, s, stackDepth + 1);
            if (!s) return null;
            return matchPattern(compP.f, compT.f, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'FunctorCategoryTerm': {
            const fcP = rtPattern; const fcT = rtTermToMatch as Term & {tag:'FunctorCategoryTerm'};
            let s = matchPattern(fcP.domainCat, fcT.domainCat, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s) return null;
            return matchPattern(fcP.codomainCat, fcT.codomainCat, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'FMap0Term': {
            const fm0P = rtPattern; const fm0T = rtTermToMatch as Term & {tag:'FMap0Term'};
            let s: Substitution | null = subst;
            // Matching implicits: if pattern specifies them, term must match.
            if (fm0P.catA_IMPLICIT) {
                if (!fm0T.catA_IMPLICIT) return null;
                s = matchPattern(fm0P.catA_IMPLICIT, fm0T.catA_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1);
                if (!s) return null;
            }
            if (fm0P.catB_IMPLICIT) {
                if (!fm0T.catB_IMPLICIT) return null;
                s = matchPattern(fm0P.catB_IMPLICIT, fm0T.catB_IMPLICIT, ctx, patternVarDecls, s, stackDepth + 1);
                if (!s) return null;
            }
            s = matchPattern(fm0P.functor, fm0T.functor, ctx, patternVarDecls, s, stackDepth + 1);
            if (!s) return null;
            return matchPattern(fm0P.objectX, fm0T.objectX, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'FMap1Term': {
            const fm1P = rtPattern; const fm1T = rtTermToMatch as Term & {tag:'FMap1Term'};
            let s: Substitution | null = subst;
            const implicitsP = [fm1P.catA_IMPLICIT, fm1P.catB_IMPLICIT, fm1P.objX_A_IMPLICIT, fm1P.objY_A_IMPLICIT];
            const implicitsT = [fm1T.catA_IMPLICIT, fm1T.catB_IMPLICIT, fm1T.objX_A_IMPLICIT, fm1T.objY_A_IMPLICIT];
            for(let i=0; i<implicitsP.length; i++) {
                if (implicitsP[i]) {
                    if (!implicitsT[i]) return null;
                    s = matchPattern(implicitsP[i]!, implicitsT[i]!, ctx, patternVarDecls, s, stackDepth + 1);
                    if (!s) return null;
                }
            }
            s = matchPattern(fm1P.functor, fm1T.functor, ctx, patternVarDecls, s, stackDepth + 1);
            if (!s) return null;
            return matchPattern(fm1P.morphism_a, fm1T.morphism_a, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'NatTransTypeTerm': {
            const ntP = rtPattern; const ntT = rtTermToMatch as Term & {tag:'NatTransTypeTerm'};
            let s = matchPattern(ntP.catA, ntT.catA, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s) return null;
            s = matchPattern(ntP.catB, ntT.catB, ctx, patternVarDecls, s, stackDepth + 1);
            if (!s) return null;
            s = matchPattern(ntP.functorF, ntT.functorF, ctx, patternVarDecls, s, stackDepth + 1);
            if (!s) return null;
            return matchPattern(ntP.functorG, ntT.functorG, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'NatTransComponentTerm': {
            const ncP = rtPattern; const ncT = rtTermToMatch as Term & {tag:'NatTransComponentTerm'};
            let s: Substitution | null = subst;
            const implicitsP = [ncP.catA_IMPLICIT, ncP.catB_IMPLICIT, ncP.functorF_IMPLICIT, ncP.functorG_IMPLICIT];
            const implicitsT = [ncT.catA_IMPLICIT, ncT.catB_IMPLICIT, ncT.functorF_IMPLICIT, ncT.functorG_IMPLICIT];
             for(let i=0; i<implicitsP.length; i++) {
                if (implicitsP[i]) {
                    if (!implicitsT[i]) return null;
                    s = matchPattern(implicitsP[i]!, implicitsT[i]!, ctx, patternVarDecls, s, stackDepth + 1);
                    if (!s) return null;
                }
            }
            s = matchPattern(ncP.transformation, ncT.transformation, ctx, patternVarDecls, s, stackDepth + 1);
            if (!s) return null;
            return matchPattern(ncP.objectX, ncT.objectX, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'HomCovFunctorIdentity': {
            const hcP = rtPattern as Term & {tag:'HomCovFunctorIdentity'};
            const hcT = rtTermToMatch as Term & {tag:'HomCovFunctorIdentity'};
            let s = matchPattern(hcP.domainCat, hcT.domainCat, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s) return null;
            return matchPattern(hcP.objW_InDomainCat, hcT.objW_InDomainCat, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'SetTerm': return subst; // If tags match (already checked), it's a match
        default:
             const exhaustiveCheck: never = rtPattern;
             console.warn(`matchPattern: Unhandled pattern tag: ${(exhaustiveCheck as any).tag}.`);
             return null;
    }
}


export function applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[]): Term {
    const current = getTermRef(term);

    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        if (current.name === '_') return Hole('_'); 
        const replacement = subst.get(current.name);
        return replacement !== undefined ? replacement : current; 
    }
    if (current.tag === 'Hole' && isPatternVarName(current.id, patternVarDecls)) {
        if (current.id === '_') return Hole('_');
        const replacement = subst.get(current.id);
        return replacement !== undefined ? replacement : current;
    }

    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': case 'CatTerm': return current;
        case 'App':
            return App(applySubst(current.func, subst, patternVarDecls), applySubst(current.arg, subst, patternVarDecls), current.icit);
        case 'Lam': {
            const lam = current;
            const appliedParamType = lam.paramType ? applySubst(lam.paramType, subst, patternVarDecls) : undefined;
            const newBodyFn = (v_arg: Term): Term => {
                const bodyCtxSubst = new Map(subst);
                return applySubst(lam.body(v_arg), bodyCtxSubst, patternVarDecls);
            };

            const newLam = Lam(lam.paramName, lam.icit, appliedParamType, newBodyFn);
            (newLam as Term & {tag: 'Lam'})._isAnnotated = lam._isAnnotated && appliedParamType !== undefined;
            return newLam;
        }
        case 'Pi': {
            const pi = current;
            const newBodyTypeFn = (v_arg: Term) => {
                const bodyCtxSubst = new Map(subst);
                return applySubst(pi.bodyType(v_arg), bodyCtxSubst, patternVarDecls);
            };
            return Pi(pi.paramName, pi.icit, applySubst(pi.paramType, subst, patternVarDecls), newBodyTypeFn);
        }
        case 'ObjTerm': return ObjTerm(applySubst(current.cat, subst, patternVarDecls));
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
        case 'FunctorCategoryTerm':
            return FunctorCategoryTerm(
                applySubst(current.domainCat, subst, patternVarDecls),
                applySubst(current.codomainCat, subst, patternVarDecls)
            );
        case 'FMap0Term':
            return FMap0Term(
                applySubst(current.functor, subst, patternVarDecls),
                applySubst(current.objectX, subst, patternVarDecls),
                current.catA_IMPLICIT ? applySubst(current.catA_IMPLICIT, subst, patternVarDecls) : undefined,
                current.catB_IMPLICIT ? applySubst(current.catB_IMPLICIT, subst, patternVarDecls) : undefined
            );
        case 'FMap1Term':
            return FMap1Term(
                applySubst(current.functor, subst, patternVarDecls),
                applySubst(current.morphism_a, subst, patternVarDecls),
                current.catA_IMPLICIT ? applySubst(current.catA_IMPLICIT, subst, patternVarDecls) : undefined,
                current.catB_IMPLICIT ? applySubst(current.catB_IMPLICIT, subst, patternVarDecls) : undefined,
                current.objX_A_IMPLICIT ? applySubst(current.objX_A_IMPLICIT, subst, patternVarDecls) : undefined,
                current.objY_A_IMPLICIT ? applySubst(current.objY_A_IMPLICIT, subst, patternVarDecls) : undefined
            );
        case 'NatTransTypeTerm':
            return NatTransTypeTerm(
                applySubst(current.catA, subst, patternVarDecls),
                applySubst(current.catB, subst, patternVarDecls),
                applySubst(current.functorF, subst, patternVarDecls),
                applySubst(current.functorG, subst, patternVarDecls)
            );
        case 'NatTransComponentTerm':
            return NatTransComponentTerm(
                applySubst(current.transformation, subst, patternVarDecls),
                applySubst(current.objectX, subst, patternVarDecls),
                current.catA_IMPLICIT ? applySubst(current.catA_IMPLICIT, subst, patternVarDecls) : undefined,
                current.catB_IMPLICIT ? applySubst(current.catB_IMPLICIT, subst, patternVarDecls) : undefined,
                current.functorF_IMPLICIT ? applySubst(current.functorF_IMPLICIT, subst, patternVarDecls) : undefined,
                current.functorG_IMPLICIT ? applySubst(current.functorG_IMPLICIT, subst, patternVarDecls) : undefined
            );
        case 'HomCovFunctorIdentity':
            return HomCovFunctorIdentity(
                applySubst(current.domainCat, subst, patternVarDecls),
                applySubst(current.objW_InDomainCat, subst, patternVarDecls)
            );
        case 'SetTerm': return current; // SetTerm has no subterms to apply substitutions to
        default:
            const exhaustiveCheck: never = current;
            throw new Error(`applySubst: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
}

export function printTerm(term: Term, boundVarsMap: Map<string, string> = new Map(), stackDepth = 0): string {
    if (stackDepth > MAX_STACK_DEPTH * 2) return "<print_depth_exceeded>";
    if (!term) return "<null_term>";

    const current = getTermRef(term);

    const getUniqueName = (baseName: string): string => {
        if (!boundVarsMap.has(baseName) && !globalDefs.has(baseName) && !Array.from(boundVarsMap.values()).includes(baseName)) {
            return baseName;
        }
        let uniqueName = baseName;
        let suffix = 1;
        while (globalDefs.has(uniqueName) || Array.from(boundVarsMap.values()).includes(uniqueName) || boundVarsMap.has(uniqueName) ) {
            uniqueName = `${baseName}_${suffix++}`;
            if (suffix > 100) return `${baseName}_too_many`; 
        }
        return uniqueName;
    };

    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return boundVarsMap.get(current.name) || current.name;
        case 'Hole': {
            let typeInfo = "";
            if (current.elaboratedType && getTermRef(current.elaboratedType) !== current) { 
                const elabTypeRef = getTermRef(current.elaboratedType);
                const isSelfRefPrint = (elabTypeRef.tag === 'Hole' && elabTypeRef.id === current.id && elabTypeRef.elaboratedType === current.elaboratedType);
                const isTypeForType = (elabTypeRef.tag === 'Type' && term.tag === 'Type'); 
                
                if (!isSelfRefPrint && !isTypeForType) {
                    const elabTypePrint = printTerm(elabTypeRef, new Map(boundVarsMap), stackDepth + 1);
                     if(!elabTypePrint.startsWith("?h") || elabTypePrint.length > current.id.length + 3 ) { 
                        typeInfo = `(:${elabTypePrint})`;
                    }
                }
            }
            return (current.id === '_' ? '_' : (boundVarsMap.get(current.id) || current.id)) + typeInfo;
        }
        case 'Lam': {
            const paramDisplayName = getUniqueName(current.paramName);
            const newBoundVars = new Map(boundVarsMap);
            newBoundVars.set(current.paramName, paramDisplayName);

            const typeAnnotation = (current._isAnnotated && current.paramType)
                ? ` : ${printTerm(current.paramType, new Map(boundVarsMap), stackDepth + 1)}`
                : '';
            const bodyTerm = current.body(Var(current.paramName, true)); 
            const binder = current.icit === Icit.Impl ? `{${paramDisplayName}${typeAnnotation}}` : `(${paramDisplayName}${typeAnnotation})`;
            return `(λ ${binder}. ${printTerm(bodyTerm, newBoundVars, stackDepth + 1)})`;
        }
        case 'App':
            const funcStr = printTerm(current.func, new Map(boundVarsMap), stackDepth + 1);
            const argStr = printTerm(current.arg, new Map(boundVarsMap), stackDepth + 1);
            return current.icit === Icit.Impl ? `(${funcStr} {${argStr}})` : `(${funcStr} ${argStr})`;
        case 'Pi': {
            const paramDisplayName = getUniqueName(current.paramName);
            const newBoundVars = new Map(boundVarsMap);
            newBoundVars.set(current.paramName, paramDisplayName);

            const paramTypeStr = printTerm(current.paramType, new Map(boundVarsMap), stackDepth + 1);
            const bodyTypeTerm = current.bodyType(Var(current.paramName, true)); 
            const binder = current.icit === Icit.Impl ? `{${paramDisplayName} : ${paramTypeStr}}` : `(${paramDisplayName} : ${paramTypeStr})`;
            return `(Π ${binder}. ${printTerm(bodyTypeTerm, newBoundVars, stackDepth + 1)})`;
        }
        case 'CatTerm': return 'Cat';
        case 'ObjTerm': return `(Obj ${printTerm(current.cat, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'HomTerm':
            return `(Hom ${printTerm(current.cat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.dom, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.cod, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'MkCat_':
            return `(mkCat_ {O=${printTerm(current.objRepresentation, new Map(boundVarsMap), stackDepth + 1)}, H=${printTerm(current.homRepresentation, new Map(boundVarsMap), stackDepth + 1)}, C=${printTerm(current.composeImplementation, new Map(boundVarsMap), stackDepth + 1)}})`;
        case 'IdentityMorph': {
            let catIdStr = "";
            if (current.cat_IMPLICIT && (getTermRef(current.cat_IMPLICIT).tag !== 'Hole' || (getTermRef(current.cat_IMPLICIT) as Term & {tag: 'Hole'}).id.startsWith("_type_of_"))) { 
                 catIdStr = ` {cat=${printTerm(current.cat_IMPLICIT, new Map(boundVarsMap), stackDepth + 1)}}`;
            }
            return `(id${catIdStr} ${printTerm(current.obj, new Map(boundVarsMap), stackDepth + 1)})`;
        }
        case 'ComposeMorph': {
            let catCompStr = "";
            if (current.cat_IMPLICIT && (getTermRef(current.cat_IMPLICIT).tag !== 'Hole' || (getTermRef(current.cat_IMPLICIT) as Term & {tag: 'Hole'}).id.startsWith("_type_of_"))) {
                 catCompStr = ` {cat=${printTerm(current.cat_IMPLICIT, new Map(boundVarsMap), stackDepth + 1)}}`;
            }
            return `(${printTerm(current.g, new Map(boundVarsMap), stackDepth + 1)} ∘${catCompStr} ${printTerm(current.f, new Map(boundVarsMap), stackDepth + 1)})`;
        }
        case 'FunctorCategoryTerm':
            return `(Functor ${printTerm(current.domainCat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.codomainCat, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'FMap0Term':
            return `(fmap0 ${printTerm(current.functor, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.objectX, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'FMap1Term':
            return `(fmap1 ${printTerm(current.functor, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.morphism_a, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'NatTransTypeTerm':
            return `(Transf ${printTerm(current.catA, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.catB, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.functorF, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.functorG, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'NatTransComponentTerm':
            return `(tapp ${printTerm(current.transformation, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.objectX, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'HomCovFunctorIdentity':
            return `(HomCovFunctor ${printTerm(current.domainCat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.objW_InDomainCat, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'SetTerm': return 'Set';
        default:
            const exhaustiveCheck: never = current;
            throw new Error(`printTerm: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
}