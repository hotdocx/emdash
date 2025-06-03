/**
 * @file elaboration.ts
 * @description Implements the type checking and inference algorithms (`check` and `infer`),
 * and the main `elaborate` function that drives the process.
 * Handles insertion of implicit arguments and ensuring kernel implicits are present.
 */

import {
    Term, Context, ElaborationResult, Icit, Hole, Var, App, Lam, Pi, Type, CatTerm,
    ObjTerm, HomTerm, FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm,
    NatTransComponentTerm, HomCovFunctorIdentity, SetTerm, FunctorTypeTerm, BaseTerm
} from './types';
import {
    emptyCtx, extendCtx, lookupCtx, globalDefs, addConstraint, getTermRef,
    freshHoleName, freshVarName, consoleLog, constraints, printTerm
} from './state';
import { whnf, normalize, areEqual, solveConstraints, MAX_STACK_DEPTH, matchPattern, applySubst, isPatternVarName } from './logic'; // Added matchPattern, applySubst, isPatternVarName
import { KERNEL_IMPLICIT_SPECS, KernelImplicitSpec } from './kernel_metadata';

// Type aliases for specific term kinds, useful for casting
type FunctorCategoryTermType = Extract<BaseTerm, { tag: 'FunctorCategoryTerm' }>;
type FunctorTypeTermType = Extract<BaseTerm, { tag: 'FunctorTypeTerm' }>;
type FMap0TermType = Extract<BaseTerm, { tag: 'FMap0Term' }>;
type FMap1TermType = Extract<BaseTerm, { tag: 'FMap1Term' }>;
type NatTransTypeTermType = Extract<BaseTerm, { tag: 'NatTransTypeTerm' }>;
type NatTransComponentTermType = Extract<BaseTerm, { tag: 'NatTransComponentTerm' }>;
type HomCovFunctorIdentityType = Extract<BaseTerm, { tag: 'HomCovFunctorIdentity' }>;


export interface ElaborationOptions {
    normalizeResultTerm?: boolean; // Whether to fully normalize the elaborated term.
}

/**
 * Ensures that kernel-defined implicit arguments are present in a term.
 * If an implicit field defined in KERNEL_IMPLICIT_SPECS is undefined,
 * it's filled with a fresh hole.
 * @param term The term to process.
 * @returns The term, potentially modified with new holes for missing implicits.
 */
export function ensureKernelImplicitsPresent(term: Term): Term {
    const originalTermTag = term.tag;
    // Iterate over a copy, as KERNEL_IMPLICIT_SPECS might be mutated elsewhere if not careful, though it shouldn't be.
    const specs = [...KERNEL_IMPLICIT_SPECS];

    for (const spec of specs as KernelImplicitSpec<Term>[]) { // Cast to allow general iteration
        if (originalTermTag === spec.tag) {
            const specificTerm = term as Term & { [key: string]: any }; // Type assertion for property access
            for (const fieldName of spec.fields) { // fieldName is typed correctly by ImplicitField<T>
                if (specificTerm[fieldName as string] === undefined) {
                    let baseHint = spec.tag.toLowerCase().replace(/morph|term/g, '').replace(/_/g, '');
                    const fieldHint = (fieldName as string).replace('_IMPLICIT', '').toLowerCase();

                    let dynamicHintPart = "";
                    // Example: Add dynamic hints based on term content if useful
                    // if (spec.tag === 'IdentityMorph' && specificTerm.obj) { // IdentityMorph example
                    //     const idObj = getTermRef(specificTerm.obj);
                    //     if (idObj.tag === 'Var') dynamicHintPart = `_${idObj.name}`;
                    //     else if (idObj.tag === 'Hole') dynamicHintPart = `_${idObj.id.replace("?","h")}`;
                    // }
                    specificTerm[fieldName as string] = Hole(freshHoleName() + `_k_${baseHint}${dynamicHintPart}_${fieldHint}`);
                }
            }
            break; // Found the spec for this term tag, no need to check others
        }
    }
    return term;
}

export interface InferResult {
    elaboratedTerm: Term;
    type: Term;
}

/**
 * Inserts implicit applications to a term based on its type.
 * If `term` has type `Π {x:A}. B`, it becomes `term {?h}` of type `B[?h/x]`.
 * This process repeats until the type is not an implicit Pi type.
 * @param ctx The current context.
 * @param term The term to which implicit arguments might be applied.
 * @param type The type of the term.
 * @param stackDepth Recursion depth.
 * @param unConditional If true, inserts implicits even if term is an implicit lambda (rarely needed).
 * @returns An object containing the new term, its new type, and whether progress was made.
 */
function insertImplicitApps(ctx: Context, term: Term, type: Term, stackDepth: number, unConditional: boolean = false): { term: Term, type: Term, progress?: boolean } {
    let currentTerm = term;
    let currentType = whnf(type, ctx, stackDepth + 1);

    // Typically, don't insert if the term itself is an implicit lambda waiting to be applied.
    const termRef = getTermRef(currentTerm);
    if (termRef.tag === 'Lam' && termRef.icit === Icit.Impl && !unConditional) {
        return { term: currentTerm, type: currentType, progress: false };
    }

    let progress = false;
    while (currentType.tag === 'Pi' && currentType.icit === Icit.Impl) {
        const implHole = Hole(freshHoleName() + "_auto_inserted_impl_arg");
        if (currentType.paramType) { // Annotate the hole if param type is known
            (implHole as Term & {tag:'Hole'}).elaboratedType = currentType.paramType;
        }
        currentTerm = App(currentTerm, implHole, Icit.Impl);
        currentType = whnf(currentType.bodyType(implHole), ctx, stackDepth + 1); // Substitute hole into body type
        progress = true;
    }
    return { term: currentTerm, type: currentType, progress };
}

/**
 * Infers the type of a term.
 * @param ctx The current context.
 * @param term The term to infer the type of.
 * @param stackDepth Recursion depth.
 * @param isSubElaboration Flag to indicate if this is a recursive call within a larger elaboration.
 * @returns An InferResult containing the elaborated term and its inferred type.
 */
export function infer(ctx: Context, term: Term, stackDepth: number = 0, isSubElaboration: boolean = false): InferResult {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Infer stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);

    const originalTerm = term;
    const termWithKernelImplicits = ensureKernelImplicitsPresent(originalTerm);
    let current = getTermRef(termWithKernelImplicits);

    if (current.tag === 'Var') {
        const localBinding = lookupCtx(ctx, current.name);
        if (localBinding) {
            // If it's a local let-binding with a definition, use the definition.
            // The type is already known from the binding.
            return { elaboratedTerm: localBinding.definition || current, type: localBinding.type };
        }

        const gdef = globalDefs.get(current.name);
        if (gdef) return { elaboratedTerm: current, type: gdef.type };

        // Handle special placeholder variables from occurs checks
        if (current.origin === "occurs_check") {
            consoleLog(`[Infer Special Placeholder] Detected placeholder var: ${current.name}`);
            const placeholderType = Hole("_type_of_placeholder_" + current.name.replace(/[?$]/g, ""));
            (placeholderType as Term & {tag:'Hole'}).elaboratedType = Type(); // It's a type for some term
            return { elaboratedTerm: current, type: placeholderType };
        }

        throw new Error(`Unbound variable: ${current.name} in context [${ctx.map(b => b.name).join(', ')}]`);
    }

    switch (current.tag) {
        case 'Type': return { elaboratedTerm: current, type: Type() };
        case 'Hole': {
            if (current.elaboratedType) return { elaboratedTerm: current, type: getTermRef(current.elaboratedType) };
            // If a hole's type is not known, assign a fresh hole type to it.
            const newTypeForHole = Hole(freshHoleName() + "_type_of_" + current.id.replace("?", "h"));
            (newTypeForHole as Term & {tag:'Hole'}).elaboratedType = Type(); // This new hole is itself a type.
            current.elaboratedType = newTypeForHole;
            return { elaboratedTerm: current, type: newTypeForHole };
        }
        case 'App': {
            const appNode = current;
            let { elaboratedTerm: inferredFuncElab, type: inferredFuncType } = infer(ctx, appNode.func, stackDepth + 1, true);

            let funcAfterImplicits = inferredFuncElab;
            let typeFAfterImplicits = whnf(inferredFuncType, ctx, stackDepth + 1);

            // If current application is explicit, try inserting implicit apps to the function part.
            if (appNode.icit === Icit.Expl) {
                const inserted = insertImplicitApps(ctx, funcAfterImplicits, typeFAfterImplicits, stackDepth + 1, true); // Unconditional insertion
                funcAfterImplicits = inserted.term;
                typeFAfterImplicits = inserted.type;
            }

            const whnfOfFuncTypeAfterImplicits = whnf(typeFAfterImplicits, ctx, stackDepth + 1);
            let expectedParamTypeFromPi: Term;
            let bodyTypeFnFromPi: (argVal: Term) => Term;

            if (whnfOfFuncTypeAfterImplicits.tag === 'Pi' && whnfOfFuncTypeAfterImplicits.icit === appNode.icit) {
                expectedParamTypeFromPi = whnfOfFuncTypeAfterImplicits.paramType;
                bodyTypeFnFromPi = whnfOfFuncTypeAfterImplicits.bodyType;
            } else if (whnfOfFuncTypeAfterImplicits.tag === 'Pi' && whnfOfFuncTypeAfterImplicits.icit !== appNode.icit) {
                throw new Error(`Type error in App: Function ${printTerm(funcAfterImplicits)} of type ${printTerm(whnfOfFuncTypeAfterImplicits)} expects a ${whnfOfFuncTypeAfterImplicits.icit === Icit.Expl ? "explicit" : "implicit"} argument, but an ${appNode.icit === Icit.Expl ? "explicit" : "implicit"} one was provided for ${printTerm(appNode.arg)}.`);
            } else {
                // Function type is not a Pi or icit mismatches; try to unify it with a Pi type.
                const freshPiParamName = freshVarName("pi_param_app");
                const paramTypeHole = Hole(freshHoleName() + "_app_paramT_infer");
                (paramTypeHole as Term & {tag:'Hole'}).elaboratedType = Type();
                const bodyTypeHole = Hole(freshHoleName() + "_app_bodyT_infer");
                (bodyTypeHole as Term & {tag:'Hole'}).elaboratedType = Type();
                const targetPiType = Pi(freshPiParamName, appNode.icit, paramTypeHole, (_arg: Term) => bodyTypeHole);

                addConstraint(typeFAfterImplicits, targetPiType, `App: func ${printTerm(funcAfterImplicits)} type needs to be Pi for arg ${printTerm(appNode.arg)}`);
                // Attempt to solve constraints to refine function type.
                // If this fails, the error will be caught by the top-level elaborate or by a later solveConstraints call.
                solveConstraints(ctx, stackDepth + 1);

                expectedParamTypeFromPi = paramTypeHole; // Use the hole as expected type
                bodyTypeFnFromPi = (_argVal: Term) => bodyTypeHole; // Use the hole for body type
            }

            const elaboratedArg = check(ctx, appNode.arg, expectedParamTypeFromPi, stackDepth + 1, true);
            const finalAppTerm = App(getTermRef(funcAfterImplicits), getTermRef(elaboratedArg), appNode.icit);
            const resultType = whnf(bodyTypeFnFromPi(getTermRef(elaboratedArg)), ctx, stackDepth + 1);

            return { elaboratedTerm: finalAppTerm, type: resultType };
        }
        case 'Lam': {
            const lamNode = current;
            let actualParamType: Term;
            const originalAnnotationState = { annotated: lamNode._isAnnotated, type: lamNode.paramType };

            if (lamNode._isAnnotated && lamNode.paramType) {
                actualParamType = check(ctx, lamNode.paramType, Type(), stackDepth + 1, true);
            } else {
                // Infer parameter type if not annotated
                actualParamType = Hole(freshHoleName() + "_lam_" + lamNode.paramName + "_paramT_infer");
                (actualParamType as Term & {tag:'Hole'}).elaboratedType = Type();
                // Temporarily update lamNode for recursive calls, will be restored if originalTerm was this lamNode.
                lamNode.paramType = actualParamType;
                lamNode._isAnnotated = true;
            }

            // Construct the Pi type for the lambda
            const piType = Pi(
                lamNode.paramName,
                lamNode.icit,
                getTermRef(actualParamType), // Use the (potentially elaborated or inferred) param type
                (pi_body_argument_term: Term): Term => {
                    // Context for inferring body's type: extend with param name, its type, and the placeholder argument
                    const body_infer_ctx = extendCtx(ctx, lamNode.paramName, getTermRef(actualParamType), lamNode.icit, pi_body_argument_term);
                    const lambda_body_structure = lamNode.body(Var(lamNode.paramName, true)); // Instantiate body with a Var
                    let { elaboratedTerm: inferredBodyElab, type: inferredBodyType } = infer(body_infer_ctx, lambda_body_structure, stackDepth + 1, true);
                    // Insert implicits for the body if needed
                    const insertedBody = insertImplicitApps(body_infer_ctx, inferredBodyElab, inferredBodyType, stackDepth + 1);
                    return insertedBody.type; // The type of the body becomes the result type of the Pi
                }
            );

            // Construct the elaborated lambda
            const elaboratedLam = Lam(
                lamNode.paramName,
                lamNode.icit,
                getTermRef(actualParamType),
                (v: Term) => { // v is the argument placeholder for the lambda body
                    const bodyInferCtx = extendCtx(ctx, lamNode.paramName, getTermRef(actualParamType), lamNode.icit, v);
                    const bodyTermRaw = lamNode.body(Var(lamNode.paramName, true));
                    let { elaboratedTerm: inferredBodyElab, type: inferredBodyType } = infer(bodyInferCtx, bodyTermRaw, stackDepth +1, true);
                    const insertedBody = insertImplicitApps(bodyInferCtx, inferredBodyElab, inferredBodyType, stackDepth + 1);
                    return insertedBody.term; // Return the elaborated body
                }
            );
            (elaboratedLam as Term & {tag: 'Lam'})._isAnnotated = true; // Mark as annotated

            // Restore original annotation state if the 'current' was a mutated version of the input 'term'
            if (originalTerm === lamNode && originalTerm.tag === 'Lam' && !originalAnnotationState.annotated) {
                originalTerm.paramType = originalAnnotationState.type;
                originalTerm._isAnnotated = false;
            } else if (current === lamNode && !originalAnnotationState.annotated) { // If 'current' was the one mutated
                lamNode.paramType = originalAnnotationState.type;
                lamNode._isAnnotated = false;
            }


            return { elaboratedTerm: elaboratedLam, type: piType };
        }
        case 'Pi': {
            const piNode = current;
            const elaboratedParamType = check(ctx, piNode.paramType, Type(), stackDepth + 1, true);
            // Context for checking the body type: extend with param name and its elaborated type
            const extendedCtxForBody = extendCtx(ctx, piNode.paramName, elaboratedParamType, piNode.icit);
            const bodyTypeInstance = piNode.bodyType(Var(piNode.paramName, true)); // Instantiate with a Var
            // Check that the body type itself is a Type
            check(extendedCtxForBody, bodyTypeInstance, Type(), stackDepth + 1, true);

            // Reconstruct the Pi with elaborated components for the elaborated term
            const finalPi = Pi(piNode.paramName, piNode.icit, getTermRef(elaboratedParamType), (v: Term) => {
                const bodyCtx = extendCtx(ctx, piNode.paramName, getTermRef(elaboratedParamType), piNode.icit, v);
                const piNodeBodyInstance = piNode.bodyType(Var(piNode.paramName, true));
                return check(bodyCtx, piNodeBodyInstance, Type(), stackDepth+1, true); // Elaborate body type
            });
            return { elaboratedTerm: finalPi, type: Type() }; // A Pi type itself has type Type
        }
        // Category Theory Primitives
        case 'CatTerm': return { elaboratedTerm: current, type: Type() };
        case 'ObjTerm': {
            const elabCat = check(ctx, current.cat, CatTerm(), stackDepth + 1, true);
            return { elaboratedTerm: ObjTerm(elabCat), type: Type() };
        }
        case 'HomTerm': {
            const elabCat = check(ctx, current.cat, CatTerm(), stackDepth + 1, true);
            const catForHom = getTermRef(elabCat); // Use the elaborated category
            const elabDom = check(ctx, current.dom, ObjTerm(catForHom), stackDepth + 1, true);
            const elabCod = check(ctx, current.cod, ObjTerm(catForHom), stackDepth + 1, true);
            return { elaboratedTerm: HomTerm(elabCat, elabDom, elabCod), type: Type() };
        }
        case 'FunctorCategoryTerm': {
            const fcTerm = current as Term & FunctorCategoryTermType;
            const elabDomainCat = check(ctx, fcTerm.domainCat, CatTerm(), stackDepth + 1, true);
            const elabCodomainCat = check(ctx, fcTerm.codomainCat, CatTerm(), stackDepth + 1, true);
            return { elaboratedTerm: FunctorCategoryTerm(elabDomainCat, elabCodomainCat), type: CatTerm() }; // Functor category is a category
        }
        case 'FunctorTypeTerm': {
            const fttTerm = current as Term & FunctorTypeTermType;
            const elabDomainCat = check(ctx, fttTerm.domainCat, CatTerm(), stackDepth + 1, true);
            const elabCodomainCat = check(ctx, fttTerm.codomainCat, CatTerm(), stackDepth + 1, true);
            return { elaboratedTerm: FunctorTypeTerm(elabDomainCat, elabCodomainCat), type: Type() }; // Functor type is a type
        }
        case 'FMap0Term': { // Functor application to an object
            const fm0Term = current as Term & FMap0TermType;
            // Ensure implicit category arguments are elaborated if present (they should be after ensureKernelImplicitsPresent)
            const elabCatA = check(ctx, fm0Term.catA_IMPLICIT!, CatTerm(), stackDepth + 1, true);
            const elabCatB = check(ctx, fm0Term.catB_IMPLICIT!, CatTerm(), stackDepth + 1, true);

            const expectedFunctorType = FunctorTypeTerm(elabCatA, elabCatB);
            const elabFunctor = check(ctx, fm0Term.functor, expectedFunctorType, stackDepth + 1, true);

            const expectedObjectType = ObjTerm(elabCatA); // Object must be in the domain category
            const elabObjectX = check(ctx, fm0Term.objectX, expectedObjectType, stackDepth + 1, true);

            const finalFMap0 = FMap0Term(elabFunctor, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB));
            return { elaboratedTerm: finalFMap0, type: ObjTerm(getTermRef(elabCatB)) }; // Result is an object in the codomain category
        }
        case 'FMap1Term': { // Functor application to a morphism
            const fm1Term = current as Term & FMap1TermType;
            const elabCatA = check(ctx, fm1Term.catA_IMPLICIT!, CatTerm(), stackDepth + 1, true);
            const elabCatB = check(ctx, fm1Term.catB_IMPLICIT!, CatTerm(), stackDepth + 1, true);
            const elabObjX_A = check(ctx, fm1Term.objX_A_IMPLICIT!, ObjTerm(elabCatA), stackDepth + 1, true);
            const elabObjY_A = check(ctx, fm1Term.objY_A_IMPLICIT!, ObjTerm(elabCatA), stackDepth + 1, true);

            const expectedFunctorType = FunctorTypeTerm(elabCatA, elabCatB);
            const elabFunctor = check(ctx, fm1Term.functor, expectedFunctorType, stackDepth + 1, true);

            const expectedMorphismType = HomTerm(elabCatA, elabObjX_A, elabObjY_A); // Morphism is in domain category
            const elabMorphism_a = check(ctx, fm1Term.morphism_a, expectedMorphismType, stackDepth + 1, true);

            // Result type: Hom catB (FMap0 F X) (FMap0 F Y)
            const fmap0_X = FMap0Term(elabFunctor, elabObjX_A, getTermRef(elabCatA), getTermRef(elabCatB));
            const fmap0_Y = FMap0Term(elabFunctor, elabObjY_A, getTermRef(elabCatA), getTermRef(elabCatB));

            const finalFMap1 = FMap1Term(elabFunctor, elabMorphism_a, getTermRef(elabCatA), getTermRef(elabCatB), getTermRef(elabObjX_A), getTermRef(elabObjY_A));
            return { elaboratedTerm: finalFMap1, type: HomTerm(getTermRef(elabCatB), fmap0_X, fmap0_Y) };
        }
        case 'NatTransTypeTerm': { // Type of a natural transformation
            const ntTerm = current as Term & NatTransTypeTermType;
            const elabCatA = check(ctx, ntTerm.catA, CatTerm(), stackDepth + 1, true);
            const elabCatB = check(ctx, ntTerm.catB, CatTerm(), stackDepth + 1, true);
            const expectedFunctorType = FunctorTypeTerm(elabCatA, elabCatB);
            const elabFunctorF = check(ctx, ntTerm.functorF, expectedFunctorType, stackDepth + 1, true);
            const elabFunctorG = check(ctx, ntTerm.functorG, expectedFunctorType, stackDepth + 1, true);

            const finalNatTransType = NatTransTypeTerm(elabCatA, elabCatB, elabFunctorF, elabFunctorG);
            return { elaboratedTerm: finalNatTransType, type: Type() }; // NatTrans type is a type
        }
        case 'NatTransComponentTerm': { // Component of a natural transformation
            const ncTerm = current as Term & NatTransComponentTermType;
            const elabCatA = check(ctx, ncTerm.catA_IMPLICIT!, CatTerm(), stackDepth + 1, true);
            const elabCatB = check(ctx, ncTerm.catB_IMPLICIT!, CatTerm(), stackDepth + 1, true);
            const elabFunctorF = check(ctx, ncTerm.functorF_IMPLICIT!, FunctorTypeTerm(elabCatA, elabCatB), stackDepth + 1, true);
            const elabFunctorG = check(ctx, ncTerm.functorG_IMPLICIT!, FunctorTypeTerm(elabCatA, elabCatB), stackDepth + 1, true);

            const expectedTransformationType = NatTransTypeTerm(elabCatA, elabCatB, elabFunctorF, elabFunctorG);
            const elabTransformation = check(ctx, ncTerm.transformation, expectedTransformationType, stackDepth + 1, true);

            const expectedObjectType = ObjTerm(elabCatA); // Object is in domain category CatA
            const elabObjectX = check(ctx, ncTerm.objectX, expectedObjectType, stackDepth + 1, true);

            // Result type: Hom catB (FMap0 F X) (FMap0 G X)
            const fmap0_F_X = FMap0Term(elabFunctorF, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB));
            const fmap0_G_X = FMap0Term(elabFunctorG, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB));

            const finalNatTransComp = NatTransComponentTerm(elabTransformation, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB), getTermRef(elabFunctorF), getTermRef(elabFunctorG));
            return { elaboratedTerm: finalNatTransComp, type: HomTerm(getTermRef(elabCatB), fmap0_F_X, fmap0_G_X) };
        }
        case 'HomCovFunctorIdentity': { // Hom_A(W, -) functor
            const hciTerm = current as Term & HomCovFunctorIdentityType;
            const elabDomainCat = check(ctx, hciTerm.domainCat, CatTerm(), stackDepth + 1, true);
            const elabObjW = check(ctx, hciTerm.objW_InDomainCat, ObjTerm(elabDomainCat), stackDepth + 1, true);

            const setGlobal = globalDefs.get("Set");
            if (!setGlobal || !setGlobal.value) throw new Error("Global 'Set' category not defined for HomCovFunctorIdentity type inference.");
            const globalSetTerm = getTermRef(setGlobal.value);

            const finalHCITerm = HomCovFunctorIdentity(elabDomainCat, elabObjW);
            // Type is Functor A Set
            return { elaboratedTerm: finalHCITerm, type: FunctorTypeTerm(elabDomainCat, globalSetTerm) };
        }
        case 'SetTerm': return { elaboratedTerm: current, type: CatTerm() }; // Set is a category
        default:
            const exhaustiveCheck: never = current;
            throw new Error(`Infer: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
}

/**
 * Checks if a term has an expected type.
 * @param ctx The current context.
 * @param term The term to check.
 * @param expectedType The type the term is expected to have.
 * @param stackDepth Recursion depth.
 * @param isSubElaboration Flag to indicate if this is a recursive call.
 * @returns The elaborated term if it checks against the expected type.
 * @throws Error if type checking fails.
 */
export function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0, isSubElaboration: boolean = false): Term {
    if (stackDepth > MAX_STACK_DEPTH) {
        throw new Error(`check: Max stack depth exceeded. Term: ${printTerm(term)}, Expected: ${printTerm(expectedType)}`);
    }

    const originalTerm = term;
    const termWithKernelImplicits = ensureKernelImplicitsPresent(originalTerm);
    let currentTerm = getTermRef(termWithKernelImplicits);
    const currentExpectedType = getTermRef(expectedType); // Dereference expected type too

    const expectedTypeWhnf = whnf(currentExpectedType, ctx, stackDepth + 1);

    // Rule for implicit lambda insertion (eta-expansion for implicit Pi types)
    // If expecting Π {x:A}.B and term is not an implicit lambda, wrap term in λ {x:A}. (check term B[x])
    if (expectedTypeWhnf.tag === 'Pi' && expectedTypeWhnf.icit === Icit.Impl) {
        const termRef = getTermRef(currentTerm);
        if (!(termRef.tag === 'Lam' && termRef.icit === Icit.Impl)) {
            const lamParamName = expectedTypeWhnf.paramName;
            const lamParamType = getTermRef(expectedTypeWhnf.paramType);

            const newLam = Lam(
                lamParamName,
                Icit.Impl,
                lamParamType,
                (v_actual_arg: Term) => { // v_actual_arg is the placeholder for the implicitly bound variable
                    const bodyCheckCtx = extendCtx(ctx, lamParamName, lamParamType, Icit.Impl, v_actual_arg);
                    const bodyExpectedTypeInner = whnf(expectedTypeWhnf.bodyType(v_actual_arg), bodyCheckCtx);
                    // The original term `termRef` is checked against the expected body type in the new context
                    return check(bodyCheckCtx, termRef, bodyExpectedTypeInner, stackDepth + 1, true);
                }
            );
            return newLam; // Return the new lambda
        }
    }

    // Rule for checking lambdas against Pi types
    if (currentTerm.tag === 'Lam' && expectedTypeWhnf.tag === 'Pi' && currentTerm.icit === expectedTypeWhnf.icit) {
        const lamNode = currentTerm;
        const expectedPiNode = expectedTypeWhnf;
        let lamParamType = lamNode.paramType; // Type annotation on the lambda
        const originalAnnotationState = { annotated: lamNode._isAnnotated, type: lamNode.paramType };


        if (!lamNode._isAnnotated) { // Lambda is not annotated, take type from Pi
            lamParamType = expectedPiNode.paramType;
            // Mutate the original term if it was the unannotated lambda passed in.
            // This allows the elaborated term to carry the inferred type annotation.
            if (originalTerm === lamNode && originalTerm.tag === 'Lam' && !originalTerm._isAnnotated) {
                originalTerm.paramType = lamParamType;
                originalTerm._isAnnotated = true;
            }
            // Also update currentTerm's view if it was the unannotated Lam
            lamNode.paramType = lamParamType;
            lamNode._isAnnotated = true;
        } else if (lamNode.paramType) { // Lambda is annotated, check its type against Pi's domain type
            const elabLamParamType = check(ctx, lamNode.paramType, Type(), stackDepth + 1, true);
            addConstraint(elabLamParamType, expectedPiNode.paramType, `Lam param type vs Pi param type for ${lamNode.paramName}`);
            // It's often beneficial to try to solve constraints here, especially if lamParamType was a hole.
            solveConstraints(ctx, stackDepth + 1);
            lamParamType = elabLamParamType; // Use the elaborated type
        }

        if (!lamParamType) { // Should not happen if logic above is correct
            throw new Error(`Lambda parameter type missing for ${lamNode.paramName} when checking against Pi`);
        }

        const finalLamParamType = getTermRef(lamParamType); // Ensure it's dereferenced

        // Construct the elaborated lambda
        const elabLam = Lam(lamNode.paramName, lamNode.icit, finalLamParamType,
            (v_arg: Term) => { // v_arg is placeholder for lambda's argument
                const extendedCtx = extendCtx(ctx, lamNode.paramName, finalLamParamType, lamNode.icit, v_arg);
                const actualBodyTerm = lamNode.body(Var(lamNode.paramName, true)); // Instantiate body with Var
                const expectedBodyPiType = whnf(expectedPiNode.bodyType(v_arg), extendedCtx); // Get expected type for body
                return check(extendedCtx, actualBodyTerm, expectedBodyPiType, stackDepth + 1, true); // Check body
            }
        );
        (elabLam as Term & {tag:'Lam'})._isAnnotated = true; // Mark elaborated lambda as annotated

        // Restore original annotation state on the input `term` if it was mutated and unannotated.
        if (originalTerm === lamNode && originalTerm.tag === 'Lam' && !originalAnnotationState.annotated) {
            originalTerm.paramType = originalAnnotationState.type;
            originalTerm._isAnnotated = false;
        } else if (currentTerm === lamNode && !originalAnnotationState.annotated) {
            lamNode.paramType = originalAnnotationState.type;
            lamNode._isAnnotated = false;
        }

        return elabLam;
    }

    // Special handling for holes: if a hole is checked against a type,
    // its elaboratedType is unified with the expected type.
    if (currentTerm.tag === 'Hole') {
        if (!currentTerm.elaboratedType) {
            currentTerm.elaboratedType = expectedTypeWhnf; // Assign if not already typed
        } else {
            // If already has a type, add a constraint.
            addConstraint(getTermRef(currentTerm.elaboratedType), expectedTypeWhnf, `check Hole ${currentTerm.id}: elaboratedType vs expectedType`);
            solveConstraints(ctx, stackDepth + 1); // Try to solve immediately
        }
        return currentTerm;
    }

    // Default case: infer type, insert implicits, then check against expected
    let { elaboratedTerm: inferredElabTerm, type: inferredType } = infer(ctx, currentTerm, stackDepth + 1, true);

    // Insert implicit applications based on the inferred type before comparing with expectedTypeWhnf
    const afterInsert = insertImplicitApps(ctx, inferredElabTerm, inferredType, stackDepth + 1);

    // Add constraint: (type of term after implicit insertion) should be equal to (expected type)
    addConstraint(whnf(afterInsert.type, ctx), expectedTypeWhnf, `check general: inferredType(${printTerm(afterInsert.term)}) vs expectedType(${printTerm(expectedTypeWhnf)})`);
    // It's crucial to attempt to solve constraints here. If this fails, the check fails.
    // This was moved to the end of the `elaborate` function for the top-level call,
    // but sub-elaborations might benefit from intermediate solving.
    // For now, let the final solve handle it unless specific issues arise.
    // solveConstraints(ctx, stackDepth + 1);


    return afterInsert.term; // Return the term after potential implicit applications
}

/**
 * Main elaboration function. Drives either `check` or `infer` based on
 * whether an expected type is provided. Solves all generated constraints.
 * @param term The term to elaborate.
 * @param expectedType Optional expected type for the term.
 * @param initialCtx The initial context for elaboration.
 * @param options Elaboration options (e.g., whether to normalize the result).
 * @returns An ElaborationResult containing the elaborated term and its final type.
 * @throws Error if elaboration fails (e.g., type mismatch, unsolved constraints).
 */
export function elaborate(
    term: Term,
    expectedType?: Term,
    initialCtx: Context = emptyCtx,
    options: ElaborationOptions = { normalizeResultTerm: true }
): ElaborationResult {
    const originalConstraintsBackup = [...constraints]; // Backup constraints
    constraints.length = 0; // Clear global constraints for this elaboration session

    let finalTermToReport: Term;
    let finalTypeToReport: Term;

    try {
        if (expectedType) {
            // First, ensure the expectedType itself is well-formed (i.e., it is a Type)
            const elaboratedExpectedType = check(initialCtx, expectedType, Type(), 0, true);
            finalTermToReport = check(initialCtx, term, elaboratedExpectedType);
            finalTypeToReport = elaboratedExpectedType; // The type of the result is the (elaborated) expected type
        } else {
            // No expected type, so infer, then insert implicits
            const inferResult = infer(initialCtx, term);
            const afterInsert = insertImplicitApps(initialCtx, inferResult.elaboratedTerm, inferResult.type, 0);
            finalTermToReport = afterInsert.term;
            finalTypeToReport = afterInsert.type;
        }

        // Attempt to solve all generated constraints
        if (!solveConstraints(initialCtx)) {
            const fc = constraints.find(c_debug => !areEqual(getTermRef(c_debug.t1), getTermRef(c_debug.t2), initialCtx, 0));
            let fcMsg = "Unknown constraint";
            if (fc) {
                fcMsg = `${printTerm(getTermRef(fc.t1))} vs ${printTerm(getTermRef(fc.t2))} (orig: ${fc.origin || 'unspecified'})`;
            }
            console.error("Remaining constraints on failure during elaboration:");
            constraints.forEach(c_debug => {
                 const c_t1_dbg = getTermRef(c_debug.t1); const c_t2_dbg = getTermRef(c_debug.t2);
                 console.error(`  ${printTerm(c_t1_dbg)} ${areEqual(c_t1_dbg, c_t2_dbg, initialCtx,0) ? "===" : "=/="} ${printTerm(c_t2_dbg)} (origin: ${c_debug.origin || 'unknown'})`);
            });
            throw new Error(`Type error: Could not solve constraints. Approx failing: ${fcMsg}`);
        }
    } catch (e) {
        // Restore constraints before re-throwing
        constraints.splice(0, constraints.length, ...originalConstraintsBackup);
        if (e instanceof Error && (e.message.startsWith("Type error:") || e.message.includes("Unbound variable:") || e.message.includes("Cannot apply non-function:") || e.message.includes("Constant symbol") || e.message.includes("stack depth exceeded"))) {
            throw e; // Re-throw known elaboration errors
        }
        // For unknown errors, wrap them
        throw new Error(`Elaboration internal error: ${(e as Error).message} on term ${printTerm(term)}. Stack: ${(e as Error).stack}`);
    } finally {
        // Always restore constraints if not re-thrown
        if (constraints.length !== originalConstraintsBackup.length || !constraints.every((c, i) => c === originalConstraintsBackup[i])) {
             constraints.splice(0, constraints.length, ...originalConstraintsBackup);
        }
    }

    // Final processing of the result
    const finalResultTerm = options.normalizeResultTerm
        ? normalize(finalTermToReport, initialCtx)
        : getTermRef(finalTermToReport); // At least dereference it
    const finalResultType = whnf(getTermRef(finalTypeToReport), initialCtx); // WHNF the final type

    return { term: finalResultTerm, type: finalResultType };
}