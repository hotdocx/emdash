/**
 * @file elaboration.ts
 *
 * Handles the elaboration process for Emdash terms.
 * This includes type inference (`infer`), type checking (`check`),
 * managing implicit arguments, and applying substitutions for rewrite rules.
 * It bridges the gap between raw input terms and fully typed, elaborated terms.
 */

import {
    Term, Context, PatternVarDecl, Substitution, ElaborationResult, Icit,
    Hole, Var, App, Lam, Pi, Type, CatTerm, ObjTerm, HomTerm, FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm, NatTransComponentTerm,
    HomCovFunctorIdentity, SetTerm, FunctorTypeTerm,
    BaseTerm // For type extraction
} from './types';
import {
    emptyCtx, extendCtx, lookupCtx, globalDefs, addConstraint, getTermRef,
    freshHoleName, freshVarName, consoleLog, constraints, CORE_MAX_STACK_DEPTH
} from './state';
import { whnf, normalize, areEqual, solveConstraints } from './logic';
import { KERNEL_IMPLICIT_SPECS, KernelImplicitSpec } from './kernel_metadata';
import { printTerm } from './utils';


// --- Type Aliases for Extracted Term Types (used for casting within specific cases) ---
type FunctorCategoryTermType = Extract<BaseTerm, { tag: 'FunctorCategoryTerm' }>;
type FunctorTypeTermType = Extract<BaseTerm, { tag: 'FunctorTypeTerm' }>;
type FMap0TermType = Extract<BaseTerm, { tag: 'FMap0Term' }>;
type FMap1TermType = Extract<BaseTerm, { tag: 'FMap1Term' }>;
type NatTransTypeTermType = Extract<BaseTerm, { tag: 'NatTransTypeTerm' }>;
type NatTransComponentTermType = Extract<BaseTerm, { tag: 'NatTransComponentTerm' }>;


export interface ElaborationOptions {
    normalizeResultTerm?: boolean;
}

/**
 * Ensures that kernel-defined terms have their specified implicit arguments present.
 * If an implicit argument is missing (undefined), it's filled with a fresh hole.
 * This is crucial for allowing users to write kernel terms more concisely.
 * @param term The term to process.
 * @returns The term, potentially modified with filled-in implicit arguments.
 */
export function ensureKernelImplicitsPresent(term: Term): Term {
    const originalTermTag = term.tag;

    for (const spec of KERNEL_IMPLICIT_SPECS as Array<KernelImplicitSpec<Term>>) {
        if (originalTermTag === spec.tag) {
            // Cast to a more generic type to allow dynamic property access,
            // knowing that the tag match ensures 'term' is of the type T expected by spec.fields.
            const specificTerm = term as Term & { [key: string]: any };
            for (const fieldName of spec.fields) { // fieldName is typed correctly due to KernelImplicitSpec
                if (specificTerm[fieldName as string] === undefined) {
                    let baseHint = spec.tag.toLowerCase().replace(/morph|term/g, '').replace(/_/g, '');
                    const fieldHint = (fieldName as string).replace('_IMPLICIT', '').toLowerCase();

                    // Add more specific hints for common terms if useful
                    let dynamicHintPart = "";
                    // Example: if (spec.tag === 'IdentityMorph' && specificTerm.obj) { ... }

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
 * Inserts implicit applications to a term based on its Pi type.
 * If `type` is `Π {i:T}. U`, and `term` is not an implicit lambda,
 * this function transforms `term` into `term {@h}` and `type` into `U{@h/i}`.
 * This process repeats for all leading implicit Pi binders.
 * @param ctx The current context.
 * @param term The term to which implicit arguments might be applied.
 * @param type The type of the term.
 * @param stackDepth Current recursion depth.
 * @param unConditional If true, inserts implicits even if term is an implicit lambda (used by App explicit case).
 * @returns The modified term, its new type, and whether progress was made.
 */
function insertImplicitApps(ctx: Context, term: Term, type: Term, stackDepth: number, unConditional: boolean = false): { term: Term, type: Term, progress?: boolean } {
    let currentTerm = term;
    let currentType = whnf(type, ctx, stackDepth + 1);
    let progress = false;

    // Standard behavior: Do not insert if the term itself is an implicit lambda,
    // unless `unConditional` is true (e.g. when an explicit application definitely expects prior implicits to be filled).
    const termRef = getTermRef(currentTerm);
    if (termRef.tag === 'Lam' && termRef.icit === Icit.Impl && !unConditional) {
        return { term: currentTerm, type: currentType, progress: false };
    }

    while (currentType.tag === 'Pi' && currentType.icit === Icit.Impl) {
        const implHole = Hole(freshHoleName() + "_auto_impl_arg");
        if (currentType.paramType) {
            // Annotate the hole with its expected type for better diagnostics and subsequent checks
            (implHole as Term & {tag:'Hole'}).elaboratedType = currentType.paramType;
        }
        currentTerm = App(currentTerm, implHole, Icit.Impl);
        currentType = whnf(currentType.bodyType(implHole), ctx, stackDepth + 1); // Apply hole to body type
        progress = true;
    }
    return { term: currentTerm, type: currentType, progress };
}

/**
 * Infers the type of a given term in the provided context.
 * @param ctx The current context.
 * @param term The term to infer the type of.
 * @param stackDepth Current recursion depth.
 * @param isSubElaboration True if this call is part of a larger ongoing elaboration (e.g. checking body of a Lam/Pi).
 * @returns An object containing the elaborated term and its inferred type.
 */
export function infer(ctx: Context, term: Term, stackDepth: number = 0, isSubElaboration: boolean = false): InferResult {
    if (stackDepth > CORE_MAX_STACK_DEPTH) throw new Error(`Infer stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);

    const termWithKernelImplicits = ensureKernelImplicitsPresent(term);
    let current = getTermRef(termWithKernelImplicits);

    if (current.tag === 'Var') {
        const localBinding = lookupCtx(ctx, current.name);
        if (localBinding) {
            // If variable has a local definition (let-binding), use its definition and type.
            // The definition itself should be elaborated/normalized as needed by whnf if it's used.
            return { elaboratedTerm: localBinding.definition || current, type: localBinding.type };
        }

        const gdef = globalDefs.get(current.name);
        if (gdef) return { elaboratedTerm: current, type: gdef.type };

        // Handle special placeholder variables from occurs checks etc.
        if (current.origin === "occurs_check" || current.origin === "pattern_var") {
            consoleLog(`[Infer Special Placeholder/PatternVar] Detected var: ${current.name}`);
            const placeholderType = Hole("_type_of_placeholder_var_" + current.name.replace(/[?$]/g, ""));
            (placeholderType as Term & {tag:'Hole'}).elaboratedType = Type(); // It's a type for some term
            return { elaboratedTerm: current, type: placeholderType };
        }

        throw new Error(`Unbound variable: ${current.name} in context [${ctx.map(b => b.name).join(', ')}]`);
    }

    switch (current.tag) {
        case 'Type': return { elaboratedTerm: current, type: Type() };
        case 'Hole': {
            if (current.elaboratedType) return { elaboratedTerm: current, type: getTermRef(current.elaboratedType) };
            // If a hole's type is not yet known, assign a fresh hole type to it.
            const newTypeForHole = Hole(freshHoleName() + "_type_of_" + current.id.replace("?", "h"));
            (newTypeForHole as Term & {tag:'Hole'}).elaboratedType = Type(); // This new hole is itself a type.
            current.elaboratedType = newTypeForHole;
            return { elaboratedTerm: current, type: newTypeForHole };
        }
        case 'App': {
            const appNode = current;
            let { elaboratedTerm: inferredFuncElab, type: inferredFuncType } = infer(ctx, appNode.func, stackDepth + 1, isSubElaboration);

            let funcAfterImplicits = inferredFuncElab;
            let typeFAfterImplicits = whnf(inferredFuncType, ctx, stackDepth + 1);

            // If current application is explicit, try to insert any pending implicit arguments for the function.
            if (appNode.icit === Icit.Expl) {
                const inserted = insertImplicitApps(ctx, funcAfterImplicits, typeFAfterImplicits, stackDepth + 1, true); // `unConditional = true`
                funcAfterImplicits = inserted.term;
                typeFAfterImplicits = inserted.type;
            }

            const whnfOfFuncType = whnf(typeFAfterImplicits, ctx, stackDepth + 1);
            let expectedParamTypeFromPi: Term;
            let bodyTypeFnFromPi: (argVal: Term) => Term;

            if (whnfOfFuncType.tag === 'Pi' && whnfOfFuncType.icit === appNode.icit) {
                expectedParamTypeFromPi = whnfOfFuncType.paramType;
                bodyTypeFnFromPi = whnfOfFuncType.bodyType;
            } else if (whnfOfFuncType.tag === 'Pi' && whnfOfFuncType.icit !== appNode.icit) {
                throw new Error(`Type error in App (${appNode.icit === Icit.Expl ? "explicit" : "implicit"}): function ${printTerm(funcAfterImplicits)} of type ${printTerm(whnfOfFuncType)} expects a ${whnfOfFuncType.icit === Icit.Expl ? "explicit" : "implicit"} argument, but an ${appNode.icit === Icit.Expl ? "explicit" : "implicit"} one was provided for ${printTerm(appNode.arg)}.`);
            } else {
                // Function type is not a Pi or doesn't match icit. We need to make it one.
                const freshPiParamName = freshVarName("pi_param_app");
                const paramTypeHole = Hole(freshHoleName() + "_app_paramT_infer");
                (paramTypeHole as Term & {tag:'Hole'}).elaboratedType = Type();
                const bodyTypeHole = Hole(freshHoleName() + "_app_bodyT_infer");
                (bodyTypeHole as Term & {tag:'Hole'}).elaboratedType = Type();

                const targetPiType = Pi(freshPiParamName, appNode.icit, paramTypeHole, (_arg: Term) => bodyTypeHole);
                addConstraint(typeFAfterImplicits, targetPiType, `App: func ${printTerm(funcAfterImplicits)} type must be Pi for arg ${printTerm(appNode.arg)}`);
                // Attempt to solve constraints to determine paramTypeHole and bodyTypeHole if possible.
                // If this sub-elaboration is part of a larger one, solving might be deferred.
                if (!isSubElaboration) solveConstraints(ctx, stackDepth + 1);


                expectedParamTypeFromPi = paramTypeHole; // Use the hole as the expected type
                bodyTypeFnFromPi = (_argVal: Term) => bodyTypeHole; // And the body hole for the result type
            }

            const elaboratedArg = check(ctx, appNode.arg, expectedParamTypeFromPi, stackDepth + 1, isSubElaboration);
            const finalAppTerm = App(getTermRef(funcAfterImplicits), getTermRef(elaboratedArg), appNode.icit);
            const resultType = whnf(bodyTypeFnFromPi(getTermRef(elaboratedArg)), ctx, stackDepth + 1);

            return { elaboratedTerm: finalAppTerm, type: resultType };
        }
        case 'Lam': {
            const lamNode = current;
            let actualParamType: Term;
            const originalAnnotationState = { annotated: lamNode._isAnnotated, type: lamNode.paramType };

            if (lamNode._isAnnotated && lamNode.paramType) {
                // If annotated, check that the provided type is indeed a Type.
                actualParamType = check(ctx, lamNode.paramType, Type(), stackDepth + 1, isSubElaboration);
            } else {
                // If not annotated, create a hole for the parameter type.
                actualParamType = Hole(freshHoleName() + "_lam_" + lamNode.paramName + "_paramT_infer");
                (actualParamType as Term & {tag:'Hole'}).elaboratedType = Type(); // This hole stands for a type.
                // Temporarily update the LamNode for subsequent logic, will be restored if needed.
                lamNode.paramType = actualParamType;
                lamNode._isAnnotated = true;
            }

            // Construct the Pi type for this lambda.
            const piType = Pi(
                lamNode.paramName,
                lamNode.icit,
                actualParamType, // Use the (potentially holed) parameter type.
                (piBodyArg: Term): Term => {
                    // Infer the type of the lambda's body in a context extended with the parameter.
                    // The piBodyArg represents the parameter variable for the body's type.
                    const bodyInferCtx = extendCtx(ctx, lamNode.paramName, actualParamType, lamNode.icit, piBodyArg);
                    const lambdaBodyStructure = lamNode.body(Var(lamNode.paramName, true)); // Get body structure
                    let { elaboratedTerm: inferredBodyElab, type: inferredBodyType } = infer(bodyInferCtx, lambdaBodyStructure, stackDepth + 1, true); // isSubElaboration = true

                    // Insert implicits for the body if necessary
                    const insertedBody = insertImplicitApps(bodyInferCtx, inferredBodyElab, inferredBodyType, stackDepth + 1);
                    return insertedBody.type; // The type of the (potentially implicit-applied) body
                }
            );

            // Construct the elaborated lambda term.
            const elaboratedLam = Lam(
                lamNode.paramName,
                lamNode.icit,
                getTermRef(actualParamType), // Use the final, potentially refined, parameter type.
                (v: Term) => { // v is the argument placeholder for the lambda body
                    const bodyInferCtx = extendCtx(ctx, lamNode.paramName, getTermRef(actualParamType), lamNode.icit, v);
                    const bodyTermRaw = lamNode.body(Var(lamNode.paramName, true)); // Get body structure
                    let { elaboratedTerm: inferredBodyElab, type: inferredBodyType } = infer(bodyInferCtx, bodyTermRaw, stackDepth + 1, true);

                    const insertedBody = insertImplicitApps(bodyInferCtx, inferredBodyElab, inferredBodyType, stackDepth + 1);
                    return insertedBody.term; // Return the elaborated body
                }
            );
            (elaboratedLam as Term & {tag: 'Lam'})._isAnnotated = true; // The elaborated form is always "annotated"

            // Restore original annotation state if the input `term` was directly mutated
            if (term === lamNode && term.tag === 'Lam' && !originalAnnotationState.annotated) {
                term.paramType = originalAnnotationState.type;
                term._isAnnotated = originalAnnotationState.annotated;
            }


            return { elaboratedTerm: elaboratedLam, type: piType };
        }
        case 'Pi': {
            const piNode = current;
            // Check that the parameter type is a valid type.
            const elaboratedParamType = check(ctx, piNode.paramType, Type(), stackDepth + 1, isSubElaboration);
            // Check that the body type (instantiated with the param) is a valid type.
            const extendedCtx = extendCtx(ctx, piNode.paramName, elaboratedParamType, piNode.icit);
            const bodyTypeInstance = piNode.bodyType(Var(piNode.paramName, true)); // Get body type structure
            check(extendedCtx, bodyTypeInstance, Type(), stackDepth + 1, true); // isSubElaboration = true

            // Construct the final Pi term with elaborated components.
            const finalPi = Pi(piNode.paramName, piNode.icit, getTermRef(elaboratedParamType), (v: Term) => {
                const bodyCtx = extendCtx(ctx, piNode.paramName, getTermRef(elaboratedParamType), piNode.icit, v);
                const piNodeBodyType = piNode.bodyType(Var(piNode.paramName, true));
                // The body type function for the final Pi should return an already checked type.
                return check(bodyCtx, piNodeBodyType, Type(), stackDepth + 1, true);
            });
            return { elaboratedTerm: finalPi, type: Type() }; // A Pi type itself has type Type.
        }
        // --- Category Theory Terms ---
        case 'CatTerm': return { elaboratedTerm: current, type: Type() };
        case 'ObjTerm': {
            const elabCat = check(ctx, current.cat, CatTerm(), stackDepth + 1, isSubElaboration);
            return { elaboratedTerm: ObjTerm(elabCat), type: Type() };
        }
        case 'HomTerm': {
            const elabCat = check(ctx, current.cat, CatTerm(), stackDepth + 1, isSubElaboration);
            const catForHom = getTermRef(elabCat); // Use whnf'd cat for object checks
            const elabDom = check(ctx, current.dom, ObjTerm(catForHom), stackDepth + 1, isSubElaboration);
            const elabCod = check(ctx, current.cod, ObjTerm(catForHom), stackDepth + 1, isSubElaboration);
            return { elaboratedTerm: HomTerm(elabCat, elabDom, elabCod), type: Type() };
        }
        case 'FunctorCategoryTerm': {
            const fcTerm = current as Term & FunctorCategoryTermType;
            const elabDomainCat = check(ctx, fcTerm.domainCat, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabCodomainCat = check(ctx, fcTerm.codomainCat, CatTerm(), stackDepth + 1, isSubElaboration);
            return { elaboratedTerm: FunctorCategoryTerm(elabDomainCat, elabCodomainCat), type: CatTerm() };
        }
        case 'FunctorTypeTerm': {
            const fttTerm = current as Term & FunctorTypeTermType;
            const elabDomainCat = check(ctx, fttTerm.domainCat, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabCodomainCat = check(ctx, fttTerm.codomainCat, CatTerm(), stackDepth + 1, isSubElaboration);
            return { elaboratedTerm: FunctorTypeTerm(elabDomainCat, elabCodomainCat), type: Type() };
        }
        case 'FMap0Term': {
            const fm0Term = current as Term & FMap0TermType;
            // Implicit arguments must be filled by ensureKernelImplicitsPresent before this point
            if (!fm0Term.catA_IMPLICIT || !fm0Term.catB_IMPLICIT) throw new Error("FMap0Term missing implicit categories during inference.");

            const elabCatA = check(ctx, fm0Term.catA_IMPLICIT, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabCatB = check(ctx, fm0Term.catB_IMPLICIT, CatTerm(), stackDepth + 1, isSubElaboration);

            const expectedFunctorType = FunctorTypeTerm(elabCatA, elabCatB);
            const elabFunctor = check(ctx, fm0Term.functor, expectedFunctorType, stackDepth + 1, isSubElaboration);

            const expectedObjectType = ObjTerm(elabCatA);
            const elabObjectX = check(ctx, fm0Term.objectX, expectedObjectType, stackDepth + 1, isSubElaboration);

            const finalFMap0 = FMap0Term(elabFunctor, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB));
            return { elaboratedTerm: finalFMap0, type: ObjTerm(getTermRef(elabCatB)) };
        }
        case 'FMap1Term': {
            const fm1Term = current as Term & FMap1TermType;
            if (!fm1Term.catA_IMPLICIT || !fm1Term.catB_IMPLICIT || !fm1Term.objX_A_IMPLICIT || !fm1Term.objY_A_IMPLICIT) {
                throw new Error("FMap1Term missing implicit arguments during inference.");
            }

            const elabCatA = check(ctx, fm1Term.catA_IMPLICIT, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabCatB = check(ctx, fm1Term.catB_IMPLICIT, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabObjX_A = check(ctx, fm1Term.objX_A_IMPLICIT, ObjTerm(elabCatA), stackDepth + 1, isSubElaboration);
            const elabObjY_A = check(ctx, fm1Term.objY_A_IMPLICIT, ObjTerm(elabCatA), stackDepth + 1, isSubElaboration);

            const expectedFunctorType = FunctorTypeTerm(elabCatA, elabCatB);
            const elabFunctor = check(ctx, fm1Term.functor, expectedFunctorType, stackDepth + 1, isSubElaboration);

            const expectedMorphismType = HomTerm(elabCatA, elabObjX_A, elabObjY_A);
            const elabMorphism_a = check(ctx, fm1Term.morphism_a, expectedMorphismType, stackDepth + 1, isSubElaboration);

            // Result type: Hom catB (FMap0 F X) (FMap0 F Y)
            const fmap0_X = FMap0Term(elabFunctor, elabObjX_A, getTermRef(elabCatA), getTermRef(elabCatB));
            const fmap0_Y = FMap0Term(elabFunctor, elabObjY_A, getTermRef(elabCatA), getTermRef(elabCatB));

            const finalFMap1 = FMap1Term(elabFunctor, elabMorphism_a, getTermRef(elabCatA), getTermRef(elabCatB), getTermRef(elabObjX_A), getTermRef(elabObjY_A));
            return { elaboratedTerm: finalFMap1, type: HomTerm(getTermRef(elabCatB), fmap0_X, fmap0_Y) };
        }
        case 'NatTransTypeTerm': {
            const ntTerm = current as Term & NatTransTypeTermType;
            const elabCatA = check(ctx, ntTerm.catA, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabCatB = check(ctx, ntTerm.catB, CatTerm(), stackDepth + 1, isSubElaboration);
            const expectedFunctorType = FunctorTypeTerm(elabCatA, elabCatB);
            const elabFunctorF = check(ctx, ntTerm.functorF, expectedFunctorType, stackDepth + 1, isSubElaboration);
            const elabFunctorG = check(ctx, ntTerm.functorG, expectedFunctorType, stackDepth + 1, isSubElaboration);

            const finalNatTransType = NatTransTypeTerm(elabCatA, elabCatB, elabFunctorF, elabFunctorG);
            return { elaboratedTerm: finalNatTransType, type: Type() };
        }
        case 'NatTransComponentTerm': {
            const ncTerm = current as Term & NatTransComponentTermType;
            if (!ncTerm.catA_IMPLICIT || !ncTerm.catB_IMPLICIT || !ncTerm.functorF_IMPLICIT || !ncTerm.functorG_IMPLICIT) {
                throw new Error("NatTransComponentTerm missing implicit arguments during inference.");
            }
            const elabCatA = check(ctx, ncTerm.catA_IMPLICIT, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabCatB = check(ctx, ncTerm.catB_IMPLICIT, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabFunctorF = check(ctx, ncTerm.functorF_IMPLICIT, FunctorTypeTerm(elabCatA, elabCatB), stackDepth + 1, isSubElaboration);
            const elabFunctorG = check(ctx, ncTerm.functorG_IMPLICIT, FunctorTypeTerm(elabCatA, elabCatB), stackDepth + 1, isSubElaboration);

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
            const elabDomainCat = check(ctx, hciTerm.domainCat, CatTerm(), stackDepth + 1, isSubElaboration);
            const elabObjW = check(ctx, hciTerm.objW_InDomainCat, ObjTerm(elabDomainCat), stackDepth + 1, isSubElaboration);

            const setGlobal = globalDefs.get("Set");
            if (!setGlobal || !setGlobal.value) throw new Error("Global 'Set' category not defined for HomCovFunctorIdentity type inference.");
            const globalSetTerm = getTermRef(setGlobal.value); // Should be SetTerm()

            const finalHCITerm = HomCovFunctorIdentity(elabDomainCat, elabObjW);
            return {
                elaboratedTerm: finalHCITerm,
                type: FunctorTypeTerm(elabDomainCat, globalSetTerm)
            };
        }
        case 'SetTerm': return { elaboratedTerm: current, type: CatTerm() };
        default:
            const exhaustiveCheck: never = current;
            throw new Error(`Infer: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
}

/**
 * Checks if a term has the expected type in the given context.
 * @param ctx The current context.
 * @param term The term to check.
 * @param expectedType The type the term is expected to have.
 * @param stackDepth Current recursion depth.
 * @param isSubElaboration True if this call is part of a larger ongoing elaboration.
 * @returns The elaborated term, which is guaranteed to have the expected type (possibly via added constraints).
 */
export function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0, isSubElaboration: boolean = false): Term {
    if (stackDepth > CORE_MAX_STACK_DEPTH) {
        throw new Error(`check: Max stack depth exceeded. Term: ${printTerm(term)}, Expected: ${printTerm(expectedType)}`);
    }

    const termWithKernelImplicits = ensureKernelImplicitsPresent(term);
    let currentTerm = getTermRef(termWithKernelImplicits);
    const currentExpectedType = getTermRef(expectedType); // Ensure expected type is also dereferenced

    const expectedTypeWhnf = whnf(currentExpectedType, ctx, stackDepth + 1);

    // Rule for implicit lambda insertion (η-expansion for implicit Pi types)
    // If expecting Π {x:A}.B and term is t, check (λ {x:A}. t) against Π {x:A}.B
    // This effectively means checking t against B in context extended with x:A.
    if (expectedTypeWhnf.tag === 'Pi' && expectedTypeWhnf.icit === Icit.Impl) {
        const termRef = getTermRef(currentTerm); // Re-evaluate currentTerm after potential modifications
        // Only insert implicit lambda if term is NOT already an implicit lambda
        if (!(termRef.tag === 'Lam' && termRef.icit === Icit.Impl)) {
            const lamParamName = expectedTypeWhnf.paramName; // Or freshVarName if clashes are an issue
            const lamParamType = getTermRef(expectedTypeWhnf.paramType); // Param type from Pi

            // Construct the new lambda that will be checked.
            // The body of this new lambda is the original term `termRef`.
            // We need to check this original term `termRef` against the body of the Pi type.
            const newLam = Lam(
                lamParamName,
                Icit.Impl,
                lamParamType,
                (v_actual_arg: Term) => { // v_actual_arg is the placeholder for the lambda's parameter
                    const bodyCheckCtx = extendCtx(ctx, lamParamName, lamParamType, Icit.Impl, v_actual_arg);
                    // The expected type for the original term `termRef` is the body of the Pi, instantiated with v_actual_arg.
                    const bodyExpectedTypeInner = whnf(expectedTypeWhnf.bodyType(v_actual_arg), bodyCheckCtx);
                    // Check the original term `termRef` against this new expected type.
                    return check(bodyCheckCtx, termRef, bodyExpectedTypeInner, stackDepth + 1, true); // isSubElaboration = true
                }
            );
            // The elaborated term is this newly constructed lambda.
            return newLam;
        }
    }

    // Rule for checking lambdas against Pi types (conversion rule or basic type checking)
    if (currentTerm.tag === 'Lam' && expectedTypeWhnf.tag === 'Pi' && currentTerm.icit === expectedTypeWhnf.icit) {
        const lamNode = currentTerm;
        const expectedPiNode = expectedTypeWhnf;
        let lamParamType = lamNode.paramType; // Type annotation on the lambda, if any.
        const originalAnnotationState = { annotated: lamNode._isAnnotated, type: lamNode.paramType };


        if (!lamNode._isAnnotated) { // Lambda is unannotated, e.g., λ x. body
            // Infer parameter type from the Pi type.
            lamParamType = expectedPiNode.paramType;
            // Mutate the currentTerm (if it's the original unannotated Lam) or a copy to be annotated.
             if (term === lamNode && term.tag === 'Lam' && !term._isAnnotated) {
                term.paramType = lamParamType;
                term._isAnnotated = true;
            }
            lamNode.paramType = lamParamType; // Ensure lamNode used below has the type
            lamNode._isAnnotated = true;
        } else if (lamParamType) { // Lambda is annotated, e.g., λ (x : T). body
            // Check the lambda's annotated type against the Pi's parameter type.
            const elabLamParamType = check(ctx, lamParamType, Type(), stackDepth + 1, isSubElaboration); // Annotation must be a type
            addConstraint(elabLamParamType, expectedPiNode.paramType, `Lam param type vs Pi param type for ${lamNode.paramName}`);
            if (!isSubElaboration) solveConstraints(ctx, stackDepth + 1);
            lamParamType = elabLamParamType; // Use the elaborated form of the annotation.
        }

        if (!lamParamType) { // Should not happen if logic above is correct
            throw new Error(`Lambda parameter type missing for ${lamNode.paramName} when checking against Pi type ${printTerm(expectedPiNode)}`);
        }

        const finalLamParamType = lamParamType; // Capture for closure.
        const elaboratedLamBodyFn = (v_arg: Term) => {
            const extendedBodyCtx = extendCtx(ctx, lamNode.paramName, finalLamParamType, lamNode.icit, v_arg);
            const actualBodyTerm = lamNode.body(Var(lamNode.paramName, true)); // Instantiate lambda body
            const expectedBodyPiType = whnf(expectedPiNode.bodyType(v_arg), extendedBodyCtx); // Instantiate Pi body type
            return check(extendedBodyCtx, actualBodyTerm, expectedBodyPiType, stackDepth + 1, true); // isSubElaboration = true
        };

        // Restore original annotation state if the input `term` was directly mutated
        if (term === lamNode && term.tag === 'Lam' && !originalAnnotationState.annotated) {
            term.paramType = originalAnnotationState.type;
            term._isAnnotated = originalAnnotationState.annotated;
        }

        return Lam(lamNode.paramName, lamNode.icit, finalLamParamType, elaboratedLamBodyFn);
    }

    // Rule for Holes: if ?h : A, and we check ?h against B, then A = B.
    if (currentTerm.tag === 'Hole') {
        if (!currentTerm.elaboratedType) {
            // If hole has no type yet, assign it the expected type.
            currentTerm.elaboratedType = expectedTypeWhnf;
        } else {
            // If hole already has a type, constrain it to be equal to the expected type.
            addConstraint(getTermRef(currentTerm.elaboratedType), expectedTypeWhnf, `check Hole ${currentTerm.id}: elaboratedType vs expectedType`);
            if (!isSubElaboration) solveConstraints(ctx, stackDepth + 1);
        }
        return currentTerm;
    }

    // Default case (conversion rule): infer type of term, then check if it's convertible to expected type.
    let { elaboratedTerm: inferredElabTerm, type: inferredType } = infer(ctx, currentTerm, stackDepth + 1, isSubElaboration);

    // After inferring, the term might be a function that needs implicit arguments applied.
    const afterInsert = insertImplicitApps(ctx, inferredElabTerm, inferredType, stackDepth + 1);

    // Constrain the (potentially implicit-applied) inferred type with the expected type.
    addConstraint(whnf(afterInsert.type, ctx), expectedTypeWhnf, `check general: inferredType(${printTerm(afterInsert.term)}) vs expectedType(${printTerm(expectedTypeWhnf)})`);
    if (!isSubElaboration) solveConstraints(ctx, stackDepth + 1); // Solve constraints at the end of a check boundary.

    return afterInsert.term; // Return the term after implicit applications and constraint generation.
}


/**
 * Top-level elaboration function.
 * Infers or checks a term, solves all constraints, and optionally normalizes the result.
 * @param term The term to elaborate.
 * @param expectedType Optional expected type. If provided, `check` is used; otherwise, `infer`.
 * @param initialCtx The initial context for elaboration.
 * @param options Elaboration options, e.g., whether to normalize the final term.
 * @returns An object containing the fully elaborated term and its type.
 */
export function elaborate(
    term: Term,
    expectedType?: Term,
    initialCtx: Context = emptyCtx,
    options: ElaborationOptions = { normalizeResultTerm: true }
): ElaborationResult {
    // Backup and clear global constraints for this elaboration session.
    const originalConstraintsBackup = [...constraints];
    constraints.length = 0;

    let finalTermToReport: Term;
    let finalTypeToReport: Term;

    try {
        if (expectedType) {
            // First, ensure the expectedType itself is a valid type (i.e., it checks against Type()).
            const elaboratedExpectedType = check(initialCtx, expectedType, Type());
            finalTermToReport = check(initialCtx, term, elaboratedExpectedType);
            // The type of the result is the (elaborated) expected type.
            finalTypeToReport = elaboratedExpectedType;
        } else {
            const inferResult = infer(initialCtx, term);
            // If no expected type, infer, then insert implicits as needed.
            const afterInsert = insertImplicitApps(initialCtx, inferResult.elaboratedTerm, inferResult.type, 0);
            finalTermToReport = afterInsert.term;
            finalTypeToReport = afterInsert.type;
        }

        // Attempt to solve all generated constraints.
        if (!solveConstraints(initialCtx)) {
            const remainingConstraints = constraints.map(c =>
                `${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))} (orig: ${c.origin || 'unspecified'})`
            ).join('; ');
            throw new Error(`Type error: Could not solve constraints. Remaining: ${remainingConstraints}`);
        }
    } catch (e) {
        // Restore constraints before re-throwing.
        constraints.splice(0, constraints.length, ...originalConstraintsBackup);
        // Propagate known error types or wrap others.
        if (e instanceof Error && (e.message.startsWith("Type error:") || e.message.includes("Unbound variable:") || e.message.includes("Cannot apply non-function:") || e.message.includes("Constant symbol") || e.message.includes("stack depth exceeded"))) {
            throw e;
        }
        throw new Error(`Elaboration internal error: ${(e as Error).message} on term ${printTerm(term)}. Stack: ${(e as Error).stack}`);
    } finally {
        // Always restore constraints.
        if (constraints.length > 0 && !originalConstraintsBackup.length) {
            // If we cleared constraints but an error occurred *before* solving and there were no prior constraints,
            // it's possible some unsolved constraints remain from this failed elaboration.
            // This is tricky. Ideally, solveConstraints either solves them or throws.
            // For now, if the backup is empty, it means we started fresh.
        } else {
             constraints.splice(0, constraints.length, ...originalConstraintsBackup);
        }
    }

    // Normalize the final term and type if requested.
    // `getTermRef` is important here to resolve any hole assignments made during constraint solving.
    const finalResultTerm = options.normalizeResultTerm
        ? normalize(getTermRef(finalTermToReport), initialCtx)
        : getTermRef(finalTermToReport);
    const finalResultType = whnf(getTermRef(finalTypeToReport), initialCtx);

    return { term: finalResultTerm, type: finalResultType };
}


// --- Pattern Matching and Substitution (for Rewrite Rules) ---

/**
 * Checks if a variable name is a declared pattern variable.
 * @param name The variable name.
 * @param patternVarDecls Array of declared pattern variable names (e.g., ["$x", "$y"]).
 * @returns True if the name is a pattern variable.
 */
export function isPatternVarName(name: string, patternVarDecls: PatternVarDecl[]): boolean {
    // Pattern variables typically start with a specific prefix, e.g., '$'.
    // And they must be declared in the rule's patternVarDecls.
    return name.startsWith('$') && patternVarDecls.includes(name);
}

/**
 * Matches a pattern term against a concrete term.
 * @param pattern The pattern term (may contain pattern variables).
 * @param termToMatch The concrete term.
 * @param ctx Context (used for equality checks if needed, though matching is mostly syntactic).
 * @param patternVarDecls Declared pattern variables for this rule.
 * @param currentSubst Current substitution map (for accumulating matches).
 * @param stackDepth Recursion depth.
 * @returns A new substitution map if matching is successful, otherwise null.
 */
export function matchPattern(
    pattern: Term,
    termToMatch: Term,
    ctx: Context, // For areEqual, if it becomes necessary (e.g. matching under binders with α-eq)
    patternVarDecls: PatternVarDecl[],
    currentSubst?: Substitution,
    stackDepth = 0
): Substitution | null {
    if (stackDepth > CORE_MAX_STACK_DEPTH) throw new Error(`matchPattern stack depth exceeded for pattern ${printTerm(pattern)} vs term ${printTerm(termToMatch)}`);

    const rtPattern = getTermRef(pattern);
    const rtTermToMatch = getTermRef(termToMatch); // Term to match should be fully resolved.

    const subst = currentSubst ? new Map(currentSubst) : new Map<string, Term>();

    // Case 1: Pattern is a declared pattern variable (Var or Hole syntax for pattern var)
    if ((rtPattern.tag === 'Var' && isPatternVarName(rtPattern.name, patternVarDecls)) ||
        (rtPattern.tag === 'Hole' && isPatternVarName(rtPattern.id, patternVarDecls))) {
        const pvarName = rtPattern.tag === 'Var' ? rtPattern.name : rtPattern.id;

        if (pvarName === '_') return subst; // Wildcard matches anything, no binding.

        const existingBinding = subst.get(pvarName);
        if (existingBinding) {
            // If pattern variable already bound, current term must be equal to existing binding.
            // areEqual performs WHNF, which might be too much for simple pattern matching.
            // Structural equality or a simpler form of equality might be preferred here.
            // For now, using areEqual as it's the defined equality.
            return areEqual(rtTermToMatch, getTermRef(existingBinding), ctx, stackDepth + 1) ? subst : null;
        }
        // Bind pattern variable to the term.
        subst.set(pvarName, rtTermToMatch);
        return subst;
    }

    // Case 2: Pattern is a non-pattern Hole (e.g. a specific hole instance, not a pvar placeholder)
    if (rtPattern.tag === 'Hole') { // And not a pattern var (handled above)
        // A concrete hole in a pattern matches only the same hole in the term.
        if (rtTermToMatch.tag === 'Hole' && rtPattern.id === rtTermToMatch.id) return subst;
        return null; // Doesn't match other terms or different holes.
    }

    // Case 3: Term to match is a Hole (and pattern is not a matching Hole or pvar)
    // Generally, a non-variable pattern does not match a hole unless the pattern itself is that hole.
    if (rtTermToMatch.tag === 'Hole') return null;

    // Case 4: Tags must match for structural comparison.
    if (rtPattern.tag !== rtTermToMatch.tag) return null;

    // Case 5: Icit must match for App, Lam, Pi
    if ((rtPattern.tag === 'App' || rtPattern.tag === 'Lam' || rtPattern.tag === 'Pi') &&
        (rtTermToMatch.tag === rtPattern.tag) && rtPattern.icit !== rtTermToMatch.icit) {
        return null;
    }

    // Case 6: Structural matching for different term types.
    switch (rtPattern.tag) {
        case 'Type': case 'CatTerm': case 'SetTerm': return subst; // Tags matched, success.
        case 'Var': // Not a pattern var (handled above)
            return rtPattern.name === (rtTermToMatch as Term & {tag:'Var'}).name ? subst : null;
        case 'App': {
            const termApp = rtTermToMatch as Term & {tag:'App'};
            const s1 = matchPattern(rtPattern.func, termApp.func, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s1) return null;
            return matchPattern(rtPattern.arg, termApp.arg, ctx, patternVarDecls, s1, stackDepth + 1);
        }
        case 'Lam': {
            // Matching lambdas: parameters, icit, and bodies (under alpha-equivalence).
            // For simplicity in pattern matching, often only structural body match is done after alpha-renaming,
            // or patterns don't contain lambdas, or only match specific lambda structures.
            // Here, we assume param names don't matter for the pattern itself (they are binders).
            // Type annotations must match if present in pattern.
            const lamP = rtPattern; const lamT = rtTermToMatch as Term & {tag:'Lam'};
            if (lamP._isAnnotated !== lamT._isAnnotated) return null;
            let tempSubst = subst;
            if (lamP._isAnnotated) { // If pattern Lam is annotated, term Lam must be too, and types must match.
                if (!lamP.paramType || !lamT.paramType) return null;
                 const sType = matchPattern(lamP.paramType, lamT.paramType, ctx, patternVarDecls, tempSubst, stackDepth + 1);
                 if (!sType) return null;
                 tempSubst = sType;
            }
            // Match bodies: instantiate with a fresh var to handle bound vars correctly.
            // This basic version assumes the bodies are structurally equal after substitution.
            // A more robust version might require matching under binders or normalizing.
            const freshV = Var(freshVarName("match_lam_body"), true, "pattern_var"); // Treat as a special var for matching
            // Context extension for body matching is subtle. If pattern vars can be types, this is complex.
            // Assuming pattern vars are terms, not types used in context extension here.
            const pBody = lamP.body(freshV);
            const tBody = lamT.body(freshV);
            return matchPattern(pBody, tBody, ctx, patternVarDecls, tempSubst, stackDepth + 1);
        }
        case 'Pi': {
            // Similar to Lam, match parameter types and body types (under alpha-equivalence).
            const piP = rtPattern; const piT = rtTermToMatch as Term & {tag:'Pi'};
            const sType = matchPattern(piP.paramType, piT.paramType, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!sType) return null;
            const freshV = Var(freshVarName("match_pi_body"), true, "pattern_var");
            const pBodyType = piP.bodyType(freshV);
            const tBodyType = piT.bodyType(freshV);
            return matchPattern(pBodyType, tBodyType, ctx, patternVarDecls, sType, stackDepth + 1);
        }
        // --- Category Theory Terms ---
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
        case 'FunctorCategoryTerm': {
            const fcP = rtPattern; const fcT = rtTermToMatch as Term & {tag:'FunctorCategoryTerm'};
            let s = matchPattern(fcP.domainCat, fcT.domainCat, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s) return null;
            return matchPattern(fcP.codomainCat, fcT.codomainCat, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'FunctorTypeTerm': {
            const fttP = rtPattern as Term & FunctorTypeTermType; const fttT = rtTermToMatch as Term & FunctorTypeTermType;
            let s = matchPattern(fttP.domainCat, fttT.domainCat, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s) return null;
            return matchPattern(fttP.codomainCat, fttT.codomainCat, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'FMap0Term': {
            const fm0P = rtPattern; const fm0T = rtTermToMatch as Term & {tag:'FMap0Term'};
            let s: Substitution | null = subst;
            // Matching implicits: if pattern specifies them, term must match.
            // If pattern omits them (they are undefined), term can have anything (or hole if it was filled).
            if (fm0P.catA_IMPLICIT) {
                if (!fm0T.catA_IMPLICIT) return null; // Term must also have it if pattern does
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
        default:
             const exhaustiveCheck: never = rtPattern; // Ensures all tags are handled.
             console.warn(`matchPattern: Unhandled pattern tag: ${(exhaustiveCheck as any).tag}.`);
             return null;
    }
}

/**
 * Applies a substitution (from pattern matching) to a term.
 * @param term The term to apply substitution to.
 * @param subst The substitution map (pattern var name -> term).
 * @param patternVarDecls Declared pattern variables for the rule.
 * @returns A new term with substitutions applied.
 */
export function applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[]): Term {
    const current = getTermRef(term); // Resolve holes in the term structure itself before applying pvar subst.

    // Case 1: Term is a pattern variable (Var or Hole syntax)
    if ((current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) ||
        (current.tag === 'Hole' && isPatternVarName(current.id, patternVarDecls))) {
        const pvarName = current.tag === 'Var' ? current.name : current.id;
        if (pvarName === '_') return Hole('_'); // Wildcard remains wildcard.

        const replacement = subst.get(pvarName);
        // If pvar is in subst, return its replacement. Otherwise, return the pvar itself (should ideally not happen if all pvars in RHS are bound by LHS).
        return replacement !== undefined ? getTermRef(replacement) : current;
    }

    // Case 2: Recursively apply substitution to subterms.
    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': case 'CatTerm': case 'SetTerm': return current; // Non-pvars or no subterms.
        case 'App':
            return App(
                applySubst(current.func, subst, patternVarDecls),
                applySubst(current.arg, subst, patternVarDecls),
                current.icit
            );
        case 'Lam': {
            const lam = current;
            // Substitute in parameter type if it exists.
            const appliedParamType = lam.paramType ? applySubst(lam.paramType, subst, patternVarDecls) : undefined;

            // For the body, we need to be careful if a pattern variable in `subst`
            // has the same name as the lambda's parameter `lam.paramName`.
            // The lambda's parameter `lam.paramName` shadows any pattern variable with the same name within its body.
            // So, we remove `lam.paramName` from the substitution map when substituting into the body.
            const bodySubst = new Map(subst);
            if (bodySubst.has(lam.paramName) && isPatternVarName(lam.paramName, patternVarDecls)) {
                 // This case is tricky: if lam.paramName is e.g. "$x", and "$x" is also a pattern variable
                 // that got bound to some term `T`. Inside (λ $x ...), this inner "$x" is a binder, not the pattern var.
                 // However, our `isPatternVarName` check on `lam.paramName` would be true.
                 // The `applySubst` for `lam.body(v_arg)` should handle `v_arg` correctly without trying to substitute it
                 // if `v_arg` is just `Var(lam.paramName)`.
                 // The current `applySubst` logic for `Var` already checks `isPatternVarName`.
                 // If `lam.paramName` is a pvar, it's usually a sign of complex pattern.
                 // Assume `lam.paramName` are fresh or distinct from pvars that appear free in body.
                 // If `lam.paramName` happens to be a pvar name, it's shadowed.
            }


            const newBodyFn = (v_arg: Term): Term => {
                // When `lam.body(v_arg)` is called, `v_arg` (which is `Var(lam.paramName)`)
                // will be passed into `applySubst`. If `lam.paramName` is NOT a pattern variable,
                // `applySubst` will return it as is. If `lam.paramName` IS a pattern variable name,
                // it would be substituted if found in `bodySubst`. This is usually not intended for binders.
                // The most common case is `lam.paramName` is a normal variable name.
                // The `v_arg` itself should not be substituted by `bodySubst` if it's the binder.
                // The simplest is to assume `lam.paramName` is not a pvar name appearing in `subst` from the outside.
                // If a pvar is shadowed, it is shadowed.
                return applySubst(lam.body(v_arg), bodySubst, patternVarDecls);
            };

            const newLam = Lam(lam.paramName, lam.icit, appliedParamType, newBodyFn);
            // Preserve annotation status based on whether a type is present after substitution.
            (newLam as Term & {tag: 'Lam'})._isAnnotated = lam._isAnnotated && appliedParamType !== undefined;
            return newLam;
        }
        case 'Pi': {
            const pi = current;
            // Similar shadowing considerations for Pi as for Lam.
            const bodyTypeSubst = new Map(subst);
            // if (bodyTypeSubst.has(pi.paramName)) { delete bodyTypeSubst.get(pi.paramName); }

            const newBodyTypeFn = (v_arg: Term) => {
                return applySubst(pi.bodyType(v_arg), bodyTypeSubst, patternVarDecls);
            };
            return Pi(pi.paramName, pi.icit, applySubst(pi.paramType, subst, patternVarDecls), newBodyTypeFn);
        }
        // --- Category Theory Terms ---
        case 'ObjTerm': return ObjTerm(applySubst(current.cat, subst, patternVarDecls));
        case 'HomTerm':
            return HomTerm(
                applySubst(current.cat, subst, patternVarDecls),
                applySubst(current.dom, subst, patternVarDecls),
                applySubst(current.cod, subst, patternVarDecls)
            );
        case 'FunctorCategoryTerm':
            return FunctorCategoryTerm(
                applySubst(current.domainCat, subst, patternVarDecls),
                applySubst(current.codomainCat, subst, patternVarDecls)
            );
        case 'FunctorTypeTerm':
            return FunctorTypeTerm(
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
        default:
            const exhaustiveCheck: never = current;
            throw new Error(`applySubst: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
}