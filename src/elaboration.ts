/**
 * @file elaboration.ts
 * @description Implements the type checking and inference algorithms (`check` and `infer`),
 * and the main `elaborate` function that drives the process.
 * Handles insertion of implicit arguments and ensuring kernel implicits are present.
 */

import {
    Term, Context, ElaborationResult, Icit, Hole, Var, App, Lam, Pi, Type, Let, CatTerm,
    ObjTerm, HomTerm, FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm,
    NatTransComponentTerm, HomCovFunctorIdentity, SetTerm, FunctorTypeTerm, BaseTerm,
    MkFunctorTerm, TApp1FApp0Term, BinderMode, LamMode, PiMode, FDApp1Term, TDApp1Term, CatCategoryTerm, CatdCategoryTerm, FunctordCategoryTerm, FunctorCatdTerm, TransfCategoryTerm, TransfCatdTerm, TransfdCategoryTerm
} from './types';
import {
    emptyCtx, extendCtx, lookupCtx, globalDefs, addConstraint, getTermRef,
    freshHoleName, freshVarName, consoleLog, constraints, printTerm
} from './state';
import { whnf, normalize } from './reduction';
import { areEqual } from './equality';
import { solveConstraints } from './unification';
import { MAX_STACK_DEPTH } from './constants';
import { matchPattern, applySubst, isPatternVarName, replaceFreeVar } from './pattern';
import { KERNEL_IMPLICIT_SPECS, KernelImplicitSpec } from './constants';

// Type aliases for specific term kinds, useful for casting
type FunctorCategoryTermType = Extract<BaseTerm, { tag: 'FunctorCategoryTerm' }>;
type CatdCategoryTermType = Extract<BaseTerm, { tag: 'CatdCategoryTerm' }>;
type FunctordCategoryTermType = Extract<BaseTerm, { tag: 'FunctordCategoryTerm' }>;
type FunctorCatdTermType = Extract<BaseTerm, { tag: 'FunctorCatdTerm' }>;
type TransfCategoryTermType = Extract<BaseTerm, { tag: 'TransfCategoryTerm' }>;
type TransfCatdTermType = Extract<BaseTerm, { tag: 'TransfCatdTerm' }>;
type TransfdCategoryTermType = Extract<BaseTerm, { tag: 'TransfdCategoryTerm' }>;
type FunctorTypeTermType = Extract<BaseTerm, { tag: 'FunctorTypeTerm' }>;
type FMap0TermType = Extract<BaseTerm, { tag: 'FMap0Term' }>;
type FMap1TermType = Extract<BaseTerm, { tag: 'FMap1Term' }>;
type NatTransTypeTermType = Extract<BaseTerm, { tag: 'NatTransTypeTerm' }>;
type NatTransComponentTermType = Extract<BaseTerm, { tag: 'NatTransComponentTerm' }>;
type TApp1FApp0TermType = Extract<BaseTerm, { tag: 'TApp1FApp0Term' }>;
type FDApp1TermType = Extract<BaseTerm, { tag: 'FDApp1Term' }>;
type TDApp1TermType = Extract<BaseTerm, { tag: 'TDApp1Term' }>;
type HomCovFunctorIdentityType = Extract<BaseTerm, { tag: 'HomCovFunctorIdentity' }>;


export interface ElaborationOptions {
    normalizeResultTerm?: boolean; // Whether to fully normalize the elaborated term.
    skipCoherenceCheck?: boolean;
    // disables trailing implicits such as `nil` elaborating to `nil {?h}`;
    // incidentally also disables eta-expansion of implicit lambdas
    // this mode is used to elaborate the LHS (and non-necessarily the RHS) of rewrite rules
    disableMaximallyInsertedImplicits?: boolean;
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

const modeLabel = (mode: BinderMode): string => {
    switch (mode) {
        case BinderMode.Functorial: return ':^f';
        case BinderMode.Natural: return ':^n';
        case BinderMode.ObjectOnly: return ':^o';
        default: return String(mode);
    }
};

function resolveBinderMeta(
    ctx: Context,
    binderName: string,
    lamMode?: BinderMode,
    lamController?: Term,
    piMode?: BinderMode,
    piController?: Term
): { mode: BinderMode, controllerCat?: Term } {
    if (lamMode !== undefined && piMode !== undefined && lamMode !== piMode) {
        throw new Error(
            `Mode error on binder '${binderName}': lambda mode ${modeLabel(lamMode)} ` +
            `conflicts with expected mode ${modeLabel(piMode)}`
        );
    }
    if (lamController && piController && !areEqual(lamController, piController, ctx)) {
        throw new Error(
            `Mode error on binder '${binderName}': lambda controller ${printTerm(lamController)} ` +
            `conflicts with expected controller ${printTerm(piController)}`
        );
    }
    return {
        mode: lamMode ?? piMode ?? BinderMode.Functorial,
        controllerCat: lamController ?? piController
    };
}

function validateBinderModeDiscipline(
    ctx: Context,
    binderName: string,
    binderType: Term,
    binderMode: BinderMode,
    binderController?: Term
): void {
    const rType = getTermRef(binderType);
    if (rType.tag !== 'HomTerm') return;

    const homCat = getTermRef(rType.cat);

    if (binderMode === BinderMode.ObjectOnly) {
        throw new Error(
            `Mode error on binder '${binderName}': ${modeLabel(BinderMode.ObjectOnly)} cannot bind arrows of type ${printTerm(rType)}`
        );
    }

    if (binderController && !areEqual(getTermRef(binderController), homCat, ctx)) {
        throw new Error(
            `Mode error on binder '${binderName}': controller ${printTerm(binderController)} ` +
            `does not match hom base category ${printTerm(homCat)}`
        );
    }

    const checkEndpoint = (endpoint: Term, endpointLabel: 'dom' | 'cod') => {
        const rEndpoint = getTermRef(endpoint);
        if (rEndpoint.tag !== 'Var') return;
        const endpointBinding = lookupCtx(ctx, rEndpoint.name);
        if (!endpointBinding) return;

        const endpointMode = endpointBinding.mode ?? BinderMode.Functorial;
        if (endpointMode !== BinderMode.Functorial) {
            throw new Error(
                `Mode error on binder '${binderName}': Hom ${endpointLabel} endpoint '${rEndpoint.name}' ` +
                `must be ${modeLabel(BinderMode.Functorial)} but is ${modeLabel(endpointMode)}`
            );
        }

        if (endpointBinding.controllerCat && !areEqual(getTermRef(endpointBinding.controllerCat), homCat, ctx)) {
            throw new Error(
                `Mode error on binder '${binderName}': Hom ${endpointLabel} endpoint '${rEndpoint.name}' ` +
                `has controller ${printTerm(endpointBinding.controllerCat)} not matching ${printTerm(homCat)}`
            );
        }
    };

    checkEndpoint(rType.dom, 'dom');
    checkEndpoint(rType.cod, 'cod');
}

const CatdOf = (Z: Term): Term => App(Var("Catd"), Z, Icit.Expl);
const FibreOf = (Z: Term, E: Term, z: Term): Term =>
    App(App(App(Var("Fibre"), Z, Icit.Expl), E, Icit.Expl), z, Icit.Expl);
const FunctordOf = (Z: Term, E: Term, D: Term): Term =>
    App(App(App(Var("Functord"), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl);
const TransfdOf = (Z: Term, E: Term, D: Term, FF: Term, GG: Term): Term =>
    App(App(App(App(App(Var("Transfd"), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), GG, Icit.Expl);
const fdapp0Of = (Z: Term, E: Term, D: Term, FF: Term, z: Term, e: Term): Term =>
    App(App(App(App(App(App(Var("fdapp0"), Z, Icit.Expl), E, Icit.Expl), D, Icit.Expl), FF, Icit.Expl), z, Icit.Expl), e, Icit.Expl);
const homdCurryOf = (Z: Term, E: Term, z: Term, e: Term, zPrime: Term, f: Term, ePrime: Term): Term =>
    App(
        App(
            App(
                App(
                    App(
                        App(
                            App(Var("homd_curry"), Z, Icit.Expl),
                            E, Icit.Expl
                        ),
                        z, Icit.Expl
                    ),
                    e, Icit.Expl
                ),
                zPrime, Icit.Expl
            ),
            f, Icit.Expl
        ),
        ePrime, Icit.Expl
    );

function assertBindingMode(
    ctx: Context,
    term: Term,
    expectedMode: BinderMode,
    roleLabel: string,
    expectedController?: Term
): void {
    const rTerm = getTermRef(term);
    if (rTerm.tag !== 'Var') return;

    const binding = lookupCtx(ctx, rTerm.name);
    if (!binding) return;

    const mode = binding.mode ?? BinderMode.Functorial;
    if (mode !== expectedMode) {
        throw new Error(
            `Mode error on ${roleLabel} '${rTerm.name}': expected ${modeLabel(expectedMode)} but got ${modeLabel(mode)}`
        );
    }
    if (expectedController && binding.controllerCat && !areEqual(binding.controllerCat, expectedController, ctx)) {
        throw new Error(
            `Mode error on ${roleLabel} '${rTerm.name}': controller ${printTerm(binding.controllerCat)} ` +
            `does not match expected ${printTerm(expectedController)}`
        );
    }
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
 * @returns An InferResult containing the elaborated term and its inferred type.
 */
export function infer(ctx: Context, term: Term, stackDepth: number = 0, options: ElaborationOptions = {}): InferResult {
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
            let { elaboratedTerm: inferredFuncElab, type: inferredFuncType } = infer(ctx, appNode.func, stackDepth + 1, options);

            let funcAfterImplicits = inferredFuncElab;
            let typeFAfterImplicits = whnf(inferredFuncType, ctx, stackDepth + 1);

            // If current application is explicit, try inserting implicit apps to the function part.
            if (appNode.icit === Icit.Expl) {
                // [TODO] Review carefully whether `options.skipCoherenceCheck` (or similar options.patternCheckSkipOuterImplicits) should skip the `insertImplicitApps` call 
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
                // We assume it could be a dependent Pi type, so we use HO unification.
                const freshPiParamName = freshVarName("pi_param_app");
                const paramTypeHole = Hole(freshHoleName() + "_app_paramT_infer");
                (paramTypeHole as Term & {tag:'Hole'}).elaboratedType = Type();

                // The body type is represented by a higher-order hole, ?body_type_fun,
                // which is a function from the parameter type to Type.
                const bodyTypeFunHole = Hole(freshHoleName() + "_app_bodyT_fun_infer");
                // Its type is Π (_:paramTypeHole). Type
                (bodyTypeFunHole as Term & {tag:'Hole'}).elaboratedType = Pi(
                    "_", Icit.Expl, paramTypeHole, _ => Type()
                );

                // The target Pi type has a body that is an application of this HO hole.
                const targetPiType = Pi(
                    freshPiParamName,
                    appNode.icit,
                    paramTypeHole,
                    (arg: Term) => App(bodyTypeFunHole, arg, Icit.Expl) // body is ?F(arg)
                );

                addConstraint(typeFAfterImplicits, targetPiType, `App: func ${printTerm(funcAfterImplicits)} type needs to be Pi for arg ${printTerm(appNode.arg)}`);
                // Attempt to solve constraints to refine function type.
                // This may solve paramTypeHole and parts of bodyTypeFunHole.
                solveConstraints(ctx, stackDepth + 1);

                expectedParamTypeFromPi = paramTypeHole; // Use the hole as expected type
                bodyTypeFnFromPi = (argVal: Term) => App(bodyTypeFunHole, argVal, Icit.Expl); // The body type is now dependent on the argument.
            }

            const elaboratedArg = check(ctx, appNode.arg, expectedParamTypeFromPi, stackDepth + 1, options);
            const finalAppTerm = App(getTermRef(funcAfterImplicits), getTermRef(elaboratedArg), appNode.icit);
            const resultType = whnf(bodyTypeFnFromPi(getTermRef(elaboratedArg)), ctx, stackDepth + 1);

            return { elaboratedTerm: finalAppTerm, type: resultType };
        }
        case 'Lam': {
            const lamNode = current;
            let actualParamType: Term;

            if (lamNode._isAnnotated && lamNode.paramType) {
                actualParamType = check(ctx, lamNode.paramType, Type(), stackDepth + 1, options);
            } else {
                // Infer parameter type if not annotated
                actualParamType = Hole(freshHoleName() + "_lam_" + lamNode.paramName + "_paramT_infer");
                (actualParamType as Term & {tag:'Hole'}).elaboratedType = Type();
            }
            const elaboratedParamType = getTermRef(actualParamType);
            const lamMode = lamNode.mode ?? BinderMode.Functorial;
            const lamController = lamNode.controllerCat;
            validateBinderModeDiscipline(ctx, lamNode.paramName, elaboratedParamType, lamMode, lamController);

            // To infer the body, we need a context with the parameter and a placeholder variable
            const freshV = Var(lamNode.paramName, true);
            const bodyInferCtx = extendCtx(ctx, lamNode.paramName, elaboratedParamType, lamNode.icit, undefined, lamMode, lamController);
            const lambdaBodyStructure = lamNode.body(freshV); // Instantiate body with a Var
            
            // Infer the body structure ONCE.
            let { elaboratedTerm: inferredBodyElab, type: inferredBodyType } = infer(bodyInferCtx, lambdaBodyStructure, stackDepth + 1, options);
            
            // Insert implicits for the body if needed
            const insertedBody = insertImplicitApps(bodyInferCtx, inferredBodyElab, inferredBodyType, stackDepth + 1);
            const finalElaboratedBody = insertedBody.term;
            const finalInferredBodyType = insertedBody.type;

            // Construct the elaborated lambda with a simple substitution body
            const elaboratedLam = LamMode(
                lamNode.paramName,
                lamNode.icit,
                elaboratedParamType,
                (v: Term): Term => {
                    // The body function now only performs substitution
                    return replaceFreeVar(finalElaboratedBody, freshV.name, v);
                },
                { mode: lamMode, controllerCat: lamController }
            );

            // Construct the Pi type for the lambda, also with a simple substitution body
            const piType = PiMode(
                lamNode.paramName,
                lamNode.icit,
                elaboratedParamType,
                (pi_body_argument_term: Term): Term => {
                    return replaceFreeVar(finalInferredBodyType, freshV.name, pi_body_argument_term);
                },
                { mode: lamMode, controllerCat: lamController }
            );
            
            return { elaboratedTerm: elaboratedLam, type: piType };
        }
        case 'Pi': {
            const piNode = current;
            const elaboratedParamType = check(ctx, piNode.paramType, Type(), stackDepth + 1, options);
            const canonicalParamType = whnf(elaboratedParamType, ctx, stackDepth + 1);
            const piMode = piNode.mode ?? BinderMode.Functorial;
            const piController = piNode.controllerCat;
            validateBinderModeDiscipline(ctx, piNode.paramName, canonicalParamType, piMode, piController);
            
            // To check the body, we need a context with the parameter and a placeholder variable.
            const freshV = Var(piNode.paramName, true);
            // The context is extended with the param type, but not a `let` definition for the variable itself.
            const extendedCtxForBody = extendCtx(ctx, piNode.paramName, canonicalParamType, piNode.icit, undefined, piMode, piController);
            const bodyTypeInstance = piNode.bodyType(freshV); // Instantiate body with the placeholder
            
            // Check that the body is a valid type and get its elaborated form.
            const elaboratedBodyType = check(extendedCtxForBody, bodyTypeInstance, Type(), stackDepth + 1, options);

            // Reconstruct the Pi with the elaborated parameter type and a new body function
            // that correctly substitutes the placeholder in the elaborated body.
            const finalPi = PiMode(piNode.paramName, piNode.icit, getTermRef(canonicalParamType), (v_arg: Term) => {
                // The elaboratedBodyType has `freshV` as a free variable.
                // We must replace it with `v_arg` to produce the final body type.
                return replaceFreeVar(elaboratedBodyType, freshV.name, v_arg);
            }, { mode: piMode, controllerCat: piController });

            return { elaboratedTerm: finalPi, type: Type() }; // A Pi type itself has type Type
        }
        case 'Let': {
            const letNode = current;
            
            // Infer the definition's type.
            const { elaboratedTerm: elabDef, type: elabDefType } = infer(ctx, letNode.letDef, stackDepth + 1, options);
            let finalDefType = getTermRef(elabDefType);

            // If the let-binding is annotated, check the definition against the annotation.
            let elabLetType: Term | undefined = undefined;
            if (letNode._isAnnotated && letNode.letType) {
                elabLetType = check(ctx, letNode.letType, Type(), stackDepth + 1, options);
                addConstraint(finalDefType, elabLetType, `Let-binding type annotation mismatch for '${letNode.letName}'`);
                solveConstraints(ctx, stackDepth + 1);
                finalDefType = getTermRef(elabLetType); // The annotated type is authoritative.
            }

            // Infer the body's type in a context extended with the let-bound variable.
            const placeholderVar = Var(letNode.letName, true);
            // Crucially, we do NOT pass the definition `elabDef` here.
            // The context for type checking just knows `letName : finalDefType`.
            // The reduction of the `Let` term itself is handled by `whnf`.
            const bodyCtx = extendCtx(ctx, letNode.letName, finalDefType, Icit.Expl);
            const { elaboratedTerm: elabBody, type: bodyType } = infer(bodyCtx, letNode.body(placeholderVar), stackDepth + 1, options);
            
            // Reconstruct the `Let` term with elaborated components.
            const newLet = Let(
                letNode.letName,
                finalDefType, // Use the now-known type as the annotation
                elabDef,
                (v: Term) => replaceFreeVar(elabBody, placeholderVar.name, v)
            );
            return { elaboratedTerm: newLet, type: bodyType };
        }
        // Category Theory Primitives
        case 'CatTerm': return { elaboratedTerm: current, type: Type() };
        case 'CatCategoryTerm': return { elaboratedTerm: current, type: CatTerm() };
        case 'CatdCategoryTerm': {
            const cdcTerm = current as Term & CatdCategoryTermType;
            const elabBase = check(ctx, cdcTerm.baseCat, CatTerm(), stackDepth + 1, options);
            return { elaboratedTerm: CatdCategoryTerm(elabBase), type: CatTerm() };
        }
        case 'ObjTerm': {
            const elabCat = check(ctx, current.cat, CatTerm(), stackDepth + 1, options);
            return { elaboratedTerm: ObjTerm(elabCat), type: Type() };
        }
        case 'HomTerm': {
            const elabCat = check(ctx, current.cat, CatTerm(), stackDepth + 1, options);
            const catForHom = getTermRef(elabCat); // Use the elaborated category
            const elabDom = check(ctx, current.dom, ObjTerm(catForHom), stackDepth + 1, options);
            const elabCod = check(ctx, current.cod, ObjTerm(catForHom), stackDepth + 1, options);
            return { elaboratedTerm: HomTerm(elabCat, elabDom, elabCod), type: Type() };
        }
        case 'FunctorCategoryTerm': {
            const fcTerm = current as Term & FunctorCategoryTermType;
            const elabDomainCat = check(ctx, fcTerm.domainCat, CatTerm(), stackDepth + 1, options);
            const elabCodomainCat = check(ctx, fcTerm.codomainCat, CatTerm(), stackDepth + 1, options);
            return { elaboratedTerm: FunctorCategoryTerm(elabDomainCat, elabCodomainCat), type: CatTerm() }; // Functor category is a category
        }
        case 'FunctordCategoryTerm': {
            const fdcTerm = current as Term & FunctordCategoryTermType;
            const elabZ = check(ctx, fdcTerm.baseCat, CatTerm(), stackDepth + 1, options);
            const elabE = check(ctx, fdcTerm.displayedDom, CatdOf(elabZ), stackDepth + 1, options);
            const elabD = check(ctx, fdcTerm.displayedCod, CatdOf(elabZ), stackDepth + 1, options);
            return { elaboratedTerm: FunctordCategoryTerm(elabZ, elabE, elabD), type: CatTerm() };
        }
        case 'FunctorCatdTerm': {
            const fcdTerm = current as Term & FunctorCatdTermType;
            const elabZ = check(ctx, fcdTerm.baseCat, CatTerm(), stackDepth + 1, options);
            const elabE = check(ctx, fcdTerm.displayedDom, CatdOf(elabZ), stackDepth + 1, options);
            const elabD = check(ctx, fcdTerm.displayedCod, CatdOf(elabZ), stackDepth + 1, options);
            return { elaboratedTerm: FunctorCatdTerm(elabZ, elabE, elabD), type: CatdOf(elabZ) };
        }
        case 'TransfCategoryTerm': {
            const tcTerm = current as Term & TransfCategoryTermType;
            const elabA = check(ctx, tcTerm.catA, CatTerm(), stackDepth + 1, options);
            const elabB = check(ctx, tcTerm.catB, CatTerm(), stackDepth + 1, options);
            const functorCatAB = FunctorCategoryTerm(elabA, elabB);
            const elabF = check(ctx, tcTerm.functorF, ObjTerm(functorCatAB), stackDepth + 1, options);
            const elabG = check(ctx, tcTerm.functorG, ObjTerm(functorCatAB), stackDepth + 1, options);
            return { elaboratedTerm: TransfCategoryTerm(elabA, elabB, elabF, elabG), type: CatTerm() };
        }
        case 'TransfCatdTerm': {
            const tcdTerm = current as Term & TransfCatdTermType;
            const elabZ = check(ctx, tcdTerm.baseCat, CatTerm(), stackDepth + 1, options);
            const elabE = check(ctx, tcdTerm.displayedDom, CatdOf(elabZ), stackDepth + 1, options);
            const elabD = check(ctx, tcdTerm.displayedCod, CatdOf(elabZ), stackDepth + 1, options);
            const functordCat = FunctordCategoryTerm(elabZ, elabE, elabD);
            const elabFF = check(ctx, tcdTerm.functorFF, ObjTerm(functordCat), stackDepth + 1, options);
            const elabGG = check(ctx, tcdTerm.functorGG, ObjTerm(functordCat), stackDepth + 1, options);
            return { elaboratedTerm: TransfCatdTerm(elabZ, elabE, elabD, elabFF, elabGG), type: CatdOf(elabZ) };
        }
        case 'TransfdCategoryTerm': {
            const tdcTerm = current as Term & TransfdCategoryTermType;
            const elabZ = check(ctx, tdcTerm.baseCat, CatTerm(), stackDepth + 1, options);
            const elabE = check(ctx, tdcTerm.displayedDom, CatdOf(elabZ), stackDepth + 1, options);
            const elabD = check(ctx, tdcTerm.displayedCod, CatdOf(elabZ), stackDepth + 1, options);
            const functordCat = FunctordCategoryTerm(elabZ, elabE, elabD);
            const elabFF = check(ctx, tdcTerm.functorFF, ObjTerm(functordCat), stackDepth + 1, options);
            const elabGG = check(ctx, tdcTerm.functorGG, ObjTerm(functordCat), stackDepth + 1, options);
            return { elaboratedTerm: TransfdCategoryTerm(elabZ, elabE, elabD, elabFF, elabGG), type: CatTerm() };
        }
        case 'FunctorTypeTerm': {
            const fttTerm = current as Term & FunctorTypeTermType;
            const elabDomainCat = check(ctx, fttTerm.domainCat, CatTerm(), stackDepth + 1, options);
            const elabCodomainCat = check(ctx, fttTerm.codomainCat, CatTerm(), stackDepth + 1, options);
            return { elaboratedTerm: FunctorTypeTerm(elabDomainCat, elabCodomainCat), type: Type() }; // Functor type is a type
        }
        case 'FMap0Term': { // Functor application to an object
            const fm0Term = current as Term & FMap0TermType;
            // Ensure implicit category arguments are elaborated if present (they should be after ensureKernelImplicitsPresent)
            const elabCatA = check(ctx, fm0Term.catA_IMPLICIT!, CatTerm(), stackDepth + 1, options);
            const elabCatB = check(ctx, fm0Term.catB_IMPLICIT!, CatTerm(), stackDepth + 1, options);

            const expectedFunctorType = FunctorTypeTerm(elabCatA, elabCatB);
            const elabFunctor = check(ctx, fm0Term.functor, expectedFunctorType, stackDepth + 1, options);

            const expectedObjectType = ObjTerm(elabCatA); // Object must be in the domain category
            const elabObjectX = check(ctx, fm0Term.objectX, expectedObjectType, stackDepth + 1, options);

            const finalFMap0 = FMap0Term(elabFunctor, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB));
            return { elaboratedTerm: finalFMap0, type: ObjTerm(getTermRef(elabCatB)) }; // Result is an object in the codomain category
        }
        case 'FMap1Term': { // Functor application to a morphism
            const fm1Term = current as Term & FMap1TermType;
            const elabCatA = check(ctx, fm1Term.catA_IMPLICIT!, CatTerm(), stackDepth + 1, options);
            const elabCatB = check(ctx, fm1Term.catB_IMPLICIT!, CatTerm(), stackDepth + 1, options);
            const elabObjX_A = check(ctx, fm1Term.objX_A_IMPLICIT!, ObjTerm(elabCatA), stackDepth + 1, options);
            const elabObjY_A = check(ctx, fm1Term.objY_A_IMPLICIT!, ObjTerm(elabCatA), stackDepth + 1, options);

            const expectedFunctorType = FunctorTypeTerm(elabCatA, elabCatB);
            const elabFunctor = check(ctx, fm1Term.functor, expectedFunctorType, stackDepth + 1, options);

            const expectedMorphismType = HomTerm(elabCatA, elabObjX_A, elabObjY_A); // Morphism is in domain category
            const elabMorphism_a = check(ctx, fm1Term.morphism_a, expectedMorphismType, stackDepth + 1, options);

            // Result type: Hom catB (FMap0 F X) (FMap0 F Y)
            const fmap0_X = FMap0Term(elabFunctor, elabObjX_A, getTermRef(elabCatA), getTermRef(elabCatB));
            const fmap0_Y = FMap0Term(elabFunctor, elabObjY_A, getTermRef(elabCatA), getTermRef(elabCatB));

            const finalFMap1 = FMap1Term(elabFunctor, elabMorphism_a, getTermRef(elabCatA), getTermRef(elabCatB), getTermRef(elabObjX_A), getTermRef(elabObjY_A));
            return { elaboratedTerm: finalFMap1, type: HomTerm(getTermRef(elabCatB), fmap0_X, fmap0_Y) };
        }
        case 'NatTransTypeTerm': { // Type of a natural transformation
            const ntTerm = current as Term & NatTransTypeTermType;
            const elabCatA = check(ctx, ntTerm.catA, CatTerm(), stackDepth + 1, options);
            const elabCatB = check(ctx, ntTerm.catB, CatTerm(), stackDepth + 1, options);
            const expectedFunctorType = FunctorTypeTerm(elabCatA, elabCatB);
            const elabFunctorF = check(ctx, ntTerm.functorF, expectedFunctorType, stackDepth + 1, options);
            const elabFunctorG = check(ctx, ntTerm.functorG, expectedFunctorType, stackDepth + 1, options);

            const finalNatTransType = NatTransTypeTerm(elabCatA, elabCatB, elabFunctorF, elabFunctorG);
            return { elaboratedTerm: finalNatTransType, type: Type() }; // NatTrans type is a type
        }
        case 'NatTransComponentTerm': { // Component of a natural transformation
            const ncTerm = current as Term & NatTransComponentTermType;
            const elabCatA = check(ctx, ncTerm.catA_IMPLICIT!, CatTerm(), stackDepth + 1, options);
            const elabCatB = check(ctx, ncTerm.catB_IMPLICIT!, CatTerm(), stackDepth + 1, options);
            const elabFunctorF = check(ctx, ncTerm.functorF_IMPLICIT!, FunctorTypeTerm(elabCatA, elabCatB), stackDepth + 1, options);
            const elabFunctorG = check(ctx, ncTerm.functorG_IMPLICIT!, FunctorTypeTerm(elabCatA, elabCatB), stackDepth + 1, options);

            const expectedTransformationType = NatTransTypeTerm(elabCatA, elabCatB, elabFunctorF, elabFunctorG);
            const elabTransformation = check(ctx, ncTerm.transformation, expectedTransformationType, stackDepth + 1, options);

            const expectedObjectType = ObjTerm(elabCatA); // Object is in domain category CatA
            const elabObjectX = check(ctx, ncTerm.objectX, expectedObjectType, stackDepth + 1, options);

            // Result type: Hom catB (FMap0 F X) (FMap0 G X)
            const fmap0_F_X = FMap0Term(elabFunctorF, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB));
            const fmap0_G_X = FMap0Term(elabFunctorG, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB));

            const finalNatTransComp = NatTransComponentTerm(elabTransformation, elabObjectX, getTermRef(elabCatA), getTermRef(elabCatB), getTermRef(elabFunctorF), getTermRef(elabFunctorG));
            return { elaboratedTerm: finalNatTransComp, type: HomTerm(getTermRef(elabCatB), fmap0_F_X, fmap0_G_X) };
        }
        case 'TApp1FApp0Term': { // Off-diagonal component of a natural transformation (tapp1_fapp0 eps f)
            const t1Term = current as Term & TApp1FApp0TermType;

            const elabCatA = check(ctx, t1Term.catA_IMPLICIT!, CatTerm(), stackDepth + 1, options);
            const elabCatB = check(ctx, t1Term.catB_IMPLICIT!, CatTerm(), stackDepth + 1, options);
            const elabFunctorF = check(ctx, t1Term.functorF_IMPLICIT!, FunctorTypeTerm(elabCatA, elabCatB), stackDepth + 1, options);
            const elabFunctorG = check(ctx, t1Term.functorG_IMPLICIT!, FunctorTypeTerm(elabCatA, elabCatB), stackDepth + 1, options);
            const elabObjX_A = check(ctx, t1Term.objX_A_IMPLICIT!, ObjTerm(elabCatA), stackDepth + 1, options);
            const elabObjY_A = check(ctx, t1Term.objY_A_IMPLICIT!, ObjTerm(elabCatA), stackDepth + 1, options);

            const expectedTransformationType = NatTransTypeTerm(elabCatA, elabCatB, elabFunctorF, elabFunctorG);
            const elabTransformation = check(ctx, t1Term.transformation, expectedTransformationType, stackDepth + 1, options);
            const elabMorphismF = check(ctx, t1Term.morphism_f, HomTerm(elabCatA, elabObjX_A, elabObjY_A), stackDepth + 1, options);

            const fmap0_F_X = FMap0Term(elabFunctorF, elabObjX_A, getTermRef(elabCatA), getTermRef(elabCatB));
            const fmap0_G_Y = FMap0Term(elabFunctorG, elabObjY_A, getTermRef(elabCatA), getTermRef(elabCatB));

            const finalTApp1 = TApp1FApp0Term(
                elabTransformation,
                elabMorphismF,
                getTermRef(elabCatA),
                getTermRef(elabCatB),
                getTermRef(elabFunctorF),
                getTermRef(elabFunctorG),
                getTermRef(elabObjX_A),
                getTermRef(elabObjY_A)
            );

            return { elaboratedTerm: finalTApp1, type: HomTerm(getTermRef(elabCatB), fmap0_F_X, fmap0_G_Y) };
        }
        case 'FDApp1Term': { // Off-diagonal displayed functor component (fdapp1_fapp0 FF sigma)
            const fdTerm = current as Term & FDApp1TermType;

            const elabZ = check(ctx, fdTerm.catZ_IMPLICIT!, CatTerm(), stackDepth + 1, options);
            const elabE = check(ctx, fdTerm.catdE_IMPLICIT!, CatdOf(elabZ), stackDepth + 1, options);
            const elabD = check(ctx, fdTerm.catdD_IMPLICIT!, CatdOf(elabZ), stackDepth + 1, options);
            const elabZObj = check(ctx, fdTerm.objZ_IMPLICIT!, ObjTerm(elabZ), stackDepth + 1, options);
            const elabEObj = check(ctx, fdTerm.objE_IMPLICIT!, ObjTerm(FibreOf(elabZ, elabE, elabZObj)), stackDepth + 1, options);
            const elabZPrimeObj = check(ctx, fdTerm.objZPrime_IMPLICIT!, ObjTerm(elabZ), stackDepth + 1, options);
            const elabBaseArrow = check(ctx, fdTerm.homF_IMPLICIT!, HomTerm(elabZ, elabZObj, elabZPrimeObj), stackDepth + 1, options);
            const elabEPrimeObj = check(ctx, fdTerm.objEPrime_IMPLICIT!, ObjTerm(FibreOf(elabZ, elabE, elabZPrimeObj)), stackDepth + 1, options);

            assertBindingMode(ctx, elabZObj, BinderMode.Functorial, "base object z", elabZ);
            assertBindingMode(ctx, elabEObj, BinderMode.Natural, "fibre object e");
            assertBindingMode(ctx, elabZPrimeObj, BinderMode.Functorial, "base object z'", elabZ);
            assertBindingMode(ctx, elabBaseArrow, BinderMode.Natural, "base arrow f", elabZ);
            assertBindingMode(ctx, elabEPrimeObj, BinderMode.Natural, "fibre object e'");

            const expectedFunctordType = FunctordOf(elabZ, elabE, elabD);
            const elabDisplayedFunctor = check(ctx, fdTerm.displayedFunctor, expectedFunctordType, stackDepth + 1, options);

            const sigmaType = ObjTerm(homdCurryOf(elabZ, elabE, elabZObj, elabEObj, elabZPrimeObj, elabBaseArrow, elabEPrimeObj));
            const elabSigma = check(ctx, fdTerm.morphism_sigma, sigmaType, stackDepth + 1, options);
            assertBindingMode(ctx, elabSigma, BinderMode.Functorial, "displayed arrow witness sigma");

            const ffAtZE = fdapp0Of(elabZ, elabE, elabD, elabDisplayedFunctor, elabZObj, elabEObj);
            const ffAtZPrimeEPrime = fdapp0Of(elabZ, elabE, elabD, elabDisplayedFunctor, elabZPrimeObj, elabEPrimeObj);

            const finalHead = App(
                App(
                    App(
                        App(
                            App(
                                App(
                                    App(
                                        App(
                                            App(Var("fdapp1_fapp0"), elabZ, Icit.Expl),
                                            elabE, Icit.Expl
                                        ),
                                        elabD, Icit.Expl
                                    ),
                                    elabDisplayedFunctor, Icit.Expl
                                ),
                                elabZObj, Icit.Expl
                            ),
                            elabEObj, Icit.Expl
                        ),
                        elabZPrimeObj, Icit.Expl
                    ),
                    elabBaseArrow, Icit.Expl
                ),
                elabEPrimeObj, Icit.Expl
            );
            const finalTerm = App(finalHead, elabSigma, Icit.Expl);
            const finalType = ObjTerm(homdCurryOf(elabZ, elabD, elabZObj, ffAtZE, elabZPrimeObj, elabBaseArrow, ffAtZPrimeEPrime));
            return { elaboratedTerm: finalTerm, type: finalType };
        }
        case 'TDApp1Term': { // Off-diagonal displayed transfor component (tdapp1_fapp0 eps sigma)
            const tdTerm = current as Term & TDApp1TermType;

            const elabZ = check(ctx, tdTerm.catZ_IMPLICIT!, CatTerm(), stackDepth + 1, options);
            const elabE = check(ctx, tdTerm.catdE_IMPLICIT!, CatdOf(elabZ), stackDepth + 1, options);
            const elabD = check(ctx, tdTerm.catdD_IMPLICIT!, CatdOf(elabZ), stackDepth + 1, options);
            const elabFF = check(ctx, tdTerm.functorFF_IMPLICIT!, FunctordOf(elabZ, elabE, elabD), stackDepth + 1, options);
            const elabGG = check(ctx, tdTerm.functorGG_IMPLICIT!, FunctordOf(elabZ, elabE, elabD), stackDepth + 1, options);
            const elabZObj = check(ctx, tdTerm.objZ_IMPLICIT!, ObjTerm(elabZ), stackDepth + 1, options);
            const elabEObj = check(ctx, tdTerm.objE_IMPLICIT!, ObjTerm(FibreOf(elabZ, elabE, elabZObj)), stackDepth + 1, options);
            const elabZPrimeObj = check(ctx, tdTerm.objZPrime_IMPLICIT!, ObjTerm(elabZ), stackDepth + 1, options);
            const elabBaseArrow = check(ctx, tdTerm.homF_IMPLICIT!, HomTerm(elabZ, elabZObj, elabZPrimeObj), stackDepth + 1, options);
            const elabEPrimeObj = check(ctx, tdTerm.objEPrime_IMPLICIT!, ObjTerm(FibreOf(elabZ, elabE, elabZPrimeObj)), stackDepth + 1, options);

            assertBindingMode(ctx, elabZObj, BinderMode.Functorial, "base object z", elabZ);
            assertBindingMode(ctx, elabEObj, BinderMode.Natural, "fibre object e");
            assertBindingMode(ctx, elabZPrimeObj, BinderMode.Functorial, "base object z'", elabZ);
            assertBindingMode(ctx, elabBaseArrow, BinderMode.Natural, "base arrow f", elabZ);
            assertBindingMode(ctx, elabEPrimeObj, BinderMode.Natural, "fibre object e'");

            const sigmaType = ObjTerm(homdCurryOf(elabZ, elabE, elabZObj, elabEObj, elabZPrimeObj, elabBaseArrow, elabEPrimeObj));
            const elabSigma = check(ctx, tdTerm.morphism_sigma, sigmaType, stackDepth + 1, options);
            assertBindingMode(ctx, elabSigma, BinderMode.Functorial, "displayed arrow witness sigma");

            const expectedTransfdType = TransfdOf(elabZ, elabE, elabD, elabFF, elabGG);
            const elabTransformation = check(ctx, tdTerm.transformation, expectedTransfdType, stackDepth + 1, options);

            const ffAtZE = fdapp0Of(elabZ, elabE, elabD, elabFF, elabZObj, elabEObj);
            const ggAtZPrimeEPrime = fdapp0Of(elabZ, elabE, elabD, elabGG, elabZPrimeObj, elabEPrimeObj);

            const finalHead = App(
                App(
                    App(
                        App(
                            App(
                                App(
                                    App(
                                        App(
                                            App(
                                                App(Var("tdapp1_fapp0"), elabZ, Icit.Expl),
                                                elabE, Icit.Expl
                                            ),
                                            elabD, Icit.Expl
                                        ),
                                        elabFF, Icit.Expl
                                    ),
                                    elabGG, Icit.Expl
                                ),
                                elabZObj, Icit.Expl
                            ),
                            elabEObj, Icit.Expl
                        ),
                        elabZPrimeObj, Icit.Expl
                    ),
                    elabBaseArrow, Icit.Expl
                ),
                elabEPrimeObj, Icit.Expl
            );
            const finalTerm = App(App(finalHead, elabSigma, Icit.Expl), elabTransformation, Icit.Expl);
            const finalType = ObjTerm(homdCurryOf(elabZ, elabD, elabZObj, ffAtZE, elabZPrimeObj, elabBaseArrow, ggAtZPrimeEPrime));
            return { elaboratedTerm: finalTerm, type: finalType };
        }
        case 'HomCovFunctorIdentity': { // Hom_A(W, -) functor
            const hciTerm = current as Term & HomCovFunctorIdentityType;
            const elabDomainCat = check(ctx, hciTerm.domainCat, CatTerm(), stackDepth + 1, options);
            const elabObjW = check(ctx, hciTerm.objW_InDomainCat, ObjTerm(elabDomainCat), stackDepth + 1, options);

            const setGlobal = globalDefs.get("Set");
            if (!setGlobal || !setGlobal.value) throw new Error("Global 'Set' category not defined for HomCovFunctorIdentity type inference.");
            const globalSetTerm = getTermRef(setGlobal.value);

            const finalHCITerm = HomCovFunctorIdentity(elabDomainCat, elabObjW);
            // Type is Functor A Set
            return { elaboratedTerm: finalHCITerm, type: FunctorTypeTerm(elabDomainCat, globalSetTerm) };
        }
        case 'SetTerm': return { elaboratedTerm: current, type: CatTerm() }; // Set is a category
        case 'MkFunctorTerm':
            return infer_mkFunctor(current as Term & {tag: 'MkFunctorTerm'}, ctx, stackDepth + 1, options);
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
 * @returns The elaborated term if it checks against the expected type.
 * @throws Error if type checking fails.
 */
export function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0, options: ElaborationOptions = {}): Term {
    if (stackDepth > MAX_STACK_DEPTH) {
        throw new Error(`check: Max stack depth exceeded. Term: ${printTerm(term)}, Expected: ${printTerm(expectedType)}`);
    }
    // if (stackDepth > 30) console.log("check: stackDepth > 30", {stackDepth, term: printTerm(term), expectedType: printTerm(expectedType)});
    const originalTerm = term;
    const termWithKernelImplicits = ensureKernelImplicitsPresent(originalTerm);
    let currentTerm = getTermRef(termWithKernelImplicits);
    const currentExpectedType = getTermRef(expectedType); // Dereference expected type too

    const expectedTypeWhnf = whnf(currentExpectedType, ctx, stackDepth + 1);

    // Rule for implicit lambda insertion (eta-expansion for implicit Pi types)
    // If expecting Π {x:A}.B and term is not an implicit lambda, wrap term in λ {x:A}. (check term B[x])
    if (expectedTypeWhnf.tag === 'Pi' && expectedTypeWhnf.icit === Icit.Impl && !options.disableMaximallyInsertedImplicits ) {
        const termRef = getTermRef(currentTerm);
        if (!(termRef.tag === 'Lam' && termRef.icit === Icit.Impl)) {
            const lamParamName = expectedTypeWhnf.paramName;
            const lamParamType = getTermRef(expectedTypeWhnf.paramType);
            const expectedMode = expectedTypeWhnf.mode ?? BinderMode.Functorial;
            const expectedController = expectedTypeWhnf.controllerCat;
            validateBinderModeDiscipline(ctx, lamParamName, lamParamType, expectedMode, expectedController);

            // Create a placeholder for the implicitly bound variable
            const placeholderVar = Var(lamParamName, true);
            const bodyCheckCtx = extendCtx(ctx, lamParamName, lamParamType, Icit.Impl, undefined, expectedMode, expectedController); // No definition
            
            // Determine the expected type for the body, instantiated with the placeholder
            const bodyExpectedTypeInner = whnf(expectedTypeWhnf.bodyType(placeholderVar), bodyCheckCtx);

            // Check the original term ONCE against the expected body type to get the elaborated body structure
            const elaboratedBody = check(bodyCheckCtx, termRef, bodyExpectedTypeInner, stackDepth + 1, options);
            
            // Construct the new lambda with a simple substitution body
            const newLam = LamMode(
                lamParamName,
                Icit.Impl,
                lamParamType,
                (v_actual_arg: Term): Term => {
                    return replaceFreeVar(elaboratedBody, placeholderVar.name, v_actual_arg);
                },
                { mode: expectedMode, controllerCat: expectedController }
            );
            return newLam; // Return the new lambda
        }
    }

    // Rule for checking lambdas against Pi types
    if (currentTerm.tag === 'Lam' && expectedTypeWhnf.tag === 'Pi' && currentTerm.icit === expectedTypeWhnf.icit) {
        const lamNode = currentTerm;
        const expectedPiNode = expectedTypeWhnf;
        let lamParamType: Term; // Type annotation on the lambda from the original term structure

        // When checking a lambda against a Pi, the parameter type is dictated by the Pi.
        lamParamType = expectedPiNode.paramType;

        // If the lambda IS annotated, we still check if its annotation is convertible to the Pi's parameter type.
        if (lamNode._isAnnotated && lamNode.paramType) {
            const elabLamParamType = check(ctx, lamNode.paramType, Type(), stackDepth + 1, options);
            addConstraint(elabLamParamType, lamParamType, `Lam param type annotation vs Pi param type for ${lamNode.paramName}`);
            solveConstraints(ctx, stackDepth + 1);
            // We then proceed using the Pi's parameter type for the body context.
        }

        const finalLamParamType = getTermRef(lamParamType); // Ensure it's dereferenced
        const { mode: finalBinderMode, controllerCat: finalControllerCat } = resolveBinderMeta(
            ctx,
            lamNode.paramName,
            lamNode.mode,
            lamNode.controllerCat,
            expectedPiNode.mode,
            expectedPiNode.controllerCat
        );
        validateBinderModeDiscipline(ctx, lamNode.paramName, finalLamParamType, finalBinderMode, finalControllerCat);

        // To check the body, instantiate both the lambda body and the expected pi-type body
        const placeholderVar = Var(lamNode.paramName, true);
        const extendedCtx = extendCtx(ctx, lamNode.paramName, finalLamParamType, lamNode.icit, undefined, finalBinderMode, finalControllerCat); // NO definition
        
        const actualBodyTerm = lamNode.body(placeholderVar);
        const expectedBodyPiType = whnf(expectedPiNode.bodyType(placeholderVar), extendedCtx);

        // Check the body ONCE to get the elaborated body structure
        const elaboratedBody = check(extendedCtx, actualBodyTerm, expectedBodyPiType, stackDepth + 1, options);
        
        // Reconstruct the Lam with the elaborated components
        return LamMode(lamNode.paramName, lamNode.icit, finalLamParamType, (v: Term) => {
            return replaceFreeVar(elaboratedBody, placeholderVar.name, v);
        }, { mode: finalBinderMode, controllerCat: finalControllerCat });
    }

    // Special handling for holes: if a hole is checked against a type,
    // its elaboratedType is unified with the expected type.
    if (currentTerm.tag === 'Hole') {
        if (!currentTerm.elaboratedType) {
            currentTerm.elaboratedType = expectedTypeWhnf; // Assign if not already typed
        } else {
            // If already has a type, add a constraint.
            addConstraint(getTermRef(currentTerm.elaboratedType), expectedTypeWhnf, `check Hole ${currentTerm.id}: elaboratedType vs expectedType`);
            solveConstraints(ctx, stackDepth + 1); // <<< This was marked as RESTORED THIS CALL (was already present here)
        }
        return currentTerm;
    }

    // Default case: infer the type and check if it's convertible to the expected type
    const { elaboratedTerm: inferredTerm, type: inferredType } = infer(ctx, currentTerm, stackDepth + 1, options);

    // Insert implicit applications based on the inferred type before comparing with expectedTypeWhnf
    const afterInsert = options.disableMaximallyInsertedImplicits ? {term: inferredTerm, type: inferredType} : insertImplicitApps(ctx, inferredTerm, inferredType, stackDepth + 1, true);

    // Add constraint: (type of term after implicit insertion) should be equal to (expected type)
    addConstraint(whnf(afterInsert.type, ctx), expectedTypeWhnf, `check general: inferredType(${printTerm(afterInsert.term)}) vs expectedType(${printTerm(expectedTypeWhnf)})`);
    solveConstraints(ctx, stackDepth + 1); // This was the commented out line, now restored as per previous state.

    return afterInsert.term; // Return the term after potential implicit applications
}

/**
 * Infers the type of a MkFunctorTerm and verifies its functoriality law.
 * @param term The MkFunctorTerm to infer and check.
 * @param ctx The context.
 * @param stackDepth The recursion depth.
 * @returns An InferResult with the elaborated term and its FunctorTypeTerm type.
 * @throws CoherenceError if the functoriality law does not hold.
 */
function infer_mkFunctor(term: Term & {tag: 'MkFunctorTerm'}, ctx: Context, stackDepth: number, options: ElaborationOptions = {}): InferResult {
    // 1. Elaborate Categories
    const elabA = check(ctx, term.domainCat, CatTerm(), stackDepth + 1, options);
    const elabB = check(ctx, term.codomainCat, CatTerm(), stackDepth + 1, options);

    // 2. Elaborate fmap0
    const expected_fmap0_type = Pi("x", Icit.Expl, ObjTerm(elabA), _ => ObjTerm(elabB));
    const elab_fmap0 = check(ctx, term.fmap0, expected_fmap0_type, stackDepth + 1, options);
    
    // 3. Elaborate fmap1
    const expected_fmap1_type = Pi("X", Icit.Impl, ObjTerm(elabA), X =>
        Pi("Y", Icit.Impl, ObjTerm(elabA), Y =>
            Pi("a", Icit.Expl, HomTerm(elabA, X, Y), _ => 
                HomTerm(elabB, App(elab_fmap0, X, Icit.Expl), App(elab_fmap0, Y, Icit.Expl))
            )
        )
    );
    const elab_fmap1 = check(ctx, term.fmap1, expected_fmap1_type, stackDepth + 1, options);
    
    let final_elab_proof: Term | undefined = undefined;
    if (!options.skipCoherenceCheck) {
        const compose_morph_def = globalDefs.get("compose_morph");
        if (!compose_morph_def) throw new Error("Functoriality check requires 'compose_morph' to be defined in globals.");
        const compose_morph = Var("compose_morph");

        // Helper to construct the LHS and RHS of the functoriality law to avoid code duplication.
        const buildLawComponents = (X: Term, Y: Term, Z: Term, a: Term, a_prime: Term) => {
            const fmap0X = App(elab_fmap0, X, Icit.Expl);
            const fmap0Y = App(elab_fmap0, Y, Icit.Expl);
            const fmap0Z = App(elab_fmap0, Z, Icit.Expl);
            
            const fmap1_a = App(App(App(elab_fmap1, Y, Icit.Impl), Z, Icit.Impl), a, Icit.Expl);
            const fmap1_a_prime = App(App(App(elab_fmap1, X, Icit.Impl), Y, Icit.Impl), a_prime, Icit.Expl);

            const lhs = App(App(App(App(App(App(compose_morph, 
                elabB, Icit.Impl), fmap0X, Icit.Impl), fmap0Y, Icit.Impl), fmap0Z, Icit.Impl),
                fmap1_a, Icit.Expl), fmap1_a_prime, Icit.Expl);

            const compose_A_a_a_prime = App(App(App(App(App(App(compose_morph,
                elabA, Icit.Impl), X, Icit.Impl), Y, Icit.Impl), Z, Icit.Impl),
                a, Icit.Expl), a_prime, Icit.Expl);

            const rhs = App(App(App(elab_fmap1, X, Icit.Impl), Z, Icit.Impl),
                compose_A_a_a_prime, Icit.Expl);
            
            return { lhs, rhs, fmap0X, fmap0Z };
        };

        if (term.proof) {
            // 5a. Verify by Provided Proof
            const Eq_def = globalDefs.get("Eq");
            if (!Eq_def) throw new Error("Functoriality proof checking requires 'Eq' to be defined in globals.");
            const Eq_var = Var("Eq");
            
            const X_name = "X"; const Y_name = "Y"; const Z_name = "Z";
            const g_name = "g"; const f_name = "f";

            const expectedProofType =
                Pi(X_name, Icit.Impl, ObjTerm(elabA), X =>
                Pi(Y_name, Icit.Impl, ObjTerm(elabA), Y =>
                Pi(Z_name, Icit.Impl, ObjTerm(elabA), Z =>
                Pi(g_name, Icit.Expl, HomTerm(elabA, Y, Z), g =>
                Pi(f_name, Icit.Expl, HomTerm(elabA, X, Y), f => {
                    const { lhs, rhs, fmap0X, fmap0Z } = buildLawComponents(X, Y, Z, g, f);
                    const homType = HomTerm(elabB, fmap0X, fmap0Z);
                    // The type of the equality proposition is Eq {type} (lhs) (rhs)
                    return App(App(App(Eq_var, homType, Icit.Impl), lhs, Icit.Expl), rhs, Icit.Expl);
                })))));
            
            final_elab_proof = check(ctx, term.proof, expectedProofType, stackDepth + 1, options);

        } else {
            // 5b. Verify by Computation
            const X_name = freshVarName("X");
            const Y_name = freshVarName("Y");
            const Z_name = freshVarName("Z");
            const a_name = freshVarName("a");
            const a_prime_name = freshVarName("a_prime");

            const X = Var(X_name, true);
            const Y = Var(Y_name, true);
            const Z = Var(Z_name, true);

            let lawCtx = extendCtx(ctx, X_name, ObjTerm(elabA));
            lawCtx = extendCtx(lawCtx, Y_name, ObjTerm(elabA));
            lawCtx = extendCtx(lawCtx, Z_name, ObjTerm(elabA));
            
            const a_prime = Var(a_prime_name, true); // a' : Hom X Y
            lawCtx = extendCtx(lawCtx, a_prime_name, HomTerm(elabA, X, Y));
            
            const a = Var(a_name, true); // a : Hom Y Z
            lawCtx = extendCtx(lawCtx, a_name, HomTerm(elabA, Y, Z));

            const { lhs, rhs } = buildLawComponents(X, Y, Z, a, a_prime);
        
            const normLhs = normalize(lhs, lawCtx);
            const normRhs = normalize(rhs, lawCtx);

            if (!areEqual(normLhs, normRhs, lawCtx)) {
                throw new CoherenceError("Functoriality check", lhs, rhs, normLhs, normRhs, lawCtx);
            }
        }
    }
    
    // 6. Return Result
    const finalTerm = MkFunctorTerm(elabA, elabB, elab_fmap0, elab_fmap1, final_elab_proof);
    return {
        elaboratedTerm: finalTerm,
        type: FunctorTypeTerm(elabA, elabB)
    };
}

export class CoherenceError extends Error {
    constructor(
        public title: string,
        public lhs: Term,
        public rhs: Term,
        public normLhs: Term,
        public normRhs: Term,
        public ctx: Context
    ) {
        const message = `
${title} failed.
The following equality could not be established:
  LHS: ${printTerm(lhs)}
  RHS: ${printTerm(rhs)}

After normalization, the two sides were not convertible:
  Normalized LHS: ${printTerm(normLhs)}
  Normalized RHS: ${printTerm(normRhs)}

Hint: This may be because a definition does not respect the required laws,
or a required rewrite rule for a custom category is missing.
`;
        super(message);
        this.name = 'CoherenceError';
    }
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
            const elaboratedExpectedType = check(initialCtx, expectedType, Type(), 0, options);
            finalTermToReport = check(initialCtx, term, elaboratedExpectedType, 0, options);
            finalTypeToReport = elaboratedExpectedType; // The type of the result is the (elaborated) expected type
        } else {
            // No expected type, so infer, then insert implicits
            const inferResult = infer(initialCtx, term, 0, options);
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
        if (e instanceof CoherenceError) { // Explicitly re-throw CoherenceError
            throw e;
        }
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
