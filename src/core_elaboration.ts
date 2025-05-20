import { 
    Term, Context, PatternVarDecl, Substitution, ElaborationResult, 
    Hole, Var, App, Lam, Pi, Type, CatTerm, ObjTerm, HomTerm, MkCat_, IdentityMorph, ComposeMorph
} from './core_types';
import { 
    emptyCtx, extendCtx, lookupCtx, globalDefs, addConstraint, getTermRef, 
    freshHoleName, freshVarName, consoleLog, 
    resetHoleId, // Import new reset function
    resetVarId,  // Import new reset function
    constraints // Used by elaborate
} from './core_context_globals';
import { whnf, normalize, areEqual, solveConstraints, MAX_STACK_DEPTH, areStructurallyEqualNoWhnf } from './core_logic';

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
                const paramName = lam.paramName; // Ensure paramName is from the current lam
                const paramType = lam.paramType; // Ensure paramType is from the current lam
                // The bodyType function of the Pi must use its argument.
                return Pi(paramName, paramType, (pi_arg: Term) => {
                    // Infer the type of the lambda's body, where pi_arg is the instance of the lambda's parameter.
                    // The context for this inference must bind paramName to paramType.
                    const tempCtx = extendCtx(ctx, paramName, paramType);
                    return infer(tempCtx, lam.body(pi_arg), stackDepth + 1);
                });
            } else { // Unannotated lambda, infer parameter type
                const paramName = lam.paramName; // Save paramName
                const paramTypeHole = Hole(freshHoleName() + "_lam_" + paramName + "_paramT");
                
                // Bug Fix #1: Tentatively annotate the Lam term itself with the paramTypeHole
                if (term.tag === 'Lam' && !term._isAnnotated) {
                    term.paramType = paramTypeHole;
                    term._isAnnotated = true; 
                } else if (current.tag === 'Lam' && !current._isAnnotated) {
                     current.paramType = paramTypeHole;
                     current._isAnnotated = true;
                }

                // The bodyType function of the Pi must use its argument.
                return Pi(paramName, paramTypeHole, (pi_arg: Term) => {
                    // Infer the type of the lambda's body, where pi_arg is the instance of the lambda's parameter.
                    // The context for this inference must bind paramName to paramTypeHole.
                    const tempCtx = extendCtx(ctx, paramName, paramTypeHole);
                    return infer(tempCtx, lam.body(pi_arg), stackDepth + 1);
                });
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
        default: // Should not happen due to TS exhaustiveness check
            const exhaustiveCheck: never = current;
            throw new Error(`Infer: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
}

export function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0): void {
    if (stackDepth > MAX_STACK_DEPTH) {
        throw new Error(`check: Max stack depth exceeded. Term: ${printTerm(term)}, Expected: ${printTerm(expectedType)}`);
    }
    // consoleLog(`check: term ${printTerm(term)}, expectedType ${printTerm(expectedType)}`, ctx);

    let currentTerm = getTermRef(term); // Dereference holes fully at the start
    let currentExpectedType = getTermRef(expectedType); // Also dereference expected type

    // Ensure implicits are holes for relevant terms before any processing
    if (currentTerm.tag === 'IdentityMorph' || currentTerm.tag === 'ComposeMorph') {
        currentTerm = ensureImplicitsAsHoles(currentTerm);
    }

    const expectedTypeNorm = whnf(currentExpectedType, ctx, stackDepth + 1);
    // consoleLog(`check (norm expected): term ${printTerm(currentTerm)}, expectedTypeNorm ${printTerm(expectedTypeNorm)}`, ctx);

    // Rule for checking unannotated lambda against Pi
    if (currentTerm.tag === 'Lam' && !currentTerm._isAnnotated && expectedTypeNorm.tag === 'Pi') {
        // consoleLog(`check: lam! ${printTerm(currentTerm)} against Pi ${printTerm(expectedTypeNorm)}`, ctx);
        // Deep elaboration: annotate lambda with param type from Pi, then check body
        const lamTerm = currentTerm; 
        const expectedPi = expectedTypeNorm;

        lamTerm.paramType = expectedPi.paramType;
        lamTerm._isAnnotated = true; 

        const extendedCtx = extendCtx(ctx, lamTerm.paramName, lamTerm.paramType);
        const actualBodyTerm = lamTerm.body(Var(lamTerm.paramName));
        const expectedBodyPiType = expectedPi.bodyType(Var(lamTerm.paramName)); 
        check(extendedCtx, actualBodyTerm, expectedBodyPiType, stackDepth + 1);
        return;
    }

    if (currentTerm.tag === 'Hole') {
        // consoleLog(`check: hole! ${printTerm(currentTerm)} against ${printTerm(expectedTypeNorm)}`);
        if (!currentTerm.elaboratedType) {
            currentTerm.elaboratedType = expectedTypeNorm;
        } else {
            addConstraint(getTermRef(currentTerm.elaboratedType), expectedTypeNorm, `check Hole ${currentTerm.id}: elaboratedType vs expectedType`);
        }
        check(ctx, expectedTypeNorm, Type(), stackDepth + 1); // Ensure the expected type (which is now the hole's type) is itself a Type.
        return;
    }

    if (currentTerm.tag === 'IdentityMorph' && expectedTypeNorm.tag === 'HomTerm') {
        const inferredType = infer(ctx, currentTerm, stackDepth + 1);
        addConstraint(inferredType, expectedTypeNorm, `check IdentityMorph: ${printTerm(currentTerm)} against ${printTerm(expectedTypeNorm)} (via infer)`);
        return;
    }

    if (currentTerm.tag === 'ComposeMorph' && expectedTypeNorm.tag === 'HomTerm') {
        const inferredType = infer(ctx, currentTerm, stackDepth + 1);
        addConstraint(inferredType, expectedTypeNorm, `check ComposeMorph: ${printTerm(currentTerm)} against ${printTerm(expectedTypeNorm)} (via infer)`);
        return;
    }


    // Default case: infer type and check against expected
    const inferredType = infer(ctx, currentTerm, stackDepth + 1);
    const inferredTypeNorm = whnf(inferredType, ctx, stackDepth + 1); 

    // consoleLog(`check: term ${printTerm(currentTerm)}, inferred ${printTerm(inferredTypeNorm)}, expected ${printTerm(expectedTypeNorm)}`);
    addConstraint(inferredTypeNorm, expectedTypeNorm, `check default: inferredType(${printTerm(currentTerm)}) === expectedType(${printTerm(expectedType)})`);
}

export function elaborate(term: Term, expectedType?: Term, initialCtx: Context = emptyCtx): ElaborationResult {
    (constraints as any).length = 0; // Reset global constraints (cast to any to bypass readonly if applied by TS)
    resetHoleId(); 
    resetVarId(); 
    
    let finalTypeToReport: Term;
    const termToElaborate = term; 

    try {
        if (expectedType) {
            check(initialCtx, termToElaborate, expectedType);
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
        if (e instanceof Error && (e.message.startsWith("Type error:") || e.message.startsWith("Unbound variable:") || e.message.startsWith("Cannot apply non-function:") || e.message.startsWith("Constant symbol") || e.message.startsWith("WHNF stack depth") || e.message.startsWith("Normalize stack depth") || e.message.startsWith("Unification stack depth") || e.message.startsWith("Equality check depth") || e.message.startsWith("Infer stack depth") || e.message.startsWith("Check stack depth") || e.message.startsWith("matchPattern stack depth") || e.message.startsWith("solveConstraints stack depth"))) {
            throw e;
        }
        throw new Error(`Elaboration internal error: ${(e as Error).message} on term ${printTerm(termToElaborate)}. Stack: ${(e as Error).stack}`);
    }

    const normalizedElaboratedTerm = normalize(termToElaborate, initialCtx);
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
            const consistent = areEqual(currentTermStruct, getTermRef(existing), ctx, stackDepth + 1);
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
            const consistent = areEqual(currentTermStruct, getTermRef(existing), ctx, stackDepth + 1);
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
        if (!currentS) return null;

        if (patArg) { 
            const patArgRef = getTermRef(patArg);
            if ((patArgRef.tag === 'Var' && isPatternVarName(patArgRef.name, patternVarDecls) && patArgRef.name === '_') ||
                (patArgRef.tag === 'Hole' && patArgRef.id === '_')) {
                return currentS; 
            }

            if (!termArg) return null; 
            return matchPattern(patArg, termArg, ctx, patternVarDecls, currentS, stackDepth + 1);

        }
        return currentS;
    };

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
            // For HOAS, bodies are matched using areEqual after instantiating with a fresh var.
            // This assumes pattern variable capture isn't an issue within the HOAS body of a pattern,
            // as pattern vars are usually at the term level, not inside the JS function of the body.
            const freshV = Var(freshVarName(lamP.paramName)); // Use paramName from pattern
            // The context for body comparison needs the param type from the pattern if annotated
            const paramTypeForCtx = lamP.paramType ? getTermRef(lamP.paramType) : Hole(freshHoleName() + "_match_lam_body_ctx");
            const extendedCtx = extendCtx(ctx, freshV.name, paramTypeForCtx); // Bind fresh var to its type
            consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: comparing bodies using areEqual with fresh var ${freshV.name}.`);
            // Note: Using areEqual here is standard for HOAS matching.
            // It relies on the underlying equality to handle alpha-equivalence correctly via whnf and fresh var instantiation.
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
        default: // Should not happen
             const exhaustiveCheck: never = rtPattern;
             console.warn(`[TRACE matchPattern (${stackDepth})] Unhandled pattern tag in structural match: ${(exhaustiveCheck as any).tag}. Returning null.`);
             return null;
    }
}

export function applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[]): Term {
    const current = getTermRef(term); // Dereference first

    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        if (current.name === '_') return Hole('_'); 
        const replacement = subst.get(current.name);
        if (!replacement) {
            console.warn(`applySubst: Unbound pattern variable Var "${current.name}" in RHS. Subst: ${Array.from(subst.keys())}`);
            return current; 
        }
        return replacement;
    }
    if (current.tag === 'Hole' && isPatternVarName(current.id, patternVarDecls)) {
        if (current.id === '_') return Hole('_'); 
        const replacement = subst.get(current.id);
        if (!replacement) {
            console.warn(`applySubst: Unbound pattern variable Hole "${current.id}" in RHS. Subst: ${Array.from(subst.keys())}`);
            return current;
        }
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
        default: // Should not happen
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
                if (!((elabTypeRef.tag === 'Hole' && elabTypeRef.id === current.id) || 
                      (elabTypeRef.tag === 'Type' && term.tag === 'Type'))) { 
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
            newBoundVars.set(current.paramName, paramDisplayName); 

            const typeAnnotation = (current._isAnnotated && current.paramType) 
                ? ` : ${printTerm(current.paramType, new Map(boundVarsMap), stackDepth + 1)}` 
                : '';
            const bodyTerm = current.body(Var(current.paramName)); 
            return `(λ ${paramDisplayName}${typeAnnotation}. ${printTerm(bodyTerm, newBoundVars, stackDepth + 1)})`;
        }
        case 'App':
            return `(${printTerm(current.func, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.arg, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'Pi': {
            const paramDisplayName = getUniqueName(current.paramName);
            const newBoundVars = new Map(boundVarsMap);
            newBoundVars.set(current.paramName, paramDisplayName);

            const paramTypeStr = printTerm(current.paramType, new Map(boundVarsMap), stackDepth + 1); 
            const bodyTypeTerm = current.bodyType(Var(current.paramName)); 
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
        default: // Should not happen
            const exhaustiveCheck: never = current;
            throw new Error(`printTerm: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
} 