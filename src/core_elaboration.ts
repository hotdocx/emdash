import {
    Term, Context, PatternVarDecl, Substitution, ElaborationResult, Icit, Binding,
    Hole, Var, App, Lam, Pi, Type, CatTerm, ObjTerm, HomTerm, MkCat_, IdentityMorph, ComposeMorph
} from './core_types';
import {
    emptyCtx, extendCtx, lookupCtx, globalDefs, addConstraint, getTermRef,
    freshHoleName, freshVarName, consoleLog,
    resetHoleId,
    resetVarId,
    constraints
} from './core_context_globals';
import { whnf, normalize, areEqual, solveConstraints, MAX_STACK_DEPTH } from './core_logic';

export interface ElaborationOptions {
    normalizeResultTerm?: boolean;
}

export function ensureImplicitsAsHoles(term: Term): Term {
    // This is for kernel constructor implicit arguments, not general function implicits.
    // It's called before getTermRef, so it can mutate.
    if (term.tag === 'IdentityMorph') {
        if (term.cat_IMPLICIT === undefined) {
            let objHint = "obj";
            if (term.obj.tag === 'Var') objHint = term.obj.name;
            else if (term.obj.tag === 'Hole') objHint = term.obj.id.replace("?", "");
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

    const originalTerm = term; // Keep a reference to the original term for potential annotations
    const termWithKernelImplicits = ensureImplicitsAsHoles(originalTerm); // ensureImplicitsAsHoles mutates
    const current = getTermRef(termWithKernelImplicits);


    if (current.tag === 'Var') {
        const gdef = globalDefs.get(current.name);
        if (gdef) return gdef.type; // Type stored in globalDefs should be WHNF or easily normalizable

        const binding = lookupCtx(ctx, current.name);
        if (!binding) throw new Error(`Unbound variable: ${current.name} in context [${ctx.map(b => b.name).join(', ')}]`);
        return binding.type; // Type from context
    }

    switch (current.tag) {
        case 'Type': return Type();
        case 'Hole': {
            if (current.elaboratedType) return getTermRef(current.elaboratedType);
            const newTypeForHole = Hole(freshHoleName() + "_type_of_" + current.id.replace("?", "h"));
            current.elaboratedType = newTypeForHole;
            return newTypeForHole;
        }
        case 'App': {
            const appNode = current; // current is App
            let elabF = appNode.func; // The function part to be elaborated/applied
            let typeF = whnf(infer(ctx, elabF, stackDepth + 1), ctx);

            if (appNode.icit === Icit.Expl) {
                // Insert missing leading implicit applications for elabF
                while (typeF.tag === 'Pi' && typeF.icit === Icit.Impl) {
                    const implHole = Hole(freshHoleName() + "_auto_impl_arg_");
                    if (typeF.paramType) { (implHole as Term & {tag:'Hole'}).elaboratedType = typeF.paramType; }
                    elabF = App(elabF, implHole, Icit.Impl); // This App node IS the one for the implicit arg
                    typeF = whnf(typeF.bodyType(implHole), ctx);
                }
                // After loop, typeF should be Pi _ Icit.Expl expectedArgType resultBodyType
                if (!(typeF.tag === 'Pi' && typeF.icit === Icit.Expl)) {
                    throw new Error(`Type error in App (explicit): function ${printTerm(elabF)} of type ${printTerm(typeF)} does not expect an explicit argument for ${printTerm(appNode.arg)}.`);
                }
                check(ctx, appNode.arg, typeF.paramType, stackDepth + 1);
                return whnf(typeF.bodyType(appNode.arg), ctx);
            } else { // appNode.icit === Icit.Impl
                if (!(typeF.tag === 'Pi' && typeF.icit === Icit.Impl)) {
                    throw new Error(`Type error in App (implicit): function ${printTerm(elabF)} of type ${printTerm(typeF)} does not expect an implicit argument for ${printTerm(appNode.arg)}.`);
                }
                check(ctx, appNode.arg, typeF.paramType, stackDepth + 1);
                return whnf(typeF.bodyType(appNode.arg), ctx);
            }
        }
        case 'Lam': {
            const lamNode = current; // current is Lam
            let actualParamType: Term;

            if (lamNode._isAnnotated && lamNode.paramType) {
                check(ctx, lamNode.paramType, Type(), stackDepth + 1);
                actualParamType = lamNode.paramType;
            } else { // Unannotated lambda
                actualParamType = Hole(freshHoleName() + "_lam_" + lamNode.paramName + "_paramT_infer_");
                // Annotate the Lam node itself if it was the original input
                // This relies on 'current' being the object that might need annotation.
                // If 'originalTerm' was a Hole that resolved to this Lam, this won't reach the original Hole.
                // This is a known subtlety with mutable elaboration via getTermRef.
                if (originalTerm === lamNode && originalTerm.tag === 'Lam' && !originalTerm._isAnnotated) {
                    originalTerm.paramType = actualParamType;
                    originalTerm._isAnnotated = true;
                } else if (lamNode.tag === 'Lam' && !lamNode._isAnnotated) { // Fallback: if current is the Lam
                    lamNode.paramType = actualParamType;
                    lamNode._isAnnotated = true;
                }
            }
            return Pi(lamNode.paramName, lamNode.icit, actualParamType, (pi_v_arg: Term) => {
                const extendedCtx = extendCtx(ctx, lamNode.paramName, actualParamType, lamNode.icit);
                return infer(extendedCtx, lamNode.body(pi_v_arg), stackDepth + 1);
            });
        }
        case 'Pi': {
            const piNode = current;
            check(ctx, piNode.paramType, Type(), stackDepth + 1);
            const extendedCtx = extendCtx(ctx, piNode.paramName, piNode.paramType, piNode.icit);
            const bodyTypeInstance = piNode.bodyType(Var(piNode.paramName));
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
            const O_repr_norm = getTermRef(current.objRepresentation);

            const expected_H_type = Pi("X", Icit.Expl, O_repr_norm, _X => Pi("Y", Icit.Expl, O_repr_norm, _Y => Type()));
            check(ctx, current.homRepresentation, expected_H_type, stackDepth + 1);
            const H_repr_func_norm = getTermRef(current.homRepresentation);

            const type_of_hom_X_Y = (X_val: Term, Y_val: Term) => App(App(H_repr_func_norm, X_val, Icit.Expl), Y_val, Icit.Expl);

            const expected_C_type =
                Pi("Xobj", Icit.Expl, O_repr_norm, Xobj_term =>
                Pi("Yobj", Icit.Expl, O_repr_norm, Yobj_term =>
                Pi("Zobj", Icit.Expl, O_repr_norm, Zobj_term =>
                Pi("gmorph", Icit.Expl, type_of_hom_X_Y(Yobj_term, Zobj_term), _gmorph_term =>
                Pi("fmorph", Icit.Expl, type_of_hom_X_Y(Xobj_term, Yobj_term), _fmorph_term =>
                type_of_hom_X_Y(Xobj_term, Zobj_term)
                )))));
            check(ctx, current.composeImplementation, expected_C_type, stackDepth + 1);
            return CatTerm();
        }
        case 'IdentityMorph': {
            const idTerm = current;
            const catArg = idTerm.cat_IMPLICIT!; // Should be a Hole if not provided

            const objActualType = infer(ctx, idTerm.obj, stackDepth + 1);
            addConstraint(objActualType, ObjTerm(catArg), `Object ${printTerm(idTerm.obj)} in IdentityMorph must be of type Obj(${printTerm(catArg)})`);
            return HomTerm(catArg, idTerm.obj, idTerm.obj);
        }
        case 'ComposeMorph': {
            const compTerm = current;
            const catArg = compTerm.cat_IMPLICIT!;
            const XArg = compTerm.objX_IMPLICIT!;
            const YArg = compTerm.objY_IMPLICIT!;
            const ZArg = compTerm.objZ_IMPLICIT!;

            check(ctx, compTerm.f, HomTerm(catArg, XArg, YArg), stackDepth + 1);
            check(ctx, compTerm.g, HomTerm(catArg, YArg, ZArg), stackDepth + 1);
            return HomTerm(catArg, XArg, ZArg);
        }
        default:
            const exhaustiveCheck: never = current;
            throw new Error(`Infer: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
}

export function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0): void {
    if (stackDepth > MAX_STACK_DEPTH) {
        throw new Error(`check: Max stack depth exceeded. Term: ${printTerm(term)}, Expected: ${printTerm(expectedType)}`);
    }

    const originalTerm = term; // For annotations
    const termWithKernelImplicits = ensureImplicitsAsHoles(originalTerm);
    const currentTerm = getTermRef(termWithKernelImplicits);
    const currentExpectedType = getTermRef(expectedType);

    const expectedTypeWhnf = whnf(currentExpectedType, ctx, stackDepth + 1);

    // Implicit Lambda Insertion Rule
    if (expectedTypeWhnf.tag === 'Pi' && expectedTypeWhnf.icit === Icit.Impl) {
        const termRef = getTermRef(currentTerm); // Check the actual structure of term
        if (!(termRef.tag === 'Lam' && termRef.icit === Icit.Impl)) {
            // Term is not an explicit implicit lambda. Check if 'term' can be the body.
            const extendedCtx = extendCtx(ctx, expectedTypeWhnf.paramName, expectedTypeWhnf.paramType, expectedTypeWhnf.icit);
            const expectedBodyType = whnf(expectedTypeWhnf.bodyType(Var(expectedTypeWhnf.paramName)), extendedCtx);
            check(extendedCtx, currentTerm, expectedBodyType, stackDepth + 1);
            return; // If this checks, 'term' is valid to form an implicit lambda.
        }
    }
    
    // Rule for checking unannotated user lambda against Pi
    if (currentTerm.tag === 'Lam' && !currentTerm._isAnnotated && expectedTypeWhnf.tag === 'Pi') {
        const lamNode = currentTerm;
        const expectedPiNode = expectedTypeWhnf;

        // Check if icitness matches. If not, this rule doesn't apply, fall through to general case.
        if (lamNode.icit === expectedPiNode.icit) {
            // Annotate the lambda with param type from Pi
            if (originalTerm === lamNode && originalTerm.tag === 'Lam' && !originalTerm._isAnnotated) { // Annotate original if possible
                 originalTerm.paramType = expectedPiNode.paramType;
                 originalTerm._isAnnotated = true;
            } else if (lamNode.tag === 'Lam' && !lamNode._isAnnotated) { // Fallback for current
                lamNode.paramType = expectedPiNode.paramType;
                lamNode._isAnnotated = true;
            }
            
            const extendedCtx = extendCtx(ctx, lamNode.paramName, expectedPiNode.paramType, lamNode.icit);
            const actualBodyTerm = lamNode.body(Var(lamNode.paramName));
            const expectedBodyPiType = whnf(expectedPiNode.bodyType(Var(lamNode.paramName)),extendedCtx);
            check(extendedCtx, actualBodyTerm, expectedBodyPiType, stackDepth + 1);
            return;
        }
    }


    if (currentTerm.tag === 'Hole') {
        if (!currentTerm.elaboratedType) {
            currentTerm.elaboratedType = expectedTypeWhnf;
        } else {
            addConstraint(getTermRef(currentTerm.elaboratedType), expectedTypeWhnf, `check Hole ${currentTerm.id}: elaboratedType vs expectedType`);
        }
        return;
    }

    // General case: infer type and check against expected
    const inferredType = infer(ctx, currentTerm, stackDepth + 1);
    addConstraint(whnf(inferredType, ctx), expectedTypeWhnf, `check general: inferredType(${printTerm(currentTerm)}) vs expectedType(${printTerm(expectedTypeWhnf)})`);
}


export function elaborate(
    term: Term,
    expectedType?: Term,
    initialCtx: Context = emptyCtx,
    options: ElaborationOptions = { normalizeResultTerm: true }
): ElaborationResult {
    const originalConstraints = [...constraints];
    constraints.length = 0;
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
        throw new Error(`Elaboration internal error: ${(e as Error).message} on term ${printTerm(termToElaborate)}. Stack: ${(e as Error).stack}`);
    } finally {
        constraints.splice(0, constraints.length, ...originalConstraints);
    }

    const elaboratedTermStructure = getTermRef(termToElaborate);
    const finalResultTerm = options.normalizeResultTerm ? normalize(elaboratedTermStructure, initialCtx) : elaboratedTermStructure;
    const finalResultType = whnf(getTermRef(finalTypeToReport), initialCtx);

    return { term: finalResultTerm, type: finalResultType };
}


export function isPatternVarName(name: string, patternVarDecls: PatternVarDecl[]): boolean {
    // PatternVarDecl is now string, e.g., "$x"
    return name.startsWith('$') && patternVarDecls.includes(name);
}

export function matchPattern(
    pattern: Term, // This should be an already elaborated pattern
    termToMatch: Term, // This should be in WHNF or normalized
    ctx: Context,
    patternVarDecls: PatternVarDecl[], // string[] like ["$x", "$y"]
    currentSubst?: Substitution,
    stackDepth = 0
): Substitution | null {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`matchPattern stack depth exceeded for pattern ${printTerm(pattern)} vs term ${printTerm(termToMatch)}`);

    const rtPattern = getTermRef(pattern); // Pattern should already be elaborated, getTermRef for safety
    const rtTermToMatch = getTermRef(termToMatch); // termToMatch should be whnf'd before call

    const subst = currentSubst ? new Map(currentSubst) : new Map<string, Term>();

    if (rtPattern.tag === 'Var' && isPatternVarName(rtPattern.name, patternVarDecls)) {
        const pvarName = rtPattern.name;
        if (pvarName === '_') return subst; // Wildcard var
        const existing = subst.get(pvarName);
        if (existing) {
            return areEqual(rtTermToMatch, getTermRef(existing), ctx, stackDepth + 1) ? subst : null;
        }
        subst.set(pvarName, rtTermToMatch);
        return subst;
    }

    if (rtPattern.tag === 'Hole') {
        if (rtPattern.id === '_') return subst; // Wildcard hole
        if (isPatternVarName(rtPattern.id, patternVarDecls)) { // Named hole pattern var like $?H
            const pvarId = rtPattern.id;
            const existing = subst.get(pvarId);
            if (existing) {
                return areEqual(rtTermToMatch, getTermRef(existing), ctx, stackDepth + 1) ? subst : null;
            }
            subst.set(pvarId, rtTermToMatch);
            return subst;
        }
        // If it's a specific Hole from pattern elaboration (e.g. implicit arg hole ?h_auto_...)
        // it acts as a wildcard for structure, but only matches if rtTermToMatch is also a Hole
        // with the same ID, which is unlikely unless it's the exact same elaborated term.
        // More generally, these auto-inserted holes should allow any term to match there.
        // The current logic requires specific Hole ID match or it's a named pvar hole.
        // For auto-inserted holes in patterns, they should just allow matching anything.
        // This means if rtPattern.tag === 'Hole' and it's NOT a pattern variable, it's a structural wildcard.
        if (rtTermToMatch.tag === 'Hole' && rtPattern.id === rtTermToMatch.id) return subst; // Matches specific hole
        // If rtPattern is an auto-generated hole (e.g., ?h_auto_0) and not a pattern var, it should match anything.
        if (!rtPattern.id.startsWith('$')) return subst; // Auto-holes are wildcards
        return null; // Specific non-pvar hole in pattern vs different term
    }


    if (rtTermToMatch.tag === 'Hole') return null; // Pattern is not a var/hole, but term is a hole. No match.
    if (rtPattern.tag !== rtTermToMatch.tag) return null;

    // Match Icit for App, Lam, Pi
    if ((rtPattern.tag === 'App' || rtPattern.tag === 'Lam' || rtPattern.tag === 'Pi') &&
        (rtTermToMatch.tag === rtPattern.tag) && rtPattern.icit !== rtTermToMatch.icit) {
        return null;
    }

    switch (rtPattern.tag) {
        case 'Type': case 'CatTerm': return subst;
        case 'Var': // Concrete var in pattern
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
                if (!lamP.paramType || !lamT.paramType) return null; // Both must have types if annotated
                 const sType = matchPattern(lamP.paramType, lamT.paramType, ctx, patternVarDecls, tempSubst, stackDepth + 1);
                 if (!sType) return null;
                 tempSubst = sType;
            }
            const freshV = Var(freshVarName(lamP.paramName));
            // Use actual param type from pattern if available for context, otherwise a hole.
            const paramTypeForCtx = (lamP._isAnnotated && lamP.paramType) ? getTermRef(lamP.paramType) : Hole(freshHoleName() + "_match_lam_body_ctx");
            const extendedCtx = extendCtx(ctx, freshV.name, paramTypeForCtx, lamP.icit);
            // Compare bodies under the fresh variable and extended context
            // HOAS equality: instantiate with the same fresh var and compare results.
             return areEqual(lamP.body(freshV), lamT.body(freshV), extendedCtx, stackDepth + 1) ? tempSubst : null;
        }
        case 'Pi': {
            const piP = rtPattern; const piT = rtTermToMatch as Term & {tag:'Pi'};
            const sType = matchPattern(piP.paramType, piT.paramType, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!sType) return null;
            const freshV = Var(freshVarName(piP.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(piP.paramType), piP.icit);
            // HOAS equality for body types
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
            if (idP.cat_IMPLICIT) { // Pattern specifies implicit
                if (!idT.cat_IMPLICIT) return null; // Term must also have it
                s = matchPattern(idP.cat_IMPLICIT, idT.cat_IMPLICIT, ctx, patternVarDecls, s, stackDepth +1);
                if (!s) return null;
            } // If pattern omits implicit, it's a wildcard for that slot (matches if term also omits or has any)
              // This logic might need refinement: if idP.cat_IMPLICIT is undefined, does it match idT.cat_IMPLICIT if defined?
              // Current: if idP.cat_IMPLICIT, idT.cat_IMPLICIT must exist and match. If !idP.cat_IMPLICIT, it's fine.
            return matchPattern(idP.obj, idT.obj, ctx, patternVarDecls, s, stackDepth + 1);
        }
        case 'ComposeMorph': {
            const compP = rtPattern; const compT = rtTermToMatch as Term & {tag:'ComposeMorph'};
            let s: Substitution | null = subst;
            const implicitsP = [compP.cat_IMPLICIT, compP.objX_IMPLICIT, compP.objY_IMPLICIT, compP.objZ_IMPLICIT];
            const implicitsT = [compT.cat_IMPLICIT, compT.objX_IMPLICIT, compT.objY_IMPLICIT, compT.objZ_IMPLICIT];
            for(let i=0; i<implicitsP.length; i++) {
                if (implicitsP[i]) { // Pattern specifies an implicit
                    if (!implicitsT[i]) return null; // Term must also have it
                    s = matchPattern(implicitsP[i]!, implicitsT[i]!, ctx, patternVarDecls, s, stackDepth + 1);
                    if (!s) return null;
                } // If pattern omits an implicit, it's a wildcard for that slot.
            }
            s = matchPattern(compP.g, compT.g, ctx, patternVarDecls, s, stackDepth + 1);
            if (!s) return null;
            return matchPattern(compP.f, compT.f, ctx, patternVarDecls, s, stackDepth + 1);
        }
        default:
             const exhaustiveCheck: never = rtPattern;
             console.warn(`matchPattern: Unhandled pattern tag: ${(exhaustiveCheck as any).tag}.`);
             return null;
    }
}


export function applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[]): Term {
    const current = getTermRef(term);

    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        if (current.name === '_') return Hole('_'); // Or a fresh Hole if preferred
        const replacement = subst.get(current.name);
        return replacement !== undefined ? replacement : current; // Return var if not in subst (should not happen for bound pvars)
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
            const originalBodyFn = lam.body;
            const newBodyFn = (v_arg: Term): Term => applySubst(originalBodyFn(v_arg), subst, patternVarDecls);

            // Direct construction for robustness
            return {
                tag: 'Lam',
                paramName: lam.paramName,
                icit: lam.icit,
                paramType: appliedParamType,
                body: newBodyFn,
                _isAnnotated: lam._isAnnotated
            };
        }
        case 'Pi': {
            const pi = current;
            return Pi(pi.paramName, pi.icit, applySubst(pi.paramType, subst, patternVarDecls),
                (v_arg: Term) => applySubst(pi.bodyType(v_arg), subst, patternVarDecls));
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
        // Avoid collision with existing bound vars in the map AND globals
        while (globalDefs.has(uniqueName) || Array.from(boundVarsMap.values()).includes(uniqueName) || boundVarsMap.has(uniqueName) /* check if baseName itself is a key from outer scope */ ) {
            uniqueName = `${baseName}_${suffix++}`;
            if (suffix > 100) return `${baseName}_too_many`; // safeguard
        }
        return uniqueName;
    };

    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return boundVarsMap.get(current.name) || current.name;
        case 'Hole': {
            let typeInfo = "";
            if (current.elaboratedType && getTermRef(current.elaboratedType) !== current) { // Avoid self-reference in print
                const elabTypeRef = getTermRef(current.elaboratedType);
                // Check if elabTypeRef is a self-referential hole or a simple Type for a Type term to avoid verbose prints
                const isSelfRefPrint = (elabTypeRef.tag === 'Hole' && elabTypeRef.id === current.id && elabTypeRef.elaboratedType === current.elaboratedType);
                const isTypeForType = (elabTypeRef.tag === 'Type' && term.tag === 'Type'); // original term, not current
                
                if (!isSelfRefPrint && !isTypeForType) {
                    const elabTypePrint = printTerm(elabTypeRef, new Map(boundVarsMap), stackDepth + 1);
                     // Only add type info if it's not just another hole id or excessively simple
                     if(!elabTypePrint.startsWith("?h") || elabTypePrint.length > current.id.length + 3 ) { // Heuristic
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
            const bodyTerm = current.body(Var(current.paramName)); // Instantiate with original paramName for HOAS
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
            const bodyTypeTerm = current.bodyType(Var(current.paramName)); // Instantiate with original paramName
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
            if (current.cat_IMPLICIT && getTermRef(current.cat_IMPLICIT).tag !== 'Hole') { // Only print if not a remaining hole
                 catIdStr = ` {cat=${printTerm(current.cat_IMPLICIT, new Map(boundVarsMap), stackDepth + 1)}}`;
            }
            return `(id${catIdStr} ${printTerm(current.obj, new Map(boundVarsMap), stackDepth + 1)})`;
        }
        case 'ComposeMorph': {
            let catCompStr = "";
            if (current.cat_IMPLICIT && getTermRef(current.cat_IMPLICIT).tag !== 'Hole') {
                 catCompStr = ` {cat=${printTerm(current.cat_IMPLICIT, new Map(boundVarsMap), stackDepth + 1)}}`;
                 // Could also print objX, objY, objZ if they are not holes and add value
            }
            return `(${printTerm(current.g, new Map(boundVarsMap), stackDepth + 1)} ∘${catCompStr} ${printTerm(current.f, new Map(boundVarsMap), stackDepth + 1)})`;
        }
        default:
            const exhaustiveCheck: never = current;
            throw new Error(`printTerm: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
}