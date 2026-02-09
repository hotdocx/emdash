/**
 * @file reduction.ts
 * @description Term reduction (WHNF and normalization).
 */

import {
    Term, Context, App, Lam, Var, ObjTerm, HomTerm, NatTransTypeTerm, FMap0Term, FunctorTypeTerm, Pi, Let,
    Type, Hole, CatTerm, SetTerm, FunctorCategoryTerm, FMap1Term, NatTransComponentTerm, HomCovFunctorIdentity, Icit, MkFunctorTerm, TApp1FApp0Term, BinderMode, FDApp1Term, TDApp1Term, CatCategoryTerm, CatdCategoryTerm, FunctordCategoryTerm, FunctorCatdTerm, TransfCategoryTerm, TransfCatdTerm, TransfdCategoryTerm
} from './types';
import {
    getTermRef, globalDefs, userRewriteRules, lookupCtx, isKernelConstantSymbolStructurally, printTerm,
    freshVarName, freshHoleName, extendCtx, getFlag
} from './state';
import { MAX_STACK_DEPTH } from './constants';
import { matchPattern, applySubst, getFreeVariables, replaceFreeVar } from './pattern';
import { areStructurallyEqualNoWhnf } from './structural';

export const MAX_WHNF_ITERATIONS = 10000; // Max steps for WHNF reduction to prevent infinite loops.

/**
 * Reduces a term to its Weak Head Normal Form (WHNF).
 * This involves performing beta-reductions at the head of the term,
 * unfolding global definitions, and applying rewrite rules.
 * @param term The term to reduce.
 * @param ctx The current context.
 * @param stackDepth Recursion depth.
 * @returns The term in WHNF.
 */
export function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`WHNF stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    // if (stackDepth > 30) console.log("whnf: stackDepth > 30", {stackDepth, term: printTerm(term)});
    let current = term;

    const tryReduceFibreOfDisplayedFamily = (appTerm: Term): Term | null => {
        const args: Array<{ arg: Term; icit: Icit }> = [];
        let head: Term = appTerm;
        while (getTermRef(head).tag === 'App') {
            const app = getTermRef(head) as Term & { tag: 'App' };
            args.push({ arg: app.arg, icit: app.icit });
            head = app.func;
        }
        args.reverse();

        const headRef = getTermRef(head);
        if (headRef.tag !== 'Var' || headRef.name !== 'Fibre') return null;
        if (args.length !== 3) return null;
        if (args[0].icit !== Icit.Expl || args[1].icit !== Icit.Expl || args[2].icit !== Icit.Expl) return null;

        const zObj = args[2].arg;
        const familyWhnf = getTermRef(whnf(args[1].arg, ctx, stackDepth + 1));

        const fibreOf = (family: Term): Term =>
            App(App(App(Var('Fibre'), args[0].arg, Icit.Expl), family, Icit.Expl), zObj, Icit.Expl);

        if (familyWhnf.tag === 'FunctorCatdTerm') {
            return FunctorCategoryTerm(
                fibreOf(familyWhnf.displayedDom),
                fibreOf(familyWhnf.displayedCod)
            );
        }

        if (familyWhnf.tag === 'TransfCatdTerm') {
            const fibreE = fibreOf(familyWhnf.displayedDom);
            const fibreD = fibreOf(familyWhnf.displayedCod);
            const fibreFunc = (ff: Term): Term =>
                App(
                    App(
                        App(
                            App(
                                App(Var('Fibre_func'), familyWhnf.baseCat, Icit.Expl),
                                familyWhnf.displayedDom, Icit.Expl
                            ),
                            familyWhnf.displayedCod, Icit.Expl
                        ),
                        ff, Icit.Expl
                    ),
                    zObj, Icit.Expl
                );

            return TransfCategoryTerm(
                fibreE,
                fibreD,
                fibreFunc(familyWhnf.functorFF),
                fibreFunc(familyWhnf.functorGG)
            );
        }

        return null;
    };

    const tryReduceDisplayedVerticalTdapp0 = (appTerm: Term): Term | null => {
        const args: Array<{ arg: Term; icit: Icit }> = [];
        let head: Term = appTerm;
        while (getTermRef(head).tag === 'App') {
            const app = getTermRef(head) as Term & { tag: 'App' };
            args.push({ arg: app.arg, icit: app.icit });
            head = app.func;
        }
        args.reverse();

        const headRef = getTermRef(head);
        if (headRef.tag !== 'Var' || headRef.name !== 'tdapp0_fapp0') return null;
        if (args.length !== 8) return null;
        if (!args.every(a => a.icit === Icit.Expl)) return null;

        const Z = args[0].arg;
        const E = args[1].arg;
        const D = args[2].arg;
        const FF = args[3].arg;
        const HH = args[4].arg;
        const Y = args[5].arg;
        const V = args[6].arg;
        const compEtaEpsRaw = args[7].arg;
        const compEtaEps = getTermRef(whnf(compEtaEpsRaw, ctx, stackDepth + 1));

        const compArgs: Array<{ arg: Term; icit: Icit }> = [];
        let compHead: Term = compEtaEps;
        while (getTermRef(compHead).tag === 'App') {
            const app = getTermRef(compHead) as Term & { tag: 'App' };
            compArgs.push({ arg: app.arg, icit: app.icit });
            compHead = app.func;
        }
        compArgs.reverse();

        const compHeadRef = getTermRef(compHead);
        if (compHeadRef.tag !== 'Var' || compHeadRef.name !== 'compose_morph') return null;
        if (compArgs.length !== 6) return null;

        const C = compArgs[0].arg;
        const X = compArgs[1].arg;
        const G = compArgs[2].arg;
        const Zobj = compArgs[3].arg;
        const eta = compArgs[4].arg;
        const eps = compArgs[5].arg;

        const functordCat = FunctordCategoryTerm(Z, E, D);
        if (!areStructurallyEqualNoWhnf(C, functordCat, ctx, stackDepth + 1)) return null;
        if (!areStructurallyEqualNoWhnf(X, FF, ctx, stackDepth + 1)) return null;
        if (!areStructurallyEqualNoWhnf(Zobj, HH, ctx, stackDepth + 1)) return null;
        const GG = G;

        const tdHead = (fDom: Term, fCod: Term): Term =>
            App(
                App(
                    App(
                        App(
                            App(
                                App(
                                    App(Var('tdapp0_fapp0'), Z, Icit.Expl),
                                    E, Icit.Expl
                                ),
                                D, Icit.Expl
                            ),
                            fDom, Icit.Expl
                        ),
                        fCod, Icit.Expl
                    ),
                    Y, Icit.Expl
                ),
                V, Icit.Expl
            );

        const tdEta = App(tdHead(GG, HH), eta, Icit.Expl);
        const tdEps = App(tdHead(FF, GG), eps, Icit.Expl);

        const fd = (Fobj: Term): Term =>
            App(
                App(
                    App(
                        App(
                            App(
                                App(Var('fdapp0'), Z, Icit.Expl),
                                E, Icit.Expl
                            ),
                            D, Icit.Expl
                        ),
                        Fobj, Icit.Expl
                    ),
                    Y, Icit.Expl
                ),
                V, Icit.Expl
            );

        const fibreDY = App(App(App(Var('Fibre'), Z, Icit.Expl), D, Icit.Expl), Y, Icit.Expl);
        return App(
            App(
                App(
                    App(
                        App(
                            App(Var('compose_morph'), fibreDY, Icit.Impl),
                            fd(FF), Icit.Impl
                        ),
                        fd(GG), Icit.Impl
                    ),
                    fd(HH), Icit.Impl
                ),
                tdEta, Icit.Expl
            ),
            tdEps, Icit.Expl
        );
    };

    for (let i = 0; i < MAX_WHNF_ITERATIONS; i++) {
        let changedInThisPass = false;
        const termAtStartOfOuterPass = current;

        const dereffedCurrent = getTermRef(current);
        if (dereffedCurrent !== current) {
            current = dereffedCurrent;
            changedInThisPass = true;
        }

        const termBeforeInnerReductions = current;

        // Check for local definitions first
        // Be careful of name shadowing with global definitions
        if (current.tag === 'Var' && current.isBound) {
            const binding = lookupCtx(ctx, current.name);
            if (binding && binding.definition) {
                    current = binding.definition; // Substitute with the definition
                    changedInThisPass = true;
                    continue; // Restart the whnf loop with the new term
                }
        }

        // Apply user rewrite rules (if not a kernel constant symbol)
        if (!isKernelConstantSymbolStructurally(current)) {
            for (const rule of userRewriteRules) {
                const subst = matchPattern(rule.elaboratedLhs, termBeforeInnerReductions, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    // if (stackDepth > 30) console.log("whnf matchPattern subst: stackDepth", {stackDepth}, {pattern: printTerm(rule.elaboratedLhs), termToMatch: printTerm(termBeforeInnerReductions)});
                    const rhsApplied = getTermRef(applySubst(rule.elaboratedRhs, subst, rule.patternVars));
                    // Check for actual change to prevent non-terminating rule applications like X -> X
                    if (rhsApplied !== termBeforeInnerReductions && !areStructurallyEqualNoWhnf(rhsApplied, termBeforeInnerReductions, ctx, stackDepth + 1)) {
                        current = rhsApplied;
                        changedInThisPass = true;
                        break;
                    }
                }
            }
            if (changedInThisPass) continue;
        }

        let reducedInKernelBlock = false;
        switch (current.tag) {
            case 'App': {
                const displayedVertical = tryReduceDisplayedVerticalTdapp0(current);
                if (displayedVertical) {
                    current = displayedVertical;
                    reducedInKernelBlock = true;
                    break;
                }

                const fibrePointwise = tryReduceFibreOfDisplayedFamily(current);
                if (fibrePointwise) {
                    current = fibrePointwise;
                    reducedInKernelBlock = true;
                    break;
                }

                const func_whnf_ref = getTermRef(whnf(current.func, ctx, stackDepth + 1));
                if (func_whnf_ref.tag === 'Lam' && func_whnf_ref.icit === current.icit) {
                    // Beta reduction
                    current = func_whnf_ref.body(current.arg);
                    reducedInKernelBlock = true;
                } else if (!areStructurallyEqualNoWhnf(getTermRef(current.func), func_whnf_ref, ctx, stackDepth + 1)) {
                    current = App(func_whnf_ref, current.arg, current.icit);
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'Let': {
                // Let reduction: (let x=d in b) reduces to b[d/x]
                // In HOAS, this is simply body(def).
                current = current.body(current.letDef);
                reducedInKernelBlock = true;
                break;
            }
            case 'Lam': { // Eta-contraction
                if (getFlag('etaEquality')) {
                    const lam = current;
                    // Instantiate body to inspect it. The var must be marked as lambda-bound.
                    const body = getTermRef(lam.body(Var(lam.paramName, true))); 
                    if (body.tag === 'App' && body.icit === lam.icit) {
                        const appArg = getTermRef(body.arg);
                        if (appArg.tag === 'Var' && appArg.name === lam.paramName && appArg.isBound) {
                            const funcPart = getTermRef(body.func);
                            // Check that the lambda's parameter is not free in the function part.
                            const freeVarsInF = getFreeVariables(funcPart);
                            if (!freeVarsInF.has(lam.paramName)) {
                                // This is a valid eta-contraction: λx. F x  -->  F
                                current = funcPart;
                                reducedInKernelBlock = true;
                            }
                        }
                    }
                }
                break;
            }
            case 'ObjTerm': {
                const cat_whnf_ref = getTermRef(whnf(current.cat, ctx, stackDepth + 1));
                if (cat_whnf_ref.tag === 'CatCategoryTerm') {
                    // Objects of Cat_cat are categories.
                    current = CatTerm();
                    reducedInKernelBlock = true;
                } else if (cat_whnf_ref.tag === 'CatdCategoryTerm') {
                    // Objects of Catd_cat Z are displayed categories over Z.
                    current = App(Var("Catd"), cat_whnf_ref.baseCat, Icit.Expl);
                    reducedInKernelBlock = true;
                } else if (cat_whnf_ref.tag === 'FunctorCategoryTerm') {
                    // Objects of Functor_cat A B are functors A -> B.
                    current = FunctorTypeTerm(cat_whnf_ref.domainCat, cat_whnf_ref.codomainCat);
                    reducedInKernelBlock = true;
                } else if (cat_whnf_ref.tag === 'FunctordCategoryTerm') {
                    // Objects of Functord_cat Z E D are displayed functors E -> D over Z.
                    current = App(App(App(Var("Functord"), cat_whnf_ref.baseCat, Icit.Expl), cat_whnf_ref.displayedDom, Icit.Expl), cat_whnf_ref.displayedCod, Icit.Expl);
                    reducedInKernelBlock = true;
                } else if (cat_whnf_ref.tag === 'TransfCategoryTerm') {
                    // Objects of Transf_cat A B F G are ordinary transfors F => G.
                    current = NatTransTypeTerm(cat_whnf_ref.catA, cat_whnf_ref.catB, cat_whnf_ref.functorF, cat_whnf_ref.functorG);
                    reducedInKernelBlock = true;
                } else if (cat_whnf_ref.tag === 'TransfdCategoryTerm') {
                    // Objects of Transfd_cat Z E D FF GG are displayed transfors FF => GG.
                    current = App(
                        App(
                            App(
                                App(
                                    App(Var("Transfd"), cat_whnf_ref.baseCat, Icit.Expl),
                                    cat_whnf_ref.displayedDom, Icit.Expl
                                ),
                                cat_whnf_ref.displayedCod, Icit.Expl
                            ),
                            cat_whnf_ref.functorFF, Icit.Expl
                        ),
                        cat_whnf_ref.functorGG, Icit.Expl
                    );
                    reducedInKernelBlock = true;
                } else
                if (getTermRef(current.cat) !== cat_whnf_ref) {
                    current = ObjTerm(cat_whnf_ref);
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'HomTerm': {
                const cat_whnf_ref = getTermRef(whnf(current.cat, ctx, stackDepth + 1));
                if (cat_whnf_ref.tag === 'FunctorCategoryTerm') {
                    // Hom in functor category is NatTransType
                    current = NatTransTypeTerm(cat_whnf_ref.domainCat, cat_whnf_ref.codomainCat, current.dom, current.cod);
                    reducedInKernelBlock = true;
                } else if (cat_whnf_ref.tag === 'FunctordCategoryTerm') {
                    // Hom in displayed-functor category is displayed transfor type.
                    current = App(
                        App(
                            App(
                                App(
                                    App(Var("Transfd"), cat_whnf_ref.baseCat, Icit.Expl),
                                    cat_whnf_ref.displayedDom, Icit.Expl
                                ),
                                cat_whnf_ref.displayedCod, Icit.Expl
                            ),
                            current.dom, Icit.Expl
                        ),
                        current.cod, Icit.Expl
                    );
                    reducedInKernelBlock = true;
                } else if (getTermRef(current.cat) !== cat_whnf_ref) {
                    current = HomTerm(cat_whnf_ref, current.dom, current.cod);
                    reducedInKernelBlock = true;
                } else {
                    // Hom in Set is Pi type
                    const setGlobal = globalDefs.get("Set");
                    if (setGlobal?.value && areStructurallyEqualNoWhnf(cat_whnf_ref, getTermRef(setGlobal.value), ctx)) {
                         const domWhnf = whnf(current.dom, ctx, stackDepth + 1);
                         const codWhnf = whnf(current.cod, ctx, stackDepth + 1);
                         current = Pi(freshVarName("_x_hom_set"), Icit.Expl, domWhnf, _ => codWhnf);
                         reducedInKernelBlock = true;
                    }
                }
                break;
            }
            case 'Var': { // Global definition unfolding (if not a local definition was found)
                const gdef = globalDefs.get(current.name);
                if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol) {
                    current = gdef.value;
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'FMap0Term': {
                const functor_whnf = getTermRef(whnf(current.functor, ctx, stackDepth + 1));
                if (functor_whnf.tag === 'HomCovFunctorIdentity') {
                    // Rule: fapp0 (hom_cov A W) Y  ↪  Hom A W Y
                    current = HomTerm(functor_whnf.domainCat, functor_whnf.objW_InDomainCat, current.objectX);
                    reducedInKernelBlock = true;
                } else if (functor_whnf.tag === 'MkFunctorTerm') {
                    // Rule: fmap0 (mkFunctor fmap0 fmap1) X  ↪  fmap0 X
                    current = App(functor_whnf.fmap0, current.objectX, Icit.Expl);
                    reducedInKernelBlock = true;
                } else {
                    const objectX_whnf = getTermRef(whnf(current.objectX, ctx, stackDepth + 1));
                    const catA_IMPLICIT_whnf = current.catA_IMPLICIT ? getTermRef(whnf(current.catA_IMPLICIT, ctx, stackDepth + 1)) : undefined;
                    const catB_IMPLICIT_whnf = current.catB_IMPLICIT ? getTermRef(whnf(current.catB_IMPLICIT, ctx, stackDepth + 1)) : undefined;

                    if (getTermRef(current.functor) !== functor_whnf ||
                        getTermRef(current.objectX) !== objectX_whnf ||
                        (current.catA_IMPLICIT && getTermRef(current.catA_IMPLICIT) !== catA_IMPLICIT_whnf) ||
                        (current.catB_IMPLICIT && getTermRef(current.catB_IMPLICIT) !== catB_IMPLICIT_whnf)
                    ) {
                        current = FMap0Term(functor_whnf, objectX_whnf, catA_IMPLICIT_whnf, catB_IMPLICIT_whnf);
                        reducedInKernelBlock = true;
                    }
                }
                break;
            }
            case 'FMap1Term': {
                const functor_whnf = getTermRef(whnf(current.functor, ctx, stackDepth + 1));
                if (functor_whnf.tag === 'MkFunctorTerm') {
                    // Rule: fmap1 (mkFunctor fmap0 fmap1) {X} {Y} a  ↪  fmap1 {X} {Y} a
                    const fmap1 = functor_whnf.fmap1;
                    const X = current.objX_A_IMPLICIT!;
                    const Y = current.objY_A_IMPLICIT!;
                    const a = current.morphism_a;
                    current = App(App(App(fmap1, X, Icit.Impl), Y, Icit.Impl), a, Icit.Expl);
                    reducedInKernelBlock = true;
                }
                // No further reduction for FMap1Term in this pass
                break;
            }
            case 'TApp1FApp0Term': {
                const transformation_whnf = getTermRef(whnf(current.transformation, ctx, stackDepth + 1));
                const morphism_whnf = getTermRef(whnf(current.morphism_f, ctx, stackDepth + 1));
                if (getTermRef(current.transformation) !== transformation_whnf || getTermRef(current.morphism_f) !== morphism_whnf) {
                    current = TApp1FApp0Term(
                        transformation_whnf,
                        morphism_whnf,
                        current.catA_IMPLICIT,
                        current.catB_IMPLICIT,
                        current.functorF_IMPLICIT,
                        current.functorG_IMPLICIT,
                        current.objX_A_IMPLICIT,
                        current.objY_A_IMPLICIT
                    );
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'FDApp1Term': {
                const functor_whnf = getTermRef(whnf(current.displayedFunctor, ctx, stackDepth + 1));
                const sigma_whnf = getTermRef(whnf(current.morphism_sigma, ctx, stackDepth + 1));
                if (getTermRef(current.displayedFunctor) !== functor_whnf || getTermRef(current.morphism_sigma) !== sigma_whnf) {
                    current = FDApp1Term(
                        functor_whnf,
                        sigma_whnf,
                        current.catZ_IMPLICIT,
                        current.catdE_IMPLICIT,
                        current.catdD_IMPLICIT,
                        current.objZ_IMPLICIT,
                        current.objE_IMPLICIT,
                        current.objZPrime_IMPLICIT,
                        current.homF_IMPLICIT,
                        current.objEPrime_IMPLICIT
                    );
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'TDApp1Term': {
                const transformation_whnf = getTermRef(whnf(current.transformation, ctx, stackDepth + 1));
                const sigma_whnf = getTermRef(whnf(current.morphism_sigma, ctx, stackDepth + 1));
                if (getTermRef(current.transformation) !== transformation_whnf || getTermRef(current.morphism_sigma) !== sigma_whnf) {
                    current = TDApp1Term(
                        transformation_whnf,
                        sigma_whnf,
                        current.catZ_IMPLICIT,
                        current.catdE_IMPLICIT,
                        current.catdD_IMPLICIT,
                        current.functorFF_IMPLICIT,
                        current.functorGG_IMPLICIT,
                        current.objZ_IMPLICIT,
                        current.objE_IMPLICIT,
                        current.objZPrime_IMPLICIT,
                        current.homF_IMPLICIT,
                        current.objEPrime_IMPLICIT
                    );
                    reducedInKernelBlock = true;
                }
                break;
            }
            case 'FunctorTypeTerm': {
                const domainCat_whnf = getTermRef(whnf(current.domainCat, ctx, stackDepth + 1));
                const codomainCat_whnf = getTermRef(whnf(current.codomainCat, ctx, stackDepth + 1));
                if (getTermRef(current.domainCat) !== domainCat_whnf || getTermRef(current.codomainCat) !== codomainCat_whnf) {
                    current = FunctorTypeTerm(domainCat_whnf, codomainCat_whnf);
                    reducedInKernelBlock = true;
                }
                break;
            }
             // Other cases (Pi, Type, CatTerm, SetTerm, etc.) are already in WHNF or do not reduce further at head.
        }

        if (reducedInKernelBlock) {
             changedInThisPass = true;
             continue; // Restart WHNF with the kernel-reduced term
        }

        // If only getTermRef changed the term, update and mark progress
        const currentAfterPossibleKernelOrRefChange = getTermRef(current);
        if (currentAfterPossibleKernelOrRefChange !== termBeforeInnerReductions && !changedInThisPass) {
            current = currentAfterPossibleKernelOrRefChange;
            changedInThisPass = true;
        }

        if (!changedInThisPass) break; // No change in this pass, term is in WHNF

        // Check for non-productive loops (term reduces to itself structurally)
        if (current === termAtStartOfOuterPass && !changedInThisPass && i > 0) break;


        if (i === MAX_WHNF_ITERATIONS - 1) {
             if (changedInThisPass || current !== termAtStartOfOuterPass) { // Check if it was still changing
                console.warn(`[TRACE whnf (${stackDepth})] WHNF reached max iterations for: ${printTerm(term)} -> ${printTerm(current)}`);
             }
        }
    }
    return current;
}

/**
 * Normalizes a term by reducing it to WHNF and then recursively normalizing its subterms.
 * @param term The term to normalize.
 * @param ctx The current context.
 * @param stackDepth Recursion depth.
 * @returns The normalized term.
 */
export function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Normalize stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    const headReduced = whnf(term, ctx, stackDepth + 1);
    const current = getTermRef(headReduced);
    switch (current.tag) {
        case 'Type': case 'Var' : case 'Hole': case 'CatTerm': case 'CatCategoryTerm': case 'SetTerm': return current;
        case 'CatdCategoryTerm':
            return CatdCategoryTerm(normalize(current.baseCat, ctx, stackDepth + 1));
        case 'ObjTerm': return ObjTerm(normalize(current.cat, ctx, stackDepth + 1));
        case 'HomTerm':
            return HomTerm(
                normalize(current.cat, ctx, stackDepth + 1),
                normalize(current.dom, ctx, stackDepth + 1),
                normalize(current.cod, ctx, stackDepth + 1)
            );
        case 'FunctorCategoryTerm':
            return FunctorCategoryTerm(
                normalize(current.domainCat, ctx, stackDepth + 1),
                normalize(current.codomainCat, ctx, stackDepth + 1)
            );
        case 'FunctordCategoryTerm':
            return FunctordCategoryTerm(
                normalize(current.baseCat, ctx, stackDepth + 1),
                normalize(current.displayedDom, ctx, stackDepth + 1),
                normalize(current.displayedCod, ctx, stackDepth + 1)
            );
        case 'FunctorCatdTerm':
            return FunctorCatdTerm(
                normalize(current.baseCat, ctx, stackDepth + 1),
                normalize(current.displayedDom, ctx, stackDepth + 1),
                normalize(current.displayedCod, ctx, stackDepth + 1)
            );
        case 'TransfCategoryTerm':
            return TransfCategoryTerm(
                normalize(current.catA, ctx, stackDepth + 1),
                normalize(current.catB, ctx, stackDepth + 1),
                normalize(current.functorF, ctx, stackDepth + 1),
                normalize(current.functorG, ctx, stackDepth + 1)
            );
        case 'TransfCatdTerm':
            return TransfCatdTerm(
                normalize(current.baseCat, ctx, stackDepth + 1),
                normalize(current.displayedDom, ctx, stackDepth + 1),
                normalize(current.displayedCod, ctx, stackDepth + 1),
                normalize(current.functorFF, ctx, stackDepth + 1),
                normalize(current.functorGG, ctx, stackDepth + 1)
            );
        case 'TransfdCategoryTerm':
            return TransfdCategoryTerm(
                normalize(current.baseCat, ctx, stackDepth + 1),
                normalize(current.displayedDom, ctx, stackDepth + 1),
                normalize(current.displayedCod, ctx, stackDepth + 1),
                normalize(current.functorFF, ctx, stackDepth + 1),
                normalize(current.functorGG, ctx, stackDepth + 1)
            );
        case 'FunctorTypeTerm':
            return FunctorTypeTerm(
                normalize(current.domainCat, ctx, stackDepth + 1),
                normalize(current.codomainCat, ctx, stackDepth + 1)
            );
        case 'FMap0Term':
            return FMap0Term(
                normalize(current.functor, ctx, stackDepth + 1),
                normalize(current.objectX, ctx, stackDepth + 1),
                current.catA_IMPLICIT ? normalize(current.catA_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.catB_IMPLICIT ? normalize(current.catB_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'FMap1Term':
            return FMap1Term(
                normalize(current.functor, ctx, stackDepth + 1),
                normalize(current.morphism_a, ctx, stackDepth + 1),
                current.catA_IMPLICIT ? normalize(current.catA_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.catB_IMPLICIT ? normalize(current.catB_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objX_A_IMPLICIT ? normalize(current.objX_A_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objY_A_IMPLICIT ? normalize(current.objY_A_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'NatTransTypeTerm':
            return NatTransTypeTerm(
                normalize(current.catA, ctx, stackDepth + 1),
                normalize(current.catB, ctx, stackDepth + 1),
                normalize(current.functorF, ctx, stackDepth + 1),
                normalize(current.functorG, ctx, stackDepth + 1)
            );
        case 'NatTransComponentTerm':
            return NatTransComponentTerm(
                normalize(current.transformation, ctx, stackDepth + 1),
                normalize(current.objectX, ctx, stackDepth + 1),
                current.catA_IMPLICIT ? normalize(current.catA_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.catB_IMPLICIT ? normalize(current.catB_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.functorF_IMPLICIT ? normalize(current.functorF_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.functorG_IMPLICIT ? normalize(current.functorG_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'TApp1FApp0Term':
            return TApp1FApp0Term(
                normalize(current.transformation, ctx, stackDepth + 1),
                normalize(current.morphism_f, ctx, stackDepth + 1),
                current.catA_IMPLICIT ? normalize(current.catA_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.catB_IMPLICIT ? normalize(current.catB_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.functorF_IMPLICIT ? normalize(current.functorF_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.functorG_IMPLICIT ? normalize(current.functorG_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objX_A_IMPLICIT ? normalize(current.objX_A_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objY_A_IMPLICIT ? normalize(current.objY_A_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'FDApp1Term':
            return FDApp1Term(
                normalize(current.displayedFunctor, ctx, stackDepth + 1),
                normalize(current.morphism_sigma, ctx, stackDepth + 1),
                current.catZ_IMPLICIT ? normalize(current.catZ_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.catdE_IMPLICIT ? normalize(current.catdE_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.catdD_IMPLICIT ? normalize(current.catdD_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objZ_IMPLICIT ? normalize(current.objZ_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objE_IMPLICIT ? normalize(current.objE_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objZPrime_IMPLICIT ? normalize(current.objZPrime_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.homF_IMPLICIT ? normalize(current.homF_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objEPrime_IMPLICIT ? normalize(current.objEPrime_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'TDApp1Term':
            return TDApp1Term(
                normalize(current.transformation, ctx, stackDepth + 1),
                normalize(current.morphism_sigma, ctx, stackDepth + 1),
                current.catZ_IMPLICIT ? normalize(current.catZ_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.catdE_IMPLICIT ? normalize(current.catdE_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.catdD_IMPLICIT ? normalize(current.catdD_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.functorFF_IMPLICIT ? normalize(current.functorFF_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.functorGG_IMPLICIT ? normalize(current.functorGG_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objZ_IMPLICIT ? normalize(current.objZ_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objE_IMPLICIT ? normalize(current.objE_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objZPrime_IMPLICIT ? normalize(current.objZPrime_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.homF_IMPLICIT ? normalize(current.homF_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objEPrime_IMPLICIT ? normalize(current.objEPrime_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'HomCovFunctorIdentity':
            return HomCovFunctorIdentity(
                normalize(current.domainCat, ctx, stackDepth + 1),
                normalize(current.objW_InDomainCat, ctx, stackDepth + 1)
            );
        case 'MkFunctorTerm':
            return MkFunctorTerm(
                normalize(current.domainCat, ctx, stackDepth + 1),
                normalize(current.codomainCat, ctx, stackDepth + 1),
                normalize(current.fmap0, ctx, stackDepth + 1),
                normalize(current.fmap1, ctx, stackDepth + 1)
            );
        case 'Lam': {
            const currentLam = current;
            const normLamParamType = (currentLam._isAnnotated && currentLam.paramType)
                                     ? normalize(currentLam.paramType, ctx, stackDepth + 1)
                                     : undefined;
            
            // Instantiate body with a fresh variable to normalize its structure
            const placeholderVar = Var(currentLam.paramName, true);
            const paramTypeForBodyCtx = normLamParamType || (currentLam.paramType ? getTermRef(currentLam.paramType) : Hole(freshHoleName()+"_norm_lam_body_ctx"));
            const bodyCtx = extendCtx(
                ctx,
                currentLam.paramName,
                paramTypeForBodyCtx,
                currentLam.icit,
                undefined,
                currentLam.mode ?? BinderMode.Functorial,
                currentLam.controllerCat
            );
            
            // Normalize the body structure ONCE
            const normalizedBody = normalize(currentLam.body(placeholderVar), bodyCtx, stackDepth + 1);

            // Create the new lambda with a simple substitution body
            const newBodyFn = (v_arg_placeholder: Term): Term => {
                return replaceFreeVar(normalizedBody, placeholderVar.name, v_arg_placeholder);
            };

            const normLam = Lam(currentLam.paramName, currentLam.icit, normLamParamType, newBodyFn) as Term & {tag: 'Lam'};
            normLam._isAnnotated = currentLam._isAnnotated && normLamParamType !== undefined;
            normLam.mode = currentLam.mode;
            normLam.controllerCat = currentLam.controllerCat;
            return normLam;
        }
        case 'Let': {
            const letNode = current;
            const normalizedDef = normalize(letNode.letDef, ctx, stackDepth + 1);
            const substitutedBody = letNode.body(normalizedDef);
            return normalize(substitutedBody, ctx, stackDepth + 1);
        }
        case 'App': {
            const normFunc = normalize(current.func, ctx, stackDepth + 1);
            const normArg = normalize(current.arg, ctx, stackDepth + 1);
            const finalNormFunc = getTermRef(normFunc);

            if (finalNormFunc.tag === 'Lam' && finalNormFunc.icit === current.icit) {
                // Beta reduction during normalization
                return normalize(finalNormFunc.body(normArg), ctx, stackDepth + 1);
            }
            // If it's not a beta-redex, reconstruct the application.
            const reconstructedApp = App(normFunc, normArg, current.icit);

            // This comparison is key. We are comparing the *function part* of the application.
            // If normalizing the function part changed it (e.g., `add 1` became `add (s z)`),
            // then the reconstructed application might match a new rule.
            if (areStructurallyEqualNoWhnf(normFunc, current.func, ctx, stackDepth + 1)) {
                return reconstructedApp;
            }

            // The function part changed, so re-normalize the whole App to apply new rules.
            return normalize(reconstructedApp, ctx, stackDepth + 1);
        }
        case 'Pi': {
            const currentPi = current;
            const normPiParamType = normalize(currentPi.paramType, ctx, stackDepth + 1);

            // Instantiate body with a fresh variable to normalize its structure
            const placeholderVar = Var(currentPi.paramName, true);
            const bodyTypeCtx = extendCtx(
                ctx,
                currentPi.paramName,
                normPiParamType,
                currentPi.icit,
                undefined,
                currentPi.mode ?? BinderMode.Functorial,
                currentPi.controllerCat
            );

            // Normalize the body structure ONCE
            const normalizedBodyType = normalize(currentPi.bodyType(placeholderVar), bodyTypeCtx, stackDepth + 1);
            
            // Create the new Pi with a simple substitution body
            const newBodyTypeFn = (v_arg_placeholder: Term): Term => {
                return replaceFreeVar(normalizedBodyType, placeholderVar.name, v_arg_placeholder);
            };
            const normPi = Pi(currentPi.paramName, currentPi.icit, normPiParamType, newBodyTypeFn);
            normPi.mode = currentPi.mode;
            normPi.controllerCat = currentPi.controllerCat;
            return normPi;
        }
        default: const exhaustiveCheck: never = current; throw new Error(`Normalize: Unhandled term: ${(exhaustiveCheck as any).tag }`);
    }
}
