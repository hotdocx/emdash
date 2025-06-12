/**
 * @file types.ts
 * @description Defines the core data structures for terms, types, contexts,
 * and other fundamental elements of the emdash type theory.
 */

export enum Icit { Impl, Expl }

export type BaseTerm =
    | { tag: 'Type' }
    | { tag: 'Var', name: string, isBound?: boolean, origin?: "occurs_check" | "pattern_var" }
    | { tag: 'Lam', paramName: string, icit: Icit, paramType?: Term, body: (v: Term) => Term, _isAnnotated: boolean }
    | { tag: 'App', func: Term, arg: Term, icit: Icit }
    | { tag: 'Pi', paramName: string, icit: Icit, paramType: Term, bodyType: (v: Term) => Term }
    | { tag: 'Let', letName: string, letType?: Term, letDef: Term, body: (v: Term) => Term, _isAnnotated: boolean }
    | { tag: 'Hole', 
        id: string, 
        ref?: Term, 
        elaboratedType?: Term,
        // For pattern variables: list of *names* of binders from the pattern's
        // own scope that the matched term is allowed to freely refer to.
        // If undefined: no restriction (classical pattern var).
        // If empty array []: cannot refer to any local pattern binders (e.g., for $F.[]).
        patternAllowedLocalBinders?: string[]
      }
    // Emdash Phase 1: Core Categories
    | { tag: 'CatTerm' }
    | { tag: 'ObjTerm', cat: Term }
    | { tag: 'HomTerm', cat: Term, dom: Term, cod: Term }
    // Emdash Phase 2: Functors and Natural Transformations
    | { tag: 'FunctorTypeTerm', domainCat: Term, codomainCat: Term }
    | { tag: 'FunctorCategoryTerm', domainCat: Term, codomainCat: Term }
    | { tag: 'FMap0Term', // fapp0 F X
        functor: Term, // Term of type FunctorTypeTerm(catA, catB)
        objectX: Term, // ObjTerm(catA)
        catA_IMPLICIT?: Term,
        catB_IMPLICIT?: Term
      }
    | { tag: 'FMap1Term', // fapp1 F a
        functor: Term, // Term of type FunctorTypeTerm(catA, catB)
        morphism_a: Term, // HomTerm(catA, objX_A, objY_A)
        catA_IMPLICIT?: Term,
        catB_IMPLICIT?: Term,
        objX_A_IMPLICIT?: Term,
        objY_A_IMPLICIT?: Term
      }
    | { tag: 'NatTransTypeTerm', // Transf A B F G
        catA: Term,
        catB: Term,
        functorF: Term, // Term of type FunctorTypeTerm(catA, catB)
        functorG: Term  // Term of type FunctorTypeTerm(catA, catB)
      }
    | { tag: 'NatTransComponentTerm', // tapp eps X
        transformation: Term, // Term of type NatTransTypeTerm
        objectX: Term, // ObjTerm(catA)
        catA_IMPLICIT?: Term,
        catB_IMPLICIT?: Term,
        functorF_IMPLICIT?: Term,
        functorG_IMPLICIT?: Term
      }
    // Emdash Phase 3: Yoneda and Set Category Primitives
    | { tag: 'HomCovFunctorIdentity', domainCat: Term, objW_InDomainCat: Term }
    | { tag: 'SetTerm' }
    // Emdash Phase 4: Functorial Elaboration Primitives
    | { tag: 'MkFunctorTerm', 
        domainCat: Term, 
        codomainCat: Term, 
        fmap0: Term, 
        fmap1: Term,
        proof?: Term // [TODO] definitional proof-irrelevance: discard this field for all elaborations, after type checking the provided proof
      }
    ;

export type Term = BaseTerm;
export type PatternVarDecl = string; // e.g., "$x", "$myVar"

// Term Constructors
// These functions create instances of the term types defined in BaseTerm.

export const Type = (): Term & { tag: 'Type' } => ({ tag: 'Type' });
export const Var = (name: string, isBound: boolean = false, origin?: "occurs_check" | "pattern_var"): Term & { tag: 'Var' } => ({ tag: 'Var', name, isBound, origin });
/** A locally bound variable (by a lambda or let). */
export const boundVar = (name: string): Term & { tag: 'Var' } => Var(name, true);
/** A global definition variable. */
export const Def = (name: string): Term & { tag: 'Var' } => Var(name, false);

export function Lam(paramName: string, icit: Icit, body: (v: Term) => Term): Term & { tag: 'Lam' };
export function Lam(paramName: string, icit: Icit, paramType: Term, body: (v: Term) => Term): Term & { tag: 'Lam' };
export function Lam(paramName: string, icit: Icit, paramTypeOrBody: Term | ((v: Term) => Term), bodyOrNothing?: (v: Term) => Term): Term & { tag: 'Lam' } {
    if (typeof paramTypeOrBody === 'function' && bodyOrNothing === undefined) { // Unannotated: Lam(name, icit, body)
        const bodyFn = paramTypeOrBody;
        return { tag: 'Lam', paramName, icit, paramType: undefined, body: bodyFn, _isAnnotated: false };
    } else if (typeof paramTypeOrBody !== 'function' && typeof bodyOrNothing === 'function') { // Annotated: Lam(name, icit, type, body)
        const paramType = paramTypeOrBody as Term;
        const bodyFn = bodyOrNothing;
        return { tag: 'Lam', paramName, icit, paramType, body: bodyFn, _isAnnotated: true };
    }
    throw new Error(`Invalid Lam arguments: name=${paramName}, icit=${icit}, paramTypeOrBody=${paramTypeOrBody}, bodyOrNothing=${bodyOrNothing}`);
}

export const App = (func: Term, arg: Term, icit: Icit = Icit.Expl): Term & {tag: 'App'} => ({ tag: 'App', func, arg, icit });

export const Pi = (paramName: string, icit: Icit, paramType: Term, bodyType: (v: Term) => Term): Term & {tag: 'Pi'} =>
    ({ tag: 'Pi', paramName, icit, paramType, bodyType });

export function Let(letName: string, letDef: Term, body: (v: Term) => Term): Term & { tag: 'Let' };
export function Let(letName: string, letType: Term, letDef: Term, body: (v: Term) => Term): Term & { tag: 'Let' };
export function Let(letName: string, secondParam: Term, thirdParam: Term | ((v: Term) => Term), fourthParam?: (v: Term) => Term): Term & { tag: 'Let' } {
    // Case 1: Unannotated Let(name, def, body)
    // Here, secondParam is the letDef (Term), thirdParam is the body function ((v: Term) => Term), and fourthParam is undefined.
    if (typeof thirdParam === 'function' && fourthParam === undefined) {
        const letDef = secondParam;
        const bodyFn = thirdParam;
        return { tag: 'Let', letName, letType: undefined, letDef, body: bodyFn, _isAnnotated: false };
    }
    // Case 2: Annotated Let(name, type, def, body)
    // Here, secondParam is the letType (Term), thirdParam is the letDef (Term), and fourthParam is the body function ((v: Term) => Term).
    else if (typeof thirdParam !== 'function' && typeof fourthParam === 'function') {
        const letType = secondParam;
        const letDef = thirdParam as Term;
        const bodyFn = fourthParam;
        return { tag: 'Let', letName, letType, letDef, body: bodyFn, _isAnnotated: true };
    }
    throw new Error(`Invalid Let arguments: name=${letName}, secondParam=${secondParam}, thirdParam=${thirdParam}, fourthParam=${fourthParam}`);
}

export const Hole = (id: string, patternAllowedLocalBinders?: string[]): Term & { tag: 'Hole' } => {
    const holeTerm: Term & { tag: 'Hole' } = { tag: 'Hole', id };
    if (patternAllowedLocalBinders !== undefined) {
        holeTerm.patternAllowedLocalBinders = patternAllowedLocalBinders;
    }
    // ref and elaboratedType are typically set during unification/elaboration
    return holeTerm;
};

// Category Theory Constructors
export const CatTerm = (): Term & { tag: 'CatTerm' } => ({ tag: 'CatTerm' });
export const ObjTerm = (cat: Term): Term & { tag: 'ObjTerm' } => ({ tag: 'ObjTerm', cat });
export const HomTerm = (cat: Term, dom: Term, cod: Term): Term & { tag: 'HomTerm' } => ({ tag: 'HomTerm', cat, dom, cod });

// Functors and Natural Transformations Constructors
export const FunctorTypeTerm = (domainCat: Term, codomainCat: Term): Term & { tag: 'FunctorTypeTerm' } =>
    ({ tag: 'FunctorTypeTerm', domainCat, codomainCat });

export const FunctorCategoryTerm = (domainCat: Term, codomainCat: Term): Term & { tag: 'FunctorCategoryTerm' } =>
    ({ tag: 'FunctorCategoryTerm', domainCat, codomainCat });

export const FMap0Term = (functor: Term, objectX: Term, catA_IMPLICIT?: Term, catB_IMPLICIT?: Term): Term & { tag: 'FMap0Term' } =>
    ({ tag: 'FMap0Term', functor, objectX, catA_IMPLICIT, catB_IMPLICIT });

export const FMap1Term = (functor: Term, morphism_a: Term, catA_IMPLICIT?: Term, catB_IMPLICIT?: Term, objX_A_IMPLICIT?: Term, objY_A_IMPLICIT?: Term): Term & { tag: 'FMap1Term' } =>
    ({ tag: 'FMap1Term', functor, morphism_a, catA_IMPLICIT, catB_IMPLICIT, objX_A_IMPLICIT, objY_A_IMPLICIT });

export const NatTransTypeTerm = (catA: Term, catB: Term, functorF: Term, functorG: Term): Term & { tag: 'NatTransTypeTerm' } =>
    ({ tag: 'NatTransTypeTerm', catA, catB, functorF, functorG });

export const NatTransComponentTerm = (transformation: Term, objectX: Term, catA_IMPLICIT?: Term, catB_IMPLICIT?: Term, functorF_IMPLICIT?: Term, functorG_IMPLICIT?: Term): Term & { tag: 'NatTransComponentTerm' } =>
    ({ tag: 'NatTransComponentTerm', transformation, objectX, catA_IMPLICIT, catB_IMPLICIT, functorF_IMPLICIT, functorG_IMPLICIT });

// Yoneda and Set Category Primitives Constructors
export const HomCovFunctorIdentity = (domainCat: Term, objW_InDomainCat: Term): Term & { tag: 'HomCovFunctorIdentity' } =>
    ({ tag: 'HomCovFunctorIdentity', domainCat, objW_InDomainCat });

export const SetTerm = (): Term & { tag: 'SetTerm' } => ({ tag: 'SetTerm' });

export const MkFunctorTerm = (domainCat: Term, codomainCat: Term, fmap0: Term, fmap1: Term, proof?: Term): Term & { tag: 'MkFunctorTerm' } =>
    ({ tag: 'MkFunctorTerm', domainCat, codomainCat, fmap0, fmap1, proof });


// Context and Global Definitions
export type Binding = {
    name: string;
    type: Term;
    definition?: Term;
    icit?: Icit;
};
export type Context = Binding[];

export interface GlobalDef {
    name: string;
    type: Term; // This type should be in WHNF or easily normalizable
    value?: Term;
    isConstantSymbol?: boolean;
    isInjective?: boolean; // For unification decomposition: F X = F Y => X = Y
}

// Rewrite and Unification Rules
export interface RewriteRule { // Raw rule definition for storage before elaboration
    name: string;
    patternVars: PatternVarDecl[];
    lhs: Term;
    rhs: Term;
}

export interface StoredRewriteRule { // Rule after elaboration, ready for matching
    name: string;
    patternVars: PatternVarDecl[];
    elaboratedLhs: Term;
    elaboratedRhs: Term;
}

export interface UnificationRule {
    name: string;
    patternVars: PatternVarDecl[];
    lhsPattern1: Term;
    lhsPattern2: Term;
    rhsNewConstraints: Array<{ t1: Term, t2: Term }>;
}

// Constraints and Elaboration Results
export type Substitution = Map<string, Term>;
export interface Constraint { t1: Term; t2: Term; origin?: string; }
export enum UnifyResult { Solved, Failed, RewrittenByRule, Progress }

export interface ElaborationResult { term: Term; type: Term; }