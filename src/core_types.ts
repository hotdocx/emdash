export enum Icit { Impl, Expl }

export type BaseTerm =
    | { tag: 'Type' }
    | { tag: 'Var', name: string }
    | { tag: 'Lam', paramName: string, icit: Icit, paramType?: Term, body: (v: Term) => Term, _isAnnotated: boolean }
    | { tag: 'App', func: Term, arg: Term, icit: Icit }
    | { tag: 'Pi', paramName: string, icit: Icit, paramType: Term, bodyType: (v: Term) => Term }
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
export type PatternVarDecl = string; // e.g., "$x", "$myVar"

export const Type = (): Term => ({ tag: 'Type' });
export const Var = (name: string): Term & { tag: 'Var' } => ({ tag: 'Var', name });

export const Lam = (paramName: string, icit: Icit, paramTypeOrBody: Term | ((v: Term) => Term), bodyOrNothing?: (v: Term) => Term): Term & { tag: 'Lam' } => {
    if (typeof paramTypeOrBody === 'function' && bodyOrNothing === undefined) { // Unannotated: Lam(name, icit, body)
        return { tag: 'Lam', paramName, icit, paramType: undefined, body: paramTypeOrBody, _isAnnotated: false };
    } else if (paramTypeOrBody && typeof paramTypeOrBody !== 'function' && bodyOrNothing && typeof bodyOrNothing === 'function') { // Annotated: Lam(name, icit, type, body)
        return { tag: 'Lam', paramName, icit, paramType: paramTypeOrBody as Term, body: bodyOrNothing, _isAnnotated: true };
    }
    throw new Error(`Invalid Lam arguments: name=${paramName}, icit=${icit}, paramTypeOrBody=${paramTypeOrBody}, bodyOrNothing=${bodyOrNothing}`);
};

export const App = (func: Term, arg: Term, icit: Icit = Icit.Expl): Term & {tag: 'App'} => ({ tag: 'App', func, arg, icit });

export const Pi = (paramName: string, icit: Icit, paramType: Term, bodyType: (v: Term) => Term): Term & {tag: 'Pi'} =>
    ({ tag: 'Pi', paramName, icit, paramType, bodyType });

// Forward declaration for freshHoleName, will be imported from core_context_globals
export declare const freshHoleName: () => string;

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

export type Binding = { name: string, type: Term, icit?: Icit };
export type Context = Binding[];

export interface GlobalDef {
    name: string;
    type: Term; // This type should be in WHNF or easily normalizable
    value?: Term;
    isConstantSymbol?: boolean;
    isInjective?: boolean; // For unification decomposition: F X = F Y => X = Y
}
export interface RewriteRule { // Raw rule definition for storage before elaboration
    name: string;
    patternVars: PatternVarDecl[]; // string[] e.g. ["$x"]
    lhs: Term; // Raw LHS
    rhs: Term; // Raw RHS
}

export interface StoredRewriteRule { // Rule after elaboration, ready for matching
    name: string;
    patternVars: PatternVarDecl[]; // string[] e.g. ["$x"]
    elaboratedLhs: Term;
    elaboratedRhs: Term;
}

export interface UnificationRule {
    name: string;
    patternVars: PatternVarDecl[]; // string[]
    lhsPattern1: Term;
    lhsPattern2: Term;
    rhsNewConstraints: Array<{ t1: Term, t2: Term }>;
}
export type Substitution = Map<string, Term>;
export interface Constraint { t1: Term; t2: Term; origin?: string; }
export enum UnifyResult { Solved, Failed, RewrittenByRule, Progress }

export interface ElaborationResult { term: Term; type: Term; }