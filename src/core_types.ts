// --- Term Definition ---
export type BaseTerm =
    | { tag: 'Type' }
    | { tag: 'Var', name: string }
    | { tag: 'Lam', paramName: string, paramType?: Term, body: (v: Term) => Term, _isAnnotated: boolean }
    | { tag: 'App', func: Term, arg: Term }
    | { tag: 'Pi', paramName: string, paramType: Term, bodyType: (v: Term) => Term }
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
export type PatternVarDecl = { name: string, type: Term };

export const Type = (): Term => ({ tag: 'Type' });
export const Var = (name: string): Term & { tag: 'Var' } => ({ tag: 'Var', name });
export const Lam = (paramName: string, paramTypeOrBody: Term | ((v: Term) => Term), bodyOrNothing?: (v: Term) => Term): Term & { tag: 'Lam' } => {
    if (typeof paramTypeOrBody === 'function' && bodyOrNothing === undefined) {
        return { tag: 'Lam', paramName, paramType: undefined, body: paramTypeOrBody, _isAnnotated: false };
    } else if (bodyOrNothing && typeof bodyOrNothing === 'function' && paramTypeOrBody) {
        return { tag: 'Lam', paramName, paramType: paramTypeOrBody as Term, body: bodyOrNothing, _isAnnotated: true };
    }
    throw new Error(`Invalid Lam arguments: ${paramName}, ${paramTypeOrBody}, ${bodyOrNothing}`);
}
export const App = (func: Term, arg: Term): Term => ({ tag: 'App', func, arg });
export const Pi = (paramName: string, paramType: Term, bodyType: (v: Term) => Term): Term =>
    ({ tag: 'Pi', paramName, paramType, bodyType });

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

export type Binding = { name: string, type: Term };
export type Context = Binding[];
export interface GlobalDef {
    name: string;
    type: Term;
    value?: Term;
    isConstantSymbol?: boolean;
}
export interface RewriteRule { name: string; patternVars: PatternVarDecl[]; lhs: Term; rhs: Term; }
export interface UnificationRule {
    name: string;
    patternVars: PatternVarDecl[];
    lhsPattern1: Term;
    lhsPattern2: Term;
    rhsNewConstraints: Array<{ t1: Term, t2: Term }>;
}
export type Substitution = Map<string, Term>;
export interface Constraint { t1: Term; t2: Term; origin?: string; }
export enum UnifyResult { Solved, Failed, RewrittenByRule, Progress }

export interface ElaborationResult { term: Term; type: Term; } 