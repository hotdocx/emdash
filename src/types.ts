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