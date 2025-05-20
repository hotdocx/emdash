import { Term, freshHoleName } from './globals_and_rules'; // Adjusted path, will create this file next

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