import {
    Term, Context, GlobalDef, RewriteRule, PatternVarDecl, UnificationRule, Constraint, StoredRewriteRule, Icit,
    Type, Var, Lam, App, Pi, Hole, Binding,
    CatTerm, ObjTerm, HomTerm,
    FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm, NatTransComponentTerm, SetTerm, HomCovFunctorIdentity,
    BaseTerm
} from './core_types';

// Global context for definitions and rules
export let globalDefs: Map<string, GlobalDef> = new Map();
export let userRewriteRules: StoredRewriteRule[] = [];
export let userUnificationRules: UnificationRule[] = [];
export let constraints: Constraint[] = [];
export const emptyCtx: Context = [];

export let nextVarId = 0;
export const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarId++}`;

export let nextHoleId = 0;
export const freshHoleName = (): string => `?h${nextHoleId++}`;

export const resetVarId = () => { nextVarId = 0; };
export const resetHoleId = () => { nextHoleId = 0; };

export const FH = (): Term & { tag: 'Hole' } => Hole(freshHoleName());

export function addConstraint(t1: Term, t2: Term, origin?: string) { constraints.push({ t1, t2, origin }); }

export const solveConstraintsControl = { depth: 0 };

export function getTermRef(term: Term): Term {
    let current = term;
    const visited = new Set<Term>();
    while (current.tag === 'Hole' && current.ref) {
        if (visited.has(current)) {
            console.warn(`Cycle detected in Hole references starting from ${term.tag === 'Hole' ? term.id : 'original term'}. Returning current hole: ${current.id}`);
            return current;
        }
        visited.add(current);
        current = current.ref;
    }
    return current;
}

export const extendCtx = (ctx: Context, name: string, type: Term, icit: Icit = Icit.Expl, definition?: Term): Context => {
    return [{ name, type, icit, definition }, ...ctx];
};

export const lookupCtx = (ctx: Context, name: string): Binding | undefined => ctx.find(b => b.name === name);

export const EMDASH_CONSTANT_SYMBOLS_TAGS = new Set<string>(['CatTerm', 'SetTerm']);
export const EMDASH_UNIFICATION_INJECTIVE_TAGS = new Set<string>([
    'CatTerm', 'ObjTerm', 'HomTerm',
    'FunctorCategoryTerm', 'NatTransTypeTerm', 'SetTerm'
]);

export function isKernelConstantSymbolStructurally(term: Term): boolean {
    const t = getTermRef(term);
    if (EMDASH_CONSTANT_SYMBOLS_TAGS.has(t.tag)) return true;
    if (t.tag === 'Var' && globalDefs.get(t.name)?.isConstantSymbol) return true;
    return false;
}

export function isEmdashUnificationInjectiveStructurally(tag: string): boolean {
    return EMDASH_UNIFICATION_INJECTIVE_TAGS.has(tag);
}

let _debug_verbose_flag = false;

export function setDebugVerbose(value: boolean): void {
    _debug_verbose_flag = value;
}

export function getDebugVerbose(): boolean {
    return _debug_verbose_flag;
}

export function consoleLog(message?: any, ...optionalParams: any[]): void {
    if (_debug_verbose_flag) {
        console.log("[VERBOSE]", message, ...optionalParams);
    }
}

export function cloneTerm(term: Term, clonedObjects: Map<Term, Term> = new Map()): Term {
    return term;
    // const current = getTermRef(term);
    // if (clonedObjects.has(current)) {
    //     return clonedObjects.get(current)!;
    // }
    // let cloned: Term;
    // switch (current.tag) {
    //     case 'Type': cloned = Type(); break;
    //     case 'CatTerm': cloned = CatTerm(); break;
    //     case 'SetTerm': cloned = SetTerm(); break;
    //     case 'Var': cloned = Var(current.name, current.isLambdaBound); break;
    //     case 'Hole':
    //         const newHole = Hole(current.id);
    //         clonedObjects.set(current, newHole);
    //         if (current.elaboratedType) {
    //             newHole.elaboratedType = cloneTerm(current.elaboratedType, clonedObjects);
    //         }
    //         cloned = newHole;
    //         break;
    //     case 'App':
    //         cloned = App(cloneTerm(current.func, clonedObjects), cloneTerm(current.arg, clonedObjects), current.icit);
    //         break;
    //     case 'Lam':
    //         if (current._isAnnotated && current.paramType) {
    //             cloned = Lam(current.paramName, current.icit, cloneTerm(current.paramType, clonedObjects), current.body);
    //         } else {
    //             cloned = Lam(current.paramName, current.icit, current.body);
    //         }
    //         break;
    //     case 'Pi':
    //         cloned = Pi(current.paramName, current.icit, cloneTerm(current.paramType, clonedObjects), current.bodyType);
    //         break;
    //     case 'ObjTerm': cloned = ObjTerm(cloneTerm(current.cat, clonedObjects)); break;
    //     case 'HomTerm':
    //         cloned = HomTerm(cloneTerm(current.cat, clonedObjects), cloneTerm(current.dom, clonedObjects), cloneTerm(current.cod, clonedObjects));
    //         break;
    //     case 'FunctorCategoryTerm':
    //         cloned = FunctorCategoryTerm(cloneTerm(current.domainCat, clonedObjects), cloneTerm(current.codomainCat, clonedObjects));
    //         break;
    //     case 'FMap0Term':
    //         cloned = FMap0Term(cloneTerm(current.functor, clonedObjects), cloneTerm(current.objectX, clonedObjects),
    //             current.catA_IMPLICIT ? cloneTerm(current.catA_IMPLICIT, clonedObjects) : undefined,
    //             current.catB_IMPLICIT ? cloneTerm(current.catB_IMPLICIT, clonedObjects) : undefined);
    //         break;
    //     case 'FMap1Term':
    //         cloned = FMap1Term(cloneTerm(current.functor, clonedObjects), cloneTerm(current.morphism_a, clonedObjects),
    //             current.catA_IMPLICIT ? cloneTerm(current.catA_IMPLICIT, clonedObjects) : undefined,
    //             current.catB_IMPLICIT ? cloneTerm(current.catB_IMPLICIT, clonedObjects) : undefined,
    //             current.objX_A_IMPLICIT ? cloneTerm(current.objX_A_IMPLICIT, clonedObjects) : undefined,
    //             current.objY_A_IMPLICIT ? cloneTerm(current.objY_A_IMPLICIT, clonedObjects) : undefined);
    //         break;
    //     case 'NatTransTypeTerm':
    //         cloned = NatTransTypeTerm(cloneTerm(current.catA, clonedObjects), cloneTerm(current.catB, clonedObjects),
    //             cloneTerm(current.functorF, clonedObjects), cloneTerm(current.functorG, clonedObjects));
    //         break;
    //     case 'NatTransComponentTerm':
    //         cloned = NatTransComponentTerm(cloneTerm(current.transformation, clonedObjects), cloneTerm(current.objectX, clonedObjects),
    //             current.catA_IMPLICIT ? cloneTerm(current.catA_IMPLICIT, clonedObjects) : undefined,
    //             current.catB_IMPLICIT ? cloneTerm(current.catB_IMPLICIT, clonedObjects) : undefined,
    //             current.functorF_IMPLICIT ? cloneTerm(current.functorF_IMPLICIT, clonedObjects) : undefined,
    //             current.functorG_IMPLICIT ? cloneTerm(current.functorG_IMPLICIT, clonedObjects) : undefined);
    //         break;
    //     case 'HomCovFunctorIdentity':
    //         cloned = HomCovFunctorIdentity(cloneTerm(current.domainCat, clonedObjects), cloneTerm(current.objW_InDomainCat, clonedObjects));
    //         break;
    //     default:
    //         const exhaustiveCheck: never = current;
    //         throw new Error(`cloneTerm: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    // }
    // clonedObjects.set(current, cloned);
    // return cloned;
}

// Moved from core_elaboration.ts
// MAX_STACK_DEPTH for printTerm, if needed, can be defined here or imported if it's a global constant.
const PRINT_TERM_MAX_STACK_DEPTH = 40; // Localized constant for printTerm

export function printTerm(term: Term, boundVarsMap: Map<string, string> = new Map(), stackDepth = 0): string {
    if (stackDepth > PRINT_TERM_MAX_STACK_DEPTH) return "<print_depth_exceeded>";
    if (!term) return "<null_term>";

    const current = getTermRef(term);

    const getUniqueName = (baseName: string): string => {
        if (!boundVarsMap.has(baseName) && !globalDefs.has(baseName) && !Array.from(boundVarsMap.values()).includes(baseName)) {
            return baseName;
        }
        let uniqueName = baseName;
        let suffix = 1;
        while (globalDefs.has(uniqueName) || Array.from(boundVarsMap.values()).includes(uniqueName) || boundVarsMap.has(uniqueName) ) {
            uniqueName = `${baseName}_${suffix++}`;
            if (suffix > 100) return `${baseName}_too_many`; 
        }
        return uniqueName;
    };

    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return boundVarsMap.get(current.name) || current.name;
        case 'Hole': {
            let typeInfo = "";
            if (current.elaboratedType && getTermRef(current.elaboratedType) !== current) { 
                const elabTypeRef = getTermRef(current.elaboratedType);
                const isSelfRefPrint = (elabTypeRef.tag === 'Hole' && elabTypeRef.id === current.id && elabTypeRef.elaboratedType === current.elaboratedType);
                const isTypeForType = (elabTypeRef.tag === 'Type' && term.tag === 'Type'); 
                
                if (!isSelfRefPrint && !isTypeForType) {
                    const elabTypePrint = printTerm(elabTypeRef, new Map(boundVarsMap), stackDepth + 1);
                     if(!elabTypePrint.startsWith("?h") || elabTypePrint.length > current.id.length + 3 ) { 
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
            const bodyTerm = current.body(Var(current.paramName, true)); 
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
            const bodyTypeTerm = current.bodyType(Var(current.paramName, true)); 
            const binder = current.icit === Icit.Impl ? `{${paramDisplayName} : ${paramTypeStr}}` : `(${paramDisplayName} : ${paramTypeStr})`;
            return `(Π ${binder}. ${printTerm(bodyTypeTerm, newBoundVars, stackDepth + 1)})`;
        }
        case 'CatTerm': return 'Cat';
        case 'ObjTerm': return `(Obj ${printTerm(current.cat, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'HomTerm':
            return `(Hom ${printTerm(current.cat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.dom, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.cod, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'FunctorCategoryTerm':
            return `(Functor ${printTerm(current.domainCat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.codomainCat, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'FMap0Term':
            return `(fmap0 ${printTerm(current.functor, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.objectX, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'FMap1Term':
            return `(fmap1 ${printTerm(current.functor, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.morphism_a, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'NatTransTypeTerm':
            return `(Transf ${printTerm(current.catA, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.catB, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.functorF, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.functorG, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'NatTransComponentTerm':
            return `(tapp ${printTerm(current.transformation, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.objectX, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'HomCovFunctorIdentity':
            return `(HomCovFunctor ${printTerm(current.domainCat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.objW_InDomainCat, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'SetTerm': return 'Set';
        default:
            const exhaustiveCheck: never = current;
            throw new Error(`printTerm: Unhandled term tag: ${(exhaustiveCheck as any).tag}`);
    }
} 