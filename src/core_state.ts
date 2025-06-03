import {
    Term, Context, GlobalDef, RewriteRule, PatternVarDecl, UnificationRule, Constraint, StoredRewriteRule, Icit,
    Type, Var, Lam, App, Pi, Hole, Binding,
    CatTerm, ObjTerm, HomTerm,
    FunctorCategoryTerm, FMap0Term, FMap1Term, NatTransTypeTerm, NatTransComponentTerm, SetTerm, HomCovFunctorIdentity,
    BaseTerm, FunctorTypeTerm
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
    'FunctorCategoryTerm', 'NatTransTypeTerm', 'SetTerm',
    'FunctorTypeTerm'
]);

export function isKernelConstantSymbolStructurally(term: Term): boolean {
    const rt = getTermRef(term);
    if (rt.tag === 'Var') {
        const gdef = globalDefs.get(rt.name);
        return !!(gdef && gdef.isConstantSymbol); // True if it's a Var defined as a constant
    }

    // For other term tags, decide if they should bypass rewrite rules.
    // ObjTerm and HomTerm should NOT bypass, so they are NOT listed here.
    // Other structural terms might still be shielded.
    switch (rt.tag) {
        case 'CatTerm':
        case 'FunctorCategoryTerm':
        case 'NatTransTypeTerm':
        case 'HomCovFunctorIdentity':
        case 'SetTerm':
        case 'FunctorTypeTerm':
            // These are structural and typically shouldn't be rewritten *as a whole* by general rules.
            return true;
        case 'FMap0Term':
        case 'FMap1Term':
        case 'NatTransComponentTerm':
        case 'ObjTerm':
        case 'HomTerm':
            // These should allow rewrite rules like Obj_mkCat_eval and Hom_mkCat_eval.
            return false;
        case 'Type': // Type itself is a primitive, doesn't get rewritten.
            return true;
        // Lam, App, Pi, Hole are generally not considered "kernel constants" in this sense.
        // They are either reducible or placeholders.
        default:
            // For any tag not explicitly listed as true, assume false.
            // This includes Lam, App, Pi, Hole, and any future tags not covered.
            return false;
    }
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

// [TODO] delete this function
export function cloneTerm(term: Term, clonedObjects: Map<Term, Term> = new Map()): Term {
    return term;

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
        case 'FunctorTypeTerm':
            return `(FunctorType ${printTerm(current.domainCat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.codomainCat, new Map(boundVarsMap), stackDepth + 1)})`;
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