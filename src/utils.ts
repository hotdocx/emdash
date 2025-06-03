/**
 * @file utils.ts
 *
 * Contains utility functions for the Emdash system, such as pretty-printing terms
 * and conditional logging.
 */

import { Term, Icit, Var, Hole } from './types';
import { getTermRef, globalDefs, getDebugVerbose } from './state';

/**
 * Maximum stack depth for the `printTerm` function to prevent excessively long outputs
 * or stack overflows for very complex/cyclic terms.
 */
const PRINT_TERM_MAX_STACK_DEPTH = 40;

/**
 * Pretty-prints a term for display.
 * @param term The term to print.
 * @param boundVarsMap A map to track bound variable names and ensure uniqueness.
 * @param stackDepth Current recursion depth for printing.
 * @returns A string representation of the term.
 */
export function printTerm(term: Term, boundVarsMap: Map<string, string> = new Map(), stackDepth = 0): string {
    if (stackDepth > PRINT_TERM_MAX_STACK_DEPTH) return "<print_depth_exceeded>";
    if (!term) return "<null_term>";

    const current = getTermRef(term);

    // Helper to generate unique display names for bound variables
    const getUniqueName = (baseName: string): string => {
        if (!boundVarsMap.has(baseName) && !globalDefs.has(baseName) && !Array.from(boundVarsMap.values()).includes(baseName)) {
            return baseName;
        }
        let uniqueName = baseName;
        let suffix = 1;
        // Avoid clashes with existing bound variables in the map (values) or new ones being introduced (keys), and globals
        while (globalDefs.has(uniqueName) || Array.from(boundVarsMap.values()).includes(uniqueName) || (boundVarsMap.has(uniqueName) && boundVarsMap.get(uniqueName) !== uniqueName) ) {
            uniqueName = `${baseName}_${suffix++}`;
            if (suffix > 100) return `${baseName}_too_many`; // Safety break
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
                // Avoid printing self-referential type or Type : Type for a hole of type Type
                const isSelfRefPrint = (elabTypeRef.tag === 'Hole' && elabTypeRef.id === current.id && elabTypeRef.elaboratedType === current.elaboratedType);
                const isTypeForHoleOfTypeType = (elabTypeRef.tag === 'Type' && current.elaboratedType && getTermRef(current.elaboratedType).tag === 'Type');

                if (!isSelfRefPrint && !isTypeForHoleOfTypeType) {
                    const elabTypePrint = printTerm(elabTypeRef, new Map(boundVarsMap), stackDepth + 1);
                    // Only add type info if it's informative (not just another hole name of similar length)
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
            newBoundVars.set(current.paramName, paramDisplayName); // Map original name to display name

            const typeAnnotation = (current._isAnnotated && current.paramType)
                ? ` : ${printTerm(current.paramType, new Map(boundVarsMap), stackDepth + 1)}` // Use original boundVarsMap for type
                : '';
            // Instantiate body with a Var that refers to the original paramName for consistent substitution
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

            const paramTypeStr = printTerm(current.paramType, new Map(boundVarsMap), stackDepth + 1); // Use original boundVarsMap for type
            // Instantiate bodyType with a Var that refers to the original paramName
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

/**
 * Logs messages to the console if verbose debugging is enabled.
 * @param message The primary message to log.
 * @param optionalParams Additional parameters to log.
 */
export function consoleLog(message?: any, ...optionalParams: any[]): void {
    if (getDebugVerbose()) {
        console.log("[VERBOSE]", message, ...optionalParams);
    }
}