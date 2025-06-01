import { Term, BaseTerm, Hole, Var } from './core_types';
import * as CoreTypes from './core_types'; // Import all as a namespace
import { freshHoleName } from './core_context_globals';

// Define a more precise type for the metadata
// This helps ensure that 'fieldName' is a valid key for T that can hold a Term or undefined.
type ImplicitField<T extends Term> = keyof {
    [K in keyof T as T[K] extends Term | undefined ? K : never]: T[K]
};

export interface KernelImplicitSpec<T extends Term> {
    tag: T['tag']; // This will be the string literal tag like 'IdentityMorph'
    fields: Array<ImplicitField<T>>;
    // Optional: can add custom hole name generator per field or term if needed later
    // holeNameGenerators?: { [F in ImplicitField<T>]?: (term: T) => string };
}

// Use Extract to get the specific type from the BaseTerm union
type IdentityMorphTypeExt = Extract<BaseTerm, { tag: 'IdentityMorph' }>;
type ComposeMorphTypeExt = Extract<BaseTerm, { tag: 'ComposeMorph' }>;

// Array of specs, easier to iterate and type-safe
// We cast to 'any' for the T in KernelImplicitSpec<T> because T varies for each element.
// The internal structure of each spec object will still be type-checked against KernelImplicitSpec<SpecificTerm>.
export const KERNEL_IMPLICIT_SPECS: Array<KernelImplicitSpec<any>> = [
    {
        tag: 'IdentityMorph', // The string tag value
        fields: ['cat_IMPLICIT']
    } as KernelImplicitSpec<IdentityMorphTypeExt>,
    {
        tag: 'ComposeMorph', // The string tag value
        fields: ['cat_IMPLICIT', 'objX_IMPLICIT', 'objY_IMPLICIT', 'objZ_IMPLICIT']
    } as KernelImplicitSpec<ComposeMorphTypeExt> // Explicitly use the type from CoreTypes namespace
    // Add more kernel terms with implicits here as they are defined
];

// This function is now defined in core_elaboration.ts to avoid circular dependencies
// if core_context_globals (which freshHoleName comes from) needed to import this file for some reason.
// It's here for reference during design but will be implemented in core_elaboration.ts.
/*
export function ensureKernelImplicitsPresent(term: Term): Term {
    for (const spec of KERNEL_IMPLICIT_SPECS) {
        if (term.tag === spec.tag) {
            // The cast 'as any' on spec.fields is safe because we've matched term.tag with spec.tag,
            // meaning 'term' is of the type T that spec.fields expects.
            // The 'specificTerm' cast allows dynamic property access.
            const specificTerm = term as Term & { [key: string]: any };
            for (const fieldName of spec.fields as Array<keyof Term>) {
                if (specificTerm[fieldName as string] === undefined) {
                    let baseHint = spec.tag.toLowerCase().replace(/morph|term/g, '');
                    const fieldHint = (fieldName as string).replace('_IMPLICIT', '').toLowerCase();

                    if (spec.tag === 'IdentityMorph') {
                        const idTerm = term as IdentityMorph;
                        if (idTerm.obj) {
                            if (idTerm.obj.tag === 'Var') baseHint += `_${idTerm.obj.name}`;
                            else if (idTerm.obj.tag === 'Hole') baseHint += `_${idTerm.obj.id.replace("?","h")}`;
                        }
                    }
                    // TODO: Could add similar hints for ComposeMorph based on g or f if simple and useful

                    specificTerm[fieldName as string] = Hole(freshHoleName() + `_k_${baseHint}_${fieldHint}`);
                }
            }
            break; // Found the spec for this term tag, no need to check others
        }
    }
    return term;
}
*/ 