/**
 * @file kernel_metadata.ts
 *
 * Defines metadata for kernel terms, specifically for managing their implicit arguments.
 * This information is used during elaboration to ensure kernel terms are fully instantiated.
 */

import { Term, BaseTerm, Hole } from './types';
import { freshHoleName } from './state'; // For default hole name generation if needed by ensureKernelImplicitsPresent

// Define a more precise type for the metadata
// This helps ensure that 'fieldName' is a valid key for T that can hold a Term or undefined.
type ImplicitField<T extends Term> = keyof {
    [K in keyof T as T[K] extends Term | undefined ? K : never]: T[K]
};

export interface KernelImplicitSpec<T extends Term> {
    tag: T['tag']; // This will be the string literal tag like 'FMap0Term'
    fields: Array<ImplicitField<T>>;
    // Optional: can add custom hole name generator per field or term if needed later
    // holeNameGenerators?: { [F in ImplicitField<T>]?: (term: T) => string };
}

// Use Extract to get the specific type from the BaseTerm union
type FMap0TermTypeExt = Extract<BaseTerm, { tag: 'FMap0Term' }>;
type FMap1TermTypeExt = Extract<BaseTerm, { tag: 'FMap1Term' }>;
type NatTransComponentTermTypeExt = Extract<BaseTerm, { tag: 'NatTransComponentTerm' }>;
// Add more Extractions here for other terms with implicit fields as they are defined.
// Example: type IdentityMorphTypeExt = Extract<BaseTerm, { tag: 'IdentityMorph' }>;

// Array of specifications for kernel terms that have implicit arguments.
// This array is iterated by `ensureKernelImplicitsPresent` in elaboration.ts.
// We cast to 'any' for the T in KernelImplicitSpec<T> because T varies for each element.
// The internal structure of each spec object will still be type-checked against KernelImplicitSpec<SpecificTerm>.
export const KERNEL_IMPLICIT_SPECS: Array<KernelImplicitSpec<any>> = [
    {
        tag: 'FMap0Term',
        fields: ['catA_IMPLICIT', 'catB_IMPLICIT']
    } as KernelImplicitSpec<FMap0TermTypeExt>,
    {
        tag: 'FMap1Term',
        fields: ['catA_IMPLICIT', 'catB_IMPLICIT', 'objX_A_IMPLICIT', 'objY_A_IMPLICIT']
    } as KernelImplicitSpec<FMap1TermTypeExt>,
    {
        tag: 'NatTransComponentTerm',
        fields: ['catA_IMPLICIT', 'catB_IMPLICIT', 'functorF_IMPLICIT', 'functorG_IMPLICIT']
    } as KernelImplicitSpec<NatTransComponentTermTypeExt>
    // Example for a hypothetical IdentityMorph with an implicit category argument:
    // {
    //     tag: 'IdentityMorph',
    //     fields: ['cat_IMPLICIT']
    // } as KernelImplicitSpec<IdentityMorphTypeExt>,
];

/*
Note: The `ensureKernelImplicitsPresent` function itself is located in `elaboration.ts`.
It uses `KERNEL_IMPLICIT_SPECS` from this file to fill in missing implicit arguments
on kernel terms with fresh holes during the elaboration process.
This separation is to avoid circular dependencies, as `elaboration.ts` is a consumer
of this metadata, and this metadata file should be simple and have few dependencies.
*/