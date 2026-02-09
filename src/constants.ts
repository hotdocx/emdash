/**
 * @file constants.ts
 * @description Shared constants for logic operations. Defines metadata for kernel terms that have implicit arguments.
 * This metadata is used during elaboration to ensure these implicits are present,
 * often by inserting holes if they are missing.
 */
import { Term, BaseTerm, Hole } from './types';
import { freshHoleName } from './state'; // Import freshHoleName from state.ts

export const MAX_STACK_DEPTH = 20000; 

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
type TApp1FApp0TermTypeExt = Extract<BaseTerm, { tag: 'TApp1FApp0Term' }>;
type FDApp1TermTypeExt = Extract<BaseTerm, { tag: 'FDApp1Term' }>;
type TDApp1TermTypeExt = Extract<BaseTerm, { tag: 'TDApp1Term' }>;

// Array of specs, easier to iterate and type-safe
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
    } as KernelImplicitSpec<NatTransComponentTermTypeExt>,
    {
        tag: 'TApp1FApp0Term',
        fields: ['catA_IMPLICIT', 'catB_IMPLICIT', 'functorF_IMPLICIT', 'functorG_IMPLICIT', 'objX_A_IMPLICIT', 'objY_A_IMPLICIT']
    } as KernelImplicitSpec<TApp1FApp0TermTypeExt>,
    {
        tag: 'FDApp1Term',
        fields: ['catZ_IMPLICIT', 'catdE_IMPLICIT', 'catdD_IMPLICIT', 'objZ_IMPLICIT', 'objE_IMPLICIT', 'objZPrime_IMPLICIT', 'homF_IMPLICIT', 'objEPrime_IMPLICIT']
    } as KernelImplicitSpec<FDApp1TermTypeExt>,
    {
        tag: 'TDApp1Term',
        fields: ['catZ_IMPLICIT', 'catdE_IMPLICIT', 'catdD_IMPLICIT', 'functorFF_IMPLICIT', 'functorGG_IMPLICIT', 'objZ_IMPLICIT', 'objE_IMPLICIT', 'objZPrime_IMPLICIT', 'homF_IMPLICIT', 'objEPrime_IMPLICIT']
    } as KernelImplicitSpec<TDApp1TermTypeExt>
];
