/**
 * Dependency-free Core-name contract for the displayed next-Hom foundation.
 *
 * Browser-facing categorical syntax needs these internal owner names, but it
 * must not acquire the transfer module's historical audit/review graph. The
 * transfer linkage consumes this same contract, so this is not a mirror.
 */

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_CORE_NAMES =
Object.freeze({
    identityArrow: 'emdash_v3_2_scale_stress_3a2a_id',
    displayedComposition:
        'emdash_v3_2_displayed_nd_higher_foundation_comp_catd_fapp0',
    oppositeFunctor:
        'emdash_v3_2_displayed_nd_higher_foundation_Op_func',
    displayedOppositeFunctor:
        'emdash_v3_2_displayed_nd_higher_foundation_Op_catd_func',
    internalHom:
        'emdash_v3_2_displayed_nd_higher_foundation_hom_int',
    displayedOpposite:
        'emdash_v3_2_displayed_nd_higher_foundation_Op_catd',
    displayedOppositeAction:
        'emdash_v3_2_displayed_nd_higher_foundation_Op_funcd',
    mixedFunctorFamily:
        'emdash_v3_2_displayed_nd_higher_foundation_Functor_catd_func',
    edgeFamily:
        'emdash_v3_2_displayed_nd_higher_foundation_Edge_catd_func',
    presheafFamily:
        'emdash_v3_2_displayed_nd_higher_foundation_Presheaf_catd_func',
    homPresheafFamily:
        'emdash_v3_2_displayed_nd_higher_foundation_HomPresheaf_catd_func',
    displayedHomTarget:
        'emdash_v3_2_displayed_nd_higher_foundation_Homd_target_catd',
    displayedInternalHom:
        'emdash_v3_2_displayed_nd_higher_foundation_homd_int'
} as const);

export type CoreCategoricalDisplayedNdHigherFoundationSymbolId =
    keyof typeof
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_CORE_NAMES;

export function coreCategoricalDisplayedNdHigherFoundationCoreName(
    id: CoreCategoricalDisplayedNdHigherFoundationSymbolId
): string {
    return CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_CORE_NAMES[id];
}
