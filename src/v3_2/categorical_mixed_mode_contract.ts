/**
 * Dependency-free Core-name contract for the mixed classifier families.
 *
 * The categorical surface recognizes these internal owners without importing
 * the transfer module's audit/proposal closure. The transfer linkage consumes
 * and re-exports this same contract.
 */

export const CORE_CATEGORICAL_MIXED_MODE_CORE_NAMES = Object.freeze({
    displayedHomFamily: 'emdash_v3_2_mixed_nest_0a_Hom_catd',
    displayedTransforFamily: 'emdash_v3_2_mixed_nest_0a_Transf_catd'
} as const);

export type CoreCategoricalMixedModeSymbolId =
    keyof typeof CORE_CATEGORICAL_MIXED_MODE_CORE_NAMES;

export function coreCategoricalMixedModeCoreName(
    id: CoreCategoricalMixedModeSymbolId
): string {
    return CORE_CATEGORICAL_MIXED_MODE_CORE_NAMES[id];
}
