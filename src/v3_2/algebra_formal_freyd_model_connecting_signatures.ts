/** Legacy selected-model signatures; shared window templates have their own owner. */
import { CoreLfScopedBuilder } from './lf_builder';
import { binderMode, KernelExpression, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { createFormalFreydModelMapProofEnvironment, FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS } from './algebra_formal_freyd_model_map_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { extendFormalFreydConnectingSignatures, formalFreydConnectingObservationTerm } from './algebra_formal_freyd_window_signatures';
import { createFormalFreydRawWitnessProofEnvironment } from './algebra_formal_freyd_raw_witnesses';
import { FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS } from './algebra_formal_freyd_model_signatures';

export { FREYD_MODEL_CONNECTING_ARGUMENTS, formalFreydConnectingObservationTerm,
    extendFormalFreydConnectingSignatures, FormalFreydWindowScope, FormalFreydWindowField,
    formalFreydWindowFields } from './algebra_formal_freyd_window_signatures';

export const FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS = Object.freeze({
    bridge_FreydHomologyModelNativeNormality: 'FreydHomologyModelNativeNormality',
    bridge_FreydHomologyModelNativeShortExact: 'FreydHomologyModelNativeShortExact',
    bridge_freyd_homology_model_native_connecting_observation: 'freyd_homology_model_native_connecting_observation'
});

export const FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-model-connecting-signatures-v2' as const,
    policy: 'exact-opaque-signature-mirrors' as const,
    sourceOperations: 'native-whole-delta-at-retained-H-endpoints' as const,
    requiresSuppliedNormality: true as const,
    normality: 'native-whole-Coim-Im' as const,
    rowUniversality: 'native-whole-PQ' as const,
    requiresModelShortExactness: true as const,
    constructsModel: false as const,
    infersClosedCapabilityFromRawAgreements: false as const,
    addsCoreOwner: false as const,
    addsRuntimeRule: false as const
});

export function algebraFormalFreydModelNormalityType(R: KernelExpression, M: KernelExpression): KernelExpression {
    const b = new CoreLfScopedBuilder(provenance('derived', 'supplied native whole model normality'));
    const L = formalFreydSpineLanguage(b);
    return b.lower(L.tau(L.call('bridge_FreydHomologyModelNativeNormality', [b.embed(R), b.embed(M)], 1)));
}

export function algebraFormalFreydModelConnectingObservationTerm(
    values: Readonly<Record<string, KernelExpression>>
): KernelExpression {
    return formalFreydConnectingObservationTerm(values, 'bridge_freyd_homology_model_native_connecting_observation');
}

export function createFormalFreydModelConnectingProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    return extendFormalFreydConnectingSignatures(createFormalFreydModelMapProofEnvironment([]), inputs, {
        model: 'bridge_FreydHomologyModel', normality: 'bridge_FreydHomologyModelNativeNormality',
        shortExact: 'bridge_FreydHomologyModelNativeShortExact',
        observation: 'bridge_freyd_homology_model_native_connecting_observation', declareNormality: true
    });
}

/** Compose the existing private mirrors; introduce no new mathematical signature. */
export function createFormalFreydLongExactModelProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydRawWitnessProofEnvironment([]);
    const models = createFormalFreydModelConnectingProofEnvironment([]);
    for (const name of Object.keys({ ...FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS,
        ...FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS })) {
        environment = environment.extend(models.lookup(name)!);
    }
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'bounded model input ' + input.name,
                sourceSpan('generated/bounded-model-inputs.ts', index + 1, 1)) });
    });
    return environment;
}
