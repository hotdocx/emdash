/** Exact private mirrors of the existing whole P/Q model and its normality. */
import { CoreLfScopedBuilder } from './lf_builder';
import { binderMode, KernelExpression, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { createFormalFreydRawWitnessProofEnvironment } from './algebra_formal_freyd_raw_witnesses';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';

export const FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS = Object.freeze({
    bridge_FreydAdjunctionModel: 'FreydAdjunctionModel',
    bridge_FreydAdjunctionModelNormality: 'FreydAdjunctionModelNormality'
});

export const FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-native-model-signatures-v1' as const,
    policy: 'exact-opaque-signature-mirrors' as const,
    sourceOperations: 'native-whole-adjunction-model' as const,
    suppliesModel: false as const,
    addsCoreOwner: false as const,
    addsRuntimeRule: false as const
});

export function algebraFormalFreydNativeModelType(R: KernelExpression): KernelExpression {
    const b = new CoreLfScopedBuilder(provenance('derived', 'native Freyd adjunction model type'));
    const L = formalFreydSpineLanguage(b);
    return b.lower(L.tau(L.call('bridge_FreydAdjunctionModel', [b.embed(R)])));
}

export function algebraFormalFreydNativeModelNormalityType(R: KernelExpression, M: KernelExpression): KernelExpression {
    const b = new CoreLfScopedBuilder(provenance('derived', 'native Freyd adjunction model normality type'));
    const L = formalFreydSpineLanguage(b);
    return b.lower(L.tau(L.call('bridge_FreydAdjunctionModelNormality', [b.embed(R), b.embed(M)], 1)));
}

/** Raw CAS signatures plus native inputs; no FreydHomologyModel or adapter. */
export function createFormalFreydNativeModelProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydRawWitnessProofEnvironment([]);
    const p = provenance('derived', 'native Freyd adjunction model signatures');
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    const ring = L.tau(b.free('bridge_CommRing'));
    const grpd = () => b.application('groupoid-universe', []);
    environment = environment.extend({ name: 'bridge_FreydAdjunctionModel',
        type: b.lower(b.pi('R', ring, grpd)), mode: binderMode('explicit', 'functorial'), provenance: p });
    environment = environment.extend({ name: 'bridge_FreydAdjunctionModelNormality',
        type: b.lower(b.pi('R', ring, R => b.pi('M', L.tau(L.call('bridge_FreydAdjunctionModel', [R])), grpd),
            binderMode('implicit', 'functorial'))), mode: binderMode('explicit', 'functorial'), provenance: p });
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'native Freyd model input ' + input.name,
                sourceSpan('generated/formal-freyd-native-model-inputs.ts', index + 1, 1)) });
    });
    return environment;
}
