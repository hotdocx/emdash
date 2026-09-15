/** Exact private mirrors of direct native row contracts and whole-δ observation. */
import { KernelExpression } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { createFormalFreydNativeModelObservationProofEnvironment } from './algebra_formal_freyd_native_model_observation_signatures';
import { extendFormalFreydConnectingSignatures, formalFreydConnectingObservationTerm } from './algebra_formal_freyd_model_connecting_signatures';

export const FORMAL_FREYD_NATIVE_CONNECTING_SIGNATURE_BINDINGS = Object.freeze({
    bridge_FreydAdjunctionModelRowShortExact: 'FreydAdjunctionModelRowShortExact',
    bridge_freyd_adjunction_model_connecting_observation: 'freyd_adjunction_model_connecting_observation'
});

export function algebraFormalFreydNativeConnectingObservationTerm(values: Readonly<Record<string, KernelExpression>>) {
    return formalFreydConnectingObservationTerm(values, 'bridge_freyd_adjunction_model_connecting_observation');
}

export function createFormalFreydNativeConnectingProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    return extendFormalFreydConnectingSignatures(createFormalFreydNativeModelObservationProofEnvironment([]), inputs, {
        model: 'bridge_FreydAdjunctionModel', normality: 'bridge_FreydAdjunctionModelNormality',
        shortExact: 'bridge_FreydAdjunctionModelRowShortExact',
        observation: 'bridge_freyd_adjunction_model_connecting_observation', declareNormality: false
    });
}
