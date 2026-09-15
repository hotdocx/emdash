/** Exact active-owner emission shared by native model consumers. */
import { AFFINE_FORMAL_FINITE_MODULE_BINDINGS } from '../src/v3_2/algebra_formal_finite_module';
import { AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS } from '../src/v3_2/algebra_formal_localization_signatures';
import { AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS } from '../src/v3_2/algebra_formal_presentation_morphism';
import { AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_zariski_signatures';
import { FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_spine_signatures';
import { FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_epimorphism_signatures';
import { FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_kernel_choice_provider_signatures';
import { FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_actual_homology_signatures';
import { FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_native_model_observation_signatures';
import { FORMAL_FREYD_RAW_WITNESS_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_raw_witnesses';
import { FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_native_model_signatures';
import { FORMAL_FREYD_NATIVE_CONNECTING_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_native_connecting_signatures';
import { FORMAL_FREYD_NATIVE_EXACTNESS_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_native_exactness_signatures';
import { FORMAL_FREYD_DIAGRAM_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_diagram_signatures';
import { FORMAL_FREYD_EXACTNESS_POINT_SIGNATURE_BINDINGS } from '../src/v3_2/algebra_formal_freyd_exactness_point_signatures';
import { serializeCoreLfKernelProbe } from '../src/v3_2/lf_probe';

export const FREYD_NATIVE_MODEL_PROBE_BINDINGS = Object.freeze({ ...AFFINE_FORMAL_ZARISKI_SIGNATURE_BINDINGS, ...AFFINE_FORMAL_LOCALIZATION_GOAL_BINDINGS,
                ...AFFINE_FORMAL_FINITE_MODULE_BINDINGS, ...AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS,
                ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS,
                ...FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS, ...FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS,
                ...FORMAL_FREYD_RAW_WITNESS_SIGNATURE_BINDINGS, ...FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS,
                ...FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS, ...FORMAL_FREYD_NATIVE_CONNECTING_SIGNATURE_BINDINGS,
                ...FORMAL_FREYD_NATIVE_EXACTNESS_SIGNATURE_BINDINGS, ...FORMAL_FREYD_DIAGRAM_SIGNATURE_BINDINGS,
                ...FORMAL_FREYD_EXACTNESS_POINT_SIGNATURE_BINDINGS });

export const freydNativeModelProbe = (environment: Parameters<typeof serializeCoreLfKernelProbe>[0]['environment'],
    assertions: Parameters<typeof serializeCoreLfKernelProbe>[0]['assertions']) =>
    serializeCoreLfKernelProbe({ environment, externalFreeReferences: FREYD_NATIVE_MODEL_PROBE_BINDINGS, assertions }).source.replace(
        'require open emdash.emdash3_2;',
        'require open emdash.emdash3_2_commutative_algebra_freyd_actual_homology;\n' +
        'require open emdash.emdash3_2_commutative_algebra_freyd_chain_map_introduction;\n' +
        'require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_normality;\n' +
        'require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_arrows;\n' +
        'require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_connecting_observation;\n' +
        'require open emdash.emdash3_2_commutative_algebra_freyd_diagram_observations;\n' +
        'require open emdash.emdash3_2_commutative_algebra_freyd_observation_endpoints;');
