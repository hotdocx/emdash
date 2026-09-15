/** Direct native model inputs over the original selected rational CAS data. */
import { affineFormalCommRingType, affineFormalRingElementType } from './algebra_formal_conformance';
import { AlgebraFormalFreydRationalSelectedResult, prepareAlgebraFormalFreydRationalInputs } from './algebra_formal_freyd_rational_preparation';
import { algebraFormalFreydNativeModelType, algebraFormalFreydNativeModelNormalityType } from './algebra_formal_freyd_native_model_signatures';
import { createFormalFreydExactnessPointProofEnvironment } from './algebra_formal_freyd_exactness_point_signatures';
import { createAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';

export const ALGEBRA_FORMAL_FREYD_NATIVE_RATIONAL_CONTEXT_PROFILE = Object.freeze({
    revision: 'emdash-formal-native-rational-freyd-context-v7' as const,
    backend: 'rational-polynomial-freyd' as const,
    modelInterface: 'supplied-whole-adjunction-model-and-native-normality' as const,
    coefficientNames: 'canonical-rational-codepoints' as const,
    environment: 'sealed-after-all-existing-preparations' as const,
    constructsModel: false as const,
    adoptsClaims: false as const,
    replaysWholeHomology: false as const,
    reselectsUniversals: false as const,
    requiresLegacyModel: false as const,
    nativeHomologyObservations: true as const,
    nativeCompleteArrowObservations: true as const,
    nativeWholeConnectingObservation: true as const,
    nativeCategoricalExactnessEvidence: true as const,
    nativeFiniteDiagramPath: true as const,
    nativeExactnessPointObservations: true as const,
    requiresNativeRowInterpretations: true as const,
    suppliesOutputExactness: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

export interface AlgebraFormalFreydNativeRationalBackendInput {
    readonly id: string;
    readonly revision: string;
    /** Interpretation of the formal ring, generators and coefficient references. */
    readonly coefficientContract: string;
    /** Coherent native whole P/Q semantics; not an old selected-dictionary model. */
    readonly adjunctionModelContract: string;
    /** Whole Coim⇒Im normality of that same native model. */
    readonly nativeNormalityContract: string;
}

const backends = new WeakSet<object>();
const portableText = (value: string, label: string): string => {
    if (typeof value !== 'string' || value.trim().length === 0 || value.length > 4096 ||
        /[\u0000-\u001f\u007f]/u.test(value)) {
        throw new Error('A nonempty portable ' + label + ' is required');
    }
    return value;
};

/** Record a distinct native input contract; registration is not its proof. */
export function defineAlgebraFormalFreydNativeRationalBackend(input: AlgebraFormalFreydNativeRationalBackendInput) {
    const id = portableText(input.id, 'backend ID');
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(id)) throw new Error('A stable rational Freyd backend ID is required');
    const backend = Object.freeze({
        profileRevision: ALGEBRA_FORMAL_FREYD_NATIVE_RATIONAL_CONTEXT_PROFILE.revision,
        id, revision: portableText(input.revision, 'backend revision'),
        coefficientContract: portableText(input.coefficientContract, 'coefficient contract'),
        adjunctionModelContract: portableText(input.adjunctionModelContract, 'native whole adjunction model contract'),
        nativeNormalityContract: portableText(input.nativeNormalityContract, 'native whole normality contract')
    });
    backends.add(backend);
    return backend;
}

export type AlgebraFormalFreydNativeRationalBackend = ReturnType<typeof defineAlgebraFormalFreydNativeRationalBackend>;

/**
 * Prepare native M:FreydAdjunctionModel(R) and N:FreydAdjunctionModelNormality(M).
 * M/N are supplied inputs, while matrices and selected results remain the original
 * CAS data. Model-specific realization of H/maps/δ and row hypotheses is separate;
 * this context neither assumes output exactness nor declares that realization.
 */
export function prepareAlgebraFormalFreydNativeRationalModelContext(input: {
    readonly backend: AlgebraFormalFreydNativeRationalBackend;
    readonly selected: AlgebraFormalFreydRationalSelectedResult;
    readonly namePrefix: string;
    readonly moduleId?: string;
    readonly sourceId?: string;
    readonly anchorId?: string;
}) {
    if (!backends.has(input.backend)) throw new Error('Use an issued native rational Freyd backend registration');
    const prepared = prepareAlgebraFormalFreydRationalInputs(input);
    const { formalRing, generatorTerms, formalModel, normality, coefficients } = prepared;
    const element = affineFormalRingElementType(formalRing);
    const modelType = algebraFormalFreydNativeModelType(formalRing);
    const normalityType = algebraFormalFreydNativeModelNormalityType(formalRing, formalModel);
    const environment = createFormalFreydExactnessPointProofEnvironment([
        { name: formalRing.name, type: affineFormalCommRingType() },
        ...generatorTerms.map(term => ({ name: term.name, type: element })),
        ...coefficients.map(({ term }) => ({ name: term.name, type: element })),
        { name: formalModel.name, type: modelType },
        { name: normality.name, type: normalityType }
    ]);
    const initialSource = createAlgebraFormalAssumptionSource({
        moduleId: input.moduleId ?? 'proof.cas.' + input.namePrefix,
        sourceId: input.sourceId ?? 'generated/' + input.namePrefix + '.assumptions',
        baseEnvironment: environment
    });
    const suppliedInputs = Object.freeze([
        Object.freeze({ role: 'coefficient-interpretation' as const, classification: 'supplied-input' as const,
            contract: input.backend.coefficientContract,
            references: Object.freeze([formalRing, ...generatorTerms, ...coefficients.map(c => c.term)]) }),
        Object.freeze({ role: 'whole-adjunction-model' as const, classification: 'supplied-input' as const,
            contract: input.backend.adjunctionModelContract, reference: formalModel, type: modelType }),
        Object.freeze({ role: 'native-whole-normality' as const, classification: 'supplied-input' as const,
            contract: input.backend.nativeNormalityContract, reference: normality, type: normalityType })
    ]);
    return Object.freeze({ profile: ALGEBRA_FORMAL_FREYD_NATIVE_RATIONAL_CONTEXT_PROFILE,
        backend: input.backend, selected: input.selected, ...prepared, environment, initialSource, suppliedInputs });
}
