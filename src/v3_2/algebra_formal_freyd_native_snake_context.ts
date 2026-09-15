/** Standalone rational snake context over supplied native P/Q; no LES fixture is required. */
import { AlgebraRational, AlgebraRationalField, AlgebraRationalInput } from './algebra_exact';
import { AlgebraPolynomialFreydSnakeExactSequence } from './algebra_polynomial_freyd_snake_exact';
import { affineFormalCommRingType, affineFormalRingElementType } from './algebra_formal_conformance';
import { prepareAlgebraFormalFreydRationalInventory } from './algebra_formal_freyd_rational_preparation';
import { AlgebraFormalFreydNativeRationalBackend, assertAlgebraFormalFreydNativeRationalBackend } from './algebra_formal_freyd_native_rational_model_context';
import { prepareAlgebraFormalFreydNativeSnake } from './algebra_formal_freyd_native_snake_preparation';
import { createFormalFreydNativeSnakeCertificateProofEnvironment } from './algebra_formal_freyd_native_snake_certificate_signatures';
import { algebraFormalFreydNativeModelType, algebraFormalFreydNativeModelNormalityType } from './algebra_formal_freyd_native_model_signatures';
import { createAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';

export const ALGEBRA_FORMAL_FREYD_NATIVE_SNAKE_CONTEXT_PROFILE = Object.freeze({
    revision: 'emdash-formal-native-rational-snake-context-v4' as const,
    requiresLegacyModel: false as const, requiresLongExactInput: false as const,
    constructsModel: false as const, adoptsClaims: false as const,
    reselectsUniversals: false as const, suppliesOutputExactness: false as const,
    nativeExactnessConstructors: true as const,
    nativeDiagramPaths: true as const,
    nativeIndexedExactnessCertificates: true as const,
    addsCoreOwner: false as const, performsIo: false as const
});

export function prepareAlgebraFormalFreydNativeRationalSnakeContext(input: {
    readonly backend: AlgebraFormalFreydNativeRationalBackend;
    readonly selected: AlgebraPolynomialFreydSnakeExactSequence<AlgebraRationalField, AlgebraRational, AlgebraRationalInput>;
    readonly namePrefix: string;
    readonly moduleId?: string;
    readonly sourceId?: string;
}) {
    assertAlgebraFormalFreydNativeRationalBackend(input.backend);
    const { inventory: prepared, ...context } = prepareAlgebraFormalFreydRationalInventory({
        ...input, ring: input.selected.connecting.triple.delta.source.ambient.ring,
        prepare: reifier => prepareAlgebraFormalFreydNativeSnake({ reifier, selected: input.selected })
    });
    const { formalRing, formalModel, normality, generatorTerms, coefficients } = context;
    const element = affineFormalRingElementType(formalRing);
    const modelType = algebraFormalFreydNativeModelType(formalRing);
    const normalityType = algebraFormalFreydNativeModelNormalityType(formalRing, formalModel);
    const environment = createFormalFreydNativeSnakeCertificateProofEnvironment([
        { name: formalRing.name, type: affineFormalCommRingType() },
        ...generatorTerms.map(term => ({ name: term.name, type: element })),
        ...coefficients.map(({ term }) => ({ name: term.name, type: element })),
        { name: formalModel.name, type: modelType }, { name: normality.name, type: normalityType }
    ]);
    const initialSource = createAlgebraFormalAssumptionSource({ moduleId: input.moduleId ?? 'proof.cas.' + input.namePrefix,
        sourceId: input.sourceId ?? 'generated/' + input.namePrefix + '.assumptions', baseEnvironment: environment });
    const suppliedInputs = Object.freeze([
        Object.freeze({ role: 'coefficient-interpretation' as const, classification: 'supplied-input' as const,
            contract: input.backend.coefficientContract, references: Object.freeze([formalRing, ...generatorTerms, ...coefficients.map(c => c.term)]) }),
        Object.freeze({ role: 'whole-adjunction-model' as const, classification: 'supplied-input' as const,
            contract: input.backend.adjunctionModelContract, reference: formalModel, type: modelType }),
        Object.freeze({ role: 'native-whole-normality' as const, classification: 'supplied-input' as const,
            contract: input.backend.nativeNormalityContract, reference: normality, type: normalityType })
    ]);
    return Object.freeze({ profile: ALGEBRA_FORMAL_FREYD_NATIVE_SNAKE_CONTEXT_PROFILE, backend: input.backend,
        selected: input.selected, ...context, prepared, environment, initialSource, suppliedInputs });
}
