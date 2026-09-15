/** Mechanical preparation of one retained result under a supplied model contract. */
import { affineFormalCommRingType, affineFormalRingElementType } from './algebra_formal_conformance';
import { createFormalFreydLongExactModelProofEnvironment } from './algebra_formal_freyd_long_exact_model_preparation';
import { AlgebraFormalFreydRationalSelectedResult, prepareAlgebraFormalFreydRationalInputs } from './algebra_formal_freyd_rational_preparation';
import { algebraFormalFreydModelType } from './algebra_formal_freyd_model_signatures';
import { algebraFormalFreydModelNormalityType } from './algebra_formal_freyd_model_connecting_signatures';
import { createAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';

export type { AlgebraFormalFreydRationalSelectedResult } from './algebra_formal_freyd_rational_preparation';

export const ALGEBRA_FORMAL_FREYD_RATIONAL_CONTEXT_PROFILE = Object.freeze({
    revision: 'emdash-formal-retained-rational-freyd-context-v2' as const,
    backend: 'rational-polynomial-freyd' as const,
    modelInterface: 'supplied-retained-model-and-native-whole-normality' as const,
    coefficientNames: 'canonical-rational-codepoints' as const,
    environment: 'sealed-after-all-existing-preparations' as const,
    constructsModel: false as const,
    adoptsClaims: false as const,
    replaysWholeHomology: false as const,
    reselectsUniversals: false as const,
    nativeWholeConnectingObservation: true as const,
    requiresNativeRowInterpretations: true as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

export interface AlgebraFormalFreydRationalBackendInput {
    readonly id: string;
    readonly revision: string;
    /** Interpretation of the formal ring, generators and coefficient references. */
    readonly coefficientContract: string;
    /** Coherent model semantics; this text is not a derived model inhabitant. */
    readonly modelContract: string;
    /** Native whole Coim⇒Im normality of the same model's P/Q adapter. */
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

/** Register a supported interpretation contract, without declaring or adopting a proof. */
export function defineAlgebraFormalFreydRationalBackend(input: AlgebraFormalFreydRationalBackendInput) {
    const id = portableText(input.id, 'backend ID');
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(id)) throw new Error('A stable rational Freyd backend ID is required');
    const backend = Object.freeze({
        profileRevision: ALGEBRA_FORMAL_FREYD_RATIONAL_CONTEXT_PROFILE.revision,
        id, revision: portableText(input.revision, 'backend revision'),
        coefficientContract: portableText(input.coefficientContract, 'coefficient contract'),
        modelContract: portableText(input.modelContract, 'coherent model contract'),
        nativeNormalityContract: portableText(input.nativeNormalityContract, 'native whole normality contract')
    });
    backends.add(backend);
    return backend;
}

export type AlgebraFormalFreydRationalBackend = ReturnType<typeof defineAlgebraFormalFreydRationalBackend>;

/**
 * Prepare existing inventories and all their free inputs before fixing the environment.
 * Model and native whole normality references remain supplied assumptions. The
 * prepared workflow observes whole δ through the original retained H comparisons;
 * native row interpretations are adopted separately by its explicit trust workflow.
 */
export function prepareAlgebraFormalFreydRationalModelContext(input: {
    readonly backend: AlgebraFormalFreydRationalBackend;
    readonly selected: AlgebraFormalFreydRationalSelectedResult;
    readonly namePrefix: string;
    readonly moduleId?: string;
    readonly sourceId?: string;
    readonly anchorId?: string;
}) {
    if (!backends.has(input.backend)) throw new Error('Use an issued rational Freyd backend registration');
    const { formalRing, generatorTerms, formalModel, normality, coefficients,
        reifier, bundle, preparedHomology, preparedRaw, preparedModel } = prepareAlgebraFormalFreydRationalInputs(input);
    const prefix = input.namePrefix;
    const element = affineFormalRingElementType(formalRing);
    const modelType = algebraFormalFreydModelType(formalRing);
    const normalityType = algebraFormalFreydModelNormalityType(formalRing, formalModel);
    const environment = createFormalFreydLongExactModelProofEnvironment([
        { name: formalRing.name, type: affineFormalCommRingType() },
        ...generatorTerms.map(term => ({ name: term.name, type: element })),
        ...coefficients.map(({ term }) => ({ name: term.name, type: element })),
        { name: formalModel.name, type: modelType },
        { name: normality.name, type: normalityType }
    ]);
    const initialSource = createAlgebraFormalAssumptionSource({
        moduleId: input.moduleId ?? 'proof.cas.' + prefix,
        sourceId: input.sourceId ?? 'generated/' + prefix + '.assumptions',
        baseEnvironment: environment
    });
    const suppliedInputs = Object.freeze([
        Object.freeze({ role: 'coefficient-interpretation' as const, classification: 'supplied-input' as const,
            contract: input.backend.coefficientContract,
            references: Object.freeze([formalRing, ...generatorTerms, ...coefficients.map(c => c.term)]) }),
        Object.freeze({ role: 'coherent-model' as const, classification: 'supplied-input' as const,
            contract: input.backend.modelContract, reference: formalModel, type: modelType }),
        Object.freeze({ role: 'native-whole-normality' as const, classification: 'supplied-input' as const,
            contract: input.backend.nativeNormalityContract, reference: normality, type: normalityType })
    ]);
    return Object.freeze({
        profile: ALGEBRA_FORMAL_FREYD_RATIONAL_CONTEXT_PROFILE, backend: input.backend,
        selected: input.selected, formalRing, generatorTerms, coefficients, formalModel, normality,
        reifier, bundle, preparedHomology, preparedRaw, preparedModel, environment, initialSource, suppliedInputs
    });
}
