/** Mechanical preparation of one retained result under a supplied model contract. */
import { AlgebraRational, AlgebraRationalField, AlgebraRationalInput, RATIONAL_DOMAIN } from './algebra_exact';
import { algebraPolynomialIdeal } from './algebra_ideal';
import { algebraPolynomialQuotientRing } from './algebra_quotient';
import { algebraPresentedAlgebra } from './algebra_presented_algebra';
import { defineAffineFormalPolynomialReifier } from './algebra_formal_reifier';
import { affineFormalCommRingType, affineFormalRingElementType } from './algebra_formal_conformance';
import { AlgebraPolynomialFreydLongExactSnakeReferences } from './algebra_polynomial_freyd_long_exact_reference_operations';
import { algebraFormalFreydLongExactDelegationBundle } from './algebra_formal_freyd_long_exact';
import { prepareAlgebraFormalFreydLongExactHomology } from './algebra_formal_freyd_long_exact_homology';
import { prepareAlgebraFormalFreydRawWitnesses } from './algebra_formal_freyd_raw_witnesses';
import { createFormalFreydLongExactModelProofEnvironment, prepareAlgebraFormalFreydLongExactModel } from './algebra_formal_freyd_long_exact_model_preparation';
import { algebraFormalFreydModelType } from './algebra_formal_freyd_model_signatures';
import { algebraFormalFreydModelNormalityType } from './algebra_formal_freyd_model_connecting_signatures';
import { createAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { kernelFree, provenance, sourceSpan } from './kernel';

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
export type AlgebraFormalFreydRationalSelectedResult = AlgebraPolynomialFreydLongExactSnakeReferences<
    AlgebraRationalField, AlgebraRational, AlgebraRationalInput>;

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
    if (typeof input.namePrefix !== 'string' || !/^[A-Za-z][A-Za-z0-9_]{0,127}$/u.test(input.namePrefix)) {
        throw new Error('A simple identifier of at most 128 characters is required for the model name prefix');
    }
    const ring = input.selected.result.sequence.ring;
    if (ring.coefficientDomain !== RATIONAL_DOMAIN) {
        throw new Error('This model context supports the registered rational polynomial coefficient domain only');
    }
    const prefix = input.namePrefix;
    const p = provenance('surface', 'supplied rational Freyd context ' + input.backend.id + '@' + input.backend.revision,
        sourceSpan('generated/' + prefix + '-model-inputs.ts', 1, 1));
    const formalRing = kernelFree(prefix + '_R', p);
    const generatorTerms = Object.freeze(ring.variables.map((_, i) => kernelFree(prefix + '_g_' + i, p)));
    const formalModel = kernelFree(prefix + '_model', p);
    const normality = kernelFree(prefix + '_normality', p);
    const coefficientTerms = new Map<string, ReturnType<typeof kernelFree>>();
    let sealed = false;
    const reifier = defineAffineFormalPolynomialReifier({
        algebra: algebraPresentedAlgebra(algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))),
        formalRing, generatorTerms,
        coefficientReifier: coefficient => {
            const key = RATIONAL_DOMAIN.text(coefficient);
            const previous = coefficientTerms.get(key);
            if (previous) return previous;
            if (sealed) throw new Error('Rational coefficient ' + key + ' was not included in this prepared model context');
            const encoded = [...key].map(c => c.codePointAt(0)!.toString(16)).join('_');
            const term = kernelFree(prefix + '_c_' + encoded, p);
            coefficientTerms.set(key, term);
            return term;
        },
        status: 'trusted-computation'
    });
    const bundle = algebraFormalFreydLongExactDelegationBundle({ reifier, selected: input.selected, anchorId: input.anchorId });
    const preparedHomology = prepareAlgebraFormalFreydLongExactHomology(bundle);
    const preparedRaw = prepareAlgebraFormalFreydRawWitnesses(bundle);
    const preparedModel = prepareAlgebraFormalFreydLongExactModel(bundle);
    sealed = true;
    const coefficients = Object.freeze([...coefficientTerms].sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0)
        .map(([value, term]) => Object.freeze({ value, term })));
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
