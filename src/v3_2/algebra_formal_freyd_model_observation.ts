/** Interpret one supplied whole-H point using its retained native computation.
 * This is an explicit model-interpretation agreement, not a construction of
 * the coherent model or a new theorem proving the CAS implementation correct.
 */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { algebraAlgorithmIdentity, defineAlgebraOperation, defineAlgebraRuntimeSchema } from './algebra_engine';
import { createAlgebraTypeScriptReferenceEngine, defineAlgebraReferenceImplementation } from './algebra_reference_engine';
import { AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter } from './algebra_formal_delegation';
import { CoreLfDeclarationEnvironment } from './lf_declarations';
import { createCoreProofChecker } from './proof_checker';
import { KernelExpression, kernelExpressionEquals, kernelFree, provenance } from './kernel';
import { CoreLfScopedBuilder } from './lf_builder';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import { algebraFormalMatrixTerm } from './algebra_formal_finite_module';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { algebraFormalFreydChainPairTerm } from './algebra_formal_freyd_chain_pair';
import { AlgebraFormalFreydActualHomologyRealization, defineAlgebraFormalFreydActualHomologyRealization } from './algebra_formal_freyd_actual_homology';
import { algebraFormalFreydModelType, createFormalFreydModelProofEnvironment, FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS } from './algebra_formal_freyd_model_signatures';
import { serializeAlgebraPolynomialFreydHomologyAt } from './algebra_polynomial_freyd_homology_reference_operations';
import { validateAffineFormalCoreTerm } from './algebra_formal_realization';
import { algebraFormalFreydNativeModelType, FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_model_signatures';
import { createFormalFreydNativeModelObservationProofEnvironment, FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_model_observation_signatures';

export const ALGEBRA_FORMAL_FREYD_MODEL_OBSERVATION_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-model-point-observation-v1' as const,
    inputModel: 'named-opaque-supplied-coherent-model' as const,
    interpretation: 'explicitly-trusted-retained-selection-agreement' as const,
    execution: 'observe-existing-native-homology-result' as const,
    assumptionClassification: 'trusted-presentation-semantics' as const,
    constructsModel: false as const,
    claimsQuotientEffectiveness: false as const,
    reselectsHomology: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

export const ALGEBRA_FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_PROFILE = Object.freeze({
    ...ALGEBRA_FORMAL_FREYD_MODEL_OBSERVATION_PROFILE,
    revision: 'emdash-formal-freyd-native-model-point-observation-v1' as const,
    inputModel: 'named-opaque-supplied-whole-adjunction-model' as const,
    requiresLegacyModel: false as const
});

/** Prepare result coefficients before the caller freezes its formal environment. */
export function algebraFormalFreydRetainedHomologyPresentation<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    actual: AlgebraFormalFreydActualHomologyRealization<P, C, I>
): KernelExpression {
    const b = new CoreLfScopedBuilder(provenance('derived', 'retained native homology presentation'));
    const L = formalFreydSpineLanguage(b);
    const object = actual.selected.homologyObject;
    const relations = algebraFormalMatrixTerm(actual.reifier, object.relations.generators, object.ambient.rank);
    return b.lower(L.presentation(b.embed(actual.reifier.formalRing), L.nat(object.ambient.rank),
        L.nat(object.relations.generators.length), b.embed(relations)));
}

export interface AlgebraFormalFreydModelObservationInput<P extends AlgebraParent, C extends AlgebraElement<P>, I> {
    readonly modelId: string;
    readonly observationId: string;
    readonly formalModel: KernelExpression;
    readonly environment: CoreLfDeclarationEnvironment;
    readonly actual: AlgebraFormalFreydActualHomologyRealization<P, C, I>;
    readonly aboveLaw: KernelExpression;
    readonly belowLaw: KernelExpression;
    readonly chainLaw: KernelExpression;
}

/** Compatibility observation at the older selected-dictionary model. */
export function algebraFormalFreydModelHomologyObservationBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydModelObservationInput<P, C, I>
) {
    return modelHomologyObservation(input, {
        profile: ALGEBRA_FORMAL_FREYD_MODEL_OBSERVATION_PROFILE,
        createEnvironment: () => createFormalFreydModelProofEnvironment([]),
        bindings: FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS,
        modelType: algebraFormalFreydModelType, pointOwner: 'bridge_freyd_homology_model_object',
        operationPrefix: 'proof-cas.freyd-model/'
    });
}

/** Explicit CAS realization of the direct native whole-H observation. */
export function algebraFormalFreydNativeModelHomologyObservationBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydModelObservationInput<P, C, I>
) {
    return modelHomologyObservation(input, {
        profile: ALGEBRA_FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_PROFILE,
        createEnvironment: () => createFormalFreydNativeModelObservationProofEnvironment([]),
        bindings: { ...FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS },
        modelType: algebraFormalFreydNativeModelType, pointOwner: 'bridge_freyd_adjunction_model_object',
        operationPrefix: 'proof-cas.freyd-native-model/'
    });
}

function modelHomologyObservation<P extends AlgebraParent, C extends AlgebraElement<P>, I,
    Profile extends { readonly revision: string }>(input: AlgebraFormalFreydModelObservationInput<P, C, I>, owner: {
    readonly profile: Profile;
    readonly createEnvironment: () => CoreLfDeclarationEnvironment;
    readonly bindings: Readonly<Record<string, string>>;
    readonly modelType: (R: KernelExpression) => KernelExpression;
    readonly pointOwner: string;
    readonly operationPrefix: string;
}) {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.modelId)) throw new Error('A stable coherent-model interpretation ID is required');
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.observationId)) throw new Error('A stable model-observation ID is required');
    const suppliedModel = validateAffineFormalCoreTerm(input.formalModel, 'freydModel.reference');
    if (suppliedModel.tag !== 'reference') throw new Error('The initial model binding requires a named supplied model');
    const modelReference = Object.freeze(kernelFree(suppliedModel.name, suppliedModel.provenance));
    // Retain exactly the checked private signatures this adapter compares,
    // not another copy of their full prerequisite environment per H point.
    const expectedOwners = (() => {
        const environment = owner.createEnvironment();
        return Object.keys(owner.bindings).map(name => environment.lookup(name)!);
    })();
    const assertOwners = (environment: CoreLfDeclarationEnvironment) => {
        for (const expected of expectedOwners) {
            const actual = environment.lookup(expected.name);
            if (!actual || actual.body !== undefined || !kernelExpressionEquals(actual.type, expected.type)) {
                throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'freydModel.owner', 'Missing or changed model signature ' + expected.name);
            }
        }
    };
    assertOwners(input.environment);
    const modelDeclaration = input.environment.lookup(modelReference.name);
    if (!modelDeclaration || modelDeclaration.body !== undefined) throw new Error('Interpret a supplied opaque model input; do not silently reinterpret a defined model');
    const actual = defineAlgebraFormalFreydActualHomologyRealization(input.actual);
    if (actual.formalData !== input.actual.formalData) throw new Error('Stale actual homology realization');
    const checker = createCoreProofChecker(input.environment);
    checker.check(checker.rootContext, modelReference, owner.modelType(actual.reifier.formalRing));
    const pair = algebraFormalFreydChainPairTerm(actual.chain, input.aboveLaw, input.belowLaw, input.chainLaw);
    checker.check(checker.rootContext, pair.term, pair.type);

    const b = new CoreLfScopedBuilder(provenance('derived', 'whole homology model point observation'));
    const L = formalFreydSpineLanguage(b);
    const R = b.embed(actual.reifier.formalRing);
    const values = [R, b.embed(modelReference), ...actual.chain.presentations.map(x => b.embed(x)),
        b.embed(pair.above), b.embed(pair.below), b.embed(pair.term)];
    const formalPoint = b.lower(b.call(b.free(owner.pointOwner), values.map((value, index) => ({
        value, plicity: ([0, 2, 3, 4].includes(index) ? 'implicit' : 'explicit') as 'implicit' | 'explicit'
    }))));
    const nativePoint = algebraFormalFreydRetainedHomologyPresentation(actual);
    const pointType = b.lower(L.presentationType(R));
    checker.check(checker.rootContext, formalPoint, pointType);
    checker.check(checker.rootContext, nativePoint, pointType);
    const claimType = b.lower(L.equality(L.call('bridge_CommRingPresentation', [R]), b.embed(formalPoint), b.embed(nativePoint)));
    const selectedData = serializeAlgebraPolynomialFreydHomologyAt(actual.selected);
    const serializeBinding = () => serializeCoreLfWorkspaceCanonicalJson({
        modelId: input.modelId, observationId: input.observationId, model: serializeCoreExpression(modelReference), modelType: serializeCoreExpression(modelDeclaration.type),
        actual: actual.formalData, query: serializeCoreExpression(formalPoint), value: serializeCoreExpression(nativePoint),
        claim: serializeCoreExpression(claimType)
    }, 'freydModelPointObservation');
    const formalData = serializeBinding();
    const current = () => {
        const rebuilt = defineAlgebraFormalFreydActualHomologyRealization(input.actual);
        if (rebuilt.formalData !== actual.formalData || serializeAlgebraPolynomialFreydHomologyAt(actual.selected) !== selectedData ||
            !kernelExpressionEquals(algebraFormalFreydRetainedHomologyPresentation(rebuilt), nativePoint) || serializeBinding() !== formalData) {
            throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'freydModel.selection', 'The original homology or provider choices changed');
        }
    };
    const realization = Object.freeze({ profileRevision: owner.profile.revision,
        modelId: input.modelId, observationId: input.observationId, formalModel: modelReference, actual: input.actual, pair,
        inputLaws: Object.freeze({ above: input.aboveLaw, below: input.belowLaw, chain: input.chainLaw }),
        formalPoint, nativePoint, pointType, claimType, formalData });
    const id = owner.operationPrefix + input.modelId + '/homology-point/' + input.observationId;
    const schema = defineAlgebraRuntimeSchema<typeof actual.selected>({ id: id + '/retained-result', revision: 'v1', normalize(value) {
        if (value !== actual.selected) throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'freydModel.result', 'Expected the original retained homology result');
        current(); return actual.selected;
    } });
    const operation = defineAlgebraOperation({ id, revision: 'v1', input: schema, output: schema });
    const implementation = defineAlgebraReferenceImplementation({ operation,
        algorithm: algebraAlgorithmIdentity(id + '/observe-retained', 'v1'), execute(value) { current(); return value; } });
    const engine = createAlgebraTypeScriptReferenceEngine({ id: id + '/engine', revision: 'v1', implementations: [implementation] });
    const adapter = defineAlgebraFormalComputationAdapter({ id, revision: realization.profileRevision, operation,
        normalizeRealization(value: unknown) {
            if (value !== realization) throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'freydModel.binding', 'Foreign model or realization binding');
            current(); return realization;
        },
        serializeRealization: () => formalData,
        acquire(goal) {
            assertOwners(goal.document.environment);
            const declaration = goal.document.environment.lookup(modelReference.name);
            if (!declaration || declaration.body !== undefined || !kernelExpressionEquals(declaration.type, modelDeclaration.type)) {
                throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'freydModel.context', 'The supplied model declaration changed');
            }
            if (!kernelExpressionEquals(goal.target, claimType)) throw new AlgebraFormalDelegationError(
                'CLAIM_TARGET_MISMATCH', 'freydModel.goal', 'Goal differs from this exact model point and retained selection');
            current(); return actual.selected;
        },
        serializeInput: () => selectedData,
        serializeOutput: value => { current(); return serializeAlgebraPolynomialFreydHomologyAt(value); },
        interpret: ({ goal, computed }) => {
            current();
            return computed.value === actual.selected
                ? { kind: 'claim' as const, claimType: goal.target,
                    summary: 'explicit model interpretation identifies this whole-H point with the original retained native homology; no model construction or reselection' }
                : { kind: 'observation' as const, summary: 'retained homology differs from this model binding' };
        }
    });
    return Object.freeze({ profile: owner.profile, realization, adapter, engine });
}
