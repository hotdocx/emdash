/** Explicit model interpretation of a native snake arrow at its original endpoints. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydNativeSnakePreparation, algebraFormalFreydNativeSnakeInputTerms,
    assertAlgebraFormalFreydNativeSnakePreparationCurrent } from './algebra_formal_freyd_native_snake_preparation';
import { algebraFormalFreydNativeSnakeObservationTerm, createFormalFreydNativeSnakeProofEnvironment,
    FORMAL_FREYD_NATIVE_SNAKE_SIGNATURE_BINDINGS, FREYD_NATIVE_SNAKE_MAP_ROLES, FreydNativeSnakeMapRole } from './algebra_formal_freyd_native_snake_signatures';
import { algebraFormalFreydNativeModelType, algebraFormalFreydNativeModelNormalityType } from './algebra_formal_freyd_native_model_signatures';
import { algebraFormalFreydMorphismTerm } from './algebra_formal_freyd_chain_pair';
import { CoreLfDeclarationEnvironment } from './lf_declarations';
import { CoreLfScopedBuilder } from './lf_builder';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { createCoreProofChecker } from './proof_checker';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import { algebraAlgorithmIdentity, defineAlgebraOperation, defineAlgebraRuntimeSchema } from './algebra_engine';
import { createAlgebraTypeScriptReferenceEngine, defineAlgebraReferenceImplementation } from './algebra_reference_engine';
import { AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter } from './algebra_formal_delegation';

export const ALGEBRA_FORMAL_FREYD_NATIVE_SNAKE_OBSERVATION_PROFILE = Object.freeze({
    revision: 'emdash-formal-native-snake-observation-v1' as const,
    boundary: 'complete-arrow-with-original-six-term-endpoints' as const,
    assumptionClassification: 'trusted-presentation-semantics' as const,
    requiresLegacyModel: false as const, reselectsUniversals: false as const,
    constructsModel: false as const, suppliesOutputExactness: false as const,
    addsCoreOwner: false as const, performsIo: false as const
});

export function assertAlgebraFormalFreydNativeSnakeContext(environment: CoreLfDeclarationEnvironment,
    ring: KernelExpression, model: KernelExpression): void {
    const expected = createFormalFreydNativeSnakeProofEnvironment([]);
    for (const name of ['bridge_FreydAdjunctionModel', 'bridge_FreydAdjunctionModelNormality',
        'bridge_FreydArrowObservation', 'bridge_freyd_raw_arrow_observation', ...Object.keys(FORMAL_FREYD_NATIVE_SNAKE_SIGNATURE_BINDINGS)]) {
        const d = environment.lookup(name), e = expected.lookup(name);
        if (!d || d.body !== undefined || !e || !kernelExpressionEquals(d.type, e.type)) throw new Error('Missing or changed native snake signature ' + name);
    }
    if (model.tag !== 'reference' || model.namespace !== 'free') throw new Error('Supply a named native model input');
    const d = environment.lookup(model.name);
    if (!d || d.body !== undefined || !kernelExpressionEquals(d.type, algebraFormalFreydNativeModelType(ring))) {
        throw new Error('Changed native snake model declaration');
    }
}

export function algebraFormalFreydNativeSnakeObservationBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly modelId: string;
    readonly observationId: string;
    readonly role: FreydNativeSnakeMapRole;
    readonly formalModel: KernelExpression;
    readonly normality: KernelExpression;
    readonly prepared: AlgebraFormalFreydNativeSnakePreparation<P, C, I>;
    readonly environment: CoreLfDeclarationEnvironment;
    readonly inputLaws: readonly KernelExpression[];
    readonly zeroLaw: KernelExpression;
    readonly resultLaw: KernelExpression;
}) {
    for (const id of [input.modelId, input.observationId]) if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(id)) throw new Error('A stable native snake interpretation ID is required');
    const index = FREYD_NATIVE_SNAKE_MAP_ROLES.indexOf(input.role);
    if (index < 0) throw new Error('Unknown native snake map role');
    const prepared = input.prepared, R = prepared.reifier.formalRing;
    const current = () => assertAlgebraFormalFreydNativeSnakePreparationCurrent(prepared);
    current(); assertAlgebraFormalFreydNativeSnakeContext(input.environment, R, input.formalModel);
    const checker = createCoreProofChecker(input.environment);
    if (input.role === 'connecting') checker.check(checker.rootContext, input.normality,
        algebraFormalFreydNativeModelNormalityType(R, input.formalModel));
    const terms = algebraFormalFreydNativeSnakeInputTerms(prepared, input.inputLaws, input.zeroLaw);
    checker.check(checker.rootContext, terms.zero, terms.zeroType);
    const [A, B, X, D] = terms.presentations, [a, b0, c] = terms.morphisms;
    const formalArrow = algebraFormalFreydNativeSnakeObservationTerm(input.role,
        { R, M: input.formalModel, N: input.normality, A, B, X, D, a, b: b0, c, z: terms.zero });
    const result = prepared.outputs[index], resultMap = algebraFormalFreydMorphismTerm(result, input.resultLaw);
    const b = new CoreLfScopedBuilder(provenance('derived', 'native snake selected arrow')), L = formalFreydSpineLanguage(b);
    const ring = b.embed(R), m = result.selected;
    const source = L.presentation(ring, L.nat(m.source.ambient.rank), L.nat(m.source.relations.generators.length), b.embed(result.formalSourceRelations));
    const target = L.presentation(ring, L.nat(m.target.ambient.rank), L.nat(m.target.relations.generators.length), b.embed(result.formalTargetRelations));
    const nativeArrow = b.lower(L.call('bridge_freyd_raw_arrow_observation', [ring, source, target, b.embed(resultMap)], 3));
    const observationType = b.lower(L.tau(L.call('bridge_FreydArrowObservation', [ring])));
    checker.check(checker.rootContext, formalArrow, observationType);
    checker.check(checker.rootContext, nativeArrow, observationType);
    const claimType = b.lower(L.equality(L.call('bridge_FreydArrowObservation', [ring]), b.embed(formalArrow), b.embed(nativeArrow)));
    const formalData = serializeCoreLfWorkspaceCanonicalJson({ modelId: input.modelId, observationId: input.observationId,
        role: input.role, prepared: prepared.formalData,
        expressions: [formalArrow, nativeArrow, claimType].map(x => serializeCoreExpression(x)) }, 'nativeSnakeObservation');
    const realization = Object.freeze({ prepared, role: input.role, terms, formalModel: input.formalModel,
        formalArrow, nativeArrow, claimType, observationType, resultMap, formalData });
    const id = 'proof-cas.native-snake/' + input.modelId + '/' + input.observationId;
    const schema = defineAlgebraRuntimeSchema<typeof prepared.selected>({ id: id + '/selected', revision: 'v1', normalize(value) {
        current(); if (value !== prepared.selected) throw new Error('Foreign native snake selection'); return prepared.selected;
    } });
    const operation = defineAlgebraOperation({ id, revision: 'v1', input: schema, output: schema });
    const implementation = defineAlgebraReferenceImplementation({ operation, algorithm: algebraAlgorithmIdentity(id + '/observe', 'v1'),
        execute(value) { current(); return value; } });
    const engine = createAlgebraTypeScriptReferenceEngine({ id: id + '/engine', revision: 'v1', implementations: [implementation] });
    const adapter = defineAlgebraFormalComputationAdapter({ id, revision: ALGEBRA_FORMAL_FREYD_NATIVE_SNAKE_OBSERVATION_PROFILE.revision, operation,
        normalizeRealization(value: unknown) {
            if (value !== realization) throw new Error('Foreign native snake realization'); current(); return realization;
        }, serializeRealization: () => formalData,
        acquire(goal) {
            current(); assertAlgebraFormalFreydNativeSnakeContext(goal.document.environment, R, input.formalModel);
            if (!kernelExpressionEquals(goal.target, claimType)) throw new AlgebraFormalDelegationError(
                'CLAIM_TARGET_MISMATCH', 'nativeSnake.observation', 'Goal differs from the complete native snake arrow');
            return prepared.selected;
        }, serializeInput: value => { current(); if (value !== prepared.selected) throw new Error('Changed native snake input'); return prepared.selectedData; },
        serializeOutput: value => { current(); if (value !== prepared.selected) throw new Error('Changed native snake output'); return prepared.selectedData; },
        interpret: ({ goal, computed }) => {
            current(); return computed.value === prepared.selected
                ? { kind: 'claim' as const, claimType: goal.target, summary: 'explicitly interpret the native snake arrow at the original selected endpoints' }
                : { kind: 'observation' as const, summary: 'native snake selection changed' };
        }
    });
    return Object.freeze({ profile: ALGEBRA_FORMAL_FREYD_NATIVE_SNAKE_OBSERVATION_PROFILE, realization, adapter, engine });
}
