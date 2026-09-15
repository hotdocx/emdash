/** Model interpretation of a complete retained arrow, without endpoint transport. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { algebraAlgorithmIdentity, defineAlgebraOperation, defineAlgebraRuntimeSchema } from './algebra_engine';
import { createAlgebraTypeScriptReferenceEngine, defineAlgebraReferenceImplementation } from './algebra_reference_engine';
import { AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter } from './algebra_formal_delegation';
import { algebraFormalFreydModelHomologyObservationBundle, algebraFormalFreydNativeModelHomologyObservationBundle,
    ALGEBRA_FORMAL_FREYD_MODEL_OBSERVATION_PROFILE, ALGEBRA_FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_PROFILE } from './algebra_formal_freyd_model_observation';
import { AlgebraFormalFreydModelMapPreparation, algebraFormalFreydModelChainMapTerm, assertAlgebraFormalFreydModelMapPreparationCurrent } from './algebra_formal_freyd_model_map_preparation';
import { FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS, createFormalFreydModelMapProofEnvironment } from './algebra_formal_freyd_model_map_signatures';
import { FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS, algebraFormalFreydModelType } from './algebra_formal_freyd_model_signatures';
import { CoreLfDeclarationEnvironment } from './lf_declarations';
import { CoreLfScopedBuilder } from './lf_builder';
import { createCoreProofChecker } from './proof_checker';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { algebraFormalFreydMorphismTerm } from './algebra_formal_freyd_chain_pair';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

import { algebraFormalFreydNativeModelType, FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_model_signatures';
import { createFormalFreydNativeModelObservationProofEnvironment, FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_model_observation_signatures';

type Point<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof algebraFormalFreydModelHomologyObservationBundle<P, C, I>> |
    ReturnType<typeof algebraFormalFreydNativeModelHomologyObservationBundle<P, C, I>>;

export const ALGEBRA_FORMAL_FREYD_MODEL_MAP_OBSERVATION_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-model-map-observation-v1' as const,
    boundary: 'complete-arrow-object-with-original-endpoints' as const,
    assumptionClassification: 'trusted-presentation-semantics' as const,
    endpointTransport: false as const, reselectsHomology: false as const,
    constructsModel: false as const, claimsQuotientEffectiveness: false as const,
    addsCoreOwner: false as const, performsIo: false as const
});

export const ALGEBRA_FORMAL_FREYD_NATIVE_MODEL_MAP_OBSERVATION_PROFILE = Object.freeze({
    ...ALGEBRA_FORMAL_FREYD_MODEL_MAP_OBSERVATION_PROFILE,
    revision: 'emdash-formal-freyd-native-model-map-observation-v1' as const,
    requiresLegacyModel: false as const
});

export interface AlgebraFormalFreydModelMapObservationInput<P extends AlgebraParent, C extends AlgebraElement<P>, I> {
    readonly observationId: string;
    readonly source: Point<P, C, I>;
    readonly target: Point<P, C, I>;
    readonly prepared: AlgebraFormalFreydModelMapPreparation<P, C, I>;
    readonly environment: CoreLfDeclarationEnvironment;
    readonly componentLaws: readonly [KernelExpression, KernelExpression, KernelExpression];
    readonly upperLaw: KernelExpression;
    readonly lowerLaw: KernelExpression;
    readonly resultLaw: KernelExpression;
}

export function algebraFormalFreydModelMapObservationBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydModelMapObservationInput<P, C, I>
) {
    return modelMapObservation(input, {
        profile: ALGEBRA_FORMAL_FREYD_MODEL_MAP_OBSERVATION_PROFILE,
        pointProfile: ALGEBRA_FORMAL_FREYD_MODEL_OBSERVATION_PROFILE.revision,
        createEnvironment: () => createFormalFreydModelMapProofEnvironment([]),
        bindings: { ...FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS },
        modelType: algebraFormalFreydModelType, arrowOwner: 'bridge_freyd_homology_model_arrow_observation',
        operationPrefix: 'proof-cas.freyd-model/'
    });
}

export function algebraFormalFreydNativeModelMapObservationBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydModelMapObservationInput<P, C, I>
) {
    return modelMapObservation(input, {
        profile: ALGEBRA_FORMAL_FREYD_NATIVE_MODEL_MAP_OBSERVATION_PROFILE,
        pointProfile: ALGEBRA_FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_PROFILE.revision,
        createEnvironment: () => createFormalFreydNativeModelObservationProofEnvironment([]),
        bindings: { ...FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS },
        modelType: algebraFormalFreydNativeModelType, arrowOwner: 'bridge_freyd_adjunction_model_arrow_observation',
        operationPrefix: 'proof-cas.freyd-native-model/'
    });
}

function modelMapObservation<P extends AlgebraParent, C extends AlgebraElement<P>, I,
    Profile extends { readonly revision: string }>(input: AlgebraFormalFreydModelMapObservationInput<P, C, I>, owner: {
    readonly profile: Profile;
    readonly pointProfile: string;
    readonly createEnvironment: () => CoreLfDeclarationEnvironment;
    readonly bindings: Readonly<Record<string, string>>;
    readonly modelType: (R: KernelExpression) => KernelExpression;
    readonly arrowOwner: string;
    readonly operationPrefix: string;
}) {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.observationId)) throw new Error('A stable map observation ID is required');
    const s = input.source.realization, t = input.target.realization, prepared = input.prepared;
    const currentInputs = () => {
        if (input.source.profile.revision !== owner.pointProfile || input.target.profile.revision !== owner.pointProfile) {
            throw new Error('Model map requires matching native or legacy point observation profiles');
        }
        assertAlgebraFormalFreydModelMapPreparationCurrent(prepared);
        input.source.adapter.normalizeRealization(s, 'modelMap.source');
        input.target.adapter.normalizeRealization(t, 'modelMap.target');
        if (s.modelId !== t.modelId || !kernelExpressionEquals(s.formalModel, t.formalModel) ||
            s.actual.reifier !== prepared.reifier || t.actual.reifier !== prepared.reifier ||
            s.actual.selected !== prepared.selected.chainMap.source || t.actual.selected !== prepared.selected.chainMap.target) {
            throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'modelMap.selection', 'Map needs the same supplied model and original source/target homologies');
        }
    };
    currentInputs();
    const expected = (() => {
        const environment = owner.createEnvironment();
        return Object.keys(owner.bindings)
            .map(name => environment.lookup(name)!);
    })();
    const assertContext = (environment: CoreLfDeclarationEnvironment) => {
        for (const signature of expected) {
            const value = environment.lookup(signature.name);
            if (!value || value.body !== undefined || !kernelExpressionEquals(value.type, signature.type)) throw new Error('Changed model map signature ' + signature.name);
        }
        const declaration = environment.lookup(s.formalModel.name);
        if (!declaration || declaration.body !== undefined || !kernelExpressionEquals(declaration.type, owner.modelType(prepared.reifier.formalRing))) {
            throw new Error('Changed supplied coherent model declaration');
        }
    };
    assertContext(input.environment);
    const chain = algebraFormalFreydModelChainMapTerm(prepared, { morphisms: [s.inputLaws.above, s.inputLaws.below,
        t.inputLaws.above, t.inputLaws.below, ...input.componentLaws], upper: input.upperLaw, lower: input.lowerLaw });
    const checker = createCoreProofChecker(input.environment);
    checker.check(checker.rootContext, chain.term, chain.type);
    const b = new CoreLfScopedBuilder(provenance('derived', 'complete model homology arrow observation')), L = formalFreydSpineLanguage(b);
    const R = b.embed(prepared.reifier.formalRing);
    const values = [R, b.embed(s.formalModel), ...chain.presentations.map(x => b.embed(x)), ...chain.morphisms.map(x => b.embed(x)),
        b.embed(s.pair.term), b.embed(t.pair.term), b.embed(chain.term)];
    const formalArrow = b.lower(b.call(b.free(owner.arrowOwner), values.map((value, i) => ({
        value, plicity: (i === 0 || (i >= 2 && i <= 14) ? 'implicit' : 'explicit') as 'implicit' | 'explicit'
    }))));
    const resultMap = algebraFormalFreydMorphismTerm(prepared.result, input.resultLaw);
    const nativeArrow = b.lower(L.call('bridge_freyd_raw_arrow_observation',
        [R, b.embed(s.nativePoint), b.embed(t.nativePoint), b.embed(resultMap)], 3));
    const observationType = b.lower(L.tau(L.call('bridge_FreydArrowObservation', [R])));
    checker.check(checker.rootContext, formalArrow, observationType);
    checker.check(checker.rootContext, nativeArrow, observationType);
    const claimType = b.lower(L.equality(L.call('bridge_FreydArrowObservation', [R]), b.embed(formalArrow), b.embed(nativeArrow)));
    const serialize = () => serializeCoreLfWorkspaceCanonicalJson({ observationId: input.observationId, source: s.formalData,
        target: t.formalData, prepared: prepared.formalData,
        expressions: [formalArrow, nativeArrow, claimType].map(x => serializeCoreExpression(x)) }, 'modelArrowObservation');
    const formalData = serialize();
    const current = () => {
        currentInputs();
        if (serialize() !== formalData) throw new Error('Model arrow observation changed');
    };
    const realization = Object.freeze({ prepared, source: s, target: t, chain, resultMap, formalArrow, nativeArrow,
        observationType, claimType, formalData, observationId: input.observationId });
    const id = owner.operationPrefix + s.modelId + '/homology-map/' + input.observationId;
    const schema = defineAlgebraRuntimeSchema<typeof prepared.selected>({ id: id + '/retained', revision: 'v1', normalize(value) {
        current();
        if (value !== prepared.selected) throw new Error('Foreign retained homology map');
        return prepared.selected;
    } });
    const operation = defineAlgebraOperation({ id, revision: 'v1', input: schema, output: schema });
    const implementation = defineAlgebraReferenceImplementation({ operation, algorithm: algebraAlgorithmIdentity(id + '/observe-retained', 'v1'),
        execute(value) { current(); return value; } });
    const engine = createAlgebraTypeScriptReferenceEngine({ id: id + '/engine', revision: 'v1', implementations: [implementation] });
    const adapter = defineAlgebraFormalComputationAdapter({ id, revision: owner.profile.revision, operation,
        normalizeRealization(value: unknown) {
            if (value !== realization) throw new Error('Foreign model arrow realization');
            current(); return realization;
        }, serializeRealization: () => formalData,
        acquire(goal) {
            assertContext(goal.document.environment); current();
            if (!kernelExpressionEquals(goal.target, claimType)) throw new AlgebraFormalDelegationError(
                'CLAIM_TARGET_MISMATCH', 'modelMap.goal', 'Goal differs from the complete model arrow and original endpoints');
            return prepared.selected;
        }, serializeInput: () => prepared.selectedData,
        serializeOutput: value => { current(); if (value !== prepared.selected) throw new Error('Changed model-map result'); return prepared.selectedData; },
        interpret: ({ goal, computed }) => {
            current();
            return computed.value === prepared.selected
                ? { kind: 'claim' as const, claimType: goal.target, summary: 'explicitly interpret the supplied model at this retained complete homology arrow, without endpoint transport' }
                : { kind: 'observation' as const, summary: 'retained model arrow changed' };
        }
    });
    return Object.freeze({ profile: owner.profile, realization, adapter, engine });
}
