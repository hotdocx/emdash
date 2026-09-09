/** Model interpretation of a complete retained arrow, without endpoint transport. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { algebraAlgorithmIdentity, defineAlgebraOperation, defineAlgebraRuntimeSchema } from './algebra_engine';
import { createAlgebraTypeScriptReferenceEngine, defineAlgebraReferenceImplementation } from './algebra_reference_engine';
import { AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter } from './algebra_formal_delegation';
import { algebraFormalFreydModelHomologyObservationBundle } from './algebra_formal_freyd_model_observation';
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

type Point<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof algebraFormalFreydModelHomologyObservationBundle<P, C, I>>;

export const ALGEBRA_FORMAL_FREYD_MODEL_MAP_OBSERVATION_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-model-map-observation-v1' as const,
    boundary: 'complete-arrow-object-with-original-endpoints' as const,
    assumptionClassification: 'trusted-presentation-semantics' as const,
    endpointTransport: false as const, reselectsHomology: false as const,
    constructsModel: false as const, claimsQuotientEffectiveness: false as const,
    addsCoreOwner: false as const, performsIo: false as const
});

export function algebraFormalFreydModelMapObservationBundle<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly observationId: string;
    readonly source: Point<P, C, I>;
    readonly target: Point<P, C, I>;
    readonly prepared: AlgebraFormalFreydModelMapPreparation<P, C, I>;
    readonly environment: CoreLfDeclarationEnvironment;
    readonly componentLaws: readonly [KernelExpression, KernelExpression, KernelExpression];
    readonly upperLaw: KernelExpression;
    readonly lowerLaw: KernelExpression;
    readonly resultLaw: KernelExpression;
}) {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.observationId)) throw new Error('A stable map observation ID is required');
    const s = input.source.realization, t = input.target.realization, prepared = input.prepared;
    const currentInputs = () => {
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
    const expected = createFormalFreydModelMapProofEnvironment([]);
    const assertContext = (environment: CoreLfDeclarationEnvironment) => {
        for (const name of Object.keys({ ...FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS })) {
            const value = environment.lookup(name);
            if (!value || value.body !== undefined || !kernelExpressionEquals(value.type, expected.lookup(name)!.type)) throw new Error('Changed model map signature ' + name);
        }
        const declaration = environment.lookup(s.formalModel.name);
        if (!declaration || declaration.body !== undefined || !kernelExpressionEquals(declaration.type, algebraFormalFreydModelType(prepared.reifier.formalRing))) {
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
    const formalArrow = b.lower(b.call(b.free('bridge_freyd_homology_model_arrow_observation'), values.map((value, i) => ({
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
    const id = 'proof-cas.freyd-model/' + s.modelId + '/homology-map/' + input.observationId;
    const schema = defineAlgebraRuntimeSchema<typeof prepared.selected>({ id: id + '/retained', revision: 'v1', normalize(value) {
        current();
        if (value !== prepared.selected) throw new Error('Foreign retained homology map');
        return prepared.selected;
    } });
    const operation = defineAlgebraOperation({ id, revision: 'v1', input: schema, output: schema });
    const implementation = defineAlgebraReferenceImplementation({ operation, algorithm: algebraAlgorithmIdentity(id + '/observe-retained', 'v1'),
        execute(value) { current(); return value; } });
    const engine = createAlgebraTypeScriptReferenceEngine({ id: id + '/engine', revision: 'v1', implementations: [implementation] });
    const adapter = defineAlgebraFormalComputationAdapter({ id, revision: ALGEBRA_FORMAL_FREYD_MODEL_MAP_OBSERVATION_PROFILE.revision, operation,
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
    return Object.freeze({ profile: ALGEBRA_FORMAL_FREYD_MODEL_MAP_OBSERVATION_PROFILE, realization, adapter, engine });
}
