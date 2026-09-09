/** Interpret the retained bounded H inventory in one supplied coherent model. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydLongExactAdoption, ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE } from './algebra_formal_freyd_long_exact';
import { AlgebraFormalFreydLongExactModelPreparation, algebraFormalFreydLongExactModelInventory,
    assertAlgebraFormalFreydLongExactModelPreparationCurrent, createFormalFreydLongExactModelProofEnvironment } from './algebra_formal_freyd_long_exact_model_preparation';
import { algebraFormalFreydLongExactEquations, serializeAlgebraFormalFreydLongExactEquations } from './algebra_formal_freyd_long_exact_equations';
import { algebraFormalFreydModelHomologyObservationBundle } from './algebra_formal_freyd_model_observation';
import { algebraFormalFreydModelMapObservationBundle } from './algebra_formal_freyd_model_map_observation';
import { algebraFormalFreydModelMapSquareBundle } from './algebra_formal_freyd_model_map_preparation';
import { algebraFormalFreydModelType, FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS } from './algebra_formal_freyd_model_signatures';
import { FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS } from './algebra_formal_freyd_model_map_signatures';
import { algebraFormalFreydChainPairDelegationBundle } from './algebra_formal_freyd_chain_pair';
import { algebraFormalPresentationMorphismDelegationBundle } from './algebra_formal_presentation_morphism_delegation';
import { AlgebraFormalPresentationMorphismRealization } from './algebra_formal_presentation_morphism';
import { createAlgebraPolynomialFreydHomologyEngine } from './algebra_polynomial_freyd_homology_category';
import { createAlgebraTypeScriptReferenceEngine } from './algebra_reference_engine';
import { assertAlgebraFormalComputationResultCurrent } from './algebra_formal_adoption';
import { AlgebraFormalAssumptionSource, appendAlgebraFormalAssumption, validateAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { AlgebraFormalWorkflowInput, runAlgebraFormalWorkflow, trustAlgebraFormalWorkflow } from './algebra_formal_workflow';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { CoreProofArtifactFingerprint } from './proof_document';
import { coreProofPlanHole } from './proof_plan';
import { createCoreProofChecker } from './proof_checker';
import { serializeCoreExpression } from './core_serialization';

export const ALGEBRA_FORMAL_FREYD_LONG_EXACT_MODEL_PROFILE = Object.freeze({
    revision: 'emdash-formal-bounded-homology-model-observations-v1' as const,
    input: 'one-retained-whole-replay-and-adoption' as const,
    points: 'all-retained-degrees-and-interior-exactness-homologies' as const,
    maps: 'both-retained-degreewise-induced-maps' as const,
    interpretation: 'explicit-trusted-presentation-semantics' as const,
    replaysWholeHomology: false as const, reselectsUniversals: false as const,
    transportsEndpoints: false as const, constructsModel: false as const,
    claimsGenericLongExactTheorem: false as const
});

export async function trustAlgebraFormalFreydLongExactModel<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly artifactId: string;
    readonly modelId: string;
    readonly formalModel: KernelExpression;
    readonly prepared: AlgebraFormalFreydLongExactModelPreparation<P, C, I>;
    readonly adopted: AlgebraFormalFreydLongExactAdoption<P, C, I>;
    readonly source?: AlgebraFormalAssumptionSource;
    readonly fingerprint: (goalId: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (goalId: string) => string;
}) {
    for (const id of [input.artifactId, input.modelId]) {
        if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(id)) throw new Error('A stable bounded model/artifact ID is required');
    }
    assertAlgebraFormalFreydLongExactModelPreparationCurrent(input.prepared);
    if (input.adopted.profileRevision !== ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE.revision) throw new Error('Foreign whole-adoption profile');
    const { bundle } = input.prepared, upstream = input.adopted.adoption.result;
    if (upstream.request.adapter !== bundle.adapter) throw new Error('Bounded model adoption belongs to another whole replay');
    assertAlgebraFormalComputationResultCurrent(upstream, upstream.request);
    let source = validateAlgebraFormalAssumptionSource(input.source ?? input.adopted.source);
    if (!source.entries.some(entry => entry.adoption === input.adopted.adoption)) throw new Error('Model source is missing the original whole adoption');
    const equations = algebraFormalFreydLongExactEquations({ reifier: bundle.reifier, selected: upstream.computed.value });
    if (serializeAlgebraFormalFreydLongExactEquations(equations) !== input.prepared.equationsData ||
        serializeAlgebraFormalFreydLongExactEquations(input.adopted.equations) !== input.prepared.equationsData) {
        throw new Error('The adopted whole equation inventory changed');
    }
    const inventory = algebraFormalFreydLongExactModelInventory(bundle, upstream.computed.value);
    if (inventory.data !== input.prepared.inventory.data) throw new Error('Actual replay differs from the prepared bounded model inventory');
    const expected = createFormalFreydLongExactModelProofEnvironment([]);
    for (const name of Object.keys({ ...FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS })) {
        const declaration = source.environment.lookup(name);
        if (!declaration || declaration.body !== undefined || !kernelExpressionEquals(declaration.type, expected.lookup(name)!.type)) {
            throw new Error('Missing or changed bounded model signature ' + name);
        }
    }
    const model = input.formalModel;
    if (model.tag !== 'reference' || model.namespace !== 'free' || source.environment.lookup(model.name)?.body !== undefined) {
        throw new Error('Supply a named model input, not a reinterpretation of a defined model');
    }
    const checker = createCoreProofChecker(source.environment);
    checker.check(checker.rootContext, model, algebraFormalFreydModelType(bundle.reifier.formalRing));
    const before = source.entries.length;
    const known = new Map(source.entries.map(entry => [serializeCoreExpression(entry.declaration.type), entry.reference]));
    let reused = 0;
    const ensure = async <R, A, B>(key: string, claimType: KernelExpression,
        classification: 'computed-equation' | 'trusted-presentation-semantics',
        make: () => Pick<AlgebraFormalWorkflowInput<R, A, B>, 'adapter' | 'realization' | 'engine'>
    ): Promise<KernelExpression> => {
        const claimKey = serializeCoreExpression(claimType), old = known.get(claimKey);
        if (old) { reused++; return old; }
        const goalId = (input.artifactId + '/' + key).replace(/[^A-Za-z0-9_]/gu, '_');
        const p = provenance('derived', 'bounded model observation ' + key);
        const run = await runAlgebraFormalWorkflow({ ...make(), goalId, document: {
            moduleId: source.moduleId, declarationId: goalId, environment: source.environment, type: claimType,
            plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target: claimType } }),
            provenance: p, fingerprint: input.fingerprint(goalId)
        } });
        const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: goalId.replace(/[^A-Za-z0-9_]/gu, '_'),
            decision: { kind: 'trust-exact-algebra-computation', evidence: input.decisionEvidence(goalId) } });
        source = appendAlgebraFormalAssumption({ source, adoption, classification });
        const proof = source.entries.at(-1)!.reference;
        known.set(claimKey, proof);
        return proof;
    };
    const morphismLaw = (key: string, realization: AlgebraFormalPresentationMorphismRealization<P, C, I>) =>
        ensure(key, realization.claimType, 'computed-equation', () => {
            const operation = algebraFormalPresentationMorphismDelegationBundle({ reifier: bundle.reifier, selected: realization.selected });
            return { ...operation, engine: createAlgebraTypeScriptReferenceEngine({ id: input.artifactId + '/' + key,
                revision: 'v1', implementations: operation.operations.implementations }) };
        });
    type Point = ReturnType<typeof algebraFormalFreydModelHomologyObservationBundle<P, C, I>>;
    const points: { readonly entry: (typeof inventory.points)[number]; readonly observation: Point; readonly proof: KernelExpression }[] = [];
    for (const entry of inventory.points) {
        const aboveLaw = await morphismLaw(entry.key + '/above', entry.actual.chain.above);
        const belowLaw = await morphismLaw(entry.key + '/below', entry.actual.chain.below);
        const chainLaw = await ensure(entry.key + '/chain', entry.actual.chain.claimType, 'computed-equation', () => {
            const operation = algebraFormalFreydChainPairDelegationBundle({ reifier: bundle.reifier, selected: entry.actual.selected.pair });
            return { ...operation, engine: createAlgebraPolynomialFreydHomologyEngine(operation.model) };
        });
        const observation = algebraFormalFreydModelHomologyObservationBundle({ modelId: input.modelId, observationId: entry.key,
            formalModel: model, environment: source.environment, actual: entry.actual, aboveLaw, belowLaw, chainLaw });
        const proof = await ensure(entry.key + '/interpretation', observation.realization.claimType, 'trusted-presentation-semantics', () => observation);
        points.push(Object.freeze({ entry, observation, proof }));
    }
    const byKey = new Map(points.map(point => [point.entry.key, point.observation]));
    const maps = [];
    for (const entry of inventory.maps) {
        // Adoption extends one immutable source in order; do not race its updates.
        const componentLaws: KernelExpression[] = [];
        for (const [i, value] of entry.prepared.maps.slice(4).entries()) {
            componentLaws.push(await morphismLaw(entry.key + '/component-' + i, value));
        }
        const upper = algebraFormalFreydModelMapSquareBundle(entry.prepared, 'upper');
        const lower = algebraFormalFreydModelMapSquareBundle(entry.prepared, 'lower');
        const upperLaw = await ensure(entry.key + '/upper', upper.realization.claimType, 'computed-equation', () => upper);
        const lowerLaw = await ensure(entry.key + '/lower', lower.realization.claimType, 'computed-equation', () => lower);
        const resultLaw = await morphismLaw(entry.key + '/result', entry.prepared.result);
        const observation = algebraFormalFreydModelMapObservationBundle({ observationId: entry.key,
            source: byKey.get(entry.sourceKey)!, target: byKey.get(entry.targetKey)!, prepared: entry.prepared,
            environment: source.environment, componentLaws: [componentLaws[0], componentLaws[1], componentLaws[2]], upperLaw, lowerLaw, resultLaw });
        const proof = await ensure(entry.key + '/interpretation', observation.realization.claimType, 'trusted-presentation-semantics', () => observation);
        maps.push(Object.freeze({ entry, observation, proof }));
    }
    assertAlgebraFormalComputationResultCurrent(upstream, upstream.request);
    return Object.freeze({ profile: ALGEBRA_FORMAL_FREYD_LONG_EXACT_MODEL_PROFILE,
        native: upstream.computed.value.result, upstreamAdoption: input.adopted, source,
        points: Object.freeze(points), maps: Object.freeze(maps), inventoryData: inventory.data,
        counts: Object.freeze({ points: points.length, maps: maps.length, reusedClaims: reused,
            newAssumptions: source.entries.length - before, wholeHomologyReplays: 0 as const, universalReselections: 0 as const }) });
}
