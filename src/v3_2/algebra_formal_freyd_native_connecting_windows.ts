/** All retained connecting windows in one supplied native model and source. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydLongExactModelPreparation, assertAlgebraFormalFreydLongExactModelPreparationCurrent,
    algebraFormalFreydLongExactModelInventory } from './algebra_formal_freyd_long_exact_model_preparation';
import { AlgebraFormalFreydLongExactAdoption, ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE } from './algebra_formal_freyd_long_exact';
import { algebraFormalFreydLongExactEquations, serializeAlgebraFormalFreydLongExactEquations } from './algebra_formal_freyd_long_exact_equations';
import { assertAlgebraFormalComputationResultCurrent } from './algebra_formal_adoption';
import { AlgebraFormalAssumptionSource, validateAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { assertAlgebraFormalFreydNativeConnectingContext } from './algebra_formal_freyd_model_connecting_observation';
import { algebraFormalFreydNativeModelNormalityType } from './algebra_formal_freyd_native_model_signatures';
import { trustAlgebraFormalFreydNativeConnecting } from './algebra_formal_freyd_native_connecting_workflow';
import { createCoreProofChecker } from './proof_checker';
import { CoreProofArtifactFingerprint } from './proof_document';
import { KernelExpression } from './kernel';

export const ALGEBRA_FORMAL_FREYD_NATIVE_CONNECTING_WINDOWS_PROFILE = Object.freeze({
    revision: 'emdash-formal-native-freyd-connecting-windows-v1' as const,
    coverage: 'all-original-windows-in-degree-order' as const,
    model: 'one-supplied-native-adjunction-model' as const,
    realization: 'explicit-native-row-and-complete-arrow-interpretations' as const,
    requiresLegacyModel: false as const,
    replaysHomology: false as const,
    reselectsUniversals: false as const,
    provesWholeDiagramCoherence: false as const,
    assumesOutputExactness: false as const
});

/** Preserve the actual whole CAS adoption before interpreting any window. */
export async function trustAlgebraFormalFreydNativeConnectingWindows<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly artifactId: string;
    readonly modelId: string;
    readonly formalModel: KernelExpression;
    readonly normality: KernelExpression;
    readonly prepared: AlgebraFormalFreydLongExactModelPreparation<P, C, I>;
    readonly adopted: AlgebraFormalFreydLongExactAdoption<P, C, I>;
    readonly source?: AlgebraFormalAssumptionSource;
    readonly fingerprint: (id: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (id: string) => string;
}) {
    for (const id of [input.artifactId, input.modelId]) {
        if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(id)) throw new Error('A stable native window model/artifact ID is required');
    }
    assertAlgebraFormalFreydLongExactModelPreparationCurrent(input.prepared);
    if (input.adopted.profileRevision !== ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE.revision) throw new Error('Foreign whole-adoption profile');
    const { bundle } = input.prepared, upstream = input.adopted.adoption.result;
    if (upstream.request.adapter !== bundle.adapter) throw new Error('Native windows belong to another whole CAS replay');
    assertAlgebraFormalComputationResultCurrent(upstream, upstream.request);
    let source = validateAlgebraFormalAssumptionSource(input.source ?? input.adopted.source);
    if (!source.entries.some(entry => entry.adoption === input.adopted.adoption)) throw new Error('Native window source is missing the original whole adoption');
    const equations = algebraFormalFreydLongExactEquations({ reifier: bundle.reifier, selected: upstream.computed.value });
    if (serializeAlgebraFormalFreydLongExactEquations(equations) !== input.prepared.equationsData ||
        serializeAlgebraFormalFreydLongExactEquations(input.adopted.equations) !== input.prepared.equationsData) {
        throw new Error('The adopted native window equation inventory changed');
    }
    const inventory = algebraFormalFreydLongExactModelInventory(bundle, upstream.computed.value);
    if (inventory.data !== input.prepared.inventory.data) throw new Error('Actual replay differs from the prepared native window inventory');
    assertAlgebraFormalFreydNativeConnectingContext(source.environment, bundle.reifier.formalRing, input.formalModel);
    const checker = createCoreProofChecker(source.environment);
    checker.check(checker.rootContext, input.normality, algebraFormalFreydNativeModelNormalityType(bundle.reifier.formalRing, input.formalModel));
    const before = source.entries.length;
    const windows: { readonly entry: (typeof inventory.connectings)[number];
        readonly result: Awaited<ReturnType<typeof trustAlgebraFormalFreydNativeConnecting<P, C, I>>> }[] = [];
    let reused = 0, computedEquations = 0, interpretationClaims = 0;
    for (const entry of inventory.connectings) {
        const result = await trustAlgebraFormalFreydNativeConnecting({ artifactId: input.artifactId,
            modelId: input.modelId, observationId: entry.key, formalModel: input.formalModel,
            normality: input.normality, prepared: entry.prepared, source, fingerprint: input.fingerprint,
            decisionEvidence: input.decisionEvidence });
        source = result.source;
        reused += result.counts.reused;
        computedEquations += result.counts.computedEquations;
        interpretationClaims += result.counts.interpretationClaims;
        windows.push(Object.freeze({ entry, result }));
    }
    assertAlgebraFormalComputationResultCurrent(upstream, upstream.request);
    return Object.freeze({ profile: ALGEBRA_FORMAL_FREYD_NATIVE_CONNECTING_WINDOWS_PROFILE,
        source, native: upstream.computed.value.result, upstreamAdoption: input.adopted,
        inventoryData: inventory.data, windows: Object.freeze(windows),
        counts: Object.freeze({ windows: windows.length, reused, computedEquations, interpretationClaims,
            newAssumptions: source.entries.length - before, homologyReplays: 0 as const,
            connectingReplays: 0 as const, universalReselections: 0 as const }) });
}
