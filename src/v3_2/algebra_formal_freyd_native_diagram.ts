/** Assemble the original native H/maps/δ observations in one bounded diagram. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { trustAlgebraFormalFreydNativeConnectingWindows } from './algebra_formal_freyd_native_connecting_windows';
import { trustAlgebraFormalFreydNativeHomologyMap } from './algebra_formal_freyd_native_map_workflow';
import { algebraFormalFreydLongExactModelInventory } from './algebra_formal_freyd_long_exact_model_preparation';
import { algebraFormalFreydNativeModelHomologyObservationBundle } from './algebra_formal_freyd_model_observation';
import { constructAlgebraFormalFreydNativeExactness } from './algebra_formal_freyd_native_exactness';
import { assertAlgebraFormalComputationResultCurrent } from './algebra_formal_adoption';
import { kernelExpressionEquals } from './kernel';
import { createCoreProofChecker } from './proof_checker';
import { constructAlgebraFormalFreydDiagramCoherence } from './algebra_formal_freyd_diagram_coherence';
import { constructAlgebraFormalFreydNativeDisplayedExactness } from './algebra_formal_freyd_native_displayed_exactness';

export const ALGEBRA_FORMAL_FREYD_NATIVE_DIAGRAM_PROFILE = Object.freeze({
    revision: 'emdash-formal-native-freyd-diagram-v3' as const,
    input: 'original-whole-CAS-adoption' as const,
    observations: 'all-degree-maps-and-connecting-windows' as const,
    endpointConsistency: 'same-native-term-and-original-CAS-selection' as const,
    exactness: 'derived-whole-window-and-displayed-evidence' as const,
    requiresLegacyModel: false as const,
    assumesOutputExactness: false as const,
    diagramRepresentation: 'derived-finite-arrow-observation' as const,
    provesDisplayedDiagramCoherence: true as const,
    provesDisplayedExactness: true as const
});

export async function trustAlgebraFormalFreydNativeDiagram<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: Parameters<typeof trustAlgebraFormalFreydNativeConnectingWindows<P, C, I>>[0]
) {
    const windows = await trustAlgebraFormalFreydNativeConnectingWindows(input);
    const upstream = windows.upstreamAdoption.adoption.result;
    const inventory = algebraFormalFreydLongExactModelInventory(input.prepared.bundle, upstream.computed.value);
    if (inventory.data !== windows.inventoryData) throw new Error('Native diagram inventory changed during window assembly');
    let source = windows.source;
    const maps: { readonly entry: (typeof inventory.maps)[number];
        readonly result: Awaited<ReturnType<typeof trustAlgebraFormalFreydNativeHomologyMap<P, C, I>>> }[] = [];
    let reused = windows.counts.reused, computedEquations = windows.counts.computedEquations,
        interpretationClaims = windows.counts.interpretationClaims;
    for (const entry of inventory.maps) {
        const result = await trustAlgebraFormalFreydNativeHomologyMap({ artifactId: input.artifactId,
            modelId: input.modelId, observationId: entry.key, formalModel: input.formalModel,
            prepared: entry.prepared, source, fingerprint: input.fingerprint, decisionEvidence: input.decisionEvidence });
        source = result.source;
        reused += result.counts.reused;
        computedEquations += result.counts.computedEquations;
        interpretationClaims += result.counts.interpretationClaims;
        maps.push(Object.freeze({ entry, result }));
    }
    type Point = ReturnType<typeof algebraFormalFreydNativeModelHomologyObservationBundle<P, C, I>>['realization'];
    const expectedPoints = new Map(inventory.points.filter(e => e.kind === 'degree').map(e => [e.key, e]));
    const points = new Map<string, { readonly entry: (typeof inventory.points)[number]; readonly realization: Point }>();
    const retainPoint = (key: string, point: Point) => {
        const expected = expectedPoints.get(key);
        if (!expected || point.actual.selected !== expected.actual.selected ||
            !kernelExpressionEquals(point.formalModel, input.formalModel)) throw new Error('Native diagram changed H selection or model at ' + key);
        const previous = points.get(key);
        if (previous && (!kernelExpressionEquals(previous.realization.formalPoint, point.formalPoint) ||
            !kernelExpressionEquals(previous.realization.nativePoint, point.nativePoint) ||
            !kernelExpressionEquals(previous.realization.pointType, point.pointType))) {
            throw new Error('Native diagram H endpoint differs at ' + key);
        }
        if (!previous) points.set(key, Object.freeze({ entry: expected, realization: point }));
    };
    const observations = [
        ...windows.windows.map(w => ({ ...w, kind: 'connecting' as const })),
        ...maps.map(m => ({ ...m, kind: 'map' as const }))
    ];
    for (const { entry, result } of observations) {
        retainPoint(entry.sourceKey, result.observation.realization.source);
        retainPoint(entry.targetKey, result.observation.realization.target);
    }
    if (points.size !== expectedPoints.size) throw new Error('Native diagram omitted a degree H observation');
    const displayed = observations.filter(o => o.entry.position !== undefined)
        .sort((a, b) => a.entry.position! - b.entry.position!);
    if (displayed.length !== windows.native.arrows.length) throw new Error('Native displayed arrow coverage changed');
    const checker = createCoreProofChecker(source.environment);
    displayed.forEach(({ entry, result }, position) => {
        const r = result.observation.realization;
        if (entry.position !== position || r.prepared.selected.homologyMap !== windows.native.arrows[position] ||
            r.source.actual.selected !== windows.native.terms[position].view.homology ||
            r.target.actual.selected !== windows.native.terms[position + 1].view.homology) {
            throw new Error('Native displayed arrow/endpoints changed at position ' + position);
        }
        checker.check(checker.rootContext, result.proof, r.claimType);
    });
    const displayedPoints = windows.native.terms.map(term => {
        const point = points.get('degree/' + term.degree + '/' + term.role);
        if (!point) throw new Error('Missing displayed native H point');
        return point;
    });
    const exactness = windows.windows.map(window => Object.freeze({ degree: window.entry.degree,
        evidence: constructAlgebraFormalFreydNativeExactness(window.result) }));
    const coherence = constructAlgebraFormalFreydDiagramCoherence({ source, formalRing: input.prepared.bundle.reifier.formalRing,
        arrows: displayed.map(({ result }) => {
            const r = result.observation.realization;
            return { formalArrow: r.formalArrow, nativeArrow: r.nativeArrow, proof: result.proof,
                formalSource: r.source.formalPoint, formalTarget: r.target.formalPoint,
                nativeSource: r.source.nativePoint, nativeTarget: r.target.nativePoint };
        }) });
    const displayedExactness = constructAlgebraFormalFreydNativeDisplayedExactness({ source,
        formalRing: input.prepared.bundle.reifier.formalRing, formalModel: input.formalModel, normality: input.normality,
        windows: windows.windows, maps, displayed, coherence });
    assertAlgebraFormalComputationResultCurrent(upstream, upstream.request);
    return Object.freeze({ profile: ALGEBRA_FORMAL_FREYD_NATIVE_DIAGRAM_PROFILE,
        source, native: windows.native, upstreamAdoption: windows.upstreamAdoption, inventoryData: inventory.data,
        windows: windows.windows, maps: Object.freeze(maps), points: Object.freeze([...points.values()]),
        displayedPoints: Object.freeze(displayedPoints), displayed: Object.freeze(displayed), exactness: Object.freeze(exactness), coherence, displayedExactness,
        counts: Object.freeze({ points: points.size, maps: maps.length, windows: windows.windows.length,
            displayedPoints: displayedPoints.length, displayedArrows: displayed.length, exactness: exactness.length * 3,
            reused, computedEquations, interpretationClaims,
            newAssumptions: source.entries.length - (input.source ?? input.adopted.source).entries.length,
            homologyReplays: 0 as const, universalReselections: 0 as const, connectingReplays: 0 as const }) });
}
