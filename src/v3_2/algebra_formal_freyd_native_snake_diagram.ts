/** Coherent finite diagram from the five existing native snake interpretations. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { trustAlgebraFormalFreydNativeSnake } from './algebra_formal_freyd_native_snake_workflow';
import { validateAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { assertAlgebraFormalFreydNativeSnakeContext } from './algebra_formal_freyd_native_snake_observation';
import { formalFreydNativeSnakeFields, FREYD_NATIVE_SNAKE_MAP_ROLES } from './algebra_formal_freyd_native_snake_signatures';
import { createFormalFreydNativeSnakeDiagramProofEnvironment, FORMAL_FREYD_NATIVE_SNAKE_DIAGRAM_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_snake_diagram_signatures';
import { CoreLfScopedBuilder } from './lf_builder';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { createCoreProofChecker } from './proof_checker';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';

export function constructAlgebraFormalFreydNativeSnakeDiagram<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    snake: Awaited<ReturnType<typeof trustAlgebraFormalFreydNativeSnake<P, C, I>>>
) {
    if (snake.observations.length !== 5 || snake.observations.some((o, i) => o.role !== FREYD_NATIVE_SNAKE_MAP_ROLES[i])) throw new Error('Retain all five native snake arrows in order');
    const source = validateAlgebraFormalAssumptionSource(snake.source), prepared = snake.prepared;
    const connecting = snake.observations[2], realization = connecting.observation.realization;
    for (const o of snake.observations) {
        if (o.observation.realization.prepared !== prepared || !kernelExpressionEquals(o.observation.realization.formalModel, realization.formalModel)) throw new Error('Snake diagram changed its original input or model');
        o.observation.adapter.normalizeRealization(o.observation.realization, 'snakeDiagram.arrow');
    }
    assertAlgebraFormalFreydNativeSnakeContext(source.environment, prepared.reifier.formalRing, realization.formalModel);
    const expected = createFormalFreydNativeSnakeDiagramProofEnvironment([]);
    for (const name of Object.keys(FORMAL_FREYD_NATIVE_SNAKE_DIAGRAM_SIGNATURE_BINDINGS)) {
        const d = source.environment.lookup(name);
        if (!d || d.body !== undefined || !kernelExpressionEquals(d.type, expected.lookup(name)!.type)) throw new Error('Missing or changed snake diagram signature ' + name);
    }
    const checker = createCoreProofChecker(source.environment), b = new CoreLfScopedBuilder(provenance('derived', 'native snake diagram transport')), L = formalFreydSpineLanguage(b);
    const [A0, B0, X0, D0] = realization.terms.presentations, [a0, b0, c0] = realization.terms.morphisms;
    const values = { R: prepared.reifier.formalRing, M: realization.formalModel, N: connecting.observationInput.normality,
        A: A0, B: B0, X: X0, D: D0, a: a0, b: b0, c: c0, z: realization.terms.zero };
    const args = formalFreydNativeSnakeFields(b, true).map(([name, , mode]) => ({ value: b.embed(values[name]),
        plicity: mode === 'implicit' ? 'implicit' as const : 'explicit' as const }));
    const R = b.embed(values.R), O = L.call('bridge_FreydArrowObservation', [R]);
    const formal = snake.observations.map(o => b.embed(o.observation.realization.formalArrow));
    const native = snake.observations.map(o => b.embed(o.observation.realization.nativeArrow));
    const paths = snake.observations.map(o => b.embed(o.proof));
    const nil = L.call('bridge_finite_family_nil', [O], 1), family = (n: number) => L.call('bridge_FiniteFamily', [O, L.nat(n)]);
    let formalTail = nil, nativeTail = nil, tailPath = L.call('bridge_eq_refl', [family(0), nil], 1);
    let matching = L.call('bridge_freyd_arrow_matching_nil', [R, formal[4]], 1);
    const endpointPaths: KernelExpression[] = [];
    for (let i = 4; i > 0; i--) {
        const n = L.nat(4 - i), position = ['first', 'second', 'third', 'fourth'][i - 1];
        const link = b.call(b.free('bridge_freyd_native_snake_' + position + '_pair_matching'), args);
        endpointPaths.unshift(b.lower(link));
        matching = L.call('bridge_freyd_arrow_matching_cons', [R, n, formal[i - 1], formal[i], formalTail, link, matching], 5);
        tailPath = L.call('bridge_finite_family_cons_path', [O, n, formal[i], native[i], formalTail, nativeTail, paths[i], tailPath], 6);
        formalTail = L.call('bridge_finite_family_cons', [O, n, formal[i], formalTail], 2);
        nativeTail = L.call('bridge_finite_family_cons', [O, n, native[i], nativeTail], 2);
    }
    const n = L.nat(4), nativeMatching = L.call('bridge_freyd_arrow_matching_transport',
        [R, n, formal[0], native[0], formalTail, nativeTail, matching, paths[0], tailPath], 6);
    const formalDiagram = L.call('bridge_freyd_arrow_diagram_intro', [R, n, formal[0], formalTail, matching], 2);
    const nativeDiagram = L.call('bridge_freyd_arrow_diagram_intro', [R, n, native[0], nativeTail, nativeMatching], 2);
    const diagram = L.call('bridge_FreydArrowObservationDiagram', [R, n]);
    const path = L.call('bridge_freyd_arrow_diagram_path', [R, n, formal[0], native[0], formalTail, nativeTail,
        matching, nativeMatching, paths[0], tailPath], 6);
    const diagramType = b.lower(L.tau(diagram)), pathType = b.lower(L.equality(diagram, formalDiagram, nativeDiagram));
    const f = b.lower(formalDiagram), g = b.lower(nativeDiagram), h = b.lower(path);
    checker.check(checker.rootContext, f, diagramType); checker.check(checker.rootContext, g, diagramType); checker.check(checker.rootContext, h, pathType);
    return Object.freeze({ source, prepared, formalDiagram: f, nativeDiagram: g, diagramType, path: h, pathType,
        formalMatching: b.lower(matching), nativeMatching: b.lower(nativeMatching),
        endpointPaths: Object.freeze(endpointPaths), assumptionsAdded: 0 as const, trustDecisions: 0 as const,
        wholeFiniteObservationPath: true as const, provesDisplayedCasExactness: false as const });
}
