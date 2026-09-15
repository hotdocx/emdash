/** Construct a whole finite observation path from the existing arrow agreements. */
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { CoreLfScopedBuilder } from './lf_builder';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { AlgebraFormalAssumptionSource, validateAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { createFormalFreydDiagramProofEnvironment, FORMAL_FREYD_DIAGRAM_SIGNATURE_BINDINGS } from './algebra_formal_freyd_diagram_signatures';
import { FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_model_observation_signatures';
import { FORMAL_FREYD_NATIVE_CONNECTING_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_connecting_signatures';
import { createCoreProofChecker } from './proof_checker';

export interface AlgebraFormalFreydDiagramArrow {
    readonly formalArrow: KernelExpression;
    readonly nativeArrow: KernelExpression;
    readonly formalSource: KernelExpression;
    readonly formalTarget: KernelExpression;
    readonly nativeSource: KernelExpression;
    readonly nativeTarget: KernelExpression;
    readonly proof: KernelExpression;
}

export function constructAlgebraFormalFreydDiagramCoherence(input: {
    readonly source: AlgebraFormalAssumptionSource;
    readonly formalRing: KernelExpression;
    readonly arrows: readonly AlgebraFormalFreydDiagramArrow[];
}) {
    if (input.arrows.length === 0) throw new Error('A native arrow diagram must be nonempty');
    const source = validateAlgebraFormalAssumptionSource(input.source);
    const expected = createFormalFreydDiagramProofEnvironment([]);
    for (const name of Object.keys({ ...FORMAL_FREYD_DIAGRAM_SIGNATURE_BINDINGS,
        ...FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS, ...FORMAL_FREYD_NATIVE_CONNECTING_SIGNATURE_BINDINGS })) {
        const declaration = source.environment.lookup(name);
        if (!declaration || declaration.body !== undefined || !kernelExpressionEquals(declaration.type, expected.lookup(name)!.type)) {
            throw new Error('Missing or changed native diagram signature ' + name);
        }
    }
    const b = new CoreLfScopedBuilder(provenance('derived', 'whole native finite diagram path')), L = formalFreydSpineLanguage(b);
    const R = b.embed(input.formalRing), A = L.call('bridge_FreydArrowObservation', [R]);
    const P = L.call('bridge_CommRingPresentation', [R]);
    const checker = createCoreProofChecker(source.environment);
    const check = (term: ReturnType<typeof b.free>, type: ReturnType<typeof b.free>) => {
        const lowered = b.lower(term); checker.check(checker.rootContext, lowered, b.lower(type)); return term;
    };
    const endpoint = (side: string, arrow: ReturnType<typeof b.free>) => L.call('bridge_freyd_arrow_observation_' + side, [R, arrow], 1);
    const beta = (arrow: KernelExpression, side: 'source' | 'target', point: KernelExpression) => {
        if (arrow.tag !== 'call' || arrow.callee.tag !== 'reference' || arrow.callee.namespace !== 'free' ||
            !['bridge_freyd_raw_arrow_observation', 'bridge_freyd_adjunction_model_arrow_observation',
                'bridge_freyd_adjunction_model_connecting_observation'].includes(arrow.callee.name)) {
            throw new Error('Use an original native or CAS complete-arrow observer');
        }
        const term = b.call(b.free(arrow.callee.name + '_' + side + '_beta'),
            arrow.arguments.map(a => ({ ...a, value: b.embed(a.value) })));
        return check(term, L.equality(P, endpoint(side, b.embed(arrow)), b.embed(point)));
    };
    const arrows = input.arrows.map((arrow, i) => {
        const formal = b.embed(arrow.formalArrow), native = b.embed(arrow.nativeArrow), proof = b.embed(arrow.proof);
        check(formal, L.tau(A)); check(native, L.tau(A)); check(proof, L.equality(A, formal, native));
        if (i && (!kernelExpressionEquals(input.arrows[i - 1].formalTarget, arrow.formalSource) ||
            !kernelExpressionEquals(input.arrows[i - 1].nativeTarget, arrow.nativeSource))) {
            throw new Error('Native diagram changed a shared endpoint at ' + i);
        }
        return { formal, native, proof,
            formalSource: beta(arrow.formalArrow, 'source', arrow.formalSource),
            formalTarget: beta(arrow.formalArrow, 'target', arrow.formalTarget),
            nativeSource: beta(arrow.nativeArrow, 'source', arrow.nativeSource),
            nativeTarget: beta(arrow.nativeArrow, 'target', arrow.nativeTarget) };
    });
    const nil = L.call('bridge_finite_family_nil', [A], 1);
    const family = (n: number) => L.call('bridge_FiniteFamily', [A, L.nat(n)]);
    let formalTail = nil, nativeTail = nil;
    let tailPath = L.call('bridge_eq_refl', [family(0), nil], 1);
    let formalMatching = L.call('bridge_freyd_arrow_matching_nil', [R, arrows[arrows.length - 1].formal], 1);
    let nativeMatching = L.call('bridge_freyd_arrow_matching_nil', [R, arrows[arrows.length - 1].native], 1);
    const endpointPaths: { readonly formal: KernelExpression; readonly native: KernelExpression }[] = [];
    for (let i = arrows.length - 1; i > 0; i--) {
        const current = arrows[i], previous = arrows[i - 1], n = arrows.length - i - 1;
        const join = (kind: 'formal' | 'native') => {
            const shared = b.embed(input.arrows[i - 1][kind === 'formal' ? 'formalTarget' : 'nativeTarget']);
            const left = endpoint('target', previous[kind]), right = endpoint('source', current[kind]);
            return check(L.call('bridge_eq_trans', [P, left, shared, right,
                previous[kind === 'formal' ? 'formalTarget' : 'nativeTarget'],
                L.call('bridge_eq_sym', [P, right, shared, current[kind === 'formal' ? 'formalSource' : 'nativeSource']], 3)], 4),
            L.equality(P, left, right));
        };
        const formalJoin = join('formal'), nativeJoin = join('native');
        endpointPaths.unshift({ formal: b.lower(formalJoin), native: b.lower(nativeJoin) });
        formalMatching = L.call('bridge_freyd_arrow_matching_cons', [R, L.nat(n), previous.formal, current.formal, formalTail,
            formalJoin, formalMatching], 5);
        nativeMatching = L.call('bridge_freyd_arrow_matching_cons', [R, L.nat(n), previous.native, current.native, nativeTail,
            nativeJoin, nativeMatching], 5);
        tailPath = L.call('bridge_finite_family_cons_path', [A, L.nat(n), current.formal, current.native, formalTail, nativeTail,
            current.proof, tailPath], 6);
        formalTail = L.call('bridge_finite_family_cons', [A, L.nat(n), current.formal, formalTail], 2);
        nativeTail = L.call('bridge_finite_family_cons', [A, L.nat(n), current.native, nativeTail], 2);
    }
    const n = L.nat(arrows.length - 1), diagram = L.call('bridge_FreydArrowObservationDiagram', [R, n]);
    const formalDiagram = L.call('bridge_freyd_arrow_diagram_intro', [R, n, arrows[0].formal, formalTail, formalMatching], 2);
    const nativeDiagram = L.call('bridge_freyd_arrow_diagram_intro', [R, n, arrows[0].native, nativeTail, nativeMatching], 2);
    const pathType = L.equality(diagram, formalDiagram, nativeDiagram);
    const path = L.call('bridge_freyd_arrow_diagram_path', [R, n, arrows[0].formal, arrows[0].native, formalTail, nativeTail,
        formalMatching, nativeMatching, arrows[0].proof, tailPath], 6);
    check(formalDiagram, L.tau(diagram)); check(nativeDiagram, L.tau(diagram)); check(path, pathType);
    return Object.freeze({ source, formalDiagram: b.lower(formalDiagram), nativeDiagram: b.lower(nativeDiagram),
        diagramType: b.lower(L.tau(diagram)), path: b.lower(path), pathType: b.lower(pathType),
        endpointPaths: Object.freeze(endpointPaths), arrows: Object.freeze([...input.arrows]),
        assumptionsAdded: 0 as const, trustDecisions: 0 as const,
        wholeFiniteObservationPath: true as const, provesDisplayedExactness: false as const });
}
