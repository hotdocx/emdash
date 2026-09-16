/** Certify every actual displayed LES pair using the retained native window proofs. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalAssumptionSource, validateAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { trustAlgebraFormalFreydNativeConnecting } from './algebra_formal_freyd_native_connecting_workflow';
import { trustAlgebraFormalFreydNativeHomologyMap } from './algebra_formal_freyd_native_map_workflow';
import { constructAlgebraFormalFreydDiagramCoherence } from './algebra_formal_freyd_diagram_coherence';
import { createFormalFreydNativeLesCertificateProofEnvironment, formalFreydNativeLesPairFields,
    FORMAL_FREYD_NATIVE_LES_CERTIFICATE_SIGNATURE_BINDINGS, FreydNativeLesPairPosition } from './algebra_formal_freyd_native_les_certificate_signatures';
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { createCoreProofChecker } from './proof_checker';

type MapEntry<P extends AlgebraParent, C extends AlgebraElement<P>, I> = {
    readonly entry: { readonly degree: number; readonly role: 'inclusion' | 'projection'; readonly position?: number };
    readonly result: Awaited<ReturnType<typeof trustAlgebraFormalFreydNativeHomologyMap<P, C, I>>>;
};
type WindowEntry<P extends AlgebraParent, C extends AlgebraElement<P>, I> = {
    readonly entry: { readonly degree: number; readonly position: number };
    readonly result: Awaited<ReturnType<typeof trustAlgebraFormalFreydNativeConnecting<P, C, I>>>;
};
type Displayed<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    (MapEntry<P, C, I> & { readonly kind: 'map' }) | (WindowEntry<P, C, I> & { readonly kind: 'connecting' });

export function constructAlgebraFormalFreydNativeDisplayedExactness<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly source: AlgebraFormalAssumptionSource;
    readonly formalRing: KernelExpression;
    readonly formalModel: KernelExpression;
    readonly normality: KernelExpression;
    readonly maps: readonly MapEntry<P, C, I>[];
    readonly windows: readonly WindowEntry<P, C, I>[];
    readonly displayed: readonly Displayed<P, C, I>[];
    readonly coherence: ReturnType<typeof constructAlgebraFormalFreydDiagramCoherence>;
}) {
    const source = validateAlgebraFormalAssumptionSource(input.source);
    if (input.coherence.source !== source || input.displayed.length === 0 ||
        input.coherence.arrows.length !== input.displayed.length) throw new Error('Retain the original nonempty coherent LES diagram');
    const expected = createFormalFreydNativeLesCertificateProofEnvironment([]);
    for (const name of Object.keys(FORMAL_FREYD_NATIVE_LES_CERTIFICATE_SIGNATURE_BINDINGS)) {
        const actual = source.environment.lookup(name);
        if (!actual || actual.body !== undefined || !kernelExpressionEquals(actual.type, expected.lookup(name)!.type)) {
            throw new Error('Missing or changed native LES certificate signature ' + name);
        }
    }
    const mapAt = (degree: number, role: 'inclusion' | 'projection') => {
        const matches = input.maps.filter(m => m.entry.degree === degree && m.entry.role === role);
        if (matches.length !== 1) throw new Error('Require one retained LES map at ' + degree + '/' + role);
        const result = matches[0].result;
        result.observation.adapter.normalizeRealization(result.observation.realization, 'nativeLES.exactness.map');
        return result.observation.realization;
    };
    const windowAt = (degree: number) => {
        const matches = input.windows.filter(w => w.entry.degree === degree);
        if (matches.length !== 1) throw new Error('Require one retained LES window at degree ' + degree);
        const result = matches[0].result;
        result.observation.adapter.normalizeRealization(result.observation.realization, 'nativeLES.exactness.window');
        const v = result.observation.realization.values;
        if (!kernelExpressionEquals(v.R, input.formalRing) || !kernelExpressionEquals(v.M, input.formalModel) ||
            !kernelExpressionEquals(v.N, input.normality)) throw new Error('Retain the original LES ring, model and normality');
        return v;
    };
    input.displayed.forEach((a, i) => {
        const r = a.result.observation.realization, original = input.coherence.arrows[i];
        if (a.entry.position !== i || !kernelExpressionEquals(r.formalArrow, original.formalArrow) ||
            !kernelExpressionEquals(r.nativeArrow, original.nativeArrow) || !kernelExpressionEquals(a.result.proof, original.proof)) {
            throw new Error('Changed displayed LES arrow or interpretation at ' + i);
        }
    });
    const b = new CoreLfScopedBuilder(provenance('derived', 'native displayed LES exactness')), L = formalFreydSpineLanguage(b);
    const R = b.embed(input.formalRing), M = b.embed(input.formalModel), N = b.embed(input.normality);
    const checker = createCoreProofChecker(source.environment);
    const pairs: { readonly position: number; readonly kind: FreydNativeLesPairPosition; readonly degree: number;
        readonly input: KernelExpression; readonly term: KernelExpression; readonly type: KernelExpression }[] = [];
    for (let i = 0; i + 1 < input.displayed.length; i++) {
        const a = input.displayed[i], c = input.displayed[i + 1];
        let kind: FreydNativeLesPairPosition, degree: number, values: Record<string, KernelExpression>;
        if (a.kind === 'map' && c.kind === 'map' && a.entry.role === 'inclusion' && c.entry.role === 'projection' &&
            a.entry.degree === c.entry.degree) {
            kind = 'middle'; degree = a.entry.degree;
            const v = windowAt(degree), inc = mapAt(degree, 'inclusion'), proj = mapAt(degree, 'projection');
            values = { R: v.R, M: v.M, N: v.N, middle: v.upper, left_chain: inc.source.pair.term,
                right_chain: proj.target.pair.term, incoming_map: inc.chain.term, outgoing_map: proj.chain.term };
            ['m', '0', '1'].forEach((suffix, row) => {
                for (const letter of ['A', 'B', 'D', 'i', 'p', 'c']) values[letter + row] = v[letter + suffix];
                values['E' + row] = v['x' + suffix];
            });
            ['m', '0'].forEach((suffix, row) => {
                for (const letter of ['a', 'b', 'd']) values[letter + row] = v[letter + suffix];
                values['f' + row] = v[row === 0 ? 'fm' : 'gm'];
            });
        } else if (a.kind === 'map' && a.entry.role === 'projection' && c.kind === 'connecting' && a.entry.degree === c.entry.degree) {
            kind = 'source'; degree = c.entry.degree;
            values = { ...windowAt(degree), unused_left_chain: mapAt(degree, 'inclusion').source.pair.term,
                column_map: mapAt(degree, 'projection').chain.term };
        } else if (a.kind === 'connecting' && c.kind === 'map' && c.entry.role === 'inclusion' && c.entry.degree === a.entry.degree - 1) {
            kind = 'target'; degree = a.entry.degree;
            values = { ...windowAt(degree), bottom_right_chain: mapAt(degree - 1, 'projection').target.pair.term,
                column_map: mapAt(degree - 1, 'inclusion').chain.term };
        } else throw new Error('Unsupported or reordered displayed LES pair at ' + i);
        const args = formalFreydNativeLesPairFields(b, kind).map(([name, , mode]) => {
            if (values[name] === undefined) throw new Error('Missing retained LES argument ' + name);
            return { value: b.embed(values[name]), plicity: mode === 'implicit' ? 'implicit' as const : 'explicit' as const };
        });
        const X = b.call(b.free('bridge_freyd_native_model_' + kind + '_pair_input'), args);
        const edge0 = b.embed(a.result.observation.realization.nativeArrow), edge1 = b.embed(c.result.observation.realization.nativeArrow);
        const term = b.call(b.free('bridge_freyd_native_model_' + kind + '_pair_exact_at'), [...args,
            { value: edge0, plicity: 'implicit' }, { value: edge1, plicity: 'implicit' },
            { value: b.embed(a.result.proof), plicity: 'explicit' }, { value: b.embed(c.result.proof), plicity: 'explicit' }]);
        const type = L.tau(L.call('bridge_FreydNativeObservedPairExactAt', [R, M, N, X, edge0, edge1], 1));
        const data = { position: i + 1, kind, degree, input: b.lower(X), term: b.lower(term), type: b.lower(type) };
        checker.check(checker.rootContext, data.input, b.lower(L.tau(L.call('bridge_FreydNativeInput', [R]))));
        checker.check(checker.rootContext, data.term, data.type);
        pairs.push(Object.freeze(data));
    }
    const arrows = input.displayed.map(a => b.embed(a.result.observation.realization.nativeArrow));
    const obs = L.call('bridge_FreydArrowObservation', [R]), nativeInput = L.call('bridge_FreydNativeInput', [R]);
    let inputs = L.call('bridge_finite_family_nil', [nativeInput], 1);
    let tail = L.call('bridge_finite_family_nil', [obs], 1);
    let evidence = L.call('bridge_freyd_native_observed_exact_tail_nil', [R, M, N, arrows[arrows.length - 1]], 1);
    const call = (name: string, values: readonly Term[], implicit: readonly number[]) => b.call(b.free(name),
        values.map((value, i) => ({ value, plicity: implicit.includes(i) ? 'implicit' as const : 'explicit' as const })));
    for (let i = pairs.length - 1; i >= 0; i--) {
        const n = L.nat(pairs.length - 1 - i), X = b.embed(pairs[i].input);
        evidence = call('bridge_freyd_native_observed_exact_tail_cons',
            [R, M, N, n, X, inputs, arrows[i], arrows[i + 1], tail, b.embed(pairs[i].term), evidence], [0, 3, 4, 5, 6, 7, 8]);
        inputs = L.call('bridge_finite_family_cons', [nativeInput, n, X, inputs], 2);
        tail = L.call('bridge_finite_family_cons', [obs, n, arrows[i + 1], tail], 2);
    }
    const n = L.nat(pairs.length), matching = b.embed(input.coherence.nativeMatching);
    const term = call('bridge_freyd_native_exact_diagram_intro', [R, M, N, n, inputs, arrows[0], tail, matching, evidence], [0, 3]);
    const type = L.tau(L.call('bridge_FreydNativeDiagramExactness', [R, M, N, n, inputs, b.embed(input.coherence.nativeDiagram)], 1));
    const proof = b.lower(term), proofType = b.lower(type);
    checker.check(checker.rootContext, proof, proofType);
    return Object.freeze({ source, diagram: input.coherence.nativeDiagram, inputs: b.lower(inputs),
        pairs: Object.freeze(pairs), proof, type: proofType,
        assumptionsAdded: 0 as const, trustDecisions: 0 as const, provesDisplayedCasExactness: true as const });
}
