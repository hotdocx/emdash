/** Private mirrors of fixed-input native LES observation certificates. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { createFormalFreydExactnessPointProofEnvironment } from './algebra_formal_freyd_exactness_point_signatures';
import { formalFreydWindowFields, FormalFreydWindowField, FormalFreydWindowScope,
    FREYD_MODEL_CONNECTING_ARGUMENTS } from './algebra_formal_freyd_model_connecting_signatures';

export const FREYD_NATIVE_LES_PAIR_POSITIONS = Object.freeze(['middle', 'source', 'target'] as const);
export type FreydNativeLesPairPosition = (typeof FREYD_NATIVE_LES_PAIR_POSITIONS)[number];
const commonNames = ['FreydNativeInput', 'FreydNativeObservedPairExactAt', 'FreydNativeObservedExactTail',
    'freyd_native_observed_exact_tail_nil', 'freyd_native_observed_exact_tail_cons',
    'FreydNativeDiagramExactness', 'freyd_native_exact_diagram_intro'];
export const FORMAL_FREYD_NATIVE_LES_CERTIFICATE_SIGNATURE_BINDINGS: Readonly<Record<string, string>> = Object.freeze(
    Object.fromEntries([...commonNames, ...FREYD_NATIVE_LES_PAIR_POSITIONS.flatMap(p => [
        'freyd_native_model_' + p + '_pair_input', 'freyd_native_model_' + p + '_pair_exact_at'
    ])].map(name => ['bridge_' + name, name])));

type Scope = FormalFreydWindowScope;
type Field = FormalFreydWindowField;
const nativeNames = { model: 'bridge_FreydAdjunctionModel', normality: 'bridge_FreydAdjunctionModelNormality',
    shortExact: 'bridge_FreydAdjunctionModelRowShortExact' };

/** Match the checked mathematical telescope; no K/x argument is reconstructed externally. */
export function formalFreydNativeLesPairFields(b: CoreLfScopedBuilder, position: FreydNativeLesPairPosition): readonly Field[] {
    const L = formalFreydSpineLanguage(b);
    const cm = (s: Scope, ns: readonly string[]) => L.tau(L.call('bridge_CommRingFreydHomologyChainMap',
        [s.R, ...ns.map(n => s[n])], 7));
    if (position !== 'middle') return [...formalFreydWindowFields(b, nativeNames),
        position === 'source'
            ? ['unused_left_chain', (s: Scope) => L.chainType(s.R, s.Am, s.A0, s.A1, s.am, s.a0)] as Field
            : ['bottom_right_chain', (s: Scope) => L.chainType(s.R, s.D0, s.D1, s.D2, s.d0, s.d1)] as Field,
        ['column_map', s => cm(s, position === 'source'
            ? ['Bm', 'B0', 'B1', 'Dm', 'D0', 'D1', 'bm', 'b0', 'dm', 'd0', 'pm', 'p0', 'p1']
            : ['A0', 'A1', 'A2', 'B0', 'B1', 'B2', 'a0', 'a1', 'b0', 'b1', 'i0', 'i1', 'i2'])]
    ];
    const fields: Field[] = [['R', () => L.tau(b.free('bridge_CommRing')), 'implicit'],
        ['M', s => L.tau(L.call(nativeNames.model, [s.R]))]];
    for (const i of [0, 1, 2]) for (const letter of ['A', 'B', 'D']) fields.push([
        letter + i, s => L.presentationType(s.R), 'implicit']);
    for (const i of [0, 1, 2]) fields.push(
        ['i' + i, s => L.morphismType(s.R, s['A' + i], s['B' + i]), 'implicit'],
        ['p' + i, s => L.morphismType(s.R, s['B' + i], s['D' + i]), 'implicit']);
    for (const i of [0, 1, 2]) fields.push(['c' + i, s => L.chainType(s.R,
        s['A' + i], s['B' + i], s['D' + i], s['i' + i], s['p' + i])]);
    for (const i of [0, 1]) for (const [a, A] of [['a', 'A'], ['b', 'B'], ['d', 'D']]) fields.push([
        a + i, s => L.morphismType(s.R, s[A + i], s[A + (i + 1)]), 'implicit']);
    for (const i of [0, 1]) fields.push(['f' + i, s => cm(s, [
        'A' + i, 'B' + i, 'D' + i, 'A' + (i + 1), 'B' + (i + 1), 'D' + (i + 1),
        'i' + i, 'p' + i, 'i' + (i + 1), 'p' + (i + 1), 'a' + i, 'b' + i, 'd' + i])]);
    fields.push(['middle', s => L.chainType(s.R, s.B0, s.B1, s.B2, s.b0, s.b1)]);
    for (const i of [0, 1, 2]) fields.push(['E' + i, s => L.tau(b.call(b.free(nativeNames.shortExact),
        [s.R, s.M, s['A' + i], s['B' + i], s['D' + i], s['i' + i], s['p' + i], s['c' + i]]
            .map((value, j) => ({ value, plicity: [0, 2, 3, 4].includes(j) ? 'implicit' as const : 'explicit' as const }))))]);
    fields.push(['left_chain', s => L.chainType(s.R, s.A0, s.A1, s.A2, s.a0, s.a1)],
        ['right_chain', s => L.chainType(s.R, s.D0, s.D1, s.D2, s.d0, s.d1)],
        ['incoming_map', s => cm(s, ['A0', 'A1', 'A2', 'B0', 'B1', 'B2', 'a0', 'a1', 'b0', 'b1', 'i0', 'i1', 'i2'])],
        ['outgoing_map', s => cm(s, ['B0', 'B1', 'B2', 'D0', 'D1', 'D2', 'b0', 'b1', 'd0', 'd1', 'p0', 'p1', 'p2'])],
        ['N', s => L.tau(L.call(nativeNames.normality, [s.R, s.M], 1))]);
    return fields;
}

export function createFormalFreydNativeLesCertificateProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydExactnessPointProofEnvironment([]);
    const p = provenance('derived', 'native LES certificate signatures'), b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    const grpd = () => b.application('groupoid-universe', []);
    const add = (name: string, fields: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (i: number, s: Scope): Term => i === fields.length ? result(s) :
            b.pi(fields[i][0], fields[i][1](s), value => visit(i + 1, { ...s, [fields[i][0]]: value }),
                binderMode(fields[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const common: Field[] = [['R', () => L.tau(b.free('bridge_CommRing')), 'implicit'],
        ['M', s => L.tau(L.call(nativeNames.model, [s.R]))],
        ['N', s => L.tau(L.call(nativeNames.normality, [s.R, s.M], 1))]];
    const obs = (s: Scope) => L.call('bridge_FreydArrowObservation', [s.R]);
    const input = (s: Scope) => L.call('bridge_FreydNativeInput', [s.R]);
    const family = (A: Term, n: Term) => L.call('bridge_FiniteFamily', [A, n]);
    const cons = (A: Term, n: Term, a: Term, xs: Term) => L.call('bridge_finite_family_cons', [A, n, a, xs], 2);
    const tail = (s: Scope, n: Term, xs: Term, a: Term, arrows: Term) =>
        L.call('bridge_FreydNativeObservedExactTail', [s.R, s.M, s.N, n, xs, a, arrows], 1);
    const pair = (s: Scope, x: Term, a: Term, c: Term) =>
        L.call('bridge_FreydNativeObservedPairExactAt', [s.R, s.M, s.N, x, a, c], 1);
    const nat: Field = ['n', () => L.tau(b.free('bridge_Nat_grpd'))];
    add('bridge_FreydNativeInput', [['R', common[0][1]]], grpd);
    add('bridge_FreydNativeObservedPairExactAt', [...common, ['X', s => L.tau(input(s))],
        ['a0', s => L.tau(obs(s))], ['a1', s => L.tau(obs(s))]], grpd);
    add('bridge_FreydNativeObservedExactTail', [...common, nat, ['inputs', s => L.tau(family(input(s), s.n))],
        ['first', s => L.tau(obs(s))], ['arrows', s => L.tau(family(obs(s), s.n))]], grpd);
    add('bridge_freyd_native_observed_exact_tail_nil', [...common, ['first', s => L.tau(obs(s))]],
        s => L.tau(tail(s, L.nat(0), L.call('bridge_finite_family_nil', [input(s)], 1), s.first,
            L.call('bridge_finite_family_nil', [obs(s)], 1))));
    add('bridge_freyd_native_observed_exact_tail_cons', [...common, ['n', nat[1], 'implicit'],
        ['X0', s => L.tau(input(s)), 'implicit'], ['inputs', s => L.tau(family(input(s), s.n)), 'implicit'],
        ['a0', s => L.tau(obs(s)), 'implicit'], ['a1', s => L.tau(obs(s)), 'implicit'],
        ['arrows', s => L.tau(family(obs(s), s.n)), 'implicit'], ['E', s => L.tau(pair(s, s.X0, s.a0, s.a1))],
        ['rest', s => L.tau(tail(s, s.n, s.inputs, s.a1, s.arrows))]],
        s => L.tau(tail(s, L.call('bridge_nat_succ', [s.n]), cons(input(s), s.n, s.X0, s.inputs), s.a0,
            cons(obs(s), s.n, s.a1, s.arrows))));
    const diagram = (s: Scope) => L.call('bridge_FreydArrowObservationDiagram', [s.R, s.n]);
    add('bridge_FreydNativeDiagramExactness', [...common, nat, ['inputs', s => L.tau(family(input(s), s.n))],
        ['d', s => L.tau(diagram(s))]], grpd);
    add('bridge_freyd_native_exact_diagram_intro', [...common, ['n', nat[1], 'implicit'],
        ['inputs', s => L.tau(family(input(s), s.n))], ['first', s => L.tau(obs(s))],
        ['arrows', s => L.tau(family(obs(s), s.n))],
        ['matching', s => L.tau(L.call('bridge_FreydArrowMatchingTail', [s.R, s.first, s.n, s.arrows], 1))],
        ['E', s => L.tau(tail(s, s.n, s.inputs, s.first, s.arrows))]],
        s => L.tau(L.call('bridge_FreydNativeDiagramExactness', [s.R, s.M, s.N, s.n, s.inputs,
            L.call('bridge_freyd_arrow_diagram_intro', [s.R, s.n, s.first, s.arrows, s.matching], 2)], 1)));
    const delta = (s: Scope) => b.call(b.free('bridge_freyd_adjunction_model_connecting_observation'),
        FREYD_MODEL_CONNECTING_ARGUMENTS.map(f => ({ value: s[f.name], plicity: f.implicit ? 'implicit' as const : 'explicit' as const })));
    const map = (s: Scope, names: readonly string[]) => b.call(b.free('bridge_freyd_adjunction_model_arrow_observation'),
        [s.R, s.M, ...names.map(name => s[name])].map((value, i) => ({ value,
            plicity: i === 0 || (i >= 2 && i <= 14) ? 'implicit' as const : 'explicit' as const })));
    for (const position of FREYD_NATIVE_LES_PAIR_POSITIONS) {
        const fs = formalFreydNativeLesPairFields(b, position);
        const args = (s: Scope) => fs.map(([name, , mode]) => ({ value: s[name],
            plicity: mode === 'implicit' ? 'implicit' as const : 'explicit' as const }));
        const nativeInput = (s: Scope) => b.call(b.free('bridge_freyd_native_model_' + position + '_pair_input'), args(s));
        add('bridge_freyd_native_model_' + position + '_pair_input', fs, s => L.tau(input(s)));
        const arrows = (s: Scope) => position === 'middle' ? [
            map(s, ['A0', 'A1', 'A2', 'B0', 'B1', 'B2', 'a0', 'a1', 'b0', 'b1', 'i0', 'i1', 'i2', 'left_chain', 'middle', 'incoming_map']),
            map(s, ['B0', 'B1', 'B2', 'D0', 'D1', 'D2', 'b0', 'b1', 'd0', 'd1', 'p0', 'p1', 'p2', 'middle', 'right_chain', 'outgoing_map'])
        ] : position === 'source' ? [
            map(s, ['Bm', 'B0', 'B1', 'Dm', 'D0', 'D1', 'bm', 'b0', 'dm', 'd0', 'pm', 'p0', 'p1', 'upper', 'source_chain', 'column_map']), delta(s)
        ] : [delta(s), map(s, ['A0', 'A1', 'A2', 'B0', 'B1', 'B2', 'a0', 'a1', 'b0', 'b1', 'i0', 'i1', 'i2', 'target_chain', 'lower', 'column_map'])];
        add('bridge_freyd_native_model_' + position + '_pair_exact_at', [...fs,
            ['edge0', s => L.tau(obs(s)), 'implicit'], ['edge1', s => L.tau(obs(s)), 'implicit'],
            ['p', s => L.equality(obs(s), arrows(s)[0], s.edge0)],
            ['q', s => L.equality(obs(s), arrows(s)[1], s.edge1)]],
            s => L.tau(pair(s, nativeInput(s), s.edge0, s.edge1)));
    }
    inputs.forEach((input, i) => { environment = environment.extend({ ...input,
        mode: input.mode ?? binderMode('explicit', 'functorial'), provenance: provenance('surface',
            'native LES certificate input ' + input.name, sourceSpan('generated/native-les-certificate-inputs.ts', i + 1, 1)) }); });
    return environment;
}
