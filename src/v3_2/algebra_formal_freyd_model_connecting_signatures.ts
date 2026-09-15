/** Exact private LF signatures for the native whole-δ observation at retained H objects. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, KernelExpression, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { createFormalFreydModelMapProofEnvironment } from './algebra_formal_freyd_model_map_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';

export const FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS = Object.freeze({
    bridge_FreydHomologyModelNativeNormality: 'FreydHomologyModelNativeNormality',
    bridge_FreydHomologyModelNativeShortExact: 'FreydHomologyModelNativeShortExact',
    bridge_freyd_homology_model_native_connecting_observation: 'freyd_homology_model_native_connecting_observation'
});

export const FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-model-connecting-signatures-v2' as const,
    policy: 'exact-opaque-signature-mirrors' as const,
    sourceOperations: 'native-whole-delta-at-retained-H-endpoints' as const,
    requiresSuppliedNormality: true as const,
    normality: 'native-whole-Coim-Im' as const,
    rowUniversality: 'native-whole-PQ' as const,
    requiresModelShortExactness: true as const,
    constructsModel: false as const,
    infersClosedCapabilityFromRawAgreements: false as const,
    addsCoreOwner: false as const,
    addsRuntimeRule: false as const
});

const rows = [
    ['Am', 'Bm', 'Dm', 'im', 'pm', 'cm', 'xm'],
    ['A0', 'B0', 'D0', 'i0', 'p0', 'c0', 'x0'],
    ['A1', 'B1', 'D1', 'i1', 'p1', 'c1', 'x1'],
    ['A2', 'B2', 'D2', 'i2', 'p2', 'c2', 'x2']
] as const;
const maps = [
    [0, 1, 'am', 'bm', 'dm', 'fm'],
    [1, 2, 'a0', 'b0', 'd0', 'gm'],
    [2, 3, 'a1', 'b1', 'd1', 'jm']
] as const;
const chains = [
    ['upper', 'Bm', 'B0', 'B1', 'bm', 'b0'],
    ['lower', 'B0', 'B1', 'B2', 'b0', 'b1'],
    ['source_chain', 'Dm', 'D0', 'D1', 'dm', 'd0'],
    ['target_chain', 'A0', 'A1', 'A2', 'a0', 'a1']
] as const;

/** Exact source order; the model and normality precede the implicit objects. */
export const FREYD_MODEL_CONNECTING_ARGUMENTS = Object.freeze([
    { name: 'R', implicit: true }, { name: 'M', implicit: false }, { name: 'N', implicit: false },
    ...rows.flatMap(row => row.slice(0, 3).map(name => ({ name, implicit: true }))),
    ...rows.flatMap(row => row.slice(3).map(name => ({ name, implicit: false }))),
    ...maps.flatMap(map => map.slice(2).map(name => ({ name: String(name), implicit: false }))),
    ...chains.map(chain => ({ name: chain[0], implicit: false }))
].map(value => Object.freeze(value)));

export function algebraFormalFreydModelNormalityType(R: KernelExpression, M: KernelExpression): KernelExpression {
    const b = new CoreLfScopedBuilder(provenance('derived', 'supplied native whole model normality'));
    const L = formalFreydSpineLanguage(b);
    return b.lower(L.tau(L.call('bridge_FreydHomologyModelNativeNormality', [b.embed(R), b.embed(M)], 1)));
}

export function algebraFormalFreydModelConnectingObservationTerm(
    values: Readonly<Record<string, KernelExpression>>
): KernelExpression {
    const expected = new Set(FREYD_MODEL_CONNECTING_ARGUMENTS.map(field => field.name));
    if (Object.keys(values).some(name => !expected.has(name)) ||
        FREYD_MODEL_CONNECTING_ARGUMENTS.some(field => values[field.name] === undefined)) {
        throw new Error('Supply every exact model-connecting argument and no foreign field');
    }
    const b = new CoreLfScopedBuilder(provenance('derived', 'native whole connecting observation at retained H'));
    return b.lower(b.call(b.free('bridge_freyd_homology_model_native_connecting_observation'),
        FREYD_MODEL_CONNECTING_ARGUMENTS.map(field => ({ value: b.embed(values[field.name]),
            plicity: field.implicit ? 'implicit' as const : 'explicit' as const }))));
}

export function createFormalFreydModelConnectingProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydModelMapProofEnvironment([]);
    const p = provenance('derived', 'native whole connecting signatures');
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term, ('explicit' | 'implicit')?];
    const add = (name: keyof typeof FORMAL_FREYD_MODEL_CONNECTING_SIGNATURE_BINDINGS,
        fields: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (i: number, s: Scope): Term => i === fields.length ? result(s) :
            b.pi(fields[i][0], fields[i][1](s), value => visit(i + 1, { ...s, [fields[i][0]]: value }),
                binderMode(fields[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})),
            mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const ring = () => L.tau(b.free('bridge_CommRing'));
    const model = (s: Scope) => L.tau(L.call('bridge_FreydHomologyModel', [s.R]));
    const grpd = () => b.application('groupoid-universe', []);
    const short = (s: Scope, A: string, B: string, D: string, e: string, d: string, chain: string) =>
        L.tau(b.call(b.free('bridge_FreydHomologyModelNativeShortExact'),
            [s.R, s.M, s[A], s[B], s[D], s[e], s[d], s[chain]].map((value, i) => ({ value,
                plicity: [0, 2, 3, 4].includes(i) ? 'implicit' as const : 'explicit' as const }))));
    add('bridge_FreydHomologyModelNativeNormality', [['R', ring, 'implicit'], ['M', model]], grpd);
    add('bridge_FreydHomologyModelNativeShortExact', [['R', ring, 'implicit'], ['M', model],
        ...['A', 'B', 'D'].map(name => [name, (s: Scope) => L.presentationType(s.R), 'implicit'] as Field),
        ['e', s => L.morphismType(s.R, s.A, s.B)], ['d', s => L.morphismType(s.R, s.B, s.D)],
        ['chain', s => L.chainType(s.R, s.A, s.B, s.D, s.e, s.d)]], grpd);
    const fields: Field[] = [['R', ring, 'implicit'], ['M', model],
        ['N', s => L.tau(L.call('bridge_FreydHomologyModelNativeNormality', [s.R, s.M], 1))]];
    rows.forEach(row => row.slice(0, 3).forEach(name => fields.push([name, s => L.presentationType(s.R), 'implicit'])));
    for (const [A, B, D, e, d, chain, exact] of rows) fields.push(
        [e, s => L.morphismType(s.R, s[A], s[B])], [d, s => L.morphismType(s.R, s[B], s[D])],
        [chain, s => L.chainType(s.R, s[A], s[B], s[D], s[e], s[d])],
        [exact, s => short(s, A, B, D, e, d, chain)]);
    for (const [from, to, a, bb, d, law] of maps) {
        const source = rows[from], target = rows[to];
        [a, bb, d].forEach((name, i) => fields.push([name, s => L.morphismType(s.R, s[source[i]], s[target[i]])]));
        fields.push([law, s => L.tau(L.call('bridge_CommRingFreydHomologyChainMap', [s.R,
            ...source.slice(0, 3).map(n => s[n]), ...target.slice(0, 3).map(n => s[n]),
            s[source[3]], s[source[4]], s[target[3]], s[target[4]], s[a], s[bb], s[d]], 7))]);
    }
    chains.forEach(([name, A, B, D, e, d]) => fields.push([name, s => L.chainType(s.R, s[A], s[B], s[D], s[e], s[d])]));
    add('bridge_freyd_homology_model_native_connecting_observation', fields,
        s => L.tau(L.call('bridge_FreydArrowObservation', [s.R])));
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'model-connecting input ' + input.name,
                sourceSpan('generated/formal-freyd-model-connecting.ts', index + 1, 1)) });
    });
    return environment;
}
