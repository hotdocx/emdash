/** Private mirrors of native H observations; the whole H stays in Lambdapi. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { createFormalFreydNativeModelProofEnvironment } from './algebra_formal_freyd_native_model_signatures';
import { createFormalFreydModelMapProofEnvironment, FREYD_CHAIN_MAP_MATRIX_ROLES } from './algebra_formal_freyd_model_map_signatures';

export const FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS = Object.freeze({
    bridge_CommRingFreydHomologyChainMap: 'CommRingFreydHomologyChainMap',
    bridge_comm_ring_freyd_chain_map_from_matrices: 'comm_ring_freyd_chain_map_from_matrices',
    bridge_CommRingFreydHomSet: 'CommRingFreydHomSet',
    bridge_freyd_adjunction_model_object: 'freyd_adjunction_model_object',
    bridge_freyd_adjunction_model_map: 'freyd_adjunction_model_map',
    bridge_FreydArrowObservation: 'FreydArrowObservation',
    bridge_freyd_raw_arrow_observation: 'freyd_raw_arrow_observation',
    bridge_freyd_adjunction_model_arrow_observation: 'freyd_adjunction_model_arrow_observation'
});

export function createFormalFreydNativeModelObservationProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydNativeModelProofEnvironment([]);
    // These raw-data constructors are independent of any model. Reuse
    // their exact existing mirrors; do not import the legacy model signatures.
    const rawMaps = createFormalFreydModelMapProofEnvironment([]);
    for (const name of ['bridge_CommRingFreydHomologyChainMap', 'bridge_comm_ring_freyd_chain_map_from_matrices',
        'bridge_FreydArrowObservation', 'bridge_freyd_raw_arrow_observation']) {
        environment = environment.extend(rawMaps.lookup(name)!);
    }
    const p = provenance('derived', 'native whole H observation signatures');
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term, ('explicit' | 'implicit')?];
    const add = (name: keyof typeof FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS,
        fields: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (i: number, s: Scope): Term => i === fields.length ? result(s) :
            b.pi(fields[i][0], fields[i][1](s), v => visit(i + 1, { ...s, [fields[i][0]]: v }),
                binderMode(fields[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const ring = () => L.tau(b.free('bridge_CommRing'));
    const model = (s: Scope) => L.tau(L.call('bridge_FreydAdjunctionModel', [s.R]));
    add('bridge_CommRingFreydHomSet', [['R', ring], ['P', s => L.presentationType(s.R)], ['Q', s => L.presentationType(s.R)]],
        () => b.application('groupoid-universe', []));
    add('bridge_freyd_adjunction_model_object', [['R', ring, 'implicit'], ['M', model],
        ...['A', 'B', 'D'].map(name => [name, (s: Scope) => L.presentationType(s.R), 'implicit'] as Field),
        ['e', s => L.morphismType(s.R, s.A, s.B)], ['d', s => L.morphismType(s.R, s.B, s.D)],
        ['chain', s => L.chainType(s.R, s.A, s.B, s.D, s.e, s.d)]], s => L.presentationType(s.R));
    const objects = ['S2', 'S1', 'S0', 'T2', 'T1', 'T0'];
    const maps = ['sdNext', 'sd', 'tdNext', 'td', 'f2', 'f1', 'f0'];
    const H = (s: Scope, source: boolean) => b.call(b.free('bridge_freyd_adjunction_model_object'),
        [s.R, s.M, ...(source ? [s.S2, s.S1, s.S0, s.sdNext, s.sd, s.chainS] :
            [s.T2, s.T1, s.T0, s.tdNext, s.td, s.chainT])].map((value, i) => ({ value,
            plicity: ([0, 2, 3, 4].includes(i) ? 'implicit' : 'explicit') as 'implicit' | 'explicit' })));
    const mapFields: Field[] = [['R', ring, 'implicit'], ['M', model],
        ...objects.map(name => [name, (s: Scope) => L.presentationType(s.R), 'implicit'] as Field),
        ...maps.map((name, i) => [name, (s: Scope) => L.morphismType(s.R,
            s[objects[FREYD_CHAIN_MAP_MATRIX_ROLES[i][1]]], s[objects[FREYD_CHAIN_MAP_MATRIX_ROLES[i][2]]]), 'implicit'] as Field),
        ['chainS', s => L.chainType(s.R, s.S2, s.S1, s.S0, s.sdNext, s.sd)],
        ['chainT', s => L.chainType(s.R, s.T2, s.T1, s.T0, s.tdNext, s.td)],
        ['m', s => L.tau(L.call('bridge_CommRingFreydHomologyChainMap', [s.R, ...objects.map(n => s[n]), ...maps.map(n => s[n])], 7))]];
    add('bridge_freyd_adjunction_model_map', mapFields, s => L.tau(L.call('bridge_CommRingFreydHomSet', [s.R, H(s, true), H(s, false)])));
    add('bridge_freyd_adjunction_model_arrow_observation', mapFields,
        s => L.tau(L.call('bridge_FreydArrowObservation', [s.R])));
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'native H observation input ' + input.name,
                sourceSpan('generated/formal-freyd-native-homology-inputs.ts', index + 1, 1)) });
    });
    return environment;
}
