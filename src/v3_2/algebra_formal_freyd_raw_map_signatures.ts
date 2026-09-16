/** Exact shared signatures for raw chain maps and complete arrow observations. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, provenance, sourceSpan } from './kernel';
import { CoreLfDeclarationEnvironment } from './lf_declarations';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';

export const FREYD_CHAIN_MAP_MATRIX_ROLES = Object.freeze([
    ['E0', 0, 1], ['D0', 1, 2], ['E1', 3, 4], ['D1', 4, 5],
    ['A2', 0, 3], ['A1', 1, 4], ['A0', 2, 5]
] as const);

export const FORMAL_FREYD_RAW_MAP_SIGNATURE_BINDINGS = Object.freeze({
    bridge_CommRingFreydHomologyChainMap: 'CommRingFreydHomologyChainMap',
    bridge_comm_ring_freyd_chain_map_from_matrices: 'comm_ring_freyd_chain_map_from_matrices',
    bridge_FreydArrowObservation: 'FreydArrowObservation',
    bridge_freyd_raw_arrow_observation: 'freyd_raw_arrow_observation'
});

/** Add raw data only; no model classifier or interpretation is introduced. */
export function extendFormalFreydRawMapSignatures(environment: CoreLfDeclarationEnvironment,
    inputs: readonly AffineFormalZariskiInputDeclaration[] = []
) {
    const p = provenance('derived', 'whole homology map observation signatures');
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term, ('explicit' | 'implicit')?];
    const add = (name: keyof typeof FORMAL_FREYD_RAW_MAP_SIGNATURE_BINDINGS, fields: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (i: number, s: Scope): Term => i === fields.length ? result(s) :
            b.pi(fields[i][0], fields[i][1](s), token => visit(i + 1, { ...s, [fields[i][0]]: token }),
                binderMode(fields[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const grpd = () => b.application('groupoid-universe', []);
    const ring = () => L.tau(b.free('bridge_CommRing'));
    const nat = () => L.tau(b.free('bridge_Nat_grpd'));
    const objectNames = ['S2', 'S1', 'S0', 'T2', 'T1', 'T0'];
    const mapNames = ['sdNext', 'sd', 'tdNext', 'td', 'f2', 'f1', 'f0'];
    const objects: Field[] = objectNames.map(name => [name, s => L.presentationType(s.R), 'implicit']);
    const maps: Field[] = mapNames.map((name, i) => [name,
        s => L.morphismType(s.R, s[objectNames[FREYD_CHAIN_MAP_MATRIX_ROLES[i][1]]], s[objectNames[FREYD_CHAIN_MAP_MATRIX_ROLES[i][2]]])]);
    add('bridge_CommRingFreydHomologyChainMap', [['R', ring, 'implicit'], ...objects, ...maps], grpd);

    const literalFields: Field[] = [['R', ring]];
    for (let i = 0; i < 6; i++) literalFields.push(['n' + i, nat], ['r' + i, nat]);
    for (let i = 0; i < 6; i++) literalFields.push(['P' + i, s => L.tau(L.matrix(s.R, s['n' + i], s['r' + i]))]);
    for (const [name, i, j] of FREYD_CHAIN_MAP_MATRIX_ROLES) literalFields.push(
        [name, s => L.tau(L.matrix(s.R, s['n' + j], s['n' + i]))],
        ['W' + name, s => L.tau(L.matrix(s.R, s['r' + j], s['r' + i]))],
        ['law' + name, s => L.equality(L.matrix(s.R, s['n' + j], s['r' + i]),
            L.comp(s.R, s['n' + j], s['r' + j], s['r' + i], s['P' + j], s['W' + name]),
            L.comp(s.R, s['n' + j], s['n' + i], s['r' + i], s[name], s['P' + i]))]);
    for (const [name, src, target, leftMiddle, leftAfter, leftBefore, rightMiddle, rightAfter, rightBefore] of [
        ['upper', 0, 4, 3, 'E1', 'A2', 1, 'A1', 'E0'],
        ['lower', 1, 5, 4, 'D1', 'A1', 2, 'A0', 'D0']
    ] as const) literalFields.push(
        [name, s => L.tau(L.matrix(s.R, s['r' + target], s['n' + src]))],
        [name + 'Law', s => L.equality(L.matrix(s.R, s['n' + target], s['n' + src]),
            L.comp(s.R, s['n' + target], s['r' + target], s['n' + src], s['P' + target], s[name]),
            L.call('bridge_comm_ring_matrix_sub', [s.R, s['n' + target], s['n' + src],
                L.comp(s.R, s['n' + target], s['n' + leftMiddle], s['n' + src], s[leftAfter], s[leftBefore]),
                L.comp(s.R, s['n' + target], s['n' + rightMiddle], s['n' + src], s[rightAfter], s[rightBefore])]))]);
    add('bridge_comm_ring_freyd_chain_map_from_matrices', literalFields, s => {
        const points = objectNames.map((_, i) => L.presentation(s.R, s['n' + i], s['r' + i], s['P' + i]));
        const values = FREYD_CHAIN_MAP_MATRIX_ROLES.map(([name, i, j]) => L.morphism([s.R,
            s['n' + i], s['r' + i], s['n' + j], s['r' + j], s['P' + i], s['P' + j], s[name], s['W' + name], s['law' + name]]));
        return L.tau(L.call('bridge_CommRingFreydHomologyChainMap', [s.R, ...points, ...values], 7));
    });

    add('bridge_FreydArrowObservation', [['R', ring]], grpd);
    add('bridge_freyd_raw_arrow_observation', [['R', ring, 'implicit'], ['A', s => L.presentationType(s.R), 'implicit'],
        ['B', s => L.presentationType(s.R), 'implicit'], ['f', s => L.morphismType(s.R, s.A, s.B)]],
    s => L.tau(L.call('bridge_FreydArrowObservation', [s.R])));
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'model-map input ' + input.name,
                sourceSpan('generated/formal-freyd-model-map-inputs.ts', index + 1, 1)) });
    });
    return environment;
}
