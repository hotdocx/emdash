/** Exact matrix-entry and complete-arrow observation signature mirrors. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { createFormalFreydModelProofEnvironment } from './algebra_formal_freyd_model_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { FORMAL_FREYD_RAW_MAP_SIGNATURE_BINDINGS, FREYD_CHAIN_MAP_MATRIX_ROLES,
    extendFormalFreydRawMapSignatures } from './algebra_formal_freyd_raw_map_signatures';

export { FREYD_CHAIN_MAP_MATRIX_ROLES } from './algebra_formal_freyd_raw_map_signatures';

export const FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS = Object.freeze({
    ...FORMAL_FREYD_RAW_MAP_SIGNATURE_BINDINGS,
    bridge_freyd_homology_model_arrow_observation: 'freyd_homology_model_arrow_observation'
});

export function createFormalFreydModelMapProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = extendFormalFreydRawMapSignatures(createFormalFreydModelProofEnvironment([]));
    const p = provenance('derived', 'whole homology map observation signatures');
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term, ('explicit' | 'implicit')?];
    const add = (name: keyof typeof FORMAL_FREYD_MODEL_MAP_SIGNATURE_BINDINGS, fields: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (i: number, s: Scope): Term => i === fields.length ? result(s) :
            b.pi(fields[i][0], fields[i][1](s), token => visit(i + 1, { ...s, [fields[i][0]]: token }),
                binderMode(fields[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const ring = () => L.tau(b.free('bridge_CommRing'));
    const objectNames = ['S2', 'S1', 'S0', 'T2', 'T1', 'T0'];
    const mapNames = ['sdNext', 'sd', 'tdNext', 'td', 'f2', 'f1', 'f0'];
    const objects: Field[] = objectNames.map(name => [name, s => L.presentationType(s.R), 'implicit']);
    const maps: Field[] = mapNames.map((name, i) => [name,
        s => L.morphismType(s.R, s[objectNames[FREYD_CHAIN_MAP_MATRIX_ROLES[i][1]]], s[objectNames[FREYD_CHAIN_MAP_MATRIX_ROLES[i][2]]])]);
    const chainMap = (s: Scope) => L.tau(L.call('bridge_CommRingFreydHomologyChainMap',
        [s.R, ...objectNames.map(n => s[n]), ...mapNames.map(n => s[n])], 7));
    add('bridge_freyd_homology_model_arrow_observation', [['R', ring, 'implicit'],
        ['M', s => L.tau(L.call('bridge_FreydHomologyModel', [s.R]))], ...objects,
        ...maps.map(([name, type]) => [name, type, 'implicit'] as Field),
        ['chainS', s => L.chainType(s.R, s.S2, s.S1, s.S0, s.sdNext, s.sd)],
        ['chainT', s => L.chainType(s.R, s.T2, s.T1, s.T0, s.tdNext, s.td)], ['m', chainMap]],
    s => L.tau(L.call('bridge_FreydArrowObservation', [s.R])));
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'model-map input ' + input.name,
                sourceSpan('generated/formal-freyd-model-map-inputs.ts', index + 1, 1)) });
    });
    return environment;
}
