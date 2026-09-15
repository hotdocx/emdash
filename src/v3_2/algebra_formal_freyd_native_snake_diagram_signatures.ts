/** Structural diagram transport and the original snake's shared endpoints. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { createFormalFreydNativeSnakeExactnessProofEnvironment } from './algebra_formal_freyd_native_snake_exactness_signatures';
import { formalFreydNativeSnakeFields, FormalFreydNativeSnakeField, FormalFreydNativeSnakeScope,
    FREYD_NATIVE_SNAKE_MAP_ROLES } from './algebra_formal_freyd_native_snake_signatures';
import { extendFormalFreydDiagramStructureSignatures, FORMAL_FREYD_DIAGRAM_STRUCTURE_SIGNATURE_BINDINGS } from './algebra_formal_freyd_diagram_signatures';

const positions = ['first', 'second', 'third', 'fourth'] as const;
export const FORMAL_FREYD_NATIVE_SNAKE_DIAGRAM_SIGNATURE_BINDINGS: Readonly<Record<string, string>> = Object.freeze({
    ...FORMAL_FREYD_DIAGRAM_STRUCTURE_SIGNATURE_BINDINGS,
    bridge_freyd_arrow_matching_transport: 'freyd_arrow_matching_transport',
    ...Object.fromEntries(positions.map(p => ['bridge_freyd_native_snake_' + p + '_pair_matching', 'freyd_native_snake_' + p + '_pair_matching']))
});

export function createFormalFreydNativeSnakeDiagramProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = extendFormalFreydDiagramStructureSignatures(createFormalFreydNativeSnakeExactnessProofEnvironment([]));
    const p = provenance('derived', 'native snake diagram signatures'), b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    const add = (name: string, fields: readonly FormalFreydNativeSnakeField[], result: (s: FormalFreydNativeSnakeScope) => Term) => {
        const visit = (i: number, s: FormalFreydNativeSnakeScope): Term => i === fields.length ? result(s) :
            b.pi(fields[i][0], fields[i][1](s), value => visit(i + 1, { ...s, [fields[i][0]]: value }),
                binderMode(fields[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const obs = (s: FormalFreydNativeSnakeScope) => L.call('bridge_FreydArrowObservation', [s.R]);
    const family = (s: FormalFreydNativeSnakeScope) => L.call('bridge_FiniteFamily', [obs(s), s.n]);
    const matching = (s: FormalFreydNativeSnakeScope, a: Term, xs: Term) => L.tau(L.call('bridge_FreydArrowMatchingTail', [s.R, a, s.n, xs], 1));
    add('bridge_freyd_arrow_matching_transport', [
        ['R', () => L.tau(b.free('bridge_CommRing')), 'implicit'],
        ['n', () => L.tau(b.free('bridge_Nat_grpd')), 'implicit'],
        ['a', s => L.tau(obs(s)), 'implicit'], ['b', s => L.tau(obs(s)), 'implicit'],
        ['xs', s => L.tau(family(s)), 'implicit'], ['ys', s => L.tau(family(s)), 'implicit'],
        ['m', s => matching(s, s.a, s.xs)], ['p', s => L.equality(obs(s), s.a, s.b)],
        ['q', s => L.equality(family(s), s.xs, s.ys)]
    ], s => matching(s, s.b, s.ys));
    const fields = formalFreydNativeSnakeFields(b, true);
    const arrow = (s: FormalFreydNativeSnakeScope, i: number) => b.call(
        b.free('bridge_freyd_raw_native_snake_' + FREYD_NATIVE_SNAKE_MAP_ROLES[i] + '_observation'),
        fields.filter(([name]) => name !== 'N' || i === 2).map(([name, , mode]) => ({ value: s[name],
            plicity: mode === 'implicit' ? 'implicit' as const : 'explicit' as const })));
    positions.forEach((position, i) => add('bridge_freyd_native_snake_' + position + '_pair_matching', fields,
        s => L.equality(L.call('bridge_CommRingPresentation', [s.R]),
            L.call('bridge_freyd_arrow_observation_target', [s.R, arrow(s, i)], 1),
            L.call('bridge_freyd_arrow_observation_source', [s.R, arrow(s, i + 1)], 1))));
    inputs.forEach((input, i) => { environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
        provenance: provenance('surface', 'native snake diagram input ' + input.name,
            sourceSpan('generated/native-snake-diagram-inputs.ts', i + 1, 1)) }); });
    return environment;
}
