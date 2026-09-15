/** Exact private mirrors of the native snake observations and matrix-zero introduction. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, KernelExpression, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { createFormalFreydNativeModelObservationProofEnvironment } from './algebra_formal_freyd_native_model_observation_signatures';

export const FREYD_NATIVE_SNAKE_MAP_ROLES = Object.freeze([
    'kernel_first', 'kernel_second', 'connecting', 'cokernel_first', 'cokernel_second'
] as const);
export type FreydNativeSnakeMapRole = typeof FREYD_NATIVE_SNAKE_MAP_ROLES[number];

export const FORMAL_FREYD_NATIVE_SNAKE_SIGNATURE_BINDINGS = Object.freeze({
    bridge_comm_ring_presentation_morphism_comp: 'comm_ring_presentation_morphism_comp',
    bridge_comm_ring_freyd_snake_zero_from_matrices: 'comm_ring_freyd_snake_zero_from_matrices',
    bridge_freyd_raw_native_snake_kernel_first_observation: 'freyd_raw_native_snake_kernel_first_observation',
    bridge_freyd_raw_native_snake_kernel_second_observation: 'freyd_raw_native_snake_kernel_second_observation',
    bridge_freyd_raw_native_snake_connecting_observation: 'freyd_raw_native_snake_connecting_observation',
    bridge_freyd_raw_native_snake_cokernel_first_observation: 'freyd_raw_native_snake_cokernel_first_observation',
    bridge_freyd_raw_native_snake_cokernel_second_observation: 'freyd_raw_native_snake_cokernel_second_observation'
});

export function algebraFormalFreydNativeSnakeObservationTerm(
    role: FreydNativeSnakeMapRole, values: Readonly<Record<string, KernelExpression>>
): KernelExpression {
    if (!FREYD_NATIVE_SNAKE_MAP_ROLES.includes(role)) throw new Error('Unknown native snake map role');
    const b = new CoreLfScopedBuilder(provenance('derived', 'native snake complete-arrow observation'));
    const fields = ['R', 'M', ...(role === 'connecting' ? ['N'] : []), 'A', 'B', 'X', 'D', 'a', 'b', 'c', 'z'];
    return b.lower(b.call(b.free('bridge_freyd_raw_native_snake_' + role + '_observation'), fields.map(name => {
        if (!values[name]) throw new Error('Missing native snake argument ' + name);
        return { value: b.embed(values[name]), plicity: (['R', 'A', 'B', 'X', 'D'].includes(name)
            ? 'implicit' : 'explicit') as 'implicit' | 'explicit' };
    })));
}

export function createFormalFreydNativeSnakeProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydNativeModelObservationProofEnvironment([]);
    const p = provenance('derived', 'native Freyd snake signatures');
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term, ('explicit' | 'implicit')?];
    const add = (name: string, fields: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (i: number, s: Scope): Term => i === fields.length ? result(s) :
            b.pi(fields[i][0], fields[i][1](s), value => visit(i + 1, { ...s, [fields[i][0]]: value }),
                binderMode(fields[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const ring = () => L.tau(b.free('bridge_CommRing'));
    const natural = () => L.tau(b.free('bridge_Nat_grpd'));
    const objects = (names: readonly string[], implicit = true): Field[] => names.map(name =>
        [name, s => L.presentationType(s.R), implicit ? 'implicit' : 'explicit']);
    const composite = (R: Term, A: Term, B: Term, X: Term, g: Term, f: Term) =>
        L.call('bridge_comm_ring_presentation_morphism_comp', [R, A, B, X, g, f], 4);
    add('bridge_comm_ring_presentation_morphism_comp', [['R', ring, 'implicit'], ...objects(['A', 'B', 'X']),
        ['g', s => L.morphismType(s.R, s.B, s.X)], ['f', s => L.morphismType(s.R, s.A, s.B)]],
    s => L.morphismType(s.R, s.A, s.X));
    const prefix: Field[] = [['R', ring],
        ...['pa', 'ra', 'pb', 'rb', 'px', 'rx', 'pd', 'rd'].map(name => [name, natural] as Field),
        ...['a', 'b', 'x', 'd'].map(name => ['P' + name.toUpperCase(),
            (s: Scope) => L.tau(L.matrix(s.R, s['p' + name], s['r' + name]))] as Field)];
    const roles = [['F', 'a', 'b'], ['G', 'b', 'x'], ['H', 'x', 'd']] as const;
    for (const [name, from, to] of roles) prefix.push(
        [name, s => L.tau(L.matrix(s.R, s['p' + to], s['p' + from]))],
        ['W' + name, s => L.tau(L.matrix(s.R, s['r' + to], s['r' + from]))],
        ['law' + name, s => L.equality(L.matrix(s.R, s['p' + to], s['r' + from]),
            L.comp(s.R, s['p' + to], s['r' + to], s['r' + from], s['P' + to.toUpperCase()], s['W' + name]),
            L.comp(s.R, s['p' + to], s['p' + from], s['r' + from], s[name], s['P' + from.toUpperCase()]))]);
    const pres = (s: Scope, name: string) => L.presentation(s.R, s['p' + name], s['r' + name], s['P' + name.toUpperCase()]);
    const morph = (s: Scope, name: string, from: string, to: string) => L.morphism([
        s.R, s['p' + from], s['r' + from], s['p' + to], s['r' + to],
        s['P' + from.toUpperCase()], s['P' + to.toUpperCase()], s[name], s['W' + name], s['law' + name]
    ]);
    add('bridge_comm_ring_freyd_snake_zero_from_matrices', [...prefix,
        ['Z', s => L.tau(L.matrix(s.R, s.rd, s.pa))],
        ['law', s => L.equality(L.matrix(s.R, s.pd, s.pa), L.comp(s.R, s.pd, s.rd, s.pa, s.PD, s.Z),
            L.call('bridge_comm_ring_matrix_sub', [s.R, s.pd, s.pa,
                L.comp(s.R, s.pd, s.px, s.pa, s.H, L.comp(s.R, s.px, s.pb, s.pa, s.G, s.F)),
                L.call('bridge_comm_ring_matrix_zero', [s.R, s.pd, s.pa])]))]],
    s => L.chainType(s.R, pres(s, 'a'), pres(s, 'x'), pres(s, 'd'),
        composite(s.R, pres(s, 'a'), pres(s, 'b'), pres(s, 'x'), morph(s, 'G', 'b', 'x'), morph(s, 'F', 'a', 'b')),
        morph(s, 'H', 'x', 'd')));
    for (const role of FREYD_NATIVE_SNAKE_MAP_ROLES) {
        const fields: Field[] = [['R', ring, 'implicit'], ['M', s => L.tau(L.call('bridge_FreydAdjunctionModel', [s.R]))]];
        if (role === 'connecting') fields.push(['N', s => L.tau(L.call('bridge_FreydAdjunctionModelNormality', [s.R, s.M], 1))]);
        fields.push(...objects(['A', 'B', 'X', 'D']), ['a', s => L.morphismType(s.R, s.A, s.B)],
            ['b', s => L.morphismType(s.R, s.B, s.X)], ['c', s => L.morphismType(s.R, s.X, s.D)],
            ['z', s => L.chainType(s.R, s.A, s.X, s.D, composite(s.R, s.A, s.B, s.X, s.b, s.a), s.c)]);
        add('bridge_freyd_raw_native_snake_' + role + '_observation', fields,
            s => L.tau(L.call('bridge_FreydArrowObservation', [s.R])));
    }
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'native snake input ' + input.name,
                sourceSpan('generated/formal-freyd-native-snake-inputs.ts', index + 1, 1)) });
    });
    return environment;
}
