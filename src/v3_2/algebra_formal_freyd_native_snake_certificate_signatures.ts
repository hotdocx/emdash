/** Exact mirrors of native-input-indexed pair and diagram certificates. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { formalFreydNativeSnakeFields, FormalFreydNativeSnakeField, FormalFreydNativeSnakeScope,
    FREYD_NATIVE_SNAKE_MAP_ROLES } from './algebra_formal_freyd_native_snake_signatures';
import { createFormalFreydNativeSnakeDiagramProofEnvironment } from './algebra_formal_freyd_native_snake_diagram_signatures';

export const FREYD_NATIVE_SNAKE_CERTIFICATE_POSITIONS = Object.freeze(['first', 'second', 'third', 'fourth'] as const);
export const FORMAL_FREYD_NATIVE_SNAKE_CERTIFICATE_SIGNATURE_BINDINGS: Readonly<Record<string, string>> = Object.freeze(Object.fromEntries([
    ...FREYD_NATIVE_SNAKE_CERTIFICATE_POSITIONS.flatMap(p => [
        'FreydNativeSnake' + p[0].toUpperCase() + p.slice(1) + 'ExactAt', 'freyd_native_snake_' + p + '_exact_at'
    ]), 'FreydNativeSnakeDiagramExactness', 'freyd_native_snake_exact_diagram_intro'
].map(name => ['bridge_' + name, name])));

export function createFormalFreydNativeSnakeCertificateProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydNativeSnakeDiagramProofEnvironment([]);
    const p = provenance('derived', 'native snake certificate signatures'), b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    const fields = formalFreydNativeSnakeFields(b, true);
    const add = (name: string, fs: readonly FormalFreydNativeSnakeField[], result: (s: FormalFreydNativeSnakeScope) => Term) => {
        const visit = (i: number, s: FormalFreydNativeSnakeScope): Term => i === fs.length ? result(s) :
            b.pi(fs[i][0], fs[i][1](s), value => visit(i + 1, { ...s, [fs[i][0]]: value }),
                binderMode(fs[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const args = (s: FormalFreydNativeSnakeScope) => fields.map(([name, , mode]) => ({ value: s[name],
        plicity: mode === 'implicit' ? 'implicit' as const : 'explicit' as const }));
    const call = (name: string, s: FormalFreydNativeSnakeScope, more: readonly Term[] = []) =>
        b.call(b.free(name), [...args(s), ...more.map(value => ({ value, plicity: 'explicit' as const }))]);
    const obs = (s: FormalFreydNativeSnakeScope) => L.call('bridge_FreydArrowObservation', [s.R]);
    const arrow = (s: FormalFreydNativeSnakeScope, i: number) => b.call(
        b.free('bridge_freyd_raw_native_snake_' + FREYD_NATIVE_SNAKE_MAP_ROLES[i] + '_observation'),
        args(s).filter((_, j) => fields[j][0] !== 'N' || i === 2));
    for (const [i, position] of FREYD_NATIVE_SNAKE_CERTIFICATE_POSITIONS.entries()) {
        const stem = 'bridge_FreydNativeSnake' + position[0].toUpperCase() + position.slice(1);
        add(stem + 'ExactAt', [...fields, ['edge0', s => L.tau(obs(s))], ['edge1', s => L.tau(obs(s))]],
            () => b.application('groupoid-universe', []));
        add('bridge_freyd_native_snake_' + position + '_exact_at', [...fields,
            ['u', s => L.tau(call(stem + 'Exactness', s))],
            ['edge0', s => L.tau(obs(s)), 'implicit'], ['edge1', s => L.tau(obs(s)), 'implicit'],
            ['p', s => L.equality(obs(s), arrow(s, i), s.edge0)], ['q', s => L.equality(obs(s), arrow(s, i + 1), s.edge1)]
        ], s => L.tau(call(stem + 'ExactAt', s, [s.edge0, s.edge1])));
    }
    const diagram = (s: FormalFreydNativeSnakeScope) => L.call('bridge_FreydArrowObservationDiagram', [s.R, L.nat(4)]);
    add('bridge_FreydNativeSnakeDiagramExactness', [...fields, ['d', s => L.tau(diagram(s))]],
        () => b.application('groupoid-universe', []));
    const tail = (s: FormalFreydNativeSnakeScope) => {
        let result = L.call('bridge_finite_family_nil', [obs(s)], 1);
        for (let i = 4; i > 0; i--) result = L.call('bridge_finite_family_cons', [obs(s), L.nat(4 - i), s['v' + i], result], 2);
        return result;
    };
    add('bridge_freyd_native_snake_exact_diagram_intro', [...fields,
        ...['v0', 'v1', 'v2', 'v3', 'v4'].map(name => [name, (s: FormalFreydNativeSnakeScope) => L.tau(obs(s))] as FormalFreydNativeSnakeField),
        ['matching', s => L.tau(L.call('bridge_FreydArrowMatchingTail', [s.R, s.v0, L.nat(4), tail(s)], 1))],
        ...FREYD_NATIVE_SNAKE_CERTIFICATE_POSITIONS.map((position, i) => ['e' + i, (s: FormalFreydNativeSnakeScope) =>
            L.tau(call('bridge_FreydNativeSnake' + position[0].toUpperCase() + position.slice(1) + 'ExactAt', s,
                [s['v' + i], s['v' + (i + 1)]]))] as FormalFreydNativeSnakeField)
    ], s => L.tau(call('bridge_FreydNativeSnakeDiagramExactness', s,
        [L.call('bridge_freyd_arrow_diagram_intro', [s.R, L.nat(4), s.v0, tail(s), s.matching], 2)])));
    inputs.forEach((input, i) => { environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
        provenance: provenance('surface', 'native snake certificate input ' + input.name,
            sourceSpan('generated/native-snake-certificate-inputs.ts', i + 1, 1)) }); });
    return environment;
}
