/** Exact mirrors of the four original native snake proofs and their point views. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, KernelExpression, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { createFormalFreydNativeSnakeProofEnvironment, formalFreydNativeSnakeFields,
    FormalFreydNativeSnakeField, FormalFreydNativeSnakeScope } from './algebra_formal_freyd_native_snake_signatures';
import { extendFormalFreydOmegaArrowSignatures, FORMAL_FREYD_OMEGA_ARROW_SIGNATURE_BINDINGS } from './algebra_formal_freyd_omega_arrow_signatures';

export const FREYD_NATIVE_SNAKE_EXACT_POSITIONS = Object.freeze(['first', 'second', 'third', 'fourth'] as const);
export const FORMAL_FREYD_NATIVE_SNAKE_EXACTNESS_SIGNATURE_BINDINGS: Readonly<Record<string, string>> = Object.freeze(Object.fromEntries([
    ...Object.entries(FORMAL_FREYD_OMEGA_ARROW_SIGNATURE_BINDINGS),
    ...FREYD_NATIVE_SNAKE_EXACT_POSITIONS.flatMap(position => [
        'FreydNativeSnake' + position[0].toUpperCase() + position.slice(1) + 'Exactness',
        'freyd_native_snake_' + position + '_exact_evidence', 'freyd_native_snake_' + position + '_point_exact_data'
    ].map(name => ['bridge_' + name, name]))
]));

export function createFormalFreydNativeSnakeExactnessProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = extendFormalFreydOmegaArrowSignatures(createFormalFreydNativeSnakeProofEnvironment([]));
    const p = provenance('derived', 'native snake exactness signatures'), b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    const fields = formalFreydNativeSnakeFields(b, true);
    const call = (name: string, s: FormalFreydNativeSnakeScope) => b.call(b.free(name), fields.map(([key, , mode]) =>
        ({ value: s[key], plicity: mode === 'implicit' ? 'implicit' as const : 'explicit' as const })));
    const add = (name: string, fs: readonly FormalFreydNativeSnakeField[], result: (s: FormalFreydNativeSnakeScope) => Term) => {
        const visit = (i: number, s: FormalFreydNativeSnakeScope): Term => i === fs.length ? result(s) :
            b.pi(fs[i][0], fs[i][1](s), value => visit(i + 1, { ...s, [fs[i][0]]: value }),
                binderMode(fs[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    for (const position of FREYD_NATIVE_SNAKE_EXACT_POSITIONS) {
        const predicate = 'bridge_FreydNativeSnake' + position[0].toUpperCase() + position.slice(1) + 'Exactness';
        add(predicate, fields, () => b.application('groupoid-universe', []));
        add('bridge_freyd_native_snake_' + position + '_exact_evidence', fields, s => L.tau(call(predicate, s)));
        add('bridge_freyd_native_snake_' + position + '_point_exact_data',
            [...fields, ['u', s => L.tau(call(predicate, s))]], s => L.tau(L.call('bridge_FreydOmegaArrowObservation', [s.R])));
    }
    inputs.forEach((input, i) => { environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
        provenance: provenance('surface', 'native snake exactness input ' + input.name,
            sourceSpan('generated/native-snake-exactness-inputs.ts', i + 1, 1)) }); });
    return environment;
}

export function algebraFormalFreydNativeSnakeExactnessExpressions(values: Readonly<Record<string, KernelExpression>>) {
    const b = new CoreLfScopedBuilder(provenance('derived', 'original native snake exactness proofs')), L = formalFreydSpineLanguage(b);
    const fields = formalFreydNativeSnakeFields(b, true);
    const args = fields.map(([name, , mode]) => {
        if (!values[name]) throw new Error('Missing native snake exactness argument ' + name);
        return { value: b.embed(values[name]), plicity: mode === 'implicit' ? 'implicit' as const : 'explicit' as const };
    });
    const R = b.embed(values.R);
    return Object.freeze(FREYD_NATIVE_SNAKE_EXACT_POSITIONS.map(position => {
        const predicate = 'bridge_FreydNativeSnake' + position[0].toUpperCase() + position.slice(1) + 'Exactness';
        const term = b.call(b.free('bridge_freyd_native_snake_' + position + '_exact_evidence'), args);
        const data = b.call(b.free('bridge_freyd_native_snake_' + position + '_point_exact_data'),
            [...args, { value: term, plicity: 'explicit' as const }]);
        const arrow = L.call('bridge_freyd_omega_arrow_observation', [R, data], 1);
        return Object.freeze({ position, term: b.lower(term), type: b.lower(L.tau(b.call(b.free(predicate), args))),
            data: b.lower(data), dataType: b.lower(L.tau(L.call('bridge_FreydOmegaArrowObservation', [R]))),
            arrow: b.lower(arrow), arrowType: b.lower(L.tau(L.call('bridge_FreydArrowObservation', [R]))),
            evidence: b.lower(L.call('bridge_freyd_omega_arrow_evidence', [R, data], 1)),
            evidenceType: b.lower(L.tau(L.call('bridge_FreydArrowOmegaEvidence', [R, arrow]))) });
    }));
}
