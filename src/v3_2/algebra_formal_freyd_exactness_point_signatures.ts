/** Small exact mirrors of evaluated original comparison/evidence observations. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { createFormalFreydDiagramProofEnvironment } from './algebra_formal_freyd_diagram_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { formalFreydWindowFields, FormalFreydWindowScope } from './algebra_formal_freyd_model_connecting_signatures';
import { FREYD_NATIVE_EXACTNESS_ARGUMENTS, algebraFormalFreydNativeExactnessExpressions } from './algebra_formal_freyd_native_exactness_signatures';

const positions = ['middle', 'source', 'target'] as const;
export const FORMAL_FREYD_EXACTNESS_POINT_SIGNATURE_BINDINGS: Readonly<Record<string, string>> = Object.freeze(Object.fromEntries([
    ...['FreydOmegaArrowObservation', 'FreydArrowOmegaEvidence', 'freyd_omega_arrow_observation', 'freyd_omega_arrow_evidence'].map(name => ['bridge_' + name, name]),
    ...positions.map(pos => ['bridge_freyd_adjunction_model_' + pos + '_point_observation', 'freyd_adjunction_model_' + pos + '_point_observation'])
]));

export function createFormalFreydExactnessPointProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydDiagramProofEnvironment([]);
    const p = provenance('derived', 'native exactness point observation signatures');
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    type Field = readonly [string, (s: FormalFreydWindowScope) => Term, ('explicit' | 'implicit')?];
    const add = (name: string, fields: readonly Field[], result: (s: FormalFreydWindowScope) => Term) => {
        const visit = (i: number, s: FormalFreydWindowScope): Term => i === fields.length ? result(s) :
            b.pi(fields[i][0], fields[i][1](s), v => visit(i + 1, { ...s, [fields[i][0]]: v }),
                binderMode(fields[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const grpd = () => b.application('groupoid-universe', []), ring = () => L.tau(b.free('bridge_CommRing'));
    const observation = (s: FormalFreydWindowScope) => L.call('bridge_FreydOmegaArrowObservation', [s.R]);
    add('bridge_FreydOmegaArrowObservation', [['R', ring]], grpd);
    add('bridge_FreydArrowOmegaEvidence', [['R', ring], ['a', s => L.tau(L.call('bridge_FreydArrowObservation', [s.R]))]], grpd);
    for (const name of ['observation', 'evidence']) add('bridge_freyd_omega_arrow_' + name,
        [['R', ring, 'implicit'], ['d', s => L.tau(observation(s))]], s => name === 'observation' ?
            L.tau(L.call('bridge_FreydArrowObservation', [s.R])) :
            L.tau(L.call('bridge_FreydArrowOmegaEvidence', [s.R, L.call('bridge_freyd_omega_arrow_observation', [s.R, s.d], 1)])));
    const fields = formalFreydWindowFields(b, { model: 'bridge_FreydAdjunctionModel', normality: 'bridge_FreydAdjunctionModelNormality',
        shortExact: 'bridge_FreydAdjunctionModelRowShortExact' }, false);
    for (const position of positions) {
        const predicate = 'bridge_FreydAdjunctionModel' + position[0].toUpperCase() + position.slice(1) + 'Exactness';
        add('bridge_freyd_adjunction_model_' + position + '_point_observation', [...fields,
            ['whole', s => L.tau(b.call(b.free(predicate), fields.map(([name, , mode]) => ({ value: s[name],
                plicity: mode === 'implicit' ? 'implicit' as const : 'explicit' as const }))))]], s => L.tau(observation(s)));
    }
    inputs.forEach((input, i) => { environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
        provenance: provenance('surface', 'native point observation input ' + input.name,
            sourceSpan('generated/native-exactness-point-inputs.ts', i + 1, 1)) }); });
    return environment;
}

/** Preserve the original proof term as an explicit argument of its observation. */
export function algebraFormalFreydExactnessPointExpressions(whole: ReturnType<typeof algebraFormalFreydNativeExactnessExpressions>) {
    const b = new CoreLfScopedBuilder(provenance('derived', 'original exactness point observations')), L = formalFreydSpineLanguage(b);
    if (whole.length !== positions.length) throw new Error('Supply all three original whole exactness proofs');
    return Object.freeze(whole.map((item, i) => {
        const term = item.term;
        if (item.position !== positions[i] || term.tag !== 'call' || term.callee.tag !== 'reference' || term.callee.namespace !== 'free' ||
            term.callee.name !== 'bridge_freyd_adjunction_model_' + item.position + '_exact_evidence' ||
            term.arguments.length !== FREYD_NATIVE_EXACTNESS_ARGUMENTS.length ||
            term.arguments.some((a, j) => a.plicity !== (FREYD_NATIVE_EXACTNESS_ARGUMENTS[j].implicit ? 'implicit' : 'explicit'))) {
            throw new Error('Retain the original whole exactness constructor and arguments');
        }
        const R = b.embed(term.arguments[0].value);
        const data = b.call(b.free('bridge_freyd_adjunction_model_' + item.position + '_point_observation'),
            [...term.arguments.map(a => ({ ...a, value: b.embed(a.value) })), { value: b.embed(term), plicity: 'explicit' as const }]);
        const arrow = L.call('bridge_freyd_omega_arrow_observation', [R, data], 1);
        return Object.freeze({ position: item.position, whole: item,
            data: b.lower(data), dataType: b.lower(L.tau(L.call('bridge_FreydOmegaArrowObservation', [R]))),
            arrow: b.lower(arrow), arrowType: b.lower(L.tau(L.call('bridge_FreydArrowObservation', [R]))),
            evidence: b.lower(L.call('bridge_freyd_omega_arrow_evidence', [R, data], 1)),
            type: b.lower(L.tau(L.call('bridge_FreydArrowOmegaEvidence', [R, arrow]))) });
    }));
}
