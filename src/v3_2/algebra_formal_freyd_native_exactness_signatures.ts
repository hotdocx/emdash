/** Exact mirrors of defined native Ω-exactness types and derived constructors. */
import { CoreLfScopedBuilder } from './lf_builder';
import { binderMode, KernelExpression, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { FREYD_MODEL_CONNECTING_ARGUMENTS, FormalFreydWindowScope, formalFreydWindowFields } from './algebra_formal_freyd_window_signatures';

import { createFormalFreydNativeConnectingProofEnvironment } from './algebra_formal_freyd_native_connecting_signatures';

const positions = Object.freeze([
    ['middle', 'bridge_FreydAdjunctionModelMiddleExactness', 'bridge_freyd_adjunction_model_middle_exact_evidence'],
    ['source', 'bridge_FreydAdjunctionModelSourceExactness', 'bridge_freyd_adjunction_model_source_exact_evidence'],
    ['target', 'bridge_FreydAdjunctionModelTargetExactness', 'bridge_freyd_adjunction_model_target_exact_evidence']
] as const);

export const FORMAL_FREYD_NATIVE_EXACTNESS_SIGNATURE_BINDINGS = Object.freeze({
    bridge_FreydAdjunctionModelMiddleExactness: 'FreydAdjunctionModelMiddleExactness',
    bridge_freyd_adjunction_model_middle_exact_evidence: 'freyd_adjunction_model_middle_exact_evidence',
    bridge_FreydAdjunctionModelSourceExactness: 'FreydAdjunctionModelSourceExactness',
    bridge_freyd_adjunction_model_source_exact_evidence: 'freyd_adjunction_model_source_exact_evidence',
    bridge_FreydAdjunctionModelTargetExactness: 'FreydAdjunctionModelTargetExactness',
    bridge_freyd_adjunction_model_target_exact_evidence: 'freyd_adjunction_model_target_exact_evidence'
});

export const FREYD_NATIVE_EXACTNESS_ARGUMENTS = Object.freeze(FREYD_MODEL_CONNECTING_ARGUMENTS.filter(
    field => field.name !== 'source_chain' && field.name !== 'target_chain'));

/** Whole exactness needs the raw window; δ's two endpoint-chain views are omitted. */
export function algebraFormalFreydNativeExactnessExpressions(values: Readonly<Record<string, KernelExpression>>) {
    const expected = new Set(FREYD_MODEL_CONNECTING_ARGUMENTS.map(field => field.name));
    if (Object.keys(values).some(name => !expected.has(name)) ||
        FREYD_NATIVE_EXACTNESS_ARGUMENTS.some(field => values[field.name] === undefined)) {
        throw new Error('Supply the exact native window arguments for categorical exactness');
    }
    const b = new CoreLfScopedBuilder(provenance('derived', 'whole native categorical exactness')), L = formalFreydSpineLanguage(b);
    const args = FREYD_NATIVE_EXACTNESS_ARGUMENTS.map(field => ({ value: b.embed(values[field.name]),
        plicity: field.implicit ? 'implicit' as const : 'explicit' as const }));
    return Object.freeze(positions.map(([position, predicate, evidence]) => Object.freeze({ position,
        type: b.lower(L.tau(b.call(b.free(predicate), args))), term: b.lower(b.call(b.free(evidence), args)) })));
}

export function createFormalFreydNativeExactnessProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydNativeConnectingProofEnvironment([]);
    const p = provenance('derived', 'native exactness theorem signatures');
    const b = new CoreLfScopedBuilder(p), L = formalFreydSpineLanguage(b);
    const fields = formalFreydWindowFields(b, { model: 'bridge_FreydAdjunctionModel',
        normality: 'bridge_FreydAdjunctionModelNormality', shortExact: 'bridge_FreydAdjunctionModelRowShortExact' }, false);
    const add = (name: string, result: (s: FormalFreydWindowScope) => ReturnType<typeof b.free>) => {
        const visit = (i: number, s: FormalFreydWindowScope): ReturnType<typeof b.free> => i === fields.length ? result(s) :
            b.pi(fields[i][0], fields[i][1](s), v => visit(i + 1, { ...s, [fields[i][0]]: v }),
                binderMode(fields[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    for (const [, predicate, evidence] of positions) {
        add(predicate, () => b.application('groupoid-universe', []));
        add(evidence, s => L.tau(b.call(b.free(predicate), fields.map(field => ({ value: s[field[0]],
            plicity: field[2] === 'implicit' ? 'implicit' as const : 'explicit' as const })))));
    }
    inputs.forEach((input, i) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'native exactness input ' + input.name,
                sourceSpan('generated/native-exactness-inputs.ts', i + 1, 1)) });
    });
    return environment;
}
