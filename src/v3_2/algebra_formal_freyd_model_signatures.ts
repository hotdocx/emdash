/** Exact signature-only mirrors of the supplied coherent-model point interface. */
import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, KernelExpression, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { createFormalFreydActualHomologyProofEnvironment } from './algebra_formal_freyd_actual_homology_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';

export const FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS = Object.freeze({
    bridge_FreydHomologyModel: 'FreydHomologyModel',
    bridge_freyd_homology_model_object: 'freyd_homology_model_object'
});

export const FORMAL_FREYD_MODEL_SIGNATURE_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-model-point-signatures-v1' as const,
    policy: 'exact-opaque-signature-mirrors' as const,
    sourceOperations: 'transparent-whole-homology-observations' as const,
    suppliesModel: false as const,
    addsCoreOwner: false as const,
    addsRuntimeRule: false as const
});

export function algebraFormalFreydModelType(R: KernelExpression): KernelExpression {
    const b = new CoreLfScopedBuilder(provenance('derived', 'supplied Freyd homology model type'));
    const L = formalFreydSpineLanguage(b);
    return b.lower(L.tau(L.call('bridge_FreydHomologyModel', [b.embed(R)])));
}

export function createFormalFreydModelProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydActualHomologyProofEnvironment([]);
    const p = provenance('derived', 'coherent Freyd model point signature');
    const b = new CoreLfScopedBuilder(p);
    const L = formalFreydSpineLanguage(b);
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term, ('explicit' | 'implicit')?];
    const add = (name: keyof typeof FORMAL_FREYD_MODEL_SIGNATURE_BINDINGS, fields: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (i: number, s: Scope): Term => i === fields.length ? result(s) :
            b.pi(fields[i][0], fields[i][1](s), token => visit(i + 1, { ...s, [fields[i][0]]: token }),
                binderMode(fields[i][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const ring = () => L.tau(b.free('bridge_CommRing'));
    add('bridge_FreydHomologyModel', [['R', ring]], () => b.application('groupoid-universe', []));
    add('bridge_freyd_homology_model_object', [
        ['R', ring, 'implicit'], ['M', s => L.tau(L.call('bridge_FreydHomologyModel', [s.R]))],
        ...['A', 'B', 'D'].map(name => [name, (s: Scope) => L.presentationType(s.R), 'implicit'] as Field),
        ['e', s => L.morphismType(s.R, s.A, s.B)], ['d', s => L.morphismType(s.R, s.B, s.D)],
        ['chain', s => L.chainType(s.R, s.A, s.B, s.D, s.e, s.d)]
    ], s => L.presentationType(s.R));
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'coherent Freyd model input ' + input.name,
                sourceSpan('generated/formal-freyd-model-inputs.ts', index + 1, 1)) });
    });
    return environment;
}
