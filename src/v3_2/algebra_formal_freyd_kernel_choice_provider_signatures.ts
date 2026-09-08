/** Exact signature mirrors for selected matrix-provider introductions. */

import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { createFormalFreydSpineProofEnvironment, formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';

export const FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS = Object.freeze({
    bridge_CommRingFiniteFreeWeakPullback: 'CommRingFiniteFreeWeakPullback',
    bridge_CommRingFiniteFreeWeakPullbackCone: 'CommRingFiniteFreeWeakPullbackCone',
    bridge_CommRingFiniteFreeWeakPullbackFactorOperation: 'CommRingFiniteFreeWeakPullbackFactorOperation',
    bridge_CommRingFiniteFreeWeakPullbackFactorLaw: 'CommRingFiniteFreeWeakPullbackFactorLaw',
    bridge_CommRingFiniteFreeWeakPullbackMatrixProvider: 'CommRingFiniteFreeWeakPullbackMatrixProvider',
    bridge_comm_ring_finite_free_weak_pullback_cone_from_matrices: 'comm_ring_finite_free_weak_pullback_cone_from_matrices',
    bridge_comm_ring_finite_free_weak_pullback_matrix_provider_intro: 'comm_ring_finite_free_weak_pullback_matrix_provider_intro',
    bridge_comm_ring_finite_free_weak_pullback_matrix_provider_factor: 'comm_ring_finite_free_weak_pullback_matrix_provider_factor',
    bridge_comm_ring_finite_free_weak_pullback_matrix_provider_law: 'comm_ring_finite_free_weak_pullback_matrix_provider_law',
    bridge_comm_ring_finite_free_weak_pullback_from_matrix_provider: 'comm_ring_finite_free_weak_pullback_from_matrix_provider',
    bridge_CommRingFreydKernelChoices: 'CommRingFreydKernelChoices',
    bridge_comm_ring_freyd_kernel_choices_from_matrix_providers: 'comm_ring_freyd_kernel_choices_from_matrix_providers'
});

export const FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-kernel-choice-provider-signatures-v1' as const,
    policy: 'exact-opaque-signature-mirrors' as const,
    providerLaw: 'explicit-all-test-capability-input' as const,
    suppliesGlobalWeakKernels: false as const,
    addsCoreOwner: false as const,
    addsRuntimeRule: false as const
});

export function createFormalFreydKernelChoiceProviderProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydSpineProofEnvironment([]);
    const p = provenance('derived', 'formal selected-kernel provider signatures');
    const b = new CoreLfScopedBuilder(p);
    const L = formalFreydSpineLanguage(b);
    const ring = () => L.tau(b.free('bridge_CommRing'));
    const nat = () => L.tau(b.free('bridge_Nat_grpd'));
    const grpd = () => b.application('groupoid-universe', []);
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term, ('explicit' | 'implicit')?];
    const add = (name: keyof typeof FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS,
        fields: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (index: number, s: Scope): Term => index === fields.length ? result(s) :
            b.pi(fields[index][0], fields[index][1](s), token => visit(index + 1, { ...s, [fields[index][0]]: token }),
                binderMode(fields[index][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const naturals = (names: readonly string[], implicit = false): Field[] => names.map(name => [name, nat, implicit ? 'implicit' : 'explicit']);
    const cospan = (implicit = true): Field[] => [['R', ring, implicit ? 'implicit' : 'explicit'], ...naturals(['x', 'y', 'z'], implicit),
        ['a', s => L.tau(L.matrix(s.R, s.y, s.x))], ['b', s => L.tau(L.matrix(s.R, s.y, s.z))]];
    const cospanArgs = (s: Scope) => [s.R, s.x, s.y, s.z, s.a, s.b];
    const factorType = (s: Scope) => L.tau(L.call('bridge_CommRingFiniteFreeWeakPullbackFactorOperation', [...cospanArgs(s), s.k], 4));
    const coneType = (s: Scope) => L.tau(L.call('bridge_CommRingFiniteFreeWeakPullbackCone', [...cospanArgs(s), s.k], 4));
    const lawType = (s: Scope, cone: Term, factor: Term) => L.tau(L.call('bridge_CommRingFiniteFreeWeakPullbackFactorLaw',
        [...cospanArgs(s), s.k, cone, factor], 7));
    add('bridge_CommRingFiniteFreeWeakPullback', cospan(), grpd);
    add('bridge_CommRingFiniteFreeWeakPullbackCone', [...cospan(), ['k', nat]], grpd);
    add('bridge_CommRingFiniteFreeWeakPullbackFactorOperation', [...cospan(), ['k', nat]], grpd);
    add('bridge_CommRingFiniteFreeWeakPullbackFactorLaw', [
        ...cospan().map(field => [field[0], field[1], 'implicit'] as Field), ['k', nat, 'implicit'],
        ['cone', coneType], ['factor', factorType]
    ], grpd);
    const compatibility = (s: Scope) => L.equality(L.matrix(s.R, s.y, s.k),
        L.comp(s.R, s.y, s.x, s.k, s.a, s.p), L.comp(s.R, s.y, s.z, s.k, s.b, s.q));
    const matrixFields: Field[] = [['R', ring], ...naturals(['x', 'y', 'z', 'k']),
        ['a', s => L.tau(L.matrix(s.R, s.y, s.x))], ['b', s => L.tau(L.matrix(s.R, s.y, s.z))],
        ['p', s => L.tau(L.matrix(s.R, s.x, s.k))], ['q', s => L.tau(L.matrix(s.R, s.z, s.k))], ['compatible', compatibility]];
    const matrixArgs = (s: Scope) => [s.R, s.x, s.y, s.z, s.k, s.a, s.b, s.p, s.q, s.compatible];
    const cone = (s: Scope) => L.call('bridge_comm_ring_finite_free_weak_pullback_cone_from_matrices', matrixArgs(s));
    const providerType = (s: Scope) => L.tau(L.call('bridge_CommRingFiniteFreeWeakPullbackMatrixProvider', matrixArgs(s)));
    const factor = (s: Scope) => L.call('bridge_comm_ring_finite_free_weak_pullback_matrix_provider_factor', [...matrixArgs(s), s.provider]);
    add('bridge_comm_ring_finite_free_weak_pullback_cone_from_matrices', matrixFields, coneType);
    add('bridge_CommRingFiniteFreeWeakPullbackMatrixProvider', matrixFields, grpd);
    add('bridge_comm_ring_finite_free_weak_pullback_matrix_provider_intro', [...matrixFields,
        ['factor', factorType], ['law', s => lawType(s, cone(s), s.factor)]], providerType);
    add('bridge_comm_ring_finite_free_weak_pullback_matrix_provider_factor', [...matrixFields, ['provider', providerType]], factorType);
    add('bridge_comm_ring_finite_free_weak_pullback_matrix_provider_law', [...matrixFields, ['provider', providerType]],
        s => lawType(s, cone(s), factor(s)));
    add('bridge_comm_ring_finite_free_weak_pullback_from_matrix_provider', [...matrixFields, ['provider', providerType]],
        s => L.tau(L.call('bridge_CommRingFiniteFreeWeakPullback', cospanArgs(s), 4)));
    add('bridge_CommRingFreydKernelChoices', [['R', ring, 'implicit'],
        ['P', s => L.presentationType(s.R), 'implicit'], ['Q', s => L.presentationType(s.R), 'implicit'],
        ['f', s => L.morphismType(s.R, s.P, s.Q)]], grpd);
    const firstArgs = (s: Scope) => [s.R, s.p, s.q, s.qr, s.k1, s.F, s.Q, s.p1, s.q1, s.compatible1];
    const secondArgs = (s: Scope) => [s.R, s.k1, s.p, s.pr, s.k2, s.p1, s.P, s.p2, s.q2, s.compatible2];
    add('bridge_comm_ring_freyd_kernel_choices_from_matrix_providers', [['R', ring], ...naturals(['p', 'pr', 'q', 'qr']),
        ['P', s => L.tau(L.matrix(s.R, s.p, s.pr))], ['Q', s => L.tau(L.matrix(s.R, s.q, s.qr))],
        ['F', s => L.tau(L.matrix(s.R, s.q, s.p))], ['WF', s => L.tau(L.matrix(s.R, s.qr, s.pr))],
        ['lawF', s => L.equality(L.matrix(s.R, s.q, s.pr), L.comp(s.R, s.q, s.qr, s.pr, s.Q, s.WF), L.comp(s.R, s.q, s.p, s.pr, s.F, s.P))],
        ['k1', nat], ['p1', s => L.tau(L.matrix(s.R, s.p, s.k1))], ['q1', s => L.tau(L.matrix(s.R, s.qr, s.k1))],
        ['compatible1', s => L.equality(L.matrix(s.R, s.q, s.k1), L.comp(s.R, s.q, s.p, s.k1, s.F, s.p1), L.comp(s.R, s.q, s.qr, s.k1, s.Q, s.q1))],
        ['provider1', s => L.tau(L.call('bridge_CommRingFiniteFreeWeakPullbackMatrixProvider', firstArgs(s)))],
        ['k2', nat], ['p2', s => L.tau(L.matrix(s.R, s.k1, s.k2))], ['q2', s => L.tau(L.matrix(s.R, s.pr, s.k2))],
        ['compatible2', s => L.equality(L.matrix(s.R, s.p, s.k2), L.comp(s.R, s.p, s.k1, s.k2, s.p1, s.p2), L.comp(s.R, s.p, s.pr, s.k2, s.P, s.q2))],
        ['provider2', s => L.tau(L.call('bridge_CommRingFiniteFreeWeakPullbackMatrixProvider', secondArgs(s)))]
    ], s => L.tau(L.call('bridge_CommRingFreydKernelChoices', [s.R,
        L.presentation(s.R, s.p, s.pr, s.P), L.presentation(s.R, s.q, s.qr, s.Q),
        L.morphism([s.R, s.p, s.pr, s.q, s.qr, s.P, s.Q, s.F, s.WF, s.lawF])], 3)));
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'selected provider input ' + input.name,
                sourceSpan('generated/formal-selected-provider-inputs.ts', index + 1, 1)) });
    });
    return environment;
}
