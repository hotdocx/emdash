/** Signature mirrors for the existing witnessed Freyd epimorphism introduction. */

import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { createFormalFreydSpineProofEnvironment, formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';

export const FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS = Object.freeze({
    bridge_comm_ring_matrix_add: 'comm_ring_matrix_add',
    bridge_comm_ring_finite_free_id_matrix: 'comm_ring_finite_free_id_matrix',
    bridge_CommRingFreydEpimorphismWitness: 'CommRingFreydEpimorphismWitness',
    bridge_comm_ring_freyd_epimorphism_from_matrices: 'comm_ring_freyd_epimorphism_from_matrices'
});

export const FORMAL_FREYD_EPIMORPHISM_SIGNATURE_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-epimorphism-signatures-v1' as const,
    policy: 'exact-opaque-signature-mirrors' as const,
    addsCoreOwner: false as const,
    addsRuntimeRule: false as const,
    claimsChainExactness: false as const
});

/** Keep native ranks separate; the source constructor owns the vertical block. */
export function createFormalFreydEpimorphismProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydSpineProofEnvironment([]);
    const p = provenance('derived', 'formal Freyd epimorphism signature');
    const b = new CoreLfScopedBuilder(p);
    const { call, tau, matrix, equality, comp, presentation, presentationType, morphismType, morphism } = formalFreydSpineLanguage(b);
    const ring = () => tau(b.free('bridge_CommRing'));
    const natType = () => tau(b.free('bridge_Nat_grpd'));
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term, ('explicit' | 'implicit')?];
    const add = (name: keyof typeof FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS, fields: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (index: number, s: Scope): Term => index === fields.length ? result(s) :
            b.pi(fields[index][0], fields[index][1](s), token => visit(index + 1, { ...s, [fields[index][0]]: token }),
                binderMode(fields[index][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const naturals = (...names: string[]): Field[] => names.map(name => [name, natType]);
    add('bridge_comm_ring_matrix_add', [['R', ring], ...naturals('rows', 'columns'),
        ['A', s => tau(matrix(s.R, s.rows, s.columns))], ['B', s => tau(matrix(s.R, s.rows, s.columns))]],
    s => tau(matrix(s.R, s.rows, s.columns)));
    add('bridge_comm_ring_finite_free_id_matrix', [['R', ring], ['n', natType]], s => tau(matrix(s.R, s.n, s.n)));
    add('bridge_CommRingFreydEpimorphismWitness', [['R', ring, 'implicit'],
        ['P', s => presentationType(s.R), 'implicit'], ['Q', s => presentationType(s.R), 'implicit'],
        ['f', s => morphismType(s.R, s.P, s.Q)]], () => b.application('groupoid-universe', []));
    add('bridge_comm_ring_freyd_epimorphism_from_matrices', [['R', ring], ...naturals('p', 'pr', 'q', 'qr'),
        ['P', s => tau(matrix(s.R, s.p, s.pr))], ['Q', s => tau(matrix(s.R, s.q, s.qr))],
        ['F', s => tau(matrix(s.R, s.q, s.p))], ['W', s => tau(matrix(s.R, s.qr, s.pr))],
        ['lawF', s => equality(matrix(s.R, s.q, s.pr), comp(s.R, s.q, s.qr, s.pr, s.Q, s.W), comp(s.R, s.q, s.p, s.pr, s.F, s.P))],
        ['U', s => tau(matrix(s.R, s.qr, s.q))], ['V', s => tau(matrix(s.R, s.p, s.q))],
        ['lawE', s => equality(matrix(s.R, s.q, s.q), call('bridge_comm_ring_matrix_add', [s.R, s.q, s.q,
            comp(s.R, s.q, s.qr, s.q, s.Q, s.U), comp(s.R, s.q, s.p, s.q, s.F, s.V)]),
        call('bridge_comm_ring_finite_free_id_matrix', [s.R, s.q]))]
    ], s => tau(call('bridge_CommRingFreydEpimorphismWitness', [s.R,
        presentation(s.R, s.p, s.pr, s.P), presentation(s.R, s.q, s.qr, s.Q),
        morphism([s.R, s.p, s.pr, s.q, s.qr, s.P, s.Q, s.F, s.W, s.lawF])], 3)));
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'formal Freyd epimorphism input ' + input.name,
                sourceSpan('generated/formal-freyd-epimorphism-inputs.ts', index + 1, 1)) });
    });
    return environment;
}
