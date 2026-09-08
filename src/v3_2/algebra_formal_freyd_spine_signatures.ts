/** Exact signature mirrors for transparent raw Freyd-spine introductions. */

import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { createFormalPresentationMorphismProofEnvironment } from './algebra_formal_presentation_morphism_signatures';

export const FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS = Object.freeze({
    bridge_CommRingPresentation: 'CommRingPresentation',
    bridge_comm_ring_presentation_intro: 'comm_ring_presentation_intro',
    bridge_CommRingPresentationMorphism: 'CommRingPresentationMorphism',
    bridge_comm_ring_presentation_morphism_from_matrices: 'comm_ring_presentation_morphism_from_matrices',
    bridge_CommRingFreydChainPair: 'CommRingFreydChainPair',
    bridge_comm_ring_freyd_chain_pair_from_matrices: 'comm_ring_freyd_chain_pair_from_matrices',
    bridge_CommRingFreydChainTail: 'CommRingFreydChainTail',
    bridge_comm_ring_freyd_chain_tail_nil: 'comm_ring_freyd_chain_tail_nil',
    bridge_comm_ring_freyd_chain_tail_cons: 'comm_ring_freyd_chain_tail_cons',
    bridge_CommRingFreydBoundedComplex: 'CommRingFreydBoundedComplex',
    bridge_comm_ring_freyd_bounded_complex_zero: 'comm_ring_freyd_bounded_complex_zero',
    bridge_comm_ring_freyd_bounded_complex_succ: 'comm_ring_freyd_bounded_complex_succ'
});

export const FORMAL_FREYD_SPINE_SIGNATURE_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-spine-signatures-v1' as const,
    policy: 'exact-opaque-signature-mirrors' as const,
    sourceConstructors: 'transparent-existing-owner-introductions' as const,
    addsCoreOwner: false as const,
    addsRuntimeRule: false as const,
    claimsExactness: false as const
});

/** Shared signature/term notation, lowered by the existing scoped LF builder. */
export const formalFreydSpineLanguage = (b: CoreLfScopedBuilder) => {
    const call = (name: string, values: readonly Term[], implicitCount = 0) => b.call(b.free(name),
        values.map((value, index) => ({ value, plicity: index < implicitCount ? 'implicit' : 'explicit' })));
    const tau = (value: Term) => call('bridge_tau', [value]);
    const nat = (n: number): Term => {
        if (!Number.isSafeInteger(n) || n < 0) throw new Error('A finite nonnegative spine index is required');
        let term = b.free('bridge_nat_zero');
        for (let i = 0; i < n; i++) term = call('bridge_nat_succ', [term]);
        return term;
    };
    const matrix = (R: Term, rows: Term, columns: Term) => call('bridge_FiniteFamily', [
        call('bridge_FiniteFamily', [call('bridge_comm_ring_carrier', [R]), rows]), columns
    ]);
    const equality = (type: Term, left: Term, right: Term) => tau(call('bridge_eq', [type, left, right], 1));
    const comp = (R: Term, rows: Term, middle: Term, columns: Term, after: Term, before: Term) =>
        call('bridge_comm_ring_matrix_comp', [R, rows, middle, columns, after, before]);
    const presentation = (R: Term, generators: Term, relations: Term, data: Term) =>
        call('bridge_comm_ring_presentation_intro', [R, generators, relations, data], 1);
    const presentationType = (R: Term) => tau(call('bridge_CommRingPresentation', [R]));
    const morphismType = (R: Term, P: Term, Q: Term) => tau(call('bridge_CommRingPresentationMorphism', [R, P, Q]));
    const morphism = (values: readonly Term[]) => call('bridge_comm_ring_presentation_morphism_from_matrices', values);
    const chainType = (R: Term, P2: Term, P1: Term, P0: Term, F: Term, G: Term) =>
        tau(call('bridge_CommRingFreydChainPair', [R, P2, P1, P0, F, G], 4));
    const tailType = (R: Term, n: Term, below: Term, current: Term, d: Term) =>
        tau(call('bridge_CommRingFreydChainTail', [R, n, below, current, d]));
    const complexType = (R: Term, n: Term) => tau(call('bridge_CommRingFreydBoundedComplex', [R, n]));
    return { call, tau, nat, matrix, equality, comp, presentation, presentationType, morphismType,
        morphism, chainType, tailType, complexType };
};

export function createFormalFreydSpineProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalPresentationMorphismProofEnvironment([]);
    const p = provenance('derived', 'formal Freyd-spine signature');
    const b = new CoreLfScopedBuilder(p);
    const L = formalFreydSpineLanguage(b);
    const { call, tau, matrix, equality, comp, presentation, presentationType, morphismType, morphism, chainType, tailType, complexType } = L;
    const grpd = () => b.application('groupoid-universe', []);
    const ring = () => tau(b.free('bridge_CommRing'));
    const natType = () => tau(b.free('bridge_Nat_grpd'));
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term, ('explicit' | 'implicit')?];
    const telescope = (fields: readonly Field[], result: (s: Scope) => Term): Term => {
        const visit = (index: number, s: Scope): Term => index === fields.length ? result(s) :
            b.pi(fields[index][0], fields[index][1](s), token => visit(index + 1, { ...s, [fields[index][0]]: token }),
                binderMode(fields[index][2] ?? 'explicit', 'functorial'));
        return visit(0, {});
    };
    const add = (name: keyof typeof FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, fields: readonly Field[], result: (s: Scope) => Term) => {
        environment = environment.extend({ name, type: b.lower(telescope(fields, result)), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const naturalFields = (...names: string[]): Field[] => names.map(name => [name, natType]);
    add('bridge_CommRingPresentation', [['R', ring]], grpd);
    add('bridge_comm_ring_presentation_intro', [['R', ring, 'implicit'], ...naturalFields('p', 'r'),
        ['P', s => tau(matrix(s.R, s.p, s.r))]], s => presentationType(s.R));
    add('bridge_CommRingPresentationMorphism', [['R', ring], ['P', s => presentationType(s.R)],
        ['Q', s => presentationType(s.R)]], grpd);
    add('bridge_comm_ring_presentation_morphism_from_matrices', [
        ['R', ring], ...naturalFields('p', 'pr', 'q', 'qr'),
        ['P', s => tau(matrix(s.R, s.p, s.pr))], ['Q', s => tau(matrix(s.R, s.q, s.qr))],
        ['F', s => tau(matrix(s.R, s.q, s.p))], ['W', s => tau(matrix(s.R, s.qr, s.pr))],
        ['law', s => equality(matrix(s.R, s.q, s.pr), comp(s.R, s.q, s.qr, s.pr, s.Q, s.W), comp(s.R, s.q, s.p, s.pr, s.F, s.P))]
    ], s => morphismType(s.R, presentation(s.R, s.p, s.pr, s.P), presentation(s.R, s.q, s.qr, s.Q)));
    add('bridge_CommRingFreydChainPair', [['R', ring, 'implicit'],
        ...['P2', 'P1', 'P0'].map(name => [name, (s: Scope) => presentationType(s.R), 'implicit'] as Field),
        ['F', s => morphismType(s.R, s.P2, s.P1)], ['G', s => morphismType(s.R, s.P1, s.P0)]], grpd);
    add('bridge_comm_ring_freyd_chain_pair_from_matrices', [
        ['R', ring], ...naturalFields('p2', 'r2', 'p1', 'r1', 'p0', 'r0'),
        ...[2, 1, 0].map(i => ['P' + i, (s: Scope) => tau(matrix(s.R, s['p' + i], s['r' + i]))] as Field),
        ['F', s => tau(matrix(s.R, s.p1, s.p2))], ['WF', s => tau(matrix(s.R, s.r1, s.r2))],
        ['lawF', s => equality(matrix(s.R, s.p1, s.r2), comp(s.R, s.p1, s.r1, s.r2, s.P1, s.WF), comp(s.R, s.p1, s.p2, s.r2, s.F, s.P2))],
        ['G', s => tau(matrix(s.R, s.p0, s.p1))], ['WG', s => tau(matrix(s.R, s.r0, s.r1))],
        ['lawG', s => equality(matrix(s.R, s.p0, s.r1), comp(s.R, s.p0, s.r0, s.r1, s.P0, s.WG), comp(s.R, s.p0, s.p1, s.r1, s.G, s.P1))],
        ['H', s => tau(matrix(s.R, s.r0, s.p2))],
        ['law', s => equality(matrix(s.R, s.p0, s.p2), comp(s.R, s.p0, s.r0, s.p2, s.P0, s.H),
            call('bridge_comm_ring_matrix_sub', [s.R, s.p0, s.p2, comp(s.R, s.p0, s.p1, s.p2, s.G, s.F),
                call('bridge_comm_ring_matrix_zero', [s.R, s.p0, s.p2])]))]
    ], s => chainType(s.R, presentation(s.R, s.p2, s.r2, s.P2), presentation(s.R, s.p1, s.r1, s.P1),
        presentation(s.R, s.p0, s.r0, s.P0),
        morphism([s.R, s.p2, s.r2, s.p1, s.r1, s.P2, s.P1, s.F, s.WF, s.lawF]),
        morphism([s.R, s.p1, s.r1, s.p0, s.r0, s.P1, s.P0, s.G, s.WG, s.lawG])));
    const tailPrefix: Field[] = [['R', ring], ['n', natType], ['below', s => presentationType(s.R)],
        ['current', s => presentationType(s.R)], ['d', s => morphismType(s.R, s.current, s.below)]];
    add('bridge_CommRingFreydChainTail', tailPrefix, grpd);
    const implicitTail = tailPrefix.map(([name, type]) => [name, type, 'implicit'] as Field);
    add('bridge_comm_ring_freyd_chain_tail_nil', implicitTail.filter(([name]) => name !== 'n'),
        s => tailType(s.R, L.nat(0), s.below, s.current, s.d));
    add('bridge_comm_ring_freyd_chain_tail_cons', [...implicitTail,
        ['next', s => presentationType(s.R)], ['dNext', s => morphismType(s.R, s.next, s.current)],
        ['law', s => chainType(s.R, s.next, s.current, s.below, s.dNext, s.d)],
        ['rest', s => tailType(s.R, s.n, s.current, s.next, s.dNext)]
    ], s => tailType(s.R, call('bridge_nat_succ', [s.n]), s.below, s.current, s.d));
    add('bridge_CommRingFreydBoundedComplex', [['R', ring], ['n', natType]], grpd);
    add('bridge_comm_ring_freyd_bounded_complex_zero', [['R', ring, 'implicit'], ['P0', s => presentationType(s.R)]],
        s => complexType(s.R, L.nat(0)));
    add('bridge_comm_ring_freyd_bounded_complex_succ', [['R', ring, 'implicit'], ['n', natType, 'implicit'],
        ['P0', s => presentationType(s.R)], ['P1', s => presentationType(s.R)],
        ['d1', s => morphismType(s.R, s.P1, s.P0)], ['tail', s => tailType(s.R, s.n, s.P0, s.P1, s.d1)]
    ], s => complexType(s.R, call('bridge_nat_succ', [s.n])));
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'formal Freyd-spine input ' + input.name,
                sourceSpan('generated/formal-freyd-spine-inputs.ts', index + 1, 1)) });
    });
    return environment;
}
