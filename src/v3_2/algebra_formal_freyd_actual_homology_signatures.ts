/** Signature-only frontend for transparent actual-boundary homology constructors. */

import { CoreLfBuilderTerm as Term, CoreLfScopedBuilder } from './lf_builder';
import { binderMode, provenance, sourceSpan } from './kernel';
import { AffineFormalZariskiInputDeclaration } from './algebra_formal_zariski_signatures';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { createFormalFreydKernelChoiceProviderProofEnvironment } from './algebra_formal_freyd_kernel_choice_provider_signatures';
import { createFormalFreydEpimorphismProofEnvironment, FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS } from './algebra_formal_freyd_epimorphism_signatures';

export const FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS = Object.freeze({
    bridge_CommRingFreydSelectedHomologyAt: 'CommRingFreydSelectedHomologyAt',
    bridge_CommRingFreydSelectedExactnessAt: 'CommRingFreydSelectedExactnessAt',
    bridge_comm_ring_freyd_homology_from_matrix_providers: 'comm_ring_freyd_homology_from_matrix_providers',
    bridge_comm_ring_freyd_exactness_from_matrix_providers: 'comm_ring_freyd_exactness_from_matrix_providers'
});

/** The backend declarations have transparent bodies; these are only type mirrors. */
export function createFormalFreydActualHomologyProofEnvironment(inputs: readonly AffineFormalZariskiInputDeclaration[]) {
    let environment = createFormalFreydKernelChoiceProviderProofEnvironment([]);
    const epicity = createFormalFreydEpimorphismProofEnvironment([]);
    for (const name of Object.keys(FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS)) {
        environment = environment.extend(epicity.lookup(name)!);
    }
    const p = provenance('derived', 'formal actual homology signatures');
    const b = new CoreLfScopedBuilder(p);
    const L = formalFreydSpineLanguage(b);
    type Scope = Readonly<Record<string, Term>>;
    type Field = readonly [string, (s: Scope) => Term, ('explicit' | 'implicit')?];
    const ring = () => L.tau(b.free('bridge_CommRing'));
    const nat = () => L.tau(b.free('bridge_Nat_grpd'));
    const grpd = () => b.application('groupoid-universe', []);
    const add = (name: keyof typeof FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS,
        fields: readonly Field[], result: (s: Scope) => Term) => {
        const visit = (index: number, s: Scope): Term => index === fields.length ? result(s) :
            b.pi(fields[index][0], fields[index][1](s), value => visit(index + 1, { ...s, [fields[index][0]]: value }),
                binderMode(fields[index][2] ?? 'explicit', 'functorial'));
        environment = environment.extend({ name, type: b.lower(visit(0, {})), mode: binderMode('explicit', 'functorial'), provenance: p });
    };
    const selectedPrefix: Field[] = [['R', ring, 'implicit'],
        ...['P2', 'P1', 'P0'].map(name => [name, (s: Scope) => L.presentationType(s.R), 'implicit'] as Field),
        ['F', s => L.morphismType(s.R, s.P2, s.P1)], ['G', s => L.morphismType(s.R, s.P1, s.P0)],
        ['K', s => L.tau(L.call('bridge_CommRingFreydKernelChoices', [s.R, s.P1, s.P0, s.G], 3))],
        ['chain', s => L.chainType(s.R, s.P2, s.P1, s.P0, s.F, s.G)]];
    const selectedArgs = (s: Scope) => [s.R, s.P2, s.P1, s.P0, s.F, s.G, s.K, s.chain];
    add('bridge_CommRingFreydSelectedHomologyAt', selectedPrefix, grpd);
    add('bridge_CommRingFreydSelectedExactnessAt', [
        ...selectedPrefix.map(field => [field[0], field[1], 'implicit'] as Field),
        ['homology', s => L.tau(L.call('bridge_CommRingFreydSelectedHomologyAt', selectedArgs(s), 4))]
    ], grpd);
    const pres = (s: Scope, i: number) => L.presentation(s.R, s['n' + i], s['r' + i], s['P' + i]);
    const above = (s: Scope) => L.morphism([s.R, s.n2, s.r2, s.n1, s.r1, s.P2, s.P1, s.F, s.WF, s.lawF]);
    const below = (s: Scope) => L.morphism([s.R, s.n1, s.r1, s.n0, s.r0, s.P1, s.P0, s.G, s.WG, s.lawG]);
    const boundary = (s: Scope) => L.morphism([s.R, s.n2, s.r2, s.k1, s.k2, s.P2, s.p2, s.B, s.WB, s.lawB]);
    const first = (s: Scope) => [s.R, s.n1, s.n0, s.r0, s.k1, s.G, s.P0, s.p1, s.q1, s.compatible1];
    const second = (s: Scope) => [s.R, s.k1, s.n1, s.r1, s.k2, s.p1, s.P1, s.p2, s.q2, s.compatible2];
    const choices = (s: Scope) => L.call('bridge_comm_ring_freyd_kernel_choices_from_matrix_providers',
        [s.R, s.n1, s.r1, s.n0, s.r0, s.P1, s.P0, s.G, s.WG, s.lawG,
            s.k1, s.p1, s.q1, s.compatible1, s.provider1, s.k2, s.p2, s.q2, s.compatible2, s.provider2]);
    const homologyArgs = (s: Scope) => [s.R, pres(s, 2), pres(s, 1), pres(s, 0), above(s), below(s), choices(s), s.chain];
    const fields: Field[] = [['R', ring],
        ...['n2', 'r2', 'n1', 'r1', 'n0', 'r0'].map(name => [name, nat] as Field),
        ...[2, 1, 0].map(i => ['P' + i, (s: Scope) => L.tau(L.matrix(s.R, s['n' + i], s['r' + i]))] as Field),
        ['F', s => L.tau(L.matrix(s.R, s.n1, s.n2))], ['WF', s => L.tau(L.matrix(s.R, s.r1, s.r2))],
        ['lawF', s => L.equality(L.matrix(s.R, s.n1, s.r2), L.comp(s.R, s.n1, s.r1, s.r2, s.P1, s.WF), L.comp(s.R, s.n1, s.n2, s.r2, s.F, s.P2))],
        ['G', s => L.tau(L.matrix(s.R, s.n0, s.n1))], ['WG', s => L.tau(L.matrix(s.R, s.r0, s.r1))],
        ['lawG', s => L.equality(L.matrix(s.R, s.n0, s.r1), L.comp(s.R, s.n0, s.r0, s.r1, s.P0, s.WG), L.comp(s.R, s.n0, s.n1, s.r1, s.G, s.P1))],
        ['chain', s => L.chainType(s.R, pres(s, 2), pres(s, 1), pres(s, 0), above(s), below(s))],
        ['k1', nat], ['p1', s => L.tau(L.matrix(s.R, s.n1, s.k1))], ['q1', s => L.tau(L.matrix(s.R, s.r0, s.k1))],
        ['compatible1', s => L.equality(L.matrix(s.R, s.n0, s.k1), L.comp(s.R, s.n0, s.n1, s.k1, s.G, s.p1), L.comp(s.R, s.n0, s.r0, s.k1, s.P0, s.q1))],
        ['provider1', s => L.tau(L.call('bridge_CommRingFiniteFreeWeakPullbackMatrixProvider', first(s)))],
        ['k2', nat], ['p2', s => L.tau(L.matrix(s.R, s.k1, s.k2))], ['q2', s => L.tau(L.matrix(s.R, s.r1, s.k2))],
        ['compatible2', s => L.equality(L.matrix(s.R, s.n1, s.k2), L.comp(s.R, s.n1, s.k1, s.k2, s.p1, s.p2), L.comp(s.R, s.n1, s.r1, s.k2, s.P1, s.q2))],
        ['provider2', s => L.tau(L.call('bridge_CommRingFiniteFreeWeakPullbackMatrixProvider', second(s)))],
        ['B', s => L.tau(L.matrix(s.R, s.k1, s.n2))], ['WB', s => L.tau(L.matrix(s.R, s.k2, s.r2))],
        ['lawB', s => L.equality(L.matrix(s.R, s.k1, s.r2), L.comp(s.R, s.k1, s.k2, s.r2, s.p2, s.WB), L.comp(s.R, s.k1, s.n2, s.r2, s.B, s.P2))],
        ['H', s => L.tau(L.matrix(s.R, s.r1, s.n2))],
        ['lawH', s => L.equality(L.matrix(s.R, s.n1, s.n2), L.comp(s.R, s.n1, s.r1, s.n2, s.P1, s.H),
            L.call('bridge_comm_ring_matrix_sub', [s.R, s.n1, s.n2, L.comp(s.R, s.n1, s.k1, s.n2, s.p1, s.B), s.F]))]];
    const args = (s: Scope) => fields.map(field => s[field[0]]);
    add('bridge_comm_ring_freyd_homology_from_matrix_providers', fields,
        s => L.tau(L.call('bridge_CommRingFreydSelectedHomologyAt', homologyArgs(s), 4)));
    add('bridge_comm_ring_freyd_exactness_from_matrix_providers', [...fields,
        ['epic', s => L.tau(L.call('bridge_CommRingFreydEpimorphismWitness', [s.R, pres(s, 2),
            L.presentation(s.R, s.k1, s.k2, s.p2), boundary(s)], 3))]],
    s => L.tau(L.call('bridge_CommRingFreydSelectedExactnessAt', [...homologyArgs(s),
        L.call('bridge_comm_ring_freyd_homology_from_matrix_providers', args(s))], 8)));
    inputs.forEach((input, index) => {
        environment = environment.extend({ ...input, mode: input.mode ?? binderMode('explicit', 'functorial'),
            provenance: provenance('surface', 'actual homology input ' + input.name,
                sourceSpan('generated/formal-actual-homology-inputs.ts', index + 1, 1)) });
    });
    return environment;
}
