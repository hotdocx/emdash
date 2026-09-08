/** Construct the existing formal bounded Freyd carrier, not a recipe placeholder. */

import { KernelExpression, provenance } from './kernel';
import { CoreLfScopedBuilder } from './lf_builder';
import { formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';

export const ALGEBRA_FORMAL_FREYD_BOUNDED_SPINE_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-bounded-spine-v1' as const,
    inputOrder: 'displayed-left-to-right' as const,
    formalOrder: 'P0-is-rightmost' as const,
    constructsExistingOwner: 'CommRingFreydBoundedComplex' as const,
    addsCoreOwner: false as const,
    claimsExactness: false as const,
    performsIo: false as const
});

/** Laws are the actual CommRingFreydChainPair values on consecutive arrows. */
export function algebraFormalFreydBoundedSpineTerm(input: {
    readonly formalRing: KernelExpression;
    readonly presentations: readonly KernelExpression[];
    readonly arrows: readonly KernelExpression[];
    readonly laws: readonly KernelExpression[];
}) {
    const n = input.arrows.length;
    if (input.presentations.length !== n + 1 || input.laws.length !== Math.max(0, n - 1)) {
        throw new Error('A formal bounded spine needs one more presentation than arrows and one law per adjacent pair');
    }
    const b = new CoreLfScopedBuilder(provenance('derived', 'formal Freyd bounded spine'));
    const L = formalFreydSpineLanguage(b);
    const R = b.embed(input.formalRing);
    const P = [...input.presentations].reverse().map(term => b.embed(term));
    const d = [...input.arrows].reverse().map(term => b.embed(term));
    const laws = [...input.laws].reverse().map(term => b.embed(term));
    let term;
    if (n === 0) term = L.call('bridge_comm_ring_freyd_bounded_complex_zero', [R, P[0]], 1);
    else {
        let tail = L.call('bridge_comm_ring_freyd_chain_tail_nil', [R, P[n - 1], P[n], d[n - 1]], 4);
        for (let degree = n - 1; degree >= 1; degree--) {
            tail = L.call('bridge_comm_ring_freyd_chain_tail_cons', [R, L.nat(n - degree - 1),
                P[degree - 1], P[degree], d[degree - 1], P[degree + 1], d[degree], laws[degree - 1], tail], 5);
        }
        term = L.call('bridge_comm_ring_freyd_bounded_complex_succ', [R, L.nat(n - 1), P[0], P[1], d[0], tail], 2);
    }
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_FREYD_BOUNDED_SPINE_PROFILE.revision,
        length: n, term: b.lower(term), type: b.lower(L.complexType(R, L.nat(n))),
        displayedToFormalDegree: Object.freeze(input.presentations.map((_, index) => n - index))
    });
}
