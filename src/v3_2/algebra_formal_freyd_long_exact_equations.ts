/** Labelled selected equations for the whole bounded homological computation. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AffineFormalPolynomialReifier } from './algebra_formal_reifier';
import {
    AlgebraFormalPresentationAgreementRealization,
    AlgebraFormalPresentationMorphismRealization,
    defineAlgebraFormalPresentationAgreementRealization,
    defineAlgebraFormalPresentationMorphismRealization
} from './algebra_formal_presentation_morphism';
import {
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement
} from './algebra_polynomial_presentation_morphism';
import {
    algebraFormalFreydHomologyDelegationBundle,
    algebraFormalFreydExactnessDelegationBundle,
    algebraFormalFreydInducedHomologyDelegationBundle
} from './algebra_formal_freyd_homology';
import { algebraFormalFreydSnakeDelegationBundle } from './algebra_formal_freyd_snake';
import { AlgebraPolynomialFreydExactnessAt } from './algebra_polynomial_freyd_homology';
import {
    AlgebraPolynomialFreydLongExactSnakeReferences,
    serializeAlgebraPolynomialFreydLongExactSnakeReferences
} from './algebra_polynomial_freyd_long_exact_reference_operations';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import { encodeAlgebraFormalFreydLongExactData } from './algebra_formal_freyd_long_exact_encoding';

export const ALGEBRA_FORMAL_FREYD_LONG_EXACT_EQUATIONS_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-long-exact-equations-v1' as const,
    claimSharing: 'identical-core-claim-type' as const,
    retainsEveryLabel: true as const,
    claimsGenericFormalExactness: false as const,
    claimsQuotientPathDecoding: false as const,
    addsCoreOwner: false as const
});

export type AlgebraFormalFreydLongExactEquation<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = {
    readonly id: string;
    readonly kind: 'morphism';
    readonly realization: AlgebraFormalPresentationMorphismRealization<P, C, I>;
} | {
    readonly id: string;
    readonly kind: 'agreement';
    readonly realization: AlgebraFormalPresentationAgreementRealization<P, C, I>;
};

/** Reify before creating the proof environment, so all coefficient bindings are known. */
export function algebraFormalFreydLongExactEquations<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydLongExactSnakeReferences<P, C, I>;
}) {
    const selectedOutputData = encodeAlgebraFormalFreydLongExactData(
        serializeAlgebraPolynomialFreydLongExactSnakeReferences(input.selected));
    const whole = input.selected.result;
    const entries: AlgebraFormalFreydLongExactEquation<P, C, I>[] = [];
    const ids = new Set<string>();
    const append = (entry: AlgebraFormalFreydLongExactEquation<P, C, I>) => {
        if (ids.has(entry.id)) throw new Error('Duplicate long-exact equation label: ' + entry.id);
        ids.add(entry.id);
        entries.push(Object.freeze(entry));
    };
    const morphism = (id: string, selected: AlgebraPolynomialPresentationMorphism<P, C, I>) => append({
        id, kind: 'morphism', realization: defineAlgebraFormalPresentationMorphismRealization({ reifier: input.reifier, selected })
    });
    const agreement = (id: string, selected: AlgebraPolynomialPresentationMorphismAgreement<P, C, I>) => append({
        id, kind: 'agreement', realization: defineAlgebraFormalPresentationAgreementRealization({ reifier: input.reifier, selected })
    });
    // These are existing, locally generated bundles; only their realizations
    // are reused here, not their per-equation whole-operation replay adapters.
    const bundle = (prefix: string, value: object) => {
        for (const [name, entry] of Object.entries(value)) {
            if (name === 'model' || typeof entry !== 'object' || entry === null || !('realization' in entry)) continue;
            const realization = entry.realization as AlgebraFormalPresentationMorphismRealization<P, C, I> |
                AlgebraFormalPresentationAgreementRealization<P, C, I>;
            if ('formalMap' in realization) append({ id: prefix + '/' + name, kind: 'morphism', realization });
            else append({ id: prefix + '/' + name, kind: 'agreement', realization });
        }
    };
    const exact = (prefix: string, value: AlgebraPolynomialFreydExactnessAt<P, C, I>) => {
        if (!value.exact || !value.epimorphism) throw new Error('Selected exactness witness is missing at ' + prefix);
        bundle(prefix, algebraFormalFreydExactnessDelegationBundle({ reifier: input.reifier, selected: value }));
        agreement(prefix + '/boundary-epic-cokernel-zero', value.epimorphism.cokernelZeroAgreement);
    };

    // Index every displayed map and zero. Repeated identical claim types
    // share an assumption, not their separately labelled selected data.
    agreement('long-exact/zero/0', whole.interior[0].pair.chainAgreement);
    whole.arrows.forEach((value, index) => morphism('long-exact/map/' + index, value));
    whole.interior.forEach((point, index) => {
        if (index !== 0) agreement('long-exact/zero/' + index, point.pair.chainAgreement);
        exact('long-exact/exact/' + point.term.position, point.exactness);
    });
    agreement('long-exact/initial-zero', whole.endpoints.initialZero);
    agreement('long-exact/final-zero', whole.endpoints.finalZero);
    for (const [name, map] of [['inclusion', whole.sequence.inclusion], ['projection', whole.sequence.projection]] as const) {
        map.squares.forEach(square => agreement('sequence/' + name + '/chain/' + square.degree, square.agreement));
    }
    whole.sequence.rows.forEach(row => {
        const prefix = 'sequence/row/' + row.degree;
        morphism(prefix + '/incoming', row.triple.incoming);
        morphism(prefix + '/outgoing', row.triple.outgoing);
        agreement(prefix + '/zero', row.triple.pair.chainAgreement);
        agreement(prefix + '/incoming-monic', row.triple.incomingMonomorphism.kernelZeroAgreement);
        agreement(prefix + '/outgoing-epic', row.triple.outgoingEpimorphism.cokernelZeroAgreement);
        exact(prefix + '/exact', row.triple.exactness);
    });
    whole.degrees.forEach(degree => {
        for (const role of ['A', 'B', 'C'] as const) {
            bundle('homology/' + degree.degree + '/' + role,
                algebraFormalFreydHomologyDelegationBundle({ reifier: input.reifier, selected: degree[role].homology }));
        }
        bundle('induced/' + degree.degree + '/inclusion',
            algebraFormalFreydInducedHomologyDelegationBundle({ reifier: input.reifier, selected: degree.inclusion }));
        bundle('induced/' + degree.degree + '/projection',
            algebraFormalFreydInducedHomologyDelegationBundle({ reifier: input.reifier, selected: degree.projection }));
    });
    whole.windows.forEach(window => {
        const prefix = 'connecting/' + window.degree;
        const c = window.connecting;
        morphism(prefix + '/map', c.homologyMap);
        agreement(prefix + '/reconstruction', c.reconstruction.agreement);
        agreement(prefix + '/gamma-comparison', c.trace.gammaAgreement);
        agreement(prefix + '/alpha-comparison', c.trace.alphaAgreement);
        for (const name of ['upperComparison', 'lowerComparison', 'cycleComparison', 'targetComparison'] as const) {
            agreement(prefix + '/' + name + '/left', c.trace[name].sourceAgreement);
            agreement(prefix + '/' + name + '/right', c.trace[name].targetAgreement);
        }
        for (const name of ['upperForward', 'lowerForward', 'cycleForward', 'cycleInverse',
            'targetForward', 'targetInverse', 'homologyEmbedding', 'descent'] as const) {
            agreement(prefix + '/' + name + '/zero', c.trace[name].zeroAgreement);
            agreement(prefix + '/' + name + '/reconstruction', c.trace[name].reconstructionAgreement);
        }
        agreement(prefix + '/upperInverse/test', c.trace.upperInverse.testKernelZeroAgreement);
        agreement(prefix + '/upperInverse/reconstruction', c.trace.upperInverse.reconstructionAgreement);
        for (const name of ['lowerInverse', 'targetFactor'] as const) {
            agreement(prefix + '/' + name + '/test', c.trace[name].testCokernelZeroAgreement);
            agreement(prefix + '/' + name + '/reconstruction', c.trace[name].reconstructionAgreement);
        }
        morphism(prefix + '/target-factor', c.trace.targetFactor.lift);
        bundle('snake/' + window.degree, algebraFormalFreydSnakeDelegationBundle({ reifier: input.reifier, selected: c.trace.snake }));
    });
    input.selected.sequences.forEach((sequence, degree) => {
        const prefix = 'snake-exact/' + degree;
        sequence.arrows.forEach((value, index) => morphism(prefix + '/map/' + index, value));
        sequence.pairs.forEach((value, index) => agreement(prefix + '/zero/' + index, value.chainAgreement));
        sequence.exactness.forEach((value, index) => exact(prefix + '/exact/' + index, value));
        for (const name of ['kernelAlphaBeta', 'kernelBetaGamma', 'cokernelAlphaBeta', 'cokernelBetaGamma'] as const) {
            agreement(prefix + '/' + name + '/zero', sequence[name].zeroAgreement);
            agreement(prefix + '/' + name + '/reconstruction', sequence[name].reconstructionAgreement);
        }
    });

    const byClaim = new Map<string, { representative: AlgebraFormalFreydLongExactEquation<P, C, I>; labels: string[] }>();
    for (const entry of entries) {
        const key = serializeCoreExpression(entry.realization.claimType);
        const previous = byClaim.get(key);
        if (previous) previous.labels.push(entry.id);
        else byClaim.set(key, { representative: entry, labels: [entry.id] });
    }
    const claims = Object.freeze([...byClaim.values()].map(value => Object.freeze({
        representative: value.representative, labels: Object.freeze(value.labels)
    })));
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_FREYD_LONG_EXACT_EQUATIONS_PROFILE.revision,
        selectedOutputData, entries: Object.freeze(entries), claims
    });
}

export type AlgebraFormalFreydLongExactEquations<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = ReturnType<typeof algebraFormalFreydLongExactEquations<P, C, I>>;

export function serializeAlgebraFormalFreydLongExactEquations<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraFormalFreydLongExactEquations<P, C, I>): string {
    return encodeAlgebraFormalFreydLongExactData(serializeCoreLfWorkspaceCanonicalJson({
        profileRevision: value.profileRevision, selectedOutputData: value.selectedOutputData,
        entries: value.entries.map(entry => ({
            id: entry.id, kind: entry.kind, selected: entry.realization.selectedOutputData,
            claim: serializeCoreExpression(entry.realization.claimType)
        })),
        claims: value.claims.map(claim => ({ representative: claim.representative.id, labels: claim.labels }))
    }, 'formalFreydLongExactEquations'));
}
