/** Exact Core construction for the active algebraic Zariski-cover owner. */

import {
    KernelExpression,
    kernelCall,
    kernelFree,
    provenance
} from './kernel';
import {
    AffineFormalCoverRealization
} from './algebra_formal_realization';
import { AlgebraElement, AlgebraParent } from './algebra_parent';

export const ALGEBRA_FORMAL_COVER_PROFILE = Object.freeze({
    revision: 'emdash-affine-formal-cover-v1' as const,
    target: 'CommRingZariskiCoverPresentation' as const,
    familyRepresentation: 'Nat-indexed-right-associated-Sigma' as const,
    addsCoreOwner: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export const AFFINE_FORMAL_COVER_BINDINGS = Object.freeze({
    bridge_nat_zero: 'zero',
    bridge_nat_succ: 'succ',
    bridge_comm_ring_carrier: 'comm_ring_carrier',
    bridge_finite_family_nil: 'finite_family_nil',
    bridge_finite_family_cons: 'finite_family_cons',
    bridge_comm_ring_unimodular_intro: 'comm_ring_unimodular_intro',
    bridge_comm_ring_zariski_cover_intro: 'comm_ring_zariski_cover_intro'
});

export type AlgebraFormalCoverErrorCode =
    | 'FORMAL_COVER_UNAVAILABLE'
    | 'MISSING_FORMAL_LAW'
    | 'COVER_ARITY_MISMATCH';

export class AlgebraFormalCoverError extends Error {
    constructor(
        public readonly code: AlgebraFormalCoverErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraFormalCoverError';
    }
}

const fail = (
    code: AlgebraFormalCoverErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraFormalCoverError(code, path, message);
};

const nodeProvenance = provenance('derived', 'affine formal cover construction');

type CoverBinding = keyof typeof AFFINE_FORMAL_COVER_BINDINGS;

const call = (
    name: CoverBinding,
    arguments_: readonly {
        readonly plicity: 'explicit' | 'implicit';
        readonly value: KernelExpression;
    }[]
): KernelExpression => kernelCall(
    kernelFree(name, nodeProvenance),
    arguments_,
    nodeProvenance
);

const zero = (): KernelExpression => kernelFree('bridge_nat_zero', nodeProvenance);

const succ = (value: KernelExpression): KernelExpression => call(
    'bridge_nat_succ',
    [{ plicity: 'explicit', value }]
);

export interface AffineFormalFamilyTerms {
    readonly length: KernelExpression;
    readonly family: KernelExpression;
}

export function buildAffineFormalFamily(
    carrier: KernelExpression,
    elements: readonly KernelExpression[]
): AffineFormalFamilyTerms {
    let length = zero();
    let family = call('bridge_finite_family_nil', [
        { plicity: 'implicit', value: carrier }
    ]);
    for (let index = elements.length - 1; index >= 0; index--) {
        family = call('bridge_finite_family_cons', [
            { plicity: 'implicit', value: carrier },
            { plicity: 'implicit', value: length },
            { plicity: 'explicit', value: elements[index] },
            { plicity: 'explicit', value: family }
        ]);
        length = succ(length);
    }
    return Object.freeze({ length, family });
}

export interface AffineFormalCoverTerms<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision: typeof ALGEBRA_FORMAL_COVER_PROFILE.revision;
    readonly realization: AffineFormalCoverRealization<P, C, I>;
    readonly carrier: KernelExpression;
    readonly length: KernelExpression;
    readonly generators: KernelExpression;
    readonly coefficients: KernelExpression;
    readonly unimodular: KernelExpression;
    readonly cover: KernelExpression;
}

export function buildAffineFormalCoverTerms<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    realization: AffineFormalCoverRealization<P, C, I>
): AffineFormalCoverTerms<P, C, I> {
    if (!realization.formalCoverAvailable) {
        return fail(
            'FORMAL_COVER_UNAVAILABLE',
            'formalCoverTerms.realization',
            'Formal cover construction requires explicit or checked law data'
        );
    }
    if (realization.lawTerm === undefined) {
        return fail(
            'MISSING_FORMAL_LAW',
            'formalCoverTerms.law',
            'Formal cover construction lost its required law term'
        );
    }
    if (realization.generatorTerms.length !== realization.coefficientTerms.length) {
        return fail(
            'COVER_ARITY_MISMATCH',
            'formalCoverTerms.coefficients',
            'Generator and coefficient families have different lengths'
        );
    }
    const formalRing = realization.algebra.formalRing;
    const carrier = call('bridge_comm_ring_carrier', [
        { plicity: 'explicit', value: formalRing }
    ]);
    const generators = buildAffineFormalFamily(carrier, realization.generatorTerms);
    const coefficients = buildAffineFormalFamily(carrier, realization.coefficientTerms);
    const unimodular = call('bridge_comm_ring_unimodular_intro', [
        { plicity: 'implicit', value: formalRing },
        { plicity: 'implicit', value: generators.length },
        { plicity: 'implicit', value: generators.family },
        { plicity: 'explicit', value: coefficients.family },
        { plicity: 'explicit', value: realization.lawTerm }
    ]);
    const cover = call('bridge_comm_ring_zariski_cover_intro', [
        { plicity: 'implicit', value: formalRing },
        { plicity: 'explicit', value: generators.length },
        { plicity: 'explicit', value: generators.family },
        { plicity: 'explicit', value: unimodular }
    ]);
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_COVER_PROFILE.revision,
        realization,
        carrier,
        length: generators.length,
        generators: generators.family,
        coefficients: coefficients.family,
        unimodular,
        cover
    });
}
