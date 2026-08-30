/** Parent-aware computational-to-formal affine realization contracts. */

import {
    KernelExpression,
    kernelAssertScoped
} from './kernel';
import { serializeCoreExpression } from './core_serialization';
import { serializeKernelExpression } from './lambdapi';
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraPresentedAlgebra,
    algebraPresentedAlgebraEquals
} from './algebra_presented_algebra';
import {
    AlgebraQuotientElement
} from './algebra_quotient';
import {
    AlgebraAffineCover
} from './algebra_cech';

export const ALGEBRA_FORMAL_REALIZATION_PROFILE = Object.freeze({
    revision: 'emdash-affine-formal-realization-v1' as const,
    statusRevision: 'emdash-affine-formal-status-v1' as const,
    trustedProducesFormalLaw: false as const,
    addsCoreOwner: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AffineFormalRealizationStatus =
    | 'explicit-data'
    | 'trusted-computation'
    | 'checked';

export type AlgebraFormalRealizationErrorCode =
    | 'INVALID_STATUS'
    | 'INVALID_CORE_TERM'
    | 'FOREIGN_QUOTIENT_ELEMENT'
    | 'NONDETERMINISTIC_REIFIER'
    | 'FOREIGN_AFFINE_COVER'
    | 'MISSING_FORMAL_LAW'
    | 'TRUSTED_FORMAL_LAW';

export class AlgebraFormalRealizationError extends Error {
    constructor(
        public readonly code: AlgebraFormalRealizationErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraFormalRealizationError';
    }
}

const fail = (
    code: AlgebraFormalRealizationErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraFormalRealizationError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const status = (value: unknown): AffineFormalRealizationStatus => {
    if (value === 'explicit-data' || value === 'trusted-computation' ||
        value === 'checked') return value;
    return fail(
        'INVALID_STATUS',
        'formalRealization.status',
        'Expected explicit-data, trusted-computation, or checked status'
    );
};

const checkedClosedTerm = (
    value: KernelExpression,
    path: string
): KernelExpression => {
    try {
        kernelAssertScoped(value);
        // The Lambdapi serializer additionally rejects unsolved metas.
        serializeKernelExpression(value);
        return value;
    } catch (error: unknown) {
        return fail(
            'INVALID_CORE_TERM',
            path,
            'Formal realization requires one closed meta-free Core term',
            error
        );
    }
};

export interface AffineFormalAlgebraRealizationInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly algebra: AlgebraPresentedAlgebra<P, C, I>;
    readonly formalRing: KernelExpression;
    readonly status: AffineFormalRealizationStatus;
    readonly reifyElement: (
        element: AlgebraQuotientElement<P, C, I>
    ) => KernelExpression;
}

export interface AffineFormalAlgebraRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision: typeof ALGEBRA_FORMAL_REALIZATION_PROFILE.revision;
    readonly algebra: AlgebraPresentedAlgebra<P, C, I>;
    readonly quotientId: string;
    readonly formalRing: KernelExpression;
    readonly status: AffineFormalRealizationStatus;
    reifyElement(element: AlgebraQuotientElement<P, C, I>): KernelExpression;
}

export function defineAffineFormalAlgebraRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    input: AffineFormalAlgebraRealizationInput<P, C, I>
): AffineFormalAlgebraRealization<P, C, I> {
    if (typeof input.reifyElement !== 'function') {
        return fail(
            'INVALID_CORE_TERM',
            'formalRealization.reifyElement',
            'Formal algebra realization requires one element reifier'
        );
    }
    const formalRing = checkedClosedTerm(input.formalRing, 'formalRealization.formalRing');
    const selectedStatus = status(input.status);
    const quotientId = input.algebra.quotient.identity.id;
    const reify = (element: AlgebraQuotientElement<P, C, I>): KernelExpression => {
        if (element.parent.identity.id !== quotientId ||
            element.parent.identity.revision !== input.algebra.quotient.identity.revision) {
            return fail(
                'FOREIGN_QUOTIENT_ELEMENT',
                'formalRealization.element',
                'Element belongs to a foreign computational quotient parent'
            );
        }
        return checkedClosedTerm(
            input.reifyElement(element),
            'formalRealization.reifiedElement'
        );
    };
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_REALIZATION_PROFILE.revision,
        algebra: input.algebra,
        quotientId,
        formalRing,
        status: selectedStatus,
        reifyElement: reify
    });
}

const deterministicTerms = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    realization: AffineFormalAlgebraRealization<P, C, I>,
    elements: readonly AlgebraQuotientElement<P, C, I>[],
    path: string
): readonly KernelExpression[] => Object.freeze(elements.map((element, index) => {
    const first = realization.reifyElement(element);
    const second = realization.reifyElement(element);
    if (serializeCoreExpression(first) !== serializeCoreExpression(second)) {
        return fail(
            'NONDETERMINISTIC_REIFIER',
            `${path}[${index}]`,
            'Element reifier returned different explicit Core terms'
        );
    }
    return first;
}));

export interface AffineFormalCoverRealizationInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly cover: AlgebraAffineCover<P, C, I>;
    readonly algebra: AffineFormalAlgebraRealization<P, C, I>;
    readonly status: AffineFormalRealizationStatus;
    readonly lawTerm?: KernelExpression;
}

export interface AffineFormalCoverRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision: typeof ALGEBRA_FORMAL_REALIZATION_PROFILE.revision;
    readonly cover: AlgebraAffineCover<P, C, I>;
    readonly algebra: AffineFormalAlgebraRealization<P, C, I>;
    readonly status: AffineFormalRealizationStatus;
    readonly generatorTerms: readonly KernelExpression[];
    readonly coefficientTerms: readonly KernelExpression[];
    readonly lawTerm?: KernelExpression;
    readonly computationalEquationHolds: true;
    readonly formalCoverAvailable: boolean;
}

export function defineAffineFormalCoverRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    input: AffineFormalCoverRealizationInput<P, C, I>
): AffineFormalCoverRealization<P, C, I> {
    const selectedStatus = status(input.status);
    if (!algebraPresentedAlgebraEquals(
        input.cover.ambient.coordinateAlgebra,
        input.algebra.algebra
    )) {
        return fail(
            'FOREIGN_AFFINE_COVER',
            'formalCover.cover',
            'Affine cover and formal algebra realization have different parents'
        );
    }
    const generatorTerms = deterministicTerms(
        input.algebra,
        input.cover.elements,
        'formalCover.generators'
    );
    const coefficientTerms = deterministicTerms(
        input.algebra,
        input.cover.elementCoefficients,
        'formalCover.coefficients'
    );
    if (generatorTerms.length !== coefficientTerms.length) {
        return fail(
            'FOREIGN_AFFINE_COVER',
            'formalCover.coefficients',
            'Cover generator and coefficient arities differ'
        );
    }
    let lawTerm: KernelExpression | undefined;
    if (selectedStatus === 'trusted-computation') {
        if (input.lawTerm !== undefined) {
            return fail(
                'TRUSTED_FORMAL_LAW',
                'formalCover.lawTerm',
                'Trusted computation metadata must not masquerade as a formal law'
            );
        }
    } else {
        if (input.lawTerm === undefined) {
            return fail(
                'MISSING_FORMAL_LAW',
                'formalCover.lawTerm',
                'Explicit or checked cover realization requires a formal law term'
            );
        }
        lawTerm = checkedClosedTerm(input.lawTerm, 'formalCover.lawTerm');
    }
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_REALIZATION_PROFILE.revision,
        cover: input.cover,
        algebra: input.algebra,
        status: selectedStatus,
        generatorTerms,
        coefficientTerms,
        ...(lawTerm === undefined ? {} : { lawTerm }),
        computationalEquationHolds: true,
        formalCoverAvailable: lawTerm !== undefined
    });
}
