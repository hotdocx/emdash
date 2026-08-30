/** Canonical quotient-polynomial evaluation into a supplied formal ring. */

import {
    KernelExpression,
    kernelCall,
    kernelFree,
    provenance
} from './kernel';
import { serializeCoreExpression } from './core_serialization';
import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomial,
    validateAlgebraPolynomial
} from './algebra_polynomial';
import {
    AlgebraQuotientElement
} from './algebra_quotient';
import {
    AlgebraPresentedAlgebra
} from './algebra_presented_algebra';
import {
    AffineFormalAlgebraRealization,
    AffineFormalRealizationStatus,
    defineAffineFormalAlgebraRealization,
    validateAffineFormalCoreTerm
} from './algebra_formal_realization';

export const ALGEBRA_FORMAL_REIFIER_PROFILE = Object.freeze({
    revision: 'emdash-affine-formal-polynomial-reifier-v1' as const,
    powerTree: 'binary-exponentiation' as const,
    maximumExponent: 4096n,
    addsCoreOwner: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export const AFFINE_FORMAL_RING_BINDINGS = Object.freeze({
    bridge_comm_ring_zero: 'comm_ring_zero',
    bridge_comm_ring_one: 'comm_ring_one',
    bridge_comm_ring_add: 'comm_ring_add',
    bridge_comm_ring_neg: 'comm_ring_neg',
    bridge_comm_ring_mul: 'comm_ring_mul'
});

export type AlgebraFormalReifierErrorCode =
    | 'GENERATOR_ARITY_MISMATCH'
    | 'FOREIGN_POLYNOMIAL'
    | 'FOREIGN_QUOTIENT_ELEMENT'
    | 'EXPONENT_LIMIT_EXCEEDED'
    | 'NONDETERMINISTIC_COEFFICIENT';

export class AlgebraFormalReifierError extends Error {
    constructor(
        public readonly code: AlgebraFormalReifierErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraFormalReifierError';
    }
}

const fail = (
    code: AlgebraFormalReifierErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraFormalReifierError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

export interface AffineFormalPolynomialReifierInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly algebra: AlgebraPresentedAlgebra<P, C, I>;
    readonly formalRing: KernelExpression;
    readonly generatorTerms: readonly KernelExpression[];
    readonly coefficientReifier: (coefficient: C) => KernelExpression;
    readonly status: AffineFormalRealizationStatus;
    readonly maximumExponent?: bigint;
}

export interface AffineFormalPolynomialReifier<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision: typeof ALGEBRA_FORMAL_REIFIER_PROFILE.revision;
    readonly algebra: AlgebraPresentedAlgebra<P, C, I>;
    readonly formalRing: KernelExpression;
    readonly generatorTerms: readonly KernelExpression[];
    readonly maximumExponent: bigint;
    readonly realization: AffineFormalAlgebraRealization<P, C, I>;
    reifyPolynomial(polynomial: AlgebraPolynomial<P, C, I>): KernelExpression;
    reifyElement(element: AlgebraQuotientElement<P, C, I>): KernelExpression;
}

const nodeProvenance = provenance('derived', 'affine formal polynomial reifier');

const call = (
    name: keyof typeof AFFINE_FORMAL_RING_BINDINGS,
    arguments_: readonly KernelExpression[]
): KernelExpression => kernelCall(
    kernelFree(name, nodeProvenance),
    arguments_.map(value => ({ plicity: 'explicit' as const, value })),
    nodeProvenance
);

export function defineAffineFormalPolynomialReifier<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: AffineFormalPolynomialReifierInput<P, C, I>):
    AffineFormalPolynomialReifier<P, C, I> {
    if (input.generatorTerms.length !==
        input.algebra.quotient.polynomialRing.variables.length) {
        return fail(
            'GENERATOR_ARITY_MISMATCH',
            'formalPolynomialReifier.generatorTerms',
            `Expected ${input.algebra.quotient.polynomialRing.variables.length} ` +
                'formal generator terms'
        );
    }
    const formalRing = validateAffineFormalCoreTerm(
        input.formalRing,
        'formalPolynomialReifier.formalRing'
    );
    const generatorTerms = Object.freeze(input.generatorTerms.map(
        (term, index) => validateAffineFormalCoreTerm(
            term,
            `formalPolynomialReifier.generatorTerms[${index}]`
        )
    ));
    const maximumExponent = input.maximumExponent ??
        ALGEBRA_FORMAL_REIFIER_PROFILE.maximumExponent;
    if (typeof maximumExponent !== 'bigint' || maximumExponent < 0n) {
        return fail(
            'EXPONENT_LIMIT_EXCEEDED',
            'formalPolynomialReifier.maximumExponent',
            'Maximum exponent must be a nonnegative bigint'
        );
    }
    const zero = () => call('bridge_comm_ring_zero', [formalRing]);
    const one = () => call('bridge_comm_ring_one', [formalRing]);
    const add = (left: KernelExpression, right: KernelExpression) =>
        call('bridge_comm_ring_add', [formalRing, left, right]);
    const multiply = (left: KernelExpression, right: KernelExpression) =>
        call('bridge_comm_ring_mul', [formalRing, left, right]);
    const coefficient = (value: C): KernelExpression => {
        const first = validateAffineFormalCoreTerm(
            input.coefficientReifier(value),
            'formalPolynomialReifier.coefficient'
        );
        const second = validateAffineFormalCoreTerm(
            input.coefficientReifier(value),
            'formalPolynomialReifier.coefficient'
        );
        if (serializeCoreExpression(first) !== serializeCoreExpression(second)) {
            return fail(
                'NONDETERMINISTIC_COEFFICIENT',
                'formalPolynomialReifier.coefficient',
                'Coefficient reifier returned different explicit Core terms'
            );
        }
        return first;
    };
    const power = (base: KernelExpression, exponent: bigint): KernelExpression => {
        if (exponent > maximumExponent) {
            return fail(
                'EXPONENT_LIMIT_EXCEEDED',
                'formalPolynomialReifier.exponent',
                `Exponent ${exponent} exceeds limit ${maximumExponent}`
            );
        }
        if (exponent === 0n) return one();
        if (exponent === 1n) return base;
        const half = power(base, exponent / 2n);
        const square = multiply(half, half);
        return exponent % 2n === 0n ? square : multiply(square, base);
    };
    const reifyPolynomial = (
        polynomialInput: AlgebraPolynomial<P, C, I>
    ): KernelExpression => {
        let polynomial: AlgebraPolynomial<P, C, I>;
        try {
            polynomial = validateAlgebraPolynomial(
                input.algebra.quotient.polynomialRing,
                polynomialInput,
                'formalPolynomialReifier.polynomial'
            );
        } catch (error: unknown) {
            return fail(
                'FOREIGN_POLYNOMIAL',
                'formalPolynomialReifier.polynomial',
                'Polynomial belongs to a foreign computational ring',
                error
            );
        }
        return polynomial.terms.reduce((sum, term) => {
            const monomial = term.monomial.exponents.reduce(
                (product, exponent, index) => multiply(
                    product,
                    power(generatorTerms[index], exponent)
                ),
                one()
            );
            return add(sum, multiply(coefficient(term.coefficient), monomial));
        }, zero());
    };
    const reifyElement = (
        element: AlgebraQuotientElement<P, C, I>
    ): KernelExpression => {
        if (!sameAlgebraParent(element.parent, input.algebra.quotient)) {
            return fail(
                'FOREIGN_QUOTIENT_ELEMENT',
                'formalPolynomialReifier.element',
                'Element belongs to a foreign quotient parent'
            );
        }
        return reifyPolynomial(element.representative);
    };
    const realization = defineAffineFormalAlgebraRealization({
        algebra: input.algebra,
        formalRing,
        status: input.status,
        reifyElement
    });
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_REIFIER_PROFILE.revision,
        algebra: input.algebra,
        formalRing,
        generatorTerms,
        maximumExponent,
        realization,
        reifyPolynomial,
        reifyElement
    });
}
