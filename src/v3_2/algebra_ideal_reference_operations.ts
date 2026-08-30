/** Ring-specific ideal operations for the native TypeScript reference engine. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    ALGEBRA_IDEAL_PROFILE,
    AlgebraGroebnerBasis,
    AlgebraIdealMembership,
    AlgebraPolynomialIdeal,
    algebraGroebnerBasis,
    algebraGroebnerBasisSchema,
    algebraIdealMembership,
    algebraIdealMembershipSchema,
    algebraPolynomialIdealSchema,
    algebraReducedGroebnerBasis
} from './algebra_ideal';
import {
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    algebraPolynomialSchema
} from './algebra_polynomial';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_IDEAL_REFERENCE_OPERATIONS_PROFILE = Object.freeze({
    revision: 'emdash-algebra-ideal-reference-operations-v1' as const,
    algorithmRevision: 'typescript-buchberger-reference-v1' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraIdealMembershipInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly polynomial: AlgebraPolynomial<P, C, I>;
    readonly basis: AlgebraGroebnerBasis<P, C, I>;
}

export interface AlgebraIdealReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly idealSchema: AlgebraRuntimeSchema<AlgebraPolynomialIdeal<P, C, I>>;
    readonly basisSchema: AlgebraRuntimeSchema<AlgebraGroebnerBasis<P, C, I>>;
    readonly membershipInputSchema: AlgebraRuntimeSchema<
        AlgebraIdealMembershipInput<P, C, I>
    >;
    readonly membershipOutputSchema: AlgebraRuntimeSchema<
        AlgebraIdealMembership<P, C, I>
    >;
    readonly groebner: AlgebraOperation<
        AlgebraPolynomialIdeal<P, C, I>,
        AlgebraGroebnerBasis<P, C, I>
    >;
    readonly reduceBasis: AlgebraOperation<
        AlgebraGroebnerBasis<P, C, I>,
        AlgebraGroebnerBasis<P, C, I>
    >;
    readonly membership: AlgebraOperation<
        AlgebraIdealMembershipInput<P, C, I>,
        AlgebraIdealMembership<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const algorithm = (operationId: string) => algebraAlgorithmIdentity(
    `algebra.typescript-reference/${operationId}`,
    ALGEBRA_IDEAL_REFERENCE_OPERATIONS_PROFILE.algorithmRevision
);

export function algebraIdealReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraIdealReferenceOperations<P, C, I> {
    const polynomialSchema = algebraPolynomialSchema(ring);
    const idealSchema = algebraPolynomialIdealSchema(ring);
    const basisSchema = algebraGroebnerBasisSchema(ring);
    const membershipOutputSchema = algebraIdealMembershipSchema(ring);
    const suffix = ring.identity.id;
    const membershipInputSchema = defineAlgebraRuntimeSchema<
        AlgebraIdealMembershipInput<P, C, I>
    >({
        id: `algebra.ideal-membership-input/${suffix}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                !('polynomial' in value) ||
                !('basis' in value)
            ) {
                throw new Error(`ideal-membership input expected at ${path}`);
            }
            return Object.freeze({
                polynomial: polynomialSchema.normalize(
                    value.polynomial,
                    `${path}.polynomial`
                ),
                basis: basisSchema.normalize(value.basis, `${path}.basis`)
            });
        }
    });
    const groebner = defineAlgebraOperation({
        id: `algebra.ideal.groebner/${suffix}`,
        revision: ring.identity.revision,
        input: idealSchema,
        output: basisSchema
    });
    const reduceBasis = defineAlgebraOperation({
        id: `algebra.ideal.reduced-groebner/${suffix}`,
        revision: ring.identity.revision,
        input: basisSchema,
        output: basisSchema
    });
    const membership = defineAlgebraOperation({
        id: `algebra.ideal.membership/${suffix}`,
        revision: ring.identity.revision,
        input: membershipInputSchema,
        output: membershipOutputSchema
    });

    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: groebner,
            algorithm: algorithm(groebner.identity.id),
            execute: (ideal, context) => {
                const maximumPairs = context.limits.fuel ??
                    ALGEBRA_IDEAL_PROFILE.maximumPairs;
                const maximumBasisSize = context.limits.maximumOutputItems ??
                    ALGEBRA_IDEAL_PROFILE.maximumBasisSize;
                return algebraGroebnerBasis(ideal, {
                    maximumPairs,
                    maximumBasisSize,
                    maximumTotalReductionSteps:
                        context.limits.maximumIntermediateItems ??
                        ALGEBRA_IDEAL_PROFILE.maximumTotalReductionSteps,
                    context
                });
            }
        }),
        defineAlgebraReferenceImplementation({
            operation: reduceBasis,
            algorithm: algorithm(reduceBasis.identity.id),
            execute: (basis, context) => {
                if (context.cancellation?.requested()) {
                    throw new Error(
                        context.cancellation.reason?.() ??
                        'Reduced-basis computation cancelled'
                    );
                }
                const result = algebraReducedGroebnerBasis(
                    basis,
                    context.limits.fuel ??
                        ALGEBRA_IDEAL_PROFILE.maximumReductionStepsPerPair
                );
                if (
                    context.limits.maximumOutputItems !== undefined &&
                    result.basis.length > context.limits.maximumOutputItems
                ) {
                    throw new Error(
                        `reduced basis has ${result.basis.length} elements; ` +
                        `limit is ${context.limits.maximumOutputItems}`
                    );
                }
                return result;
            }
        }),
        defineAlgebraReferenceImplementation({
            operation: membership,
            algorithm: algorithm(membership.identity.id),
            execute: (input, context) => {
                if (context.cancellation?.requested()) {
                    throw new Error(
                        context.cancellation.reason?.() ??
                        'Ideal-membership computation cancelled'
                    );
                }
                return algebraIdealMembership(
                    input.polynomial,
                    input.basis,
                    context.limits.fuel ??
                        ALGEBRA_IDEAL_PROFILE.maximumReductionStepsPerPair
                );
            }
        })
    ]);

    return Object.freeze({
        idealSchema,
        basisSchema,
        membershipInputSchema,
        membershipOutputSchema,
        groebner,
        reduceBasis,
        membership,
        implementations
    });
}
