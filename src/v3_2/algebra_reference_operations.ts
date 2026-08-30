/** Selected exact and polynomial operations for the TypeScript reference engine. */

import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    ALGEBRA_INTEGER_SCHEMA,
    ALGEBRA_RATIONAL_SCHEMA,
    AlgebraInteger,
    AlgebraRational,
    algebraIntegerAdd,
    algebraIntegerMultiply,
    algebraIntegerNegate,
    algebraRationalAdd,
    algebraRationalInverse,
    algebraRationalMultiply,
    algebraRationalNegate
} from './algebra_exact';
import {
    ALGEBRA_POLYNOMIAL_PROFILE,
    AlgebraPolynomial,
    AlgebraPolynomialDivision,
    AlgebraPolynomialRing,
    algebraPolynomialAdd,
    algebraPolynomialDivide,
    algebraPolynomialMultiply,
    algebraPolynomialNegate,
    algebraPolynomialPower,
    algebraPolynomialSchema,
    validateAlgebraPolynomial
} from './algebra_polynomial';
import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_REFERENCE_OPERATIONS_PROFILE = Object.freeze({
    revision: 'emdash-algebra-reference-operations-v1' as const,
    exactAlgorithmRevision: 'typescript-exact-reference-v1' as const,
    polynomialAlgorithmRevision: 'typescript-sparse-polynomial-reference-v1' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraBinaryInput<T> {
    readonly left: T;
    readonly right: T;
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const binarySchema = <T>(
    id: string,
    schema: AlgebraRuntimeSchema<T>
): AlgebraRuntimeSchema<AlgebraBinaryInput<T>> => defineAlgebraRuntimeSchema({
    id,
    revision: 'v1',
    normalize(value: unknown, path: string) {
        if (!record(value) || !('left' in value) || !('right' in value)) {
            throw new Error(`binary operation input expected at ${path}`);
        }
        return Object.freeze({
            left: schema.normalize(value.left, `${path}.left`),
            right: schema.normalize(value.right, `${path}.right`)
        });
    }
});

export const ALGEBRA_INTEGER_BINARY_SCHEMA = binarySchema(
    'algebra.exact.integer.binary-input',
    ALGEBRA_INTEGER_SCHEMA
);

export const ALGEBRA_RATIONAL_BINARY_SCHEMA = binarySchema(
    'algebra.exact.rational.binary-input',
    ALGEBRA_RATIONAL_SCHEMA
);

export const ALGEBRA_INTEGER_NEGATE_OPERATION = defineAlgebraOperation({
    id: 'algebra.integer.negate',
    revision: 'v1',
    input: ALGEBRA_INTEGER_SCHEMA,
    output: ALGEBRA_INTEGER_SCHEMA
});

export const ALGEBRA_INTEGER_ADD_OPERATION = defineAlgebraOperation({
    id: 'algebra.integer.add',
    revision: 'v1',
    input: ALGEBRA_INTEGER_BINARY_SCHEMA,
    output: ALGEBRA_INTEGER_SCHEMA
});

export const ALGEBRA_INTEGER_MULTIPLY_OPERATION = defineAlgebraOperation({
    id: 'algebra.integer.multiply',
    revision: 'v1',
    input: ALGEBRA_INTEGER_BINARY_SCHEMA,
    output: ALGEBRA_INTEGER_SCHEMA
});

export const ALGEBRA_RATIONAL_NEGATE_OPERATION = defineAlgebraOperation({
    id: 'algebra.rational.negate',
    revision: 'v1',
    input: ALGEBRA_RATIONAL_SCHEMA,
    output: ALGEBRA_RATIONAL_SCHEMA
});

export const ALGEBRA_RATIONAL_INVERSE_OPERATION = defineAlgebraOperation({
    id: 'algebra.rational.inverse',
    revision: 'v1',
    input: ALGEBRA_RATIONAL_SCHEMA,
    output: ALGEBRA_RATIONAL_SCHEMA
});

export const ALGEBRA_RATIONAL_ADD_OPERATION = defineAlgebraOperation({
    id: 'algebra.rational.add',
    revision: 'v1',
    input: ALGEBRA_RATIONAL_BINARY_SCHEMA,
    output: ALGEBRA_RATIONAL_SCHEMA
});

export const ALGEBRA_RATIONAL_MULTIPLY_OPERATION = defineAlgebraOperation({
    id: 'algebra.rational.multiply',
    revision: 'v1',
    input: ALGEBRA_RATIONAL_BINARY_SCHEMA,
    output: ALGEBRA_RATIONAL_SCHEMA
});

const exactAlgorithm = (operationId: string) => algebraAlgorithmIdentity(
    `algebra.typescript-reference/${operationId}`,
    ALGEBRA_REFERENCE_OPERATIONS_PROFILE.exactAlgorithmRevision
);

export const ALGEBRA_EXACT_REFERENCE_IMPLEMENTATIONS:
readonly AlgebraReferenceImplementation[] = Object.freeze([
    defineAlgebraReferenceImplementation({
        operation: ALGEBRA_INTEGER_NEGATE_OPERATION,
        algorithm: exactAlgorithm(ALGEBRA_INTEGER_NEGATE_OPERATION.identity.id),
        execute: algebraIntegerNegate
    }),
    defineAlgebraReferenceImplementation({
        operation: ALGEBRA_INTEGER_ADD_OPERATION,
        algorithm: exactAlgorithm(ALGEBRA_INTEGER_ADD_OPERATION.identity.id),
        execute: input => algebraIntegerAdd(input.left, input.right)
    }),
    defineAlgebraReferenceImplementation({
        operation: ALGEBRA_INTEGER_MULTIPLY_OPERATION,
        algorithm: exactAlgorithm(ALGEBRA_INTEGER_MULTIPLY_OPERATION.identity.id),
        fuelCost: 2,
        execute: input => algebraIntegerMultiply(input.left, input.right)
    }),
    defineAlgebraReferenceImplementation({
        operation: ALGEBRA_RATIONAL_NEGATE_OPERATION,
        algorithm: exactAlgorithm(ALGEBRA_RATIONAL_NEGATE_OPERATION.identity.id),
        execute: algebraRationalNegate
    }),
    defineAlgebraReferenceImplementation({
        operation: ALGEBRA_RATIONAL_INVERSE_OPERATION,
        algorithm: exactAlgorithm(ALGEBRA_RATIONAL_INVERSE_OPERATION.identity.id),
        fuelCost: 2,
        execute: algebraRationalInverse
    }),
    defineAlgebraReferenceImplementation({
        operation: ALGEBRA_RATIONAL_ADD_OPERATION,
        algorithm: exactAlgorithm(ALGEBRA_RATIONAL_ADD_OPERATION.identity.id),
        execute: input => algebraRationalAdd(input.left, input.right)
    }),
    defineAlgebraReferenceImplementation({
        operation: ALGEBRA_RATIONAL_MULTIPLY_OPERATION,
        algorithm: exactAlgorithm(ALGEBRA_RATIONAL_MULTIPLY_OPERATION.identity.id),
        fuelCost: 2,
        execute: input => algebraRationalMultiply(input.left, input.right)
    })
]);

export interface AlgebraPolynomialPowerInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly base: AlgebraPolynomial<P, C, I>;
    readonly exponent: bigint;
}

export interface AlgebraPolynomialDivisionInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly dividend: AlgebraPolynomial<P, C, I>;
    readonly divisors: readonly AlgebraPolynomial<P, C, I>[];
    readonly maximumSteps?: number;
}

export interface AlgebraPolynomialReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly ring: AlgebraPolynomialRing<P, C, I>;
    readonly polynomialSchema: AlgebraRuntimeSchema<AlgebraPolynomial<P, C, I>>;
    readonly binarySchema: AlgebraRuntimeSchema<AlgebraBinaryInput<
        AlgebraPolynomial<P, C, I>
    >>;
    readonly powerSchema: AlgebraRuntimeSchema<AlgebraPolynomialPowerInput<P, C, I>>;
    readonly divisionInputSchema: AlgebraRuntimeSchema<
        AlgebraPolynomialDivisionInput<P, C, I>
    >;
    readonly divisionOutputSchema: AlgebraRuntimeSchema<
        AlgebraPolynomialDivision<P, C, I>
    >;
    readonly negate: AlgebraOperation<
        AlgebraPolynomial<P, C, I>,
        AlgebraPolynomial<P, C, I>
    >;
    readonly add: AlgebraOperation<
        AlgebraBinaryInput<AlgebraPolynomial<P, C, I>>,
        AlgebraPolynomial<P, C, I>
    >;
    readonly multiply: AlgebraOperation<
        AlgebraBinaryInput<AlgebraPolynomial<P, C, I>>,
        AlgebraPolynomial<P, C, I>
    >;
    readonly power: AlgebraOperation<
        AlgebraPolynomialPowerInput<P, C, I>,
        AlgebraPolynomial<P, C, I>
    >;
    readonly divide: AlgebraOperation<
        AlgebraPolynomialDivisionInput<P, C, I>,
        AlgebraPolynomialDivision<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const positiveSafeInteger = (
    value: unknown,
    path: string
): number => {
    if (Number.isSafeInteger(value) && (value as number) > 0) {
        return value as number;
    }
    throw new Error(`positive safe integer expected at ${path}`);
};

const polynomialAlgorithm = (operationId: string) => algebraAlgorithmIdentity(
    `algebra.typescript-reference/${operationId}`,
    ALGEBRA_REFERENCE_OPERATIONS_PROFILE.polynomialAlgorithmRevision
);

export function algebraPolynomialReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraPolynomialReferenceOperations<P, C, I> {
    const polynomialSchema = algebraPolynomialSchema(ring);
    const ringSuffix = ring.identity.id;
    const binary = binarySchema(
        `algebra.polynomial.binary-input/${ringSuffix}`,
        polynomialSchema
    );
    const powerSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialPowerInput<P, C, I>
    >({
        id: `algebra.polynomial.power-input/${ringSuffix}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || !('base' in value) || !('exponent' in value)) {
                throw new Error(`polynomial power input expected at ${path}`);
            }
            if (typeof value.exponent !== 'bigint' || value.exponent < 0n) {
                throw new Error(`nonnegative bigint exponent expected at ${path}`);
            }
            return Object.freeze({
                base: polynomialSchema.normalize(value.base, `${path}.base`),
                exponent: value.exponent
            });
        }
    });
    const divisionInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialDivisionInput<P, C, I>
    >({
        id: `algebra.polynomial.division-input/${ringSuffix}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                !('dividend' in value) ||
                !Array.isArray(value.divisors)
            ) {
                throw new Error(`polynomial division input expected at ${path}`);
            }
            return Object.freeze({
                dividend: polynomialSchema.normalize(
                    value.dividend,
                    `${path}.dividend`
                ),
                divisors: Object.freeze(value.divisors.map((divisor, index) =>
                    polynomialSchema.normalize(
                        divisor,
                        `${path}.divisors[${index}]`
                    )
                )),
                ...(value.maximumSteps === undefined
                    ? {}
                    : {
                        maximumSteps: positiveSafeInteger(
                            value.maximumSteps,
                            `${path}.maximumSteps`
                        )
                    })
            });
        }
    });
    const divisionOutputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialDivision<P, C, I>
    >({
        id: `algebra.polynomial.division-output/${ringSuffix}`,
        revision: ring.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                !Array.isArray(value.quotients) ||
                !Number.isSafeInteger(value.steps) ||
                (value.steps as number) < 0 ||
                !('remainder' in value)
            ) {
                throw new Error(`polynomial division output expected at ${path}`);
            }
            return Object.freeze({
                quotients: Object.freeze(value.quotients.map((quotient, index) =>
                    polynomialSchema.normalize(
                        quotient,
                        `${path}.quotients[${index}]`
                    )
                )),
                remainder: polynomialSchema.normalize(
                    value.remainder,
                    `${path}.remainder`
                ),
                steps: value.steps as number
            });
        }
    });

    const negate = defineAlgebraOperation({
        id: `algebra.polynomial.negate/${ringSuffix}`,
        revision: ring.identity.revision,
        input: polynomialSchema,
        output: polynomialSchema
    });
    const add = defineAlgebraOperation({
        id: `algebra.polynomial.add/${ringSuffix}`,
        revision: ring.identity.revision,
        input: binary,
        output: polynomialSchema
    });
    const multiply = defineAlgebraOperation({
        id: `algebra.polynomial.multiply/${ringSuffix}`,
        revision: ring.identity.revision,
        input: binary,
        output: polynomialSchema
    });
    const power = defineAlgebraOperation({
        id: `algebra.polynomial.power/${ringSuffix}`,
        revision: ring.identity.revision,
        input: powerSchema,
        output: polynomialSchema
    });
    const divide = defineAlgebraOperation({
        id: `algebra.polynomial.divide/${ringSuffix}`,
        revision: ring.identity.revision,
        input: divisionInputSchema,
        output: divisionOutputSchema
    });

    const enforceOutputLimit = (
        polynomial: AlgebraPolynomial<P, C, I>,
        maximum: number | undefined
    ): AlgebraPolynomial<P, C, I> => {
        if (maximum !== undefined && polynomial.terms.length > maximum) {
            throw new Error(
                `polynomial result has ${polynomial.terms.length} terms; ` +
                `limit is ${maximum}`
            );
        }
        return polynomial;
    };

    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: negate,
            algorithm: polynomialAlgorithm(negate.identity.id),
            execute: (input, context) => enforceOutputLimit(
                algebraPolynomialNegate(input),
                context.limits.maximumOutputItems
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: add,
            algorithm: polynomialAlgorithm(add.identity.id),
            execute: (input, context) => enforceOutputLimit(
                algebraPolynomialAdd(input.left, input.right),
                context.limits.maximumOutputItems
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: multiply,
            algorithm: polynomialAlgorithm(multiply.identity.id),
            fuelCost: 2,
            execute: (input, context) => enforceOutputLimit(
                algebraPolynomialMultiply(input.left, input.right),
                context.limits.maximumOutputItems
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: power,
            algorithm: polynomialAlgorithm(power.identity.id),
            fuelCost: 2,
            execute: (input, context) => enforceOutputLimit(
                algebraPolynomialPower(input.base, input.exponent),
                context.limits.maximumOutputItems
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: divide,
            algorithm: polynomialAlgorithm(divide.identity.id),
            fuelCost: 2,
            execute: (input, context) => {
                const maximumSteps = input.maximumSteps ??
                    context.limits.fuel ??
                    ALGEBRA_POLYNOMIAL_PROFILE.maximumDivisionSteps;
                const result = algebraPolynomialDivide(
                    input.dividend,
                    input.divisors,
                    maximumSteps
                );
                const outputItems = result.remainder.terms.length +
                    result.quotients.reduce(
                        (sum, quotient) => sum + quotient.terms.length,
                        0
                    );
                if (
                    context.limits.maximumOutputItems !== undefined &&
                    outputItems > context.limits.maximumOutputItems
                ) {
                    throw new Error(
                        `polynomial division produced ${outputItems} terms; ` +
                        `limit is ${context.limits.maximumOutputItems}`
                    );
                }
                return result;
            }
        })
    ]);

    return Object.freeze({
        ring,
        polynomialSchema,
        binarySchema: binary,
        powerSchema,
        divisionInputSchema,
        divisionOutputSchema,
        negate,
        add,
        multiply,
        power,
        divide,
        implementations
    });
}
