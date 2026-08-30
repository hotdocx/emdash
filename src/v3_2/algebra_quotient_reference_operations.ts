/** Native operations for one canonical polynomial quotient ring. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import { AlgebraPolynomial, algebraPolynomialSchema } from './algebra_polynomial';
import {
    AlgebraPolynomialQuotientRing,
    AlgebraQuotientElement,
    AlgebraQuotientReduction,
    algebraQuotientAdd,
    algebraQuotientElement,
    algebraQuotientElementSchema,
    algebraQuotientMultiply,
    algebraQuotientNegate,
    algebraQuotientPower,
    algebraQuotientReduce
} from './algebra_quotient';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_QUOTIENT_REFERENCE_PROFILE = Object.freeze({
    revision: 'emdash-quotient-reference-operations-v1' as const,
    algorithmRevision: 'typescript-quotient-normal-form-v1' as const,
    wholeReduction: true as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraQuotientBinaryInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly left: AlgebraQuotientElement<P, C, I>;
    readonly right: AlgebraQuotientElement<P, C, I>;
}

export interface AlgebraQuotientPowerInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly value: AlgebraQuotientElement<P, C, I>;
    readonly exponent: bigint;
}

export interface AlgebraQuotientReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly elementSchema: AlgebraRuntimeSchema<AlgebraQuotientElement<P, C, I>>;
    readonly binarySchema: AlgebraRuntimeSchema<AlgebraQuotientBinaryInput<P, C, I>>;
    readonly reduce: AlgebraOperation<AlgebraPolynomial<P, C, I>, AlgebraQuotientReduction<P, C, I>>;
    readonly normalize: AlgebraOperation<AlgebraPolynomial<P, C, I>, AlgebraQuotientElement<P, C, I>>;
    readonly negate: AlgebraOperation<AlgebraQuotientElement<P, C, I>, AlgebraQuotientElement<P, C, I>>;
    readonly add: AlgebraOperation<AlgebraQuotientBinaryInput<P, C, I>, AlgebraQuotientElement<P, C, I>>;
    readonly multiply: AlgebraOperation<AlgebraQuotientBinaryInput<P, C, I>, AlgebraQuotientElement<P, C, I>>;
    readonly power: AlgebraOperation<AlgebraQuotientPowerInput<P, C, I>, AlgebraQuotientElement<P, C, I>>;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const algorithm = (id: string) => algebraAlgorithmIdentity(
    `algebra.typescript-reference/${id}`,
    ALGEBRA_QUOTIENT_REFERENCE_PROFILE.algorithmRevision
);

export function algebraQuotientReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(quotient: AlgebraPolynomialQuotientRing<P, C, I>):
    AlgebraQuotientReferenceOperations<P, C, I> {
    const suffix = quotient.identity.id;
    const polynomialSchema = algebraPolynomialSchema(quotient.polynomialRing);
    const elementSchema = algebraQuotientElementSchema(quotient);
    const binarySchema = defineAlgebraRuntimeSchema<AlgebraQuotientBinaryInput<P, C, I>>({
        id: `algebra.quotient-binary/${suffix}`,
        revision: quotient.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`quotient pair expected at ${path}`);
            return Object.freeze({
                left: elementSchema.normalize(value.left, `${path}.left`),
                right: elementSchema.normalize(value.right, `${path}.right`)
            });
        }
    });
    const powerSchema = defineAlgebraRuntimeSchema<AlgebraQuotientPowerInput<P, C, I>>({
        id: `algebra.quotient-power-input/${suffix}`,
        revision: quotient.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || typeof value.exponent !== 'bigint') {
                throw new Error(`quotient power input expected at ${path}`);
            }
            return Object.freeze({
                value: elementSchema.normalize(value.value, `${path}.value`),
                exponent: value.exponent
            });
        }
    });
    const reductionSchema = defineAlgebraRuntimeSchema<AlgebraQuotientReduction<P, C, I>>({
        id: `algebra.quotient-reduction/${suffix}`,
        revision: quotient.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !== 'algebra-quotient-reduction') {
                throw new Error(`quotient reduction expected at ${path}`);
            }
            return algebraQuotientReduce(
                quotient,
                polynomialSchema.normalize(value.input, `${path}.input`)
            );
        }
    });
    const operation = <A, B>(
        id: string,
        input: AlgebraRuntimeSchema<A>,
        output: AlgebraRuntimeSchema<B>
    ) => defineAlgebraOperation({
        id: `algebra.quotient.${id}/${suffix}`,
        revision: quotient.identity.revision,
        input,
        output
    });
    const reduce = operation('reduce', polynomialSchema, reductionSchema);
    const normalize = operation('normalize', polynomialSchema, elementSchema);
    const negate = operation('negate', elementSchema, elementSchema);
    const add = operation('add', binarySchema, elementSchema);
    const multiply = operation('multiply', binarySchema, elementSchema);
    const power = operation('power', powerSchema, elementSchema);
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({ operation: reduce,
            algorithm: algorithm(reduce.identity.id),
            execute: value => algebraQuotientReduce(quotient, value) }),
        defineAlgebraReferenceImplementation({ operation: normalize,
            algorithm: algorithm(normalize.identity.id),
            execute: value => algebraQuotientElement(quotient, value) }),
        defineAlgebraReferenceImplementation({ operation: negate,
            algorithm: algorithm(negate.identity.id),
            execute: algebraQuotientNegate }),
        defineAlgebraReferenceImplementation({ operation: add,
            algorithm: algorithm(add.identity.id),
            execute: value => algebraQuotientAdd(value.left, value.right) }),
        defineAlgebraReferenceImplementation({ operation: multiply,
            algorithm: algorithm(multiply.identity.id),
            execute: value => algebraQuotientMultiply(value.left, value.right) }),
        defineAlgebraReferenceImplementation({ operation: power,
            algorithm: algorithm(power.identity.id),
            execute: value => algebraQuotientPower(value.value, value.exponent) })
    ]);
    return Object.freeze({
        elementSchema,
        binarySchema,
        reduce,
        normalize,
        negate,
        add,
        multiply,
        power,
        implementations
    });
}
