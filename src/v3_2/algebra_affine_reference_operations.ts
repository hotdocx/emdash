/** Native whole operations for affine tensor, fiber-product, and cover data. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import { AlgebraPresentedAlgebra, AlgebraPresentedAlgebraMap } from './algebra_presented_algebra';
import { AlgebraAffineMorphism, AlgebraAffineScheme } from './algebra_affine_scheme';
import {
    AlgebraAffineFiberProduct,
    AlgebraPresentedTensorProduct,
    algebraAffineFiberProduct,
    algebraPresentedTensorProduct
} from './algebra_tensor';
import { AlgebraQuotientElement } from './algebra_quotient';
import { AlgebraAffineCover, algebraAffineCover } from './algebra_cech';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_AFFINE_REFERENCE_PROFILE = Object.freeze({
    revision: 'emdash-affine-reference-operations-v1' as const,
    algorithmRevision: 'typescript-presented-affine-v1' as const,
    wholeResults: true as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraTensorOperationInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly base: AlgebraPresentedAlgebra<P, C, I>;
    readonly leftMap: AlgebraPresentedAlgebraMap<P, C, I>;
    readonly rightMap: AlgebraPresentedAlgebraMap<P, C, I>;
}

export interface AlgebraFiberProductOperationInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly left: AlgebraAffineMorphism<P, C, I>;
    readonly right: AlgebraAffineMorphism<P, C, I>;
}

export interface AlgebraAffineCoverOperationInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly ambient: AlgebraAffineScheme<P, C, I>;
    readonly elements: readonly AlgebraQuotientElement<P, C, I>[];
    readonly maximumDegree: number;
}

export interface AlgebraAffineReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly tensorInputSchema: AlgebraRuntimeSchema<AlgebraTensorOperationInput<P, C, I>>;
    readonly fiberInputSchema: AlgebraRuntimeSchema<AlgebraFiberProductOperationInput<P, C, I>>;
    readonly coverInputSchema: AlgebraRuntimeSchema<AlgebraAffineCoverOperationInput<P, C, I>>;
    readonly tensor: AlgebraOperation<
        AlgebraTensorOperationInput<P, C, I>,
        AlgebraPresentedTensorProduct<P, C, I>
    >;
    readonly fiberProduct: AlgebraOperation<
        AlgebraFiberProductOperationInput<P, C, I>,
        AlgebraAffineFiberProduct<P, C, I>
    >;
    readonly cover: AlgebraOperation<
        AlgebraAffineCoverOperationInput<P, C, I>,
        AlgebraAffineCover<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const wholeSchema = <T extends { readonly kind: string }>(
    id: string,
    kind: T['kind']
): AlgebraRuntimeSchema<T> => defineAlgebraRuntimeSchema({
    id,
    revision: ALGEBRA_AFFINE_REFERENCE_PROFILE.revision,
    normalize(value: unknown, path: string) {
        if (!record(value) || value.kind !== kind) {
            throw new Error(`${kind} expected at ${path}`);
        }
        return value as T;
    }
});

export function algebraAffineReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(): AlgebraAffineReferenceOperations<P, C, I> {
    const tensorInputSchema = defineAlgebraRuntimeSchema<
        AlgebraTensorOperationInput<P, C, I>
    >({
        id: 'algebra.affine.tensor-input',
        revision: ALGEBRA_AFFINE_REFERENCE_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`tensor input expected at ${path}`);
            return Object.freeze({
                base: value.base as AlgebraPresentedAlgebra<P, C, I>,
                leftMap: value.leftMap as AlgebraPresentedAlgebraMap<P, C, I>,
                rightMap: value.rightMap as AlgebraPresentedAlgebraMap<P, C, I>
            });
        }
    });
    const fiberInputSchema = defineAlgebraRuntimeSchema<
        AlgebraFiberProductOperationInput<P, C, I>
    >({
        id: 'algebra.affine.fiber-product-input',
        revision: ALGEBRA_AFFINE_REFERENCE_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`fiber-product input expected at ${path}`);
            return Object.freeze({
                left: value.left as AlgebraAffineMorphism<P, C, I>,
                right: value.right as AlgebraAffineMorphism<P, C, I>
            });
        }
    });
    const coverInputSchema = defineAlgebraRuntimeSchema<
        AlgebraAffineCoverOperationInput<P, C, I>
    >({
        id: 'algebra.affine.cover-input',
        revision: ALGEBRA_AFFINE_REFERENCE_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || !Array.isArray(value.elements) ||
                !Number.isSafeInteger(value.maximumDegree)) {
                throw new Error(`affine-cover input expected at ${path}`);
            }
            return Object.freeze({
                ambient: value.ambient as AlgebraAffineScheme<P, C, I>,
                elements: Object.freeze(value.elements as AlgebraQuotientElement<P, C, I>[]),
                maximumDegree: value.maximumDegree as number
            });
        }
    });
    const tensor = defineAlgebraOperation({
        id: 'algebra.affine.tensor-product',
        revision: ALGEBRA_AFFINE_REFERENCE_PROFILE.revision,
        input: tensorInputSchema,
        output: wholeSchema<AlgebraPresentedTensorProduct<P, C, I>>(
            'algebra.affine.tensor-result',
            'algebra-presented-tensor-product'
        )
    });
    const fiberProduct = defineAlgebraOperation({
        id: 'algebra.affine.fiber-product',
        revision: ALGEBRA_AFFINE_REFERENCE_PROFILE.revision,
        input: fiberInputSchema,
        output: wholeSchema<AlgebraAffineFiberProduct<P, C, I>>(
            'algebra.affine.fiber-product-result',
            'algebra-affine-fiber-product'
        )
    });
    const cover = defineAlgebraOperation({
        id: 'algebra.affine.cover',
        revision: ALGEBRA_AFFINE_REFERENCE_PROFILE.revision,
        input: coverInputSchema,
        output: wholeSchema<AlgebraAffineCover<P, C, I>>(
            'algebra.affine.cover-result',
            'algebra-affine-cover'
        )
    });
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: tensor,
            algorithm: algebraAlgorithmIdentity('algebra.typescript-reference/affine-tensor',
                ALGEBRA_AFFINE_REFERENCE_PROFILE.algorithmRevision),
            execute: (input, context) => algebraPresentedTensorProduct(
                input.base,
                input.leftMap,
                input.rightMap,
                { context }
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: fiberProduct,
            algorithm: algebraAlgorithmIdentity('algebra.typescript-reference/affine-fiber-product',
                ALGEBRA_AFFINE_REFERENCE_PROFILE.algorithmRevision),
            execute: (input, context) => algebraAffineFiberProduct(
                input.left,
                input.right,
                { context }
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: cover,
            algorithm: algebraAlgorithmIdentity('algebra.typescript-reference/affine-cover',
                ALGEBRA_AFFINE_REFERENCE_PROFILE.algorithmRevision),
            execute: (input, context) => algebraAffineCover(
                input.ambient,
                input.elements,
                input.maximumDegree,
                { context }
            )
        })
    ]);
    return Object.freeze({
        tensorInputSchema,
        fiberInputSchema,
        coverInputSchema,
        tensor,
        fiberProduct,
        cover,
        implementations
    });
}
