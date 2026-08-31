/** Native fixed-degree operations for affine Cech differentials and squares. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraEngine,
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraAffineQuasiCoherentCochain,
    AlgebraAffineQuasiCoherentCochainDegree,
    algebraAffineQuasiCoherentCochainDegree,
    algebraAffineQuasiCoherentCochainSchema
} from './algebra_quasicoherent_cochain';
import {
    AlgebraAffineQuasiCoherentDifferential,
    algebraAffineQuasiCoherentDifferential
} from './algebra_quasicoherent_differential';
import {
    AlgebraAffineQuasiCoherentDifferentialSquare,
    algebraAffineQuasiCoherentDifferentialSquare
} from './algebra_quasicoherent_differential_square';
import {
    AlgebraReferenceImplementation,
    createAlgebraTypeScriptReferenceEngine,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_QUASICOHERENT_COCHAIN_REFERENCE_PROFILE = Object.freeze({
    revision: 'emdash-quasicoherent-cochain-reference-v1' as const,
    algorithmRevision: 'typescript-quasicoherent-cech-differential-v1' as const,
    fixedDegreeSchema: true as const,
    wholeResults: true as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraQuasiCoherentCochainReferenceErrorCode =
    'NO_SUCCESSOR_DEGREE';

export class AlgebraQuasiCoherentCochainReferenceError extends Error {
    constructor(
        public readonly code: AlgebraQuasiCoherentCochainReferenceErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraQuasiCoherentCochainReferenceError';
    }
}

export interface AlgebraQuasiCoherentCochainReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: AlgebraAffineQuasiCoherentCochainDegree<P, C, I>;
    readonly inputSchema:
        AlgebraRuntimeSchema<AlgebraAffineQuasiCoherentCochain<P, C, I>>;
    readonly differential: AlgebraOperation<
        AlgebraAffineQuasiCoherentCochain<P, C, I>,
        AlgebraAffineQuasiCoherentDifferential<P, C, I>
    >;
    readonly square?: AlgebraOperation<
        AlgebraAffineQuasiCoherentCochain<P, C, I>,
        AlgebraAffineQuasiCoherentDifferentialSquare<P, C, I>
    >;
    readonly squareAvailable: boolean;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const wholeSchema = <T extends { readonly kind: string }>(
    id: string,
    kind: T['kind']
): AlgebraRuntimeSchema<T> => defineAlgebraRuntimeSchema({
    id,
    revision: ALGEBRA_QUASICOHERENT_COCHAIN_REFERENCE_PROFILE.revision,
    normalize(value: unknown, path: string) {
        if (
            typeof value !== 'object' ||
            value === null ||
            (value as { kind?: unknown }).kind !== kind
        ) throw new Error(`${kind} expected at ${path}`);
        return value as T;
    }
});

export function algebraQuasiCoherentCochainReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    degree: AlgebraAffineQuasiCoherentCochainDegree<P, C, I>
): AlgebraQuasiCoherentCochainReferenceOperations<P, C, I> {
    try {
        algebraAffineQuasiCoherentCochainDegree(
            degree.diagram,
            degree.degree + 1
        );
    } catch {
        throw new AlgebraQuasiCoherentCochainReferenceError(
            'NO_SUCCESSOR_DEGREE',
            'cochainReference.degree',
            'A differential operation requires one retained successor degree'
        );
    }
    const inputSchema = algebraAffineQuasiCoherentCochainSchema(degree);
    const differential = defineAlgebraOperation({
        id: `algebra.quasicoherent-cochain.differential/${degree.identity.id}`,
        revision: ALGEBRA_QUASICOHERENT_COCHAIN_REFERENCE_PROFILE.revision,
        input: inputSchema,
        output: wholeSchema<AlgebraAffineQuasiCoherentDifferential<P, C, I>>(
            `algebra.quasicoherent-cochain.differential-result/` +
                degree.identity.id,
            'algebra-affine-quasicoherent-differential'
        )
    });
    let square: AlgebraOperation<
        AlgebraAffineQuasiCoherentCochain<P, C, I>,
        AlgebraAffineQuasiCoherentDifferentialSquare<P, C, I>
    > | undefined;
    try {
        algebraAffineQuasiCoherentCochainDegree(
            degree.diagram,
            degree.degree + 2
        );
        square = defineAlgebraOperation({
            id: `algebra.quasicoherent-cochain.differential-square/` +
                degree.identity.id,
            revision: ALGEBRA_QUASICOHERENT_COCHAIN_REFERENCE_PROFILE.revision,
            input: inputSchema,
            output: wholeSchema<
                AlgebraAffineQuasiCoherentDifferentialSquare<P, C, I>
            >(
                `algebra.quasicoherent-cochain.differential-square-result/` +
                    degree.identity.id,
                'algebra-affine-quasicoherent-differential-square'
            )
        });
    } catch {
        square = undefined;
    }
    const implementations: AlgebraReferenceImplementation[] = [
        defineAlgebraReferenceImplementation({
            operation: differential,
            algorithm: algebraAlgorithmIdentity(
                'algebra.typescript-reference/quasicoherent-differential',
                ALGEBRA_QUASICOHERENT_COCHAIN_REFERENCE_PROFILE.algorithmRevision
            ),
            execute: algebraAffineQuasiCoherentDifferential
        })
    ];
    if (square !== undefined) {
        implementations.push(defineAlgebraReferenceImplementation({
            operation: square,
            algorithm: algebraAlgorithmIdentity(
                'algebra.typescript-reference/quasicoherent-differential-square',
                ALGEBRA_QUASICOHERENT_COCHAIN_REFERENCE_PROFILE.algorithmRevision
            ),
            execute: algebraAffineQuasiCoherentDifferentialSquare
        }));
    }
    return Object.freeze({
        degree,
        inputSchema,
        differential,
        ...(square === undefined ? {} : { square }),
        squareAvailable: square !== undefined,
        implementations: Object.freeze(implementations)
    });
}

export const createAlgebraQuasiCoherentCochainEngine = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(operations: AlgebraQuasiCoherentCochainReferenceOperations<P, C, I>):
    AlgebraEngine => createAlgebraTypeScriptReferenceEngine({
        id: 'algebra.typescript-reference.quasicoherent-cochains',
        revision: ALGEBRA_QUASICOHERENT_COCHAIN_REFERENCE_PROFILE.revision,
        implementations: operations.implementations
    });
