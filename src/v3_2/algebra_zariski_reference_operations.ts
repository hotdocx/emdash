/** Native operations for unimodular combinations and computational covers. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation
} from './algebra_engine';
import {
    ALGEBRA_IDEAL_PROFILE,
    AlgebraPolynomialIdeal,
    algebraPolynomialIdealSchema
} from './algebra_ideal';
import {
    AlgebraPolynomialRing
} from './algebra_polynomial';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';
import {
    ALGEBRA_ZARISKI_PROFILE,
    AlgebraUnimodularCombination,
    AlgebraZariskiCoverPresentation,
    algebraUnimodularCombination,
    algebraUnimodularCombinationSchema,
    algebraZariskiCoverPresentation,
    algebraZariskiCoverPresentationSchema
} from './algebra_zariski';

export const ALGEBRA_ZARISKI_REFERENCE_OPERATIONS_PROFILE = Object.freeze({
    revision: 'emdash-algebra-zariski-reference-operations-v1' as const,
    algorithmRevision: 'typescript-unimodular-reference-v1' as const,
    formalAdapter: ALGEBRA_ZARISKI_PROFILE.formalAdapter,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraZariskiReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly idealSchema: AlgebraRuntimeSchema<AlgebraPolynomialIdeal<P, C, I>>;
    readonly unimodularSchema: AlgebraRuntimeSchema<
        AlgebraUnimodularCombination<P, C, I>
    >;
    readonly coverSchema: AlgebraRuntimeSchema<
        AlgebraZariskiCoverPresentation<P, C, I>
    >;
    readonly unimodular: AlgebraOperation<
        AlgebraPolynomialIdeal<P, C, I>,
        AlgebraUnimodularCombination<P, C, I>
    >;
    readonly cover: AlgebraOperation<
        AlgebraUnimodularCombination<P, C, I>,
        AlgebraZariskiCoverPresentation<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const algorithm = (operationId: string) => algebraAlgorithmIdentity(
    `algebra.typescript-reference/${operationId}`,
    ALGEBRA_ZARISKI_REFERENCE_OPERATIONS_PROFILE.algorithmRevision
);

export function algebraZariskiReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>
): AlgebraZariskiReferenceOperations<P, C, I> {
    const suffix = ring.identity.id;
    const idealSchema = algebraPolynomialIdealSchema(ring);
    const unimodularSchema = algebraUnimodularCombinationSchema(ring);
    const coverSchema = algebraZariskiCoverPresentationSchema(ring);
    const unimodular = defineAlgebraOperation({
        id: `algebra.zariski.unimodular/${suffix}`,
        revision: ring.identity.revision,
        input: idealSchema,
        output: unimodularSchema
    });
    const cover = defineAlgebraOperation({
        id: `algebra.zariski.cover/${suffix}`,
        revision: ring.identity.revision,
        input: unimodularSchema,
        output: coverSchema
    });
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: unimodular,
            algorithm: algorithm(unimodular.identity.id),
            execute: (ideal, context) => algebraUnimodularCombination(ideal, {
                maximumPairs: context.limits.fuel ??
                    ALGEBRA_IDEAL_PROFILE.maximumPairs,
                maximumBasisSize: context.limits.maximumOutputItems ??
                    ALGEBRA_IDEAL_PROFILE.maximumBasisSize,
                maximumTotalReductionSteps:
                    context.limits.maximumIntermediateItems ??
                    ALGEBRA_IDEAL_PROFILE.maximumTotalReductionSteps,
                membershipReductionSteps: context.limits.fuel,
                context
            })
        }),
        defineAlgebraReferenceImplementation({
            operation: cover,
            algorithm: algorithm(cover.identity.id),
            execute: algebraZariskiCoverPresentation
        })
    ]);
    return Object.freeze({
        idealSchema,
        unimodularSchema,
        coverSchema,
        unimodular,
        cover,
        implementations
    });
}
