/** Native operation bundle for one validated presented-algebra map. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraOperation, algebraAlgorithmIdentity, defineAlgebraOperation } from './algebra_engine';
import { AlgebraQuotientElement, algebraQuotientElementSchema } from './algebra_quotient';
import {
    AlgebraPresentedAlgebraMap,
    algebraPresentedAlgebraMapApply
} from './algebra_presented_algebra';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_PRESENTED_MAP_REFERENCE_PROFILE = Object.freeze({
    revision: 'emdash-presented-map-reference-v1' as const,
    algorithmRevision: 'typescript-generator-substitution-v1' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraPresentedMapReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly apply: AlgebraOperation<
        AlgebraQuotientElement<P, C, I>,
        AlgebraQuotientElement<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

export function algebraPresentedMapReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(map: AlgebraPresentedAlgebraMap<P, C, I>):
    AlgebraPresentedMapReferenceOperations<P, C, I> {
    const apply = defineAlgebraOperation({
        id: `algebra.presented-map.apply/${map.source.quotient.identity.id}/` +
            map.target.quotient.identity.id,
        revision: ALGEBRA_PRESENTED_MAP_REFERENCE_PROFILE.revision,
        input: algebraQuotientElementSchema(map.source.quotient),
        output: algebraQuotientElementSchema(map.target.quotient)
    });
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: apply,
            algorithm: algebraAlgorithmIdentity(
                `algebra.typescript-reference/${apply.identity.id}`,
                ALGEBRA_PRESENTED_MAP_REFERENCE_PROFILE.algorithmRevision
            ),
            execute: value => algebraPresentedAlgebraMapApply(map, value)
        })
    ]);
    return Object.freeze({ apply, implementations });
}
