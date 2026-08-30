/** Native principal-localization operation for one presented algebra. */

import { AlgebraElement, AlgebraParent, sameAlgebraParent } from './algebra_parent';
import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import { AlgebraQuotientElement, algebraQuotientElementSchema } from './algebra_quotient';
import { AlgebraPresentedAlgebra } from './algebra_presented_algebra';
import {
    AlgebraPrincipalLocalization,
    algebraPrincipalLocalization
} from './algebra_localization';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_LOCALIZATION_REFERENCE_PROFILE = Object.freeze({
    revision: 'emdash-localization-reference-v1' as const,
    algorithmRevision: 'typescript-adjoined-inverse-v1' as const,
    wholeResult: true as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraLocalizationReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly outputSchema: AlgebraRuntimeSchema<AlgebraPrincipalLocalization<P, C, I>>;
    readonly localize: AlgebraOperation<
        AlgebraQuotientElement<P, C, I>,
        AlgebraPrincipalLocalization<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

export function algebraLocalizationReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(source: AlgebraPresentedAlgebra<P, C, I>):
    AlgebraLocalizationReferenceOperations<P, C, I> {
    const inputSchema = algebraQuotientElementSchema(source.quotient);
    const outputSchema = defineAlgebraRuntimeSchema<
        AlgebraPrincipalLocalization<P, C, I>
    >({
        id: `algebra.principal-localization/${source.quotient.identity.id}`,
        revision: source.quotient.identity.revision,
        normalize(value: unknown, path: string) {
            if (typeof value !== 'object' || value === null ||
                (value as { kind?: unknown }).kind !== 'algebra-principal-localization') {
                throw new Error(`principal localization expected at ${path}`);
            }
            const localization = value as AlgebraPrincipalLocalization<P, C, I>;
            if (!sameAlgebraParent(localization.source.quotient, source.quotient) ||
                !sameAlgebraParent(localization.element.parent, source.quotient) ||
                localization.inverseEquation !== true) {
                throw new Error(`invalid principal localization at ${path}`);
            }
            return localization;
        }
    });
    const localize = defineAlgebraOperation({
        id: `algebra.principal-localization.compute/${source.quotient.identity.id}`,
        revision: source.quotient.identity.revision,
        input: inputSchema,
        output: outputSchema
    });
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: localize,
            algorithm: algebraAlgorithmIdentity(
                `algebra.typescript-reference/${localize.identity.id}`,
                ALGEBRA_LOCALIZATION_REFERENCE_PROFILE.algorithmRevision
            ),
            execute: (element, context) => algebraPrincipalLocalization(
                source,
                element,
                { context }
            )
        })
    ]);
    return Object.freeze({ outputSchema, localize, implementations });
}
