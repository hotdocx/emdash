/** Native graph operations for whole homological field-module computations. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraFieldDomain
} from './algebra_exact';
import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraPresentedModule
} from './algebra_module';
import {
    algebraModuleComputableCategory
} from './algebra_category_instances';
import {
    AlgebraModuleChainComplex,
    AlgebraModuleChainMap,
    AlgebraModuleComplexHomology,
    AlgebraModuleConnectingMorphism,
    AlgebraModuleHomologyMap,
    AlgebraModuleShortExactSequence,
    algebraModuleChainComplex,
    algebraModuleChainComplexHomology,
    algebraModuleChainMap,
    algebraModuleChainMapHomology,
    algebraModuleConnectingMorphism,
    algebraModuleShortExactSequence
} from './algebra_homological';
import {
    AlgebraModuleGeneralizedSpan,
    AlgebraModuleGeneralizedSpanComposition,
    algebraModuleGeneralizedSpan,
    algebraModuleGeneralizedSpanComposition
} from './algebra_generalized';
import {
    AlgebraModulePresentationResolution,
    AlgebraModuleSplitResolution,
    algebraModulePresentationResolution,
    algebraModuleSplitResolution
} from './algebra_resolution';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';

export const ALGEBRA_HOMOLOGICAL_REFERENCE_OPERATIONS_PROFILE = Object.freeze({
    revision: 'emdash-algebra-homological-reference-operations-v1' as const,
    algorithmRevision: 'typescript-field-homological-reference-v1' as const,
    wholeResults: true as const,
    categoricalDerivationInlining: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export interface AlgebraComplexDegreeInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly complex: AlgebraModuleChainComplex<P, C, I>;
    readonly degree: number;
}

export interface AlgebraChainMapDegreeInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly chainMap: AlgebraModuleChainMap<P, C, I>;
    readonly degree: number;
}

export interface AlgebraConnectingDegreeInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly sequence: AlgebraModuleShortExactSequence<P, C, I>;
    readonly degree: number;
}

export interface AlgebraGeneralizedSpanCompositionInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly after: AlgebraModuleGeneralizedSpan<P, C, I>;
    readonly before: AlgebraModuleGeneralizedSpan<P, C, I>;
}

export interface AlgebraHomologicalReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly complexSchema: AlgebraRuntimeSchema<AlgebraModuleChainComplex<P, C, I>>;
    readonly chainMapSchema: AlgebraRuntimeSchema<AlgebraModuleChainMap<P, C, I>>;
    readonly shortExactSequenceSchema: AlgebraRuntimeSchema<
        AlgebraModuleShortExactSequence<P, C, I>
    >;
    readonly generalizedSpanSchema: AlgebraRuntimeSchema<
        AlgebraModuleGeneralizedSpan<P, C, I>
    >;
    readonly homology: AlgebraOperation<
        AlgebraComplexDegreeInput<P, C, I>,
        AlgebraModuleComplexHomology<P, C, I>
    >;
    readonly functorialHomology: AlgebraOperation<
        AlgebraChainMapDegreeInput<P, C, I>,
        AlgebraModuleHomologyMap<P, C, I>
    >;
    readonly connectingMorphism: AlgebraOperation<
        AlgebraConnectingDegreeInput<P, C, I>,
        AlgebraModuleConnectingMorphism<P, C, I>
    >;
    readonly presentationResolution: AlgebraOperation<
        AlgebraPresentedModule<P, C, I>,
        AlgebraModulePresentationResolution<P, C, I>
    >;
    readonly splitResolution: AlgebraOperation<
        AlgebraPresentedModule<P, C, I>,
        AlgebraModuleSplitResolution<P, C, I>
    >;
    readonly generalizedSpanComposition: AlgebraOperation<
        AlgebraGeneralizedSpanCompositionInput<P, C, I>,
        AlgebraModuleGeneralizedSpanComposition<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const safeDegree = (value: unknown, path: string): number => {
    if (Number.isSafeInteger(value)) return value as number;
    throw new Error(`safe integer degree expected at ${path}`);
};

const algorithm = (operationId: string) => algebraAlgorithmIdentity(
    `algebra.typescript-reference/${operationId}`,
    ALGEBRA_HOMOLOGICAL_REFERENCE_OPERATIONS_PROFILE.algorithmRevision
);

export function algebraHomologicalReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(field: AlgebraFieldDomain<P, C, I>):
    AlgebraHomologicalReferenceOperations<P, C, I> {
    const suffix = field.parent.identity.id;
    const moduleRuntime = algebraModuleComputableCategory(field);
    const moduleSchema = moduleRuntime.category.objectSchema;
    const complexSchema = defineAlgebraRuntimeSchema<
        AlgebraModuleChainComplex<P, C, I>
    >({
        id: `algebra.homological.complex/${suffix}`,
        revision: field.parent.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-module-chain-complex' ||
                !Array.isArray(value.terms) ||
                !Array.isArray(value.differentials)
            ) throw new Error(`module chain complex expected at ${path}`);
            return algebraModuleChainComplex(
                field,
                value.terms as never,
                value.differentials as never
            );
        }
    });
    const chainMapSchema = defineAlgebraRuntimeSchema<
        AlgebraModuleChainMap<P, C, I>
    >({
        id: `algebra.homological.chain-map/${suffix}`,
        revision: field.parent.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-module-chain-map' ||
                !Array.isArray(value.components)
            ) throw new Error(`module chain map expected at ${path}`);
            return algebraModuleChainMap(
                complexSchema.normalize(value.source, `${path}.source`),
                complexSchema.normalize(value.target, `${path}.target`),
                value.components as never
            );
        }
    });
    const shortExactSequenceSchema = defineAlgebraRuntimeSchema<
        AlgebraModuleShortExactSequence<P, C, I>
    >({
        id: `algebra.homological.short-exact-sequence/${suffix}`,
        revision: field.parent.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-module-short-exact-sequence'
            ) throw new Error(`short exact sequence expected at ${path}`);
            return algebraModuleShortExactSequence(
                chainMapSchema.normalize(value.inclusion, `${path}.inclusion`),
                chainMapSchema.normalize(value.projection, `${path}.projection`)
            );
        }
    });
    const generalizedSpanSchema = defineAlgebraRuntimeSchema<
        AlgebraModuleGeneralizedSpan<P, C, I>
    >({
        id: `algebra.homological.generalized-span/${suffix}`,
        revision: field.parent.identity.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-module-generalized-span'
            ) throw new Error(`generalized module span expected at ${path}`);
            return algebraModuleGeneralizedSpan(
                moduleRuntime.category.morphismSchema.normalize(
                    value.sourceAid,
                    `${path}.sourceAid`
                ),
                moduleRuntime.category.morphismSchema.normalize(
                    value.arrow,
                    `${path}.arrow`
                )
            );
        }
    });
    const complexDegreeSchema = defineAlgebraRuntimeSchema<
        AlgebraComplexDegreeInput<P, C, I>
    >({
        id: `algebra.homological.complex-degree/${suffix}`,
        revision: field.parent.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`complex-degree input expected at ${path}`);
            return Object.freeze({
                complex: complexSchema.normalize(value.complex, `${path}.complex`),
                degree: safeDegree(value.degree, `${path}.degree`)
            });
        }
    });
    const chainMapDegreeSchema = defineAlgebraRuntimeSchema<
        AlgebraChainMapDegreeInput<P, C, I>
    >({
        id: `algebra.homological.chain-map-degree/${suffix}`,
        revision: field.parent.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`chain-map-degree input expected at ${path}`);
            return Object.freeze({
                chainMap: chainMapSchema.normalize(
                    value.chainMap,
                    `${path}.chainMap`
                ),
                degree: safeDegree(value.degree, `${path}.degree`)
            });
        }
    });
    const connectingDegreeSchema = defineAlgebraRuntimeSchema<
        AlgebraConnectingDegreeInput<P, C, I>
    >({
        id: `algebra.homological.connecting-degree/${suffix}`,
        revision: field.parent.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`connecting-degree input expected at ${path}`);
            return Object.freeze({
                sequence: shortExactSequenceSchema.normalize(
                    value.sequence,
                    `${path}.sequence`
                ),
                degree: safeDegree(value.degree, `${path}.degree`)
            });
        }
    });
    const spanCompositionInputSchema = defineAlgebraRuntimeSchema<
        AlgebraGeneralizedSpanCompositionInput<P, C, I>
    >({
        id: `algebra.homological.generalized-span-composition-input/${suffix}`,
        revision: field.parent.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) throw new Error(`span-composition input expected at ${path}`);
            return Object.freeze({
                after: generalizedSpanSchema.normalize(value.after, `${path}.after`),
                before: generalizedSpanSchema.normalize(value.before, `${path}.before`)
            });
        }
    });
    const wholeSchema = <T extends { readonly kind: string }>(
        id: string,
        kind: T['kind'],
        validateOwner: (value: T, path: string) => void
    ): AlgebraRuntimeSchema<T> => defineAlgebraRuntimeSchema({
        id: `${id}/${suffix}`,
        revision: field.parent.identity.revision,
        normalize(value: unknown, path: string) {
            if (!record(value) || value.kind !== kind) {
                throw new Error(`${kind} expected at ${path}`);
            }
            validateOwner(value as T, path);
            return value as T;
        }
    });
    const homologySchema = wholeSchema<AlgebraModuleComplexHomology<P, C, I>>(
        'algebra.homological.homology-result',
        'algebra-module-complex-homology',
        (value, path) => {
            moduleSchema.normalize(value.object, `${path}.object`);
        }
    );
    const homologyMapSchema = wholeSchema<AlgebraModuleHomologyMap<P, C, I>>(
        'algebra.homological.homology-map-result',
        'algebra-module-homology-map',
        (value, path) => {
            moduleRuntime.category.morphismSchema.normalize(
                value.morphism,
                `${path}.morphism`
            );
        }
    );
    const connectingSchema = wholeSchema<
        AlgebraModuleConnectingMorphism<P, C, I>
    >(
        'algebra.homological.connecting-result',
        'algebra-module-connecting-morphism',
        (value, path) => {
            moduleRuntime.category.morphismSchema.normalize(
                value.morphism,
                `${path}.morphism`
            );
        }
    );
    const presentationResolutionSchema = wholeSchema<
        AlgebraModulePresentationResolution<P, C, I>
    >(
        'algebra.homological.presentation-resolution-result',
        'algebra-module-presentation-resolution',
        (value, path) => {
            moduleSchema.normalize(value.module, `${path}.module`);
        }
    );
    const splitResolutionSchema = wholeSchema<
        AlgebraModuleSplitResolution<P, C, I>
    >(
        'algebra.homological.split-resolution-result',
        'algebra-module-split-resolution',
        (value, path) => {
            moduleSchema.normalize(value.module, `${path}.module`);
        }
    );
    const spanCompositionSchema = wholeSchema<
        AlgebraModuleGeneralizedSpanComposition<P, C, I>
    >(
        'algebra.homological.generalized-span-composition-result',
        'algebra-module-generalized-span-composition',
        (value, path) => {
            generalizedSpanSchema.normalize(value.result, `${path}.result`);
        }
    );
    const homology = defineAlgebraOperation({
        id: `algebra.homological.homology/${suffix}`,
        revision: field.parent.identity.revision,
        input: complexDegreeSchema,
        output: homologySchema
    });
    const functorialHomology = defineAlgebraOperation({
        id: `algebra.homological.functorial-homology/${suffix}`,
        revision: field.parent.identity.revision,
        input: chainMapDegreeSchema,
        output: homologyMapSchema
    });
    const connectingMorphism = defineAlgebraOperation({
        id: `algebra.homological.connecting-morphism/${suffix}`,
        revision: field.parent.identity.revision,
        input: connectingDegreeSchema,
        output: connectingSchema
    });
    const presentationResolution = defineAlgebraOperation({
        id: `algebra.homological.presentation-resolution/${suffix}`,
        revision: field.parent.identity.revision,
        input: moduleSchema,
        output: presentationResolutionSchema
    });
    const splitResolution = defineAlgebraOperation({
        id: `algebra.homological.split-resolution/${suffix}`,
        revision: field.parent.identity.revision,
        input: moduleSchema,
        output: splitResolutionSchema
    });
    const generalizedSpanComposition = defineAlgebraOperation({
        id: `algebra.homological.generalized-span-composition/${suffix}`,
        revision: field.parent.identity.revision,
        input: spanCompositionInputSchema,
        output: spanCompositionSchema
    });
    const implementations = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation: homology,
            algorithm: algorithm(homology.identity.id),
            execute: input => algebraModuleChainComplexHomology(
                input.complex,
                input.degree
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: functorialHomology,
            algorithm: algorithm(functorialHomology.identity.id),
            execute: input => algebraModuleChainMapHomology(
                input.chainMap,
                input.degree
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: connectingMorphism,
            algorithm: algorithm(connectingMorphism.identity.id),
            execute: input => algebraModuleConnectingMorphism(
                input.sequence,
                input.degree
            )
        }),
        defineAlgebraReferenceImplementation({
            operation: presentationResolution,
            algorithm: algorithm(presentationResolution.identity.id),
            execute: algebraModulePresentationResolution
        }),
        defineAlgebraReferenceImplementation({
            operation: splitResolution,
            algorithm: algorithm(splitResolution.identity.id),
            execute: algebraModuleSplitResolution
        }),
        defineAlgebraReferenceImplementation({
            operation: generalizedSpanComposition,
            algorithm: algorithm(generalizedSpanComposition.identity.id),
            execute: input => algebraModuleGeneralizedSpanComposition(
                input.after,
                input.before
            )
        })
    ]);
    return Object.freeze({
        complexSchema,
        chainMapSchema,
        shortExactSequenceSchema,
        generalizedSpanSchema,
        homology,
        functorialHomology,
        connectingMorphism,
        presentationResolution,
        splitResolution,
        generalizedSpanComposition,
        implementations
    });
}
