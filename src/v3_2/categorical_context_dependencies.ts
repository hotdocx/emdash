/**
 * FIBRED-CONTEXT-0B categorical adapter for the generic dependency graph.
 *
 * This module records sequential Sigma/pullback and grouped displayed-product
 * intent. It does not emit Core, select a Product_catd owner, or change the
 * completed categorical surface lowerers.
 */

import {
    CoreCategoricalClassifier,
    CoreCategoricalIndexedObjectClassifier
} from './categorical_surface';
import {
    CoreContextDependencyAnalysisError,
    CoreContextDependencyGraph,
    CoreContextSiblingBlockAnalysis,
    CoreDependencyGraphBinding,
    analyzeCoreContextSiblingBlock,
    coreDependencyGraphFromSlotEvidence
} from './context_dependencies';
import {
    KernelExpression,
    Provenance,
    assertSafeIdentifier,
    formatSourceSpan,
    kernelAssertScoped,
    kernelExpressionEquals
} from './kernel';
import {
    CoreType
} from './surface';

export const CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION =
    'FIBRED-CONTEXT-0B' as const;

export interface CoreCategoricalContextSlotReference {
    readonly tag: 'categorical-context-slot-reference';
    /**
     * Nearest-first index in the prefix before the owning slot.
     */
    readonly index: number;
    readonly provenance: Provenance;
}

export interface CoreCategoricalClosedContextClassifier {
    readonly tag: 'closed-categorical-classifier';
    readonly result: CoreType;
    readonly provenance: Provenance;
}

export interface CoreCategoricalDisplayedContextClassifier {
    readonly tag: 'displayed-family-application';
    readonly baseCategory: KernelExpression;
    readonly family: KernelExpression;
    readonly parameters: readonly CoreCategoricalContextSlotReference[];
    readonly result: CoreCategoricalClassifier;
    readonly provenance: Provenance;
}

export type CoreCategoricalContextSlotClassifier =
    | CoreCategoricalClosedContextClassifier
    | CoreCategoricalDisplayedContextClassifier;

export interface CoreCategoricalContextSlot
extends CoreDependencyGraphBinding {
    readonly classifier: CoreCategoricalContextSlotClassifier;
}

export interface CoreCategoricalSiblingGroupRequest {
    readonly positions: readonly number[];
    readonly provenance: Provenance;
}

export interface CoreCategoricalContextPlanningInput {
    readonly slots: readonly {
        readonly name: string;
        readonly classifier: CoreCategoricalContextSlotClassifier;
        readonly provenance: Provenance;
    }[];
    readonly siblingGroups?: readonly CoreCategoricalSiblingGroupRequest[];
}

export interface CoreCategoricalContextRepresentation {
    readonly revision:
        typeof CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION;
    readonly slots: readonly CoreCategoricalContextSlot[];
}

export type CoreCategoricalSequentialContextIntent =
    | {
        readonly kind: 'base-context-slot';
        readonly position: number;
        readonly name: string;
        readonly dependencyClosure: readonly number[];
        readonly dependencyPrefix: number;
        readonly emittedCore: null;
    }
    | {
        readonly kind: 'displayed-sigma-extension';
        readonly position: number;
        readonly name: string;
        readonly baseCategory: KernelExpression;
        readonly family: KernelExpression;
        readonly dependencyClosure: readonly number[];
        readonly dependencyPrefix: number;
        readonly pullbackPastPositions: readonly number[];
        readonly presentation:
            | 'direct-sigma-extension'
            | 'pullback-then-sigma-extension';
        readonly emittedCore: null;
    };

export interface CoreCategoricalDependencyEdge {
    readonly kind: 'genuine-dependency-edge';
    readonly dependencyPosition: number;
    readonly dependentPosition: number;
    readonly occurrences: readonly Provenance[];
}

export interface CoreCategoricalDependencyChain {
    readonly kind: 'dependent-chain';
    readonly dependentPosition: number;
    readonly dependencyPositions: readonly number[];
}

export interface CoreCategoricalGroupedProductFactor {
    readonly position: number;
    readonly name: string;
    readonly family: KernelExpression;
}

export interface CoreCategoricalGroupedProductIntent {
    readonly kind: 'grouped-displayed-product';
    readonly relation:
        | 'shared-minimal-base-siblings'
        | 'independent-after-weakening';
    readonly positions: readonly number[];
    readonly baseCategory: KernelExpression;
    readonly commonDependencies: readonly number[];
    readonly commonDependencyPrefix: number;
    readonly weakeningPositions: readonly number[];
    readonly sequentialPullbackPositions: readonly number[];
    readonly factors: readonly CoreCategoricalGroupedProductFactor[];
    readonly structuralIntents: readonly [
        'projection',
        'pairing',
        'exchange',
        'diagonal'
    ];
    readonly candidateSemanticName: 'Product_catd';
    readonly selectedCoreOwner: null;
    readonly fibreComputation:
        'pointwise-product-required';
    readonly baseArrowComputation:
        'componentwise-product-map-required';
    readonly totalCategoryPullbackAssumed: false;
    readonly status:
        'representation-only-owner-unqualified';
}

export interface CoreCategoricalContextDependencyPlan {
    readonly revision:
        typeof CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION;
    readonly context: CoreCategoricalContextRepresentation;
    readonly graph: CoreContextDependencyGraph<
        CoreCategoricalContextRepresentation,
        CoreCategoricalContextSlot
    >;
    readonly dependencyEdges: readonly CoreCategoricalDependencyEdge[];
    readonly dependencyChains: readonly CoreCategoricalDependencyChain[];
    readonly sequential:
        readonly CoreCategoricalSequentialContextIntent[];
    readonly groupedProducts:
        readonly CoreCategoricalGroupedProductIntent[];
    readonly boundary: {
        readonly emittedCoreOwnerCount: 0;
        readonly activeKernelChanged: false;
        readonly existingSurfaceBehaviorChanged: false;
        readonly productOwnerSelected: false;
        readonly genericTotalPullbackAssumed: false;
    };
}

export type CoreCategoricalContextPlanningErrorCode =
    | 'INVALID_CONTEXTUAL_SLOT_REFERENCE'
    | 'INVALID_SIBLING_GROUP'
    | 'DEPENDENT_SIBLING_GROUP'
    | 'NON_DISPLAYED_SIBLING_GROUP'
    | 'DISPLAYED_PRODUCT_BASE_MISMATCH';

export class CoreCategoricalContextPlanningError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalContextPlanningErrorCode,
        public readonly provenance: Provenance,
        message: string,
        public readonly underlying?: Error
    ) {
        const location = provenance.span
            ? ` at ${formatSourceSpan(provenance.span)}`
            : '';
        super(`${message}${location}`);
        this.name = 'CoreCategoricalContextPlanningError';
    }
}

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        Object.freeze(value);
    }
    return value;
};

const copyCoreType = (type: CoreType): CoreType => {
    switch (type.tag) {
        case 'category':
            return { tag: 'category' };
        case 'object':
            return { tag: 'object', category: type.category };
        case 'functor':
            return {
                tag: 'functor',
                sourceCategory: type.sourceCategory,
                targetCategory: type.targetCategory
            };
        case 'hom':
            return {
                tag: 'hom',
                category: type.category,
                sourceObject: type.sourceObject,
                targetObject: type.targetObject
            };
        case 'transfor':
            return {
                tag: 'transfor',
                sourceCategory: type.sourceCategory,
                targetCategory: type.targetCategory,
                sourceFunctor: type.sourceFunctor,
                targetFunctor: type.targetFunctor
            };
        case 'dependent-section':
            return {
                tag: 'dependent-section',
                category: type.category,
                baseCategory: type.baseCategory,
                family: type.family
            };
        case 'displayed-functor':
            return {
                tag: 'displayed-functor',
                category: type.category,
                baseCategory: type.baseCategory,
                sourceFamily: type.sourceFamily,
                targetFamily: type.targetFamily
            };
        case 'displayed-transfor':
            return {
                tag: 'displayed-transfor',
                category: type.category,
                baseCategory: type.baseCategory,
                sourceFamily: type.sourceFamily,
                targetFamily: type.targetFamily,
                sourceFunctor: type.sourceFunctor,
                targetFunctor: type.targetFunctor
            };
        default: {
            const exhaustive: never = type;
            return exhaustive;
        }
    }
};

const copyClassifier = (
    classifier: CoreCategoricalClassifier
): CoreCategoricalClassifier => {
    if (classifier.tag === 'indexed-object') {
        return {
            tag: 'indexed-object',
            baseCategory: classifier.baseCategory,
            family: classifier.family,
            index: classifier.index
        };
    }
    if (classifier.tag === 'indexed-functor') {
        return {
            tag: 'indexed-functor',
            baseCategory: classifier.baseCategory,
            sourceFamily: classifier.sourceFamily,
            targetFamily: classifier.targetFamily,
            index: classifier.index
        };
    }
    if (classifier.tag === 'indexed-transfor') {
        return {
            tag: 'indexed-transfor',
            baseCategory: classifier.baseCategory,
            sourceFamily: classifier.sourceFamily,
            targetFamily: classifier.targetFamily,
            sourceFunctor: classifier.sourceFunctor,
            targetFunctor: classifier.targetFunctor,
            index: classifier.index
        };
    }
    if (classifier.tag === 'nested-indexed-object') {
        return {
            tag: 'nested-indexed-object',
            outerBaseCategory: classifier.outerBaseCategory,
            outerIndex: classifier.outerIndex,
            innerBaseCategory: classifier.innerBaseCategory,
            innerIndex: classifier.innerIndex,
            classifierFamily: classifier.classifierFamily,
            sourceSection: classifier.sourceSection,
            targetSection: classifier.targetSection,
            endpoint: classifier.endpoint
        };
    }
    return copyCoreType(classifier);
};

export const coreCategoricalContextSlotReference = (
    index: number,
    nodeProvenance: Provenance
): CoreCategoricalContextSlotReference => {
    if (!Number.isSafeInteger(index) || index < 0) {
        throw new CoreCategoricalContextPlanningError(
            'INVALID_CONTEXTUAL_SLOT_REFERENCE',
            nodeProvenance,
            `Categorical contextual slot index must be a nonnegative safe ` +
            `integer; received ${index}`
        );
    }
    return deepFreeze({
        tag: 'categorical-context-slot-reference' as const,
        index,
        provenance: nodeProvenance
    });
};

export const coreCategoricalClosedContextClassifier = (
    result: CoreType,
    nodeProvenance: Provenance
): CoreCategoricalClosedContextClassifier => deepFreeze({
    tag: 'closed-categorical-classifier' as const,
    result: copyCoreType(result),
    provenance: nodeProvenance
});

export const coreCategoricalDisplayedContextClassifier = (
    baseCategory: KernelExpression,
    family: KernelExpression,
    parameters: readonly CoreCategoricalContextSlotReference[],
    result: CoreCategoricalClassifier,
    nodeProvenance: Provenance
): CoreCategoricalDisplayedContextClassifier => {
    kernelAssertScoped(baseCategory);
    kernelAssertScoped(family);
    return deepFreeze({
        tag: 'displayed-family-application' as const,
        baseCategory,
        family,
        parameters: parameters.map(parameter => ({ ...parameter })),
        result: copyClassifier(result),
        provenance: nodeProvenance
    });
};

/**
 * Adapt the one-index classifier already stored by USABILITY-2A1/D-003.
 */
export const coreCategoricalIndexedObjectContextClassifier = (
    classifier: CoreCategoricalIndexedObjectClassifier,
    nodeProvenance: Provenance
): CoreCategoricalDisplayedContextClassifier =>
    coreCategoricalDisplayedContextClassifier(
        classifier.baseCategory,
        classifier.family,
        [
            coreCategoricalContextSlotReference(
                classifier.index,
                nodeProvenance
            )
        ],
        classifier,
        nodeProvenance
    );

const range = (
    start: number,
    endExclusive: number
): readonly number[] => Object.freeze(
    Array.from(
        { length: Math.max(0, endExclusive - start) },
        (_, offset) => start + offset
    )
);

const normalizeSlots = (
    input: CoreCategoricalContextPlanningInput
): readonly CoreCategoricalContextSlot[] => Object.freeze(
    input.slots.map(slot => {
        assertSafeIdentifier(slot.name, 'Categorical context slot');
        return deepFreeze({
            name: slot.name,
            classifier: slot.classifier.tag ===
                'closed-categorical-classifier'
                ? {
                    tag: 'closed-categorical-classifier' as const,
                    result: copyCoreType(slot.classifier.result),
                    provenance: slot.classifier.provenance
                }
                : {
                    tag: 'displayed-family-application' as const,
                    baseCategory: slot.classifier.baseCategory,
                    family: slot.classifier.family,
                    parameters: slot.classifier.parameters.map(
                        parameter => ({ ...parameter })
                    ),
                    result: copyClassifier(slot.classifier.result),
                    provenance: slot.classifier.provenance
                },
            provenance: slot.provenance
        });
    })
);

const directEvidence = (
    slot: CoreCategoricalContextSlot,
    position: number
) => {
    if (slot.classifier.tag === 'closed-categorical-classifier') {
        return Object.freeze([]);
    }
    return Object.freeze(
        slot.classifier.parameters.map(parameter => {
            if (parameter.index >= position) {
                throw new CoreCategoricalContextPlanningError(
                    'INVALID_CONTEXTUAL_SLOT_REFERENCE',
                    parameter.provenance,
                    `Classifier of categorical slot '${slot.name}' at ` +
                    `position ${position} refers to contextual index ` +
                    `${parameter.index}, but only ${position} earlier ` +
                    `slots are in scope`
                );
            }
            return Object.freeze({
                position: position - parameter.index - 1,
                occurrences: Object.freeze([
                    parameter.provenance
                ])
            });
        })
    );
};

const planGroup = (
    context: CoreCategoricalContextRepresentation,
    graph: CoreCategoricalContextDependencyPlan['graph'],
    request: CoreCategoricalSiblingGroupRequest
): CoreCategoricalGroupedProductIntent => {
    let analysis: CoreContextSiblingBlockAnalysis;
    try {
        analysis = analyzeCoreContextSiblingBlock(
            graph,
            request.positions,
            request.provenance
        );
    } catch (error: unknown) {
        if (error instanceof CoreContextDependencyAnalysisError) {
            throw new CoreCategoricalContextPlanningError(
                'INVALID_SIBLING_GROUP',
                error.provenance,
                error.message,
                error
            );
        }
        throw error;
    }
    if (analysis.allowed === false) {
        throw new CoreCategoricalContextPlanningError(
            'DEPENDENT_SIBLING_GROUP',
            analysis.dependencyProvenance,
            `Cannot group categorical slots at positions ` +
            `${request.positions.join(', ')}: slot ` +
            `${analysis.dependentPosition} depends on grouped slot ` +
            `${analysis.dependencyPosition}`
        );
    }

    const factors = request.positions.map(position => {
        const slot = context.slots[position];
        if (slot.classifier.tag !== 'displayed-family-application') {
            throw new CoreCategoricalContextPlanningError(
                'NON_DISPLAYED_SIBLING_GROUP',
                slot.provenance,
                `Categorical slot '${slot.name}' at position ${position} ` +
                `is not a displayed-family application and cannot be a ` +
                `factor of grouped Product_catd intent`
            );
        }
        return {
            slot,
            classifier: slot.classifier
        };
    });
    const baseCategory = factors[0].classifier.baseCategory;
    for (const factor of factors.slice(1)) {
        if (
            !kernelExpressionEquals(
                baseCategory,
                factor.classifier.baseCategory
            )
        ) {
            throw new CoreCategoricalContextPlanningError(
                'DISPLAYED_PRODUCT_BASE_MISMATCH',
                factor.slot.provenance,
                `Displayed sibling '${factor.slot.name}' does not share the ` +
                `first factor's base category`
            );
        }
    }

    return deepFreeze({
        kind: 'grouped-displayed-product' as const,
        relation: analysis.relation,
        positions: [...request.positions],
        baseCategory,
        commonDependencies: [...analysis.commonDependencies],
        commonDependencyPrefix: analysis.commonDependencyPrefix,
        weakeningPositions: [...analysis.weakeningPositions],
        sequentialPullbackPositions: [
            ...analysis.sequentialPullbackPositions
        ],
        factors: factors.map(({ slot, classifier }, index) => ({
            position: request.positions[index],
            name: slot.name,
            family: classifier.family
        })),
        structuralIntents: analysis.structuralIntents,
        candidateSemanticName: 'Product_catd' as const,
        selectedCoreOwner: null,
        fibreComputation: 'pointwise-product-required' as const,
        baseArrowComputation:
            'componentwise-product-map-required' as const,
        totalCategoryPullbackAssumed: false as const,
        status:
            'representation-only-owner-unqualified' as const
    });
};

/**
 * Build the categorical dependency/presentation plan without lowering it.
 */
export const planCoreCategoricalContextDependencies = (
    input: CoreCategoricalContextPlanningInput
): CoreCategoricalContextDependencyPlan => {
    const slots = normalizeSlots(input);
    const context = deepFreeze({
        revision: CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION,
        slots
    });
    const graph = coreDependencyGraphFromSlotEvidence(
        context,
        slots.map((slot, position) => ({
            binding: slot,
            directDependencies: directEvidence(slot, position)
        }))
    );

    const dependencyEdges = graph.nodes.flatMap(node =>
        node.directDependencies.map(dependency => deepFreeze({
            kind: 'genuine-dependency-edge' as const,
            dependencyPosition: dependency.position,
            dependentPosition: node.position,
            occurrences: [...dependency.occurrences]
        }))
    );
    const dependencyChains = graph.nodes
        .filter(node => node.dependencyClosure.length > 1)
        .map(node => deepFreeze({
            kind: 'dependent-chain' as const,
            dependentPosition: node.position,
            dependencyPositions: [...node.dependencyClosure]
        }));
    const sequential = graph.nodes.map(node => {
        const classifier = node.binding.classifier;
        if (classifier.tag === 'closed-categorical-classifier') {
            return deepFreeze({
                kind: 'base-context-slot' as const,
                position: node.position,
                name: node.name,
                dependencyClosure: [...node.dependencyClosure],
                dependencyPrefix: node.dependencyPrefix,
                emittedCore: null
            });
        }
        const pullbackPastPositions = range(
            node.dependencyPrefix,
            node.position
        );
        return deepFreeze({
            kind: 'displayed-sigma-extension' as const,
            position: node.position,
            name: node.name,
            baseCategory: classifier.baseCategory,
            family: classifier.family,
            dependencyClosure: [...node.dependencyClosure],
            dependencyPrefix: node.dependencyPrefix,
            pullbackPastPositions,
            presentation: pullbackPastPositions.length === 0
                ? 'direct-sigma-extension' as const
                : 'pullback-then-sigma-extension' as const,
            emittedCore: null
        });
    });
    const groupedProducts = (input.siblingGroups ?? []).map(
        request => planGroup(context, graph, request)
    );

    return deepFreeze({
        revision: CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION,
        context,
        graph,
        dependencyEdges,
        dependencyChains,
        sequential,
        groupedProducts,
        boundary: {
            emittedCoreOwnerCount: 0 as const,
            activeKernelChanged: false as const,
            existingSurfaceBehaviorChanged: false as const,
            productOwnerSelected: false as const,
            genericTotalPullbackAssumed: false as const
        }
    });
};
