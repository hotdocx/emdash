/**
 * Dependency inspection for persistent locally nameless Core telescopes.
 *
 * This layer classifies genuine dependency edges and independent sibling
 * slots before a semantic lowerer chooses ordinary LF structural maps,
 * displayed Sigma/pullback structure, or a qualified fibrewise product.
 * It deliberately emits no categorical owner.
 */

import {
    CoreContext,
    CoreLocalBinding
} from './context';
import {
    Provenance,
    formatSourceSpan,
    kernelAmbientDependencies
} from './kernel';

export interface CoreContextDirectDependency {
    readonly position: number;
    readonly occurrences: readonly Provenance[];
}

export interface CoreContextDependencyNode {
    readonly position: number;
    readonly name: string;
    readonly binding: CoreLocalBinding;
    readonly directDependencies:
        readonly CoreContextDirectDependency[];
    readonly dependencyClosure: readonly number[];
    /**
     * Least outermost-first ordered prefix containing the transitive
     * dependency closure.
     */
    readonly dependencyPrefix: number;
}

export interface CoreContextDependencyGraph {
    readonly context: CoreContext;
    readonly nodes: readonly CoreContextDependencyNode[];
}

export type CoreContextDependencyAnalysisErrorCode =
    | 'INVALID_CONTEXT_POSITION'
    | 'INVALID_SIBLING_BLOCK'
    | 'INVALID_CONTEXT_USE_COUNT';

export class CoreContextDependencyAnalysisError extends Error {
    constructor(
        public readonly code:
            CoreContextDependencyAnalysisErrorCode,
        public readonly provenance: Provenance,
        message: string
    ) {
        const location = provenance.span
            ? ` at ${formatSourceSpan(provenance.span)}`
            : '';
        super(`${message}${location}`);
        this.name = 'CoreContextDependencyAnalysisError';
    }
}

const sortedUnique = (
    positions: readonly number[]
): readonly number[] => Object.freeze(
    [...new Set(positions)].sort((left, right) => left - right)
);

const samePositions = (
    left: readonly number[],
    right: readonly number[]
): boolean =>
    left.length === right.length &&
    left.every((position, index) => position === right[index]);

const dependencyPrefix = (
    positions: readonly number[]
): number => positions.length === 0
    ? 0
    : positions[positions.length - 1] + 1;

const nodeAt = (
    graph: CoreContextDependencyGraph,
    position: number,
    operationProvenance: Provenance
): CoreContextDependencyNode => {
    if (
        Number.isSafeInteger(position) &&
        position >= 0 &&
        position < graph.nodes.length
    ) {
        return graph.nodes[position];
    }
    throw new CoreContextDependencyAnalysisError(
        'INVALID_CONTEXT_POSITION',
        operationProvenance,
        `Core context dependency analysis requires a position below ` +
        `depth ${graph.nodes.length}; received ${position}`
    );
};

/**
 * Recover direct and transitive dependencies from stored binding types.
 *
 * Positions are outermost-first. No caller-maintained dependency flags are
 * trusted or duplicated.
 */
export const coreContextDependencyGraph = (
    context: CoreContext
): CoreContextDependencyGraph => {
    const nodes: CoreContextDependencyNode[] = [];

    context.telescope.forEach((binding, position) => {
        const directDependencies = kernelAmbientDependencies(
            binding.type,
            position
        ).map(dependency =>
            Object.freeze({
                position: position - dependency.index - 1,
                occurrences: dependency.occurrences
            })
        ).sort((left, right) => left.position - right.position);

        const closure = sortedUnique(
            directDependencies.flatMap(dependency => [
                dependency.position,
                ...nodes[dependency.position].dependencyClosure
            ])
        );

        nodes.push(Object.freeze({
            position,
            name: binding.name,
            binding,
            directDependencies: Object.freeze(directDependencies),
            dependencyClosure: closure,
            dependencyPrefix: dependencyPrefix(closure)
        }));
    });

    return Object.freeze({
        context,
        nodes: Object.freeze(nodes)
    });
};

export type CoreAdjacentContextExchangeAnalysis =
    | {
        readonly allowed: false;
        readonly relation: 'genuine-dependency-edge';
        readonly olderPosition: number;
        readonly newerPosition: number;
        readonly dependencyProvenance: Provenance;
    }
    | {
        readonly allowed: true;
        readonly relation:
            | 'shared-minimal-base-siblings'
            | 'independent-after-weakening';
        readonly olderPosition: number;
        readonly newerPosition: number;
        readonly commonDependencies: readonly number[];
        readonly commonDependencyPrefix: number;
        readonly suffixTransportPositions: readonly number[];
    };

/**
 * Classify one adjacent exchange without performing it.
 *
 * A permitted exchange still records later classifiers that depend on either
 * slot and therefore need transport through the permutation.
 */
export const analyzeCoreAdjacentContextExchange = (
    graph: CoreContextDependencyGraph,
    olderPosition: number,
    operationProvenance: Provenance
): CoreAdjacentContextExchangeAnalysis => {
    const older = nodeAt(
        graph,
        olderPosition,
        operationProvenance
    );
    const newer = nodeAt(
        graph,
        olderPosition + 1,
        operationProvenance
    );
    const dependency = newer.directDependencies.find(
        candidate => candidate.position === older.position
    );

    if (dependency) {
        return Object.freeze({
            allowed: false,
            relation: 'genuine-dependency-edge',
            olderPosition: older.position,
            newerPosition: newer.position,
            dependencyProvenance:
                dependency.occurrences[0] ?? newer.binding.provenance
        });
    }

    const commonDependencies = sortedUnique([
        ...older.dependencyClosure,
        ...newer.dependencyClosure
    ]);
    const suffixTransportPositions = Object.freeze(
        graph.nodes
            .slice(newer.position + 1)
            .filter(node =>
                node.dependencyClosure.includes(older.position) ||
                node.dependencyClosure.includes(newer.position)
            )
            .map(node => node.position)
    );

    return Object.freeze({
        allowed: true,
        relation: samePositions(
            older.dependencyClosure,
            newer.dependencyClosure
        )
            ? 'shared-minimal-base-siblings'
            : 'independent-after-weakening',
        olderPosition: older.position,
        newerPosition: newer.position,
        commonDependencies,
        commonDependencyPrefix:
            dependencyPrefix(commonDependencies),
        suffixTransportPositions
    });
};

export type CoreContextSiblingBlockAnalysis =
    | {
        readonly allowed: false;
        readonly relation: 'contains-dependency-edge';
        readonly positions: readonly number[];
        readonly dependentPosition: number;
        readonly dependencyPosition: number;
        readonly dependencyProvenance: Provenance;
    }
    | {
        readonly allowed: true;
        readonly relation:
            | 'shared-minimal-base-siblings'
            | 'independent-after-weakening';
        readonly positions: readonly number[];
        readonly commonDependencies: readonly number[];
        readonly commonDependencyPrefix: number;
        readonly weakeningPositions: readonly number[];
        readonly sequentialPullbackPositions: readonly number[];
        readonly structuralIntents: readonly [
            'projection',
            'pairing',
            'exchange',
            'diagonal'
        ];
    };

/**
 * Analyze a contiguous ordered block as a candidate fibrewise product.
 *
 * The result records semantic intent only. A later categorical lowerer must
 * supply active displayed product/projection/action owners.
 */
export const analyzeCoreContextSiblingBlock = (
    graph: CoreContextDependencyGraph,
    positions: readonly number[],
    operationProvenance: Provenance
): CoreContextSiblingBlockAnalysis => {
    if (
        positions.length < 2 ||
        positions.some((position, index) =>
            !Number.isSafeInteger(position) ||
            position < 0 ||
            position >= graph.nodes.length ||
            (index > 0 && position !== positions[index - 1] + 1)
        )
    ) {
        throw new CoreContextDependencyAnalysisError(
            'INVALID_SIBLING_BLOCK',
            operationProvenance,
            'Core sibling analysis requires at least two distinct, ' +
            'contiguous, outermost-first context positions'
        );
    }

    const memberPositions = new Set(positions);
    for (const position of positions) {
        const node = graph.nodes[position];
        const dependency = node.directDependencies.find(candidate =>
            memberPositions.has(candidate.position)
        );
        if (!dependency) continue;
        return Object.freeze({
            allowed: false,
            relation: 'contains-dependency-edge',
            positions: Object.freeze([...positions]),
            dependentPosition: position,
            dependencyPosition: dependency.position,
            dependencyProvenance:
                dependency.occurrences[0] ?? node.binding.provenance
        });
    }

    const commonDependencies = sortedUnique(
        positions.flatMap(position =>
            graph.nodes[position].dependencyClosure
        )
    );
    const exactSharedBase = positions.every(position =>
        samePositions(
            graph.nodes[position].dependencyClosure,
            graph.nodes[positions[0]].dependencyClosure
        )
    );
    const weakeningPositions = Object.freeze(
        positions.filter(position =>
            !samePositions(
                graph.nodes[position].dependencyClosure,
                commonDependencies
            )
        )
    );
    const structuralIntents = Object.freeze([
        'projection',
        'pairing',
        'exchange',
        'diagonal'
    ] as const);

    return Object.freeze({
        allowed: true,
        relation: exactSharedBase
            ? 'shared-minimal-base-siblings'
            : 'independent-after-weakening',
        positions: Object.freeze([...positions]),
        commonDependencies,
        commonDependencyPrefix:
            dependencyPrefix(commonDependencies),
        weakeningPositions,
        sequentialPullbackPositions:
            Object.freeze(positions.slice(1)),
        structuralIntents
    });
};

export interface CoreContextSlotUsePlan {
    readonly position: number;
    readonly count: number;
    readonly intent:
        | 'projection-weakening'
        | 'identity'
        | 'diagonal-contraction';
    readonly diagonalIterations: number;
    readonly dependencyClosure: readonly number[];
    readonly dependencyPrefix: number;
}

/**
 * Convert a checked slot-use count into structural intent.
 *
 * This is deliberately owner-neutral: categorical projection/diagonal
 * selection remains a later authority-backed lowering step.
 */
export const planCoreContextSlotUse = (
    graph: CoreContextDependencyGraph,
    position: number,
    count: number,
    operationProvenance: Provenance
): CoreContextSlotUsePlan => {
    const node = nodeAt(graph, position, operationProvenance);
    if (!Number.isSafeInteger(count) || count < 0) {
        throw new CoreContextDependencyAnalysisError(
            'INVALID_CONTEXT_USE_COUNT',
            operationProvenance,
            `Core contextual use count must be a nonnegative safe ` +
            `integer; received ${count}`
        );
    }

    return Object.freeze({
        position,
        count,
        intent: count === 0
            ? 'projection-weakening'
            : count === 1
                ? 'identity'
                : 'diagonal-contraction',
        diagonalIterations: Math.max(0, count - 1),
        dependencyClosure: node.dependencyClosure,
        dependencyPrefix: node.dependencyPrefix
    });
};
