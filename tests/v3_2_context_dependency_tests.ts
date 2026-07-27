/**
 * Focused FIBRED-CONTEXT-0A dependency-graph tests.
 */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CoreBindingInput,
    CoreContext,
    CoreContextDependencyAnalysisError,
    KernelExpression,
    analyzeCoreAdjacentContextExchange,
    analyzeCoreContextSiblingBlock,
    binderMode,
    coreContextDependencyGraph,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelPi,
    kernelUniverse,
    planCoreContextSlotUse,
    provenance,
    sourceSpan
} from '../src/v3_2';

const fixture =
    'tests/fixtures/v3_2_context_dependencies.surface.ts';
const at = (line: number) =>
    sourceSpan(fixture, line, 1, line, 2);
const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));
const mode = binderMode('explicit', 'functorial');

const local = (
    name: string,
    type: KernelExpression,
    line: number
): CoreBindingInput => ({
    name,
    type,
    mode,
    provenance: because(line, `context slot ${name}`)
});

const siblingContext = (): CoreContext => {
    const rootType = kernelUniverse(
        because(10, 'root classifier')
    );
    const bType = kernelPi(
        kernelBinder(
            'internal',
            kernelUniverse(because(11, 'internal binder type')),
            mode,
            because(11, 'internal binder')
        ),
        kernelBound(
            1,
            because(12, 'a beneath an internal binder')
        ),
        because(11, 'B(a) classifier')
    );
    const cType = kernelBound(
        1,
        because(13, 'a in C(a)')
    );
    const dType = kernelCall(
        kernelBound(0, because(14, 'c in D(b,c)')),
        [{
            plicity: 'explicit',
            value: kernelBound(
                1,
                because(15, 'b in D(b,c)')
            )
        }],
        because(14, 'D(b,c) classifier')
    );

    return CoreContext.empty()
        .extend(local('a', rootType, 10))
        .extend(local('b', bType, 11))
        .extend(local('c', cType, 13))
        .extend(local('d', dType, 14));
};

describe('FIBRED-CONTEXT-0A dependency-aware Core contexts', () => {
    it('recovers direct, transitive, and under-binder dependencies', () => {
        const graph = coreContextDependencyGraph(siblingContext());

        assert.deepEqual(
            graph.nodes.map(node => ({
                name: node.name,
                direct: node.directDependencies.map(
                    dependency => dependency.position
                ),
                closure: node.dependencyClosure,
                prefix: node.dependencyPrefix
            })),
            [
                { name: 'a', direct: [], closure: [], prefix: 0 },
                { name: 'b', direct: [0], closure: [0], prefix: 1 },
                { name: 'c', direct: [0], closure: [0], prefix: 1 },
                {
                    name: 'd',
                    direct: [1, 2],
                    closure: [0, 1, 2],
                    prefix: 3
                }
            ]
        );
        assert.equal(
            graph.nodes[1]
                .directDependencies[0]
                .occurrences[0]
                .span?.start.line,
            12
        );
    });

    it('classifies siblings and names the suffix needing transport', () => {
        const graph = coreContextDependencyGraph(siblingContext());
        const exchange = analyzeCoreAdjacentContextExchange(
            graph,
            1,
            because(20, 'exchange b and c')
        );

        assert.equal(exchange.allowed, true);
        if (!exchange.allowed) {
            throw new Error('Expected sibling exchange to be allowed');
        }
        assert.equal(
            exchange.relation,
            'shared-minimal-base-siblings'
        );
        assert.deepEqual(exchange.commonDependencies, [0]);
        assert.equal(exchange.commonDependencyPrefix, 1);
        assert.deepEqual(exchange.suffixTransportPositions, [3]);

        const group = analyzeCoreContextSiblingBlock(
            graph,
            [1, 2],
            because(21, 'group b and c')
        );
        assert.equal(group.allowed, true);
        if (!group.allowed) {
            throw new Error('Expected sibling group to be allowed');
        }
        assert.equal(group.relation, 'shared-minimal-base-siblings');
        assert.deepEqual(group.commonDependencies, [0]);
        assert.deepEqual(group.weakeningPositions, []);
        assert.deepEqual(group.sequentialPullbackPositions, [2]);
        assert.deepEqual(group.structuralIntents, [
            'projection',
            'pairing',
            'exchange',
            'diagonal'
        ]);
    });

    it('rejects exchange and grouping across a genuine dependency edge', () => {
        const graph = coreContextDependencyGraph(siblingContext());
        const exchange = analyzeCoreAdjacentContextExchange(
            graph,
            2,
            because(30, 'exchange c and d')
        );

        assert.equal(exchange.allowed, false);
        if (exchange.allowed !== false) {
            throw new Error('Expected dependent exchange to be blocked');
        }
        assert.equal(exchange.relation, 'genuine-dependency-edge');
        assert.equal(exchange.dependencyProvenance.span?.start.line, 14);

        const group = analyzeCoreContextSiblingBlock(
            graph,
            [2, 3],
            because(31, 'group c and d')
        );
        assert.equal(group.allowed, false);
        if (group.allowed !== false) {
            throw new Error('Expected dependent group to be blocked');
        }
        assert.equal(group.dependentPosition, 3);
        assert.equal(group.dependencyPosition, 2);
        assert.equal(group.dependencyProvenance.span?.start.line, 14);
    });

    it('distinguishes siblings that require weakening to a common base', () => {
        const context = CoreContext.empty()
            .extend(local(
                'base',
                kernelUniverse(because(40, 'base classifier')),
                40
            ))
            .extend(local(
                'dependent',
                kernelBound(0, because(41, 'dependent base use')),
                41
            ))
            .extend(local(
                'constant',
                kernelUniverse(because(42, 'constant classifier')),
                42
            ));
        const graph = coreContextDependencyGraph(context);
        const group = analyzeCoreContextSiblingBlock(
            graph,
            [1, 2],
            because(43, 'group after weakening')
        );

        assert.equal(group.allowed, true);
        if (!group.allowed) {
            throw new Error('Expected weakened sibling group');
        }
        assert.equal(group.relation, 'independent-after-weakening');
        assert.deepEqual(group.commonDependencies, [0]);
        assert.deepEqual(group.weakeningPositions, [2]);
        assert.equal(group.commonDependencyPrefix, 1);
    });

    it('plans discard, single use, and duplication without owners', () => {
        const graph = coreContextDependencyGraph(siblingContext());
        const operation = because(50, 'slot-use planning');

        assert.deepEqual(planCoreContextSlotUse(graph, 1, 0, operation), {
            position: 1,
            count: 0,
            intent: 'projection-weakening',
            diagonalIterations: 0,
            dependencyClosure: [0],
            dependencyPrefix: 1
        });
        assert.equal(
            planCoreContextSlotUse(graph, 1, 1, operation).intent,
            'identity'
        );
        assert.deepEqual(
            planCoreContextSlotUse(graph, 1, 3, operation),
            {
                position: 1,
                count: 3,
                intent: 'diagonal-contraction',
                diagonalIterations: 2,
                dependencyClosure: [0],
                dependencyPrefix: 1
            }
        );
    });

    it('fails closed on malformed requests and freezes evidence', () => {
        const graph = coreContextDependencyGraph(siblingContext());
        const operation = because(60, 'invalid dependency request');

        assert.throws(
            () => analyzeCoreContextSiblingBlock(
                graph,
                [1, 3],
                operation
            ),
            error =>
                error instanceof CoreContextDependencyAnalysisError &&
                error.code === 'INVALID_SIBLING_BLOCK'
        );
        assert.throws(
            () => analyzeCoreAdjacentContextExchange(
                graph,
                graph.nodes.length - 1,
                operation
            ),
            error =>
                error instanceof CoreContextDependencyAnalysisError &&
                error.code === 'INVALID_CONTEXT_POSITION'
        );
        assert.throws(
            () => planCoreContextSlotUse(graph, 1, -1, operation),
            error =>
                error instanceof CoreContextDependencyAnalysisError &&
                error.code === 'INVALID_CONTEXT_USE_COUNT'
        );

        assert.equal(Object.isFrozen(graph), true);
        assert.equal(Object.isFrozen(graph.nodes), true);
        assert.equal(Object.isFrozen(graph.nodes[1]), true);
        assert.equal(
            Object.isFrozen(graph.nodes[1].directDependencies),
            true
        );
        assert.equal(
            Object.isFrozen(
                graph.nodes[1].directDependencies[0].occurrences
            ),
            true
        );
    });
});
