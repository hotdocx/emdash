/**
 * Focused FIBRED-CONTEXT-0B categorical context-plan evidence.
 */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    CoreCategoricalContextPlanningError,
    CoreCategoricalIndexedObjectClassifier,
    coreCategoricalClosedContextClassifier,
    coreCategoricalContextSlotReference,
    coreCategoricalDisplayedContextClassifier,
    coreCategoricalIndexedObjectContextClassifier,
    kernelFree,
    planCoreCategoricalContextDependencies,
    provenance,
    sourceSpan
} from '../src/v3_2';

const fixture =
    'tests/fixtures/v3_2_categorical_context_dependencies.surface.ts';
const at = (line: number) =>
    sourceSpan(fixture, line, 1, line, 2);
const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));
const free = (name: string, line: number) =>
    kernelFree(name, because(line, `${name} expression`));

const siblingPlan = () => {
    const K = free('K', 1);
    const B = free('B', 2);
    const C = free('C', 3);
    const D = free('D', 4);
    const aClassifier = coreCategoricalClosedContextClassifier(
        { tag: 'object', category: K },
        because(10, 'a classifier')
    );
    const bClassifier = coreCategoricalDisplayedContextClassifier(
        K,
        B,
        [
            coreCategoricalContextSlotReference(
                0,
                because(11, 'a in B(a)')
            )
        ],
        { tag: 'object', category: free('B_fibre', 11) },
        because(11, 'B(a) classifier')
    );
    const cClassifier = coreCategoricalDisplayedContextClassifier(
        K,
        C,
        [
            coreCategoricalContextSlotReference(
                1,
                because(12, 'a in C(a)')
            )
        ],
        { tag: 'object', category: free('C_fibre', 12) },
        because(12, 'C(a) classifier')
    );
    const dClassifier = coreCategoricalDisplayedContextClassifier(
        K,
        D,
        [
            coreCategoricalContextSlotReference(
                0,
                because(14, 'c in D(b,c)')
            ),
            coreCategoricalContextSlotReference(
                1,
                because(15, 'b in D(b,c)')
            )
        ],
        { tag: 'object', category: free('D_fibre', 14) },
        because(14, 'D(b,c) classifier')
    );
    const input = {
        slots: [
            {
                name: 'a',
                classifier: aClassifier,
                provenance: because(10, 'a slot')
            },
            {
                name: 'b',
                classifier: bClassifier,
                provenance: because(11, 'b slot')
            },
            {
                name: 'c',
                classifier: cClassifier,
                provenance: because(12, 'c slot')
            },
            {
                name: 'd',
                classifier: dClassifier,
                provenance: because(14, 'd slot')
            }
        ],
        siblingGroups: [{
            positions: [1, 2],
            provenance: because(20, 'group b and c')
        }]
    } as const;
    return {
        K,
        B,
        C,
        D,
        input,
        plan: planCoreCategoricalContextDependencies(input)
    };
};

describe('FIBRED-CONTEXT-0B categorical dependency plans', () => {
    it('adapts locally nameless categorical classifiers to the generic graph',
        () => {
            const { plan } = siblingPlan();

            assert.equal(plan.revision, 'FIBRED-CONTEXT-0B');
            assert.deepEqual(
                plan.graph.nodes.map(node => ({
                    name: node.name,
                    direct: node.directDependencies.map(
                        dependency => dependency.position
                    ),
                    closure: node.dependencyClosure,
                    prefix: node.dependencyPrefix
                })),
                [
                    { name: 'a', direct: [], closure: [], prefix: 0 },
                    {
                        name: 'b',
                        direct: [0],
                        closure: [0],
                        prefix: 1
                    },
                    {
                        name: 'c',
                        direct: [0],
                        closure: [0],
                        prefix: 1
                    },
                    {
                        name: 'd',
                        direct: [1, 2],
                        closure: [0, 1, 2],
                        prefix: 3
                    }
                ]
            );
            assert.deepEqual(
                plan.dependencyEdges.map(edge => [
                    edge.dependencyPosition,
                    edge.dependentPosition
                ]),
                [[0, 1], [0, 2], [1, 3], [2, 3]]
            );
            assert.deepEqual(plan.dependencyChains, [{
                kind: 'dependent-chain',
                dependentPosition: 3,
                dependencyPositions: [0, 1, 2]
            }]);
        });

    it('records sequential pullback and grouped Product_catd intent', () => {
        const { B, C, plan } = siblingPlan();

        assert.deepEqual(
            plan.sequential.map(intent => ({
                kind: intent.kind,
                position: intent.position,
                prefix: intent.dependencyPrefix,
                pullback: intent.kind === 'displayed-sigma-extension'
                    ? intent.pullbackPastPositions
                    : []
            })),
            [
                {
                    kind: 'base-context-slot',
                    position: 0,
                    prefix: 0,
                    pullback: []
                },
                {
                    kind: 'displayed-sigma-extension',
                    position: 1,
                    prefix: 1,
                    pullback: []
                },
                {
                    kind: 'displayed-sigma-extension',
                    position: 2,
                    prefix: 1,
                    pullback: [1]
                },
                {
                    kind: 'displayed-sigma-extension',
                    position: 3,
                    prefix: 3,
                    pullback: []
                }
            ]
        );
        assert.equal(
            plan.sequential[2].kind === 'displayed-sigma-extension'
                ? plan.sequential[2].presentation
                : undefined,
            'pullback-then-sigma-extension'
        );

        assert.equal(plan.groupedProducts.length, 1);
        const grouped = plan.groupedProducts[0];
        assert.equal(
            grouped.relation,
            'shared-minimal-base-siblings'
        );
        assert.deepEqual(grouped.positions, [1, 2]);
        assert.deepEqual(grouped.commonDependencies, [0]);
        assert.deepEqual(grouped.weakeningPositions, []);
        assert.deepEqual(grouped.sequentialPullbackPositions, [2]);
        assert.deepEqual(
            grouped.factors.map(factor => [
                factor.position,
                factor.name,
                factor.family
            ]),
            [[1, 'b', B], [2, 'c', C]]
        );
        assert.equal(grouped.candidateSemanticName, 'Product_catd');
        assert.deepEqual(grouped.structuralIntents, [
            'projection',
            'pairing',
            'exchange',
            'diagonal'
        ]);
        assert.equal(grouped.selectedCoreOwner, null);
        assert.equal(
            grouped.baseArrowComputation,
            'componentwise-product-map-required'
        );
        assert.equal(grouped.totalCategoryPullbackAssumed, false);
        assert.deepEqual(plan.boundary, {
            emittedCoreOwnerCount: 0,
            activeKernelChanged: false,
            existingSurfaceBehaviorChanged: false,
            productOwnerSelected: false,
            genericTotalPullbackAssumed: false
        });
    });

    it('rejects grouping across a genuine dependency occurrence', () => {
        const { input } = siblingPlan();
        assert.throws(
            () => planCoreCategoricalContextDependencies({
                ...input,
                siblingGroups: [{
                    positions: [2, 3],
                    provenance: because(30, 'invalid c d group')
                }]
            }),
            error =>
                error instanceof CoreCategoricalContextPlanningError &&
                error.code === 'DEPENDENT_SIBLING_GROUP' &&
                error.provenance.span?.start.line === 14 &&
                /slot 3 depends on grouped slot 2/u.test(error.message)
        );
    });

    it('records weakening for different minimal dependency bases',
        () => {
            const K = free('K_weaken', 40);
            const B = coreCategoricalDisplayedContextClassifier(
                K,
                free('B_weaken', 41),
                [
                    coreCategoricalContextSlotReference(
                        0,
                        because(41, 'base in B')
                    )
                ],
                { tag: 'object', category: free('B_weaken_fibre', 41) },
                because(41, 'B classifier')
            );
            const constant = coreCategoricalDisplayedContextClassifier(
                K,
                free('Constant_family', 42),
                [],
                {
                    tag: 'object',
                    category: free('Constant_fibre', 42)
                },
                because(42, 'constant classifier')
            );
            const plan = planCoreCategoricalContextDependencies({
                slots: [
                    {
                        name: 'a',
                        classifier:
                            coreCategoricalClosedContextClassifier(
                                { tag: 'object', category: K },
                                because(40, 'base classifier')
                            ),
                        provenance: because(40, 'base slot')
                    },
                    {
                        name: 'b',
                        classifier: B,
                        provenance: because(41, 'B slot')
                    },
                    {
                        name: 'constant',
                        classifier: constant,
                        provenance: because(42, 'constant slot')
                    }
                ],
                siblingGroups: [{
                    positions: [1, 2],
                    provenance: because(43, 'weakened group')
                }]
            });

            assert.deepEqual(
                plan.sequential[2].kind ===
                    'displayed-sigma-extension'
                    ? plan.sequential[2].pullbackPastPositions
                    : undefined,
                [0, 1]
            );
            assert.deepEqual(
                plan.groupedProducts[0].weakeningPositions,
                [2]
            );
            assert.equal(
                plan.groupedProducts[0].relation,
                'independent-after-weakening'
            );
        });

    it('adapts the current one-index stored classifier without new flags',
        () => {
            const K = free('K_indexed', 50);
            const E = free('E_indexed', 51);
            const indexed: CoreCategoricalIndexedObjectClassifier = {
                tag: 'indexed-object',
                baseCategory: K,
                family: E,
                index: 0
            };
            const plan = planCoreCategoricalContextDependencies({
                slots: [
                    {
                        name: 'k',
                        classifier:
                            coreCategoricalClosedContextClassifier(
                                { tag: 'object', category: K },
                                because(50, 'k classifier')
                            ),
                        provenance: because(50, 'k slot')
                    },
                    {
                        name: 'e',
                        classifier:
                            coreCategoricalIndexedObjectContextClassifier(
                                indexed,
                                because(51, 'indexed E[k] classifier')
                            ),
                        provenance: because(51, 'e slot')
                    }
                ]
            });

            assert.deepEqual(
                plan.graph.nodes[1].directDependencies.map(
                    dependency => dependency.position
                ),
                [0]
            );
            assert.equal(
                plan.context.slots[1].classifier.tag,
                'displayed-family-application'
            );
        });

    it('fails closed on escaping references and incompatible groups', () => {
        const K = free('K_fail', 60);
        const bad = coreCategoricalDisplayedContextClassifier(
            K,
            free('Bad_family', 61),
            [
                coreCategoricalContextSlotReference(
                    1,
                    because(61, 'escaping classifier reference')
                )
            ],
            { tag: 'object', category: free('Bad_fibre', 61) },
            because(61, 'bad classifier')
        );
        assert.throws(
            () => planCoreCategoricalContextDependencies({
                slots: [{
                    name: 'bad',
                    classifier: bad,
                    provenance: because(61, 'bad slot')
                }]
            }),
            error =>
                error instanceof CoreCategoricalContextPlanningError &&
                error.code === 'INVALID_CONTEXTUAL_SLOT_REFERENCE' &&
                error.provenance.span?.start.line === 61
        );

        const L = free('L_fail', 62);
        const left = coreCategoricalDisplayedContextClassifier(
            K,
            free('Left_family', 63),
            [],
            { tag: 'object', category: free('Left_fibre', 63) },
            because(63, 'left classifier')
        );
        const right = coreCategoricalDisplayedContextClassifier(
            L,
            free('Right_family', 64),
            [],
            { tag: 'object', category: free('Right_fibre', 64) },
            because(64, 'right classifier')
        );
        assert.throws(
            () => planCoreCategoricalContextDependencies({
                slots: [
                    {
                        name: 'left',
                        classifier: left,
                        provenance: because(63, 'left slot')
                    },
                    {
                        name: 'right',
                        classifier: right,
                        provenance: because(64, 'right slot')
                    }
                ],
                siblingGroups: [{
                    positions: [0, 1],
                    provenance: because(65, 'base mismatch group')
                }]
            }),
            error =>
                error instanceof CoreCategoricalContextPlanningError &&
                error.code === 'DISPLAYED_PRODUCT_BASE_MISMATCH'
        );
    });

    it('deep-freezes all categorical plan records and arrays', () => {
        const { plan } = siblingPlan();
        assert.equal(Object.isFrozen(plan), true);
        assert.equal(Object.isFrozen(plan.context), true);
        assert.equal(Object.isFrozen(plan.context.slots), true);
        assert.equal(Object.isFrozen(plan.graph), true);
        assert.equal(Object.isFrozen(plan.dependencyEdges), true);
        assert.equal(Object.isFrozen(plan.sequential), true);
        assert.equal(Object.isFrozen(plan.groupedProducts), true);
        assert.equal(Object.isFrozen(plan.groupedProducts[0]), true);
        assert.equal(
            Object.isFrozen(plan.groupedProducts[0].factors),
            true
        );
    });
});
