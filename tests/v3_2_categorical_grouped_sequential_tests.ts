/**
 * End-user FIBRED-GROUPED-SEQUENTIAL-1 context lowering.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalProgram,
    CoreCategoricalProgramError
} from '../src/v3_2';

const fixture = () => {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'tests/fixtures/categorical-grouped-sequential.ts',
        profile: 'fibred-grouped-sequential-1'
    });
    const K = emdash.category('K', { line: 1 });
    const B = emdash.displayedFamily('B', K, { line: 2 });
    const C = emdash.displayedFamily('C', K, { line: 3 });
    const D = emdash.displayedFamily('D', K, { line: 4 });
    return {
        emdash,
        K,
        B,
        C,
        D
    };
};

describe('FIBRED-GROUPED-SEQUENTIAL-1 context lowering', () => {
    it('lowers three siblings through one dependency plan', () => {
        const {
            emdash,
            K,
            B,
            C,
            D
        } = fixture();
        const context = emdash.groupedSequentialContext(
            'k',
            K,
            [
                { name: 'b', family: B },
                { name: 'c', family: C },
                { name: 'd', family: D }
            ],
            { line: 10 }
        );

        assert.equal(
            context.revision,
            'FIBRED-GROUPED-SEQUENTIAL-1-CATEGORICAL-PROGRAM-1'
        );
        assert.deepEqual(
            context.plan.graph.nodes.map(node => ({
                name: node.name,
                direct: node.directDependencies.map(
                    dependency => dependency.position
                ),
                prefix: node.dependencyPrefix
            })),
            [
                { name: 'k', direct: [], prefix: 0 },
                { name: 'b', direct: [0], prefix: 1 },
                { name: 'c', direct: [0], prefix: 1 },
                { name: 'd', direct: [0], prefix: 1 }
            ]
        );
        assert.deepEqual(
            context.sequential.extensions.map(extension => ({
                name: extension.name,
                presentation: extension.presentation,
                pullbackPast: extension.pullbackPastPositions
            })),
            [
                {
                    name: 'b',
                    presentation: 'direct-sigma-extension',
                    pullbackPast: []
                },
                {
                    name: 'c',
                    presentation: 'pullback-then-sigma-extension',
                    pullbackPast: [1]
                },
                {
                    name: 'd',
                    presentation: 'pullback-then-sigma-extension',
                    pullbackPast: [1, 2]
                }
            ]
        );
        assert.equal(context.grouped.association, 'left');
        assert.match(
            context.sequential.syntax,
            /k : K; b : B\[k\]; c : C\[k\]; d : D\[k\]/u
        );
        assert.match(
            context.grouped.syntax,
            /\(b,c,d\) : P\(B,C,D\)\[k\]/u
        );
        assert.deepEqual(context.boundary, {
            newLambdapiOwnerOrRule: false,
            totalCategoryEqualityClaimed: false,
            totalCategoryEquivalenceClaimed: false,
            arrowLevelTotalComparisonClaimed: false
        });
        assert.equal(Object.isFrozen(context), true);
        assert.equal(Object.isFrozen(context.sequential.extensions), true);
    });

    it('checks ((k,b),c) and (k,(b,c)) with common components', () => {
        const {
            emdash,
            K,
            B,
            C
        } = fixture();
        const context = emdash.groupedSequentialContext(
            'k',
            K,
            [
                { name: 'b', family: B },
                { name: 'c', family: C }
            ],
            { line: 20 }
        );
        const k = emdash.object('k0', K, { line: 21 });
        const Bk = emdash.fibre(B, k, { line: 22 });
        const Ck = emdash.fibre(C, k, { line: 23 });
        const b = emdash.object('b0', Bk, { line: 24 });
        const c = emdash.object('c0', Ck, { line: 25 });
        const objects = emdash.groupedSequentialObject(
            context,
            k,
            [b, c],
            { line: 26 }
        );

        assert.equal(
            emdash.compile(objects.sequentialObject).surfaceType.tag,
            'object'
        );
        assert.equal(
            emdash.compile(objects.groupedObject).surfaceType.tag,
            'object'
        );
        assert.deepEqual(
            objects.sequentialFibreComparisons.map(item => item.status),
            ['equal', 'equal']
        );
        assert.equal(
            objects.groupedFibreComparison.status,
            'equal'
        );
        assert.equal(objects.totalCategoryCompared, false);

        assert.match(
            emdash.compile(objects.groupedTuple).explicitCore,
            /product-pair/u
        );
        const leftAtK = emdash.apply(
            emdash.displayedProductLeftProjection(B, C),
            k,
            { expectedShape: 'fibre-functor' }
        );
        const rightAtK = emdash.apply(
            emdash.displayedProductRightProjection(B, C),
            k,
            { expectedShape: 'fibre-functor' }
        );
        assert.equal(
            emdash.compare(
                leftAtK,
                emdash.productLeftProjection(Bk, Ck),
                4_000
            ).status,
            'equal'
        );
        assert.equal(
            emdash.compare(
                rightAtK,
                emdash.productRightProjection(Bk, Ck),
                4_000
            ).status,
            'equal'
        );

        const prefix = emdash.apply(
            context.sequential.extensions[1].projectionToPrevious,
            objects.sequentialObject
        );
        assert.equal(
            emdash.compare(
                prefix,
                objects.sequentialPrefixObjects[0],
                4_000
            ).status,
            'equal'
        );
        const sequentialBase = emdash.apply(
            context.sequential.extensions[1].projectionToBase,
            objects.sequentialObject
        );
        assert.equal(
            emdash.compare(sequentialBase, k, 4_000).status,
            'equal'
        );
        const groupedBase = emdash.apply(
            emdash.sigmaProjection(context.grouped.family),
            objects.groupedObject
        );
        assert.equal(
            emdash.compare(groupedBase, k, 4_000).status,
            'equal'
        );
    });

    it('fails closed outside the profile and on malformed blocks', () => {
        const legacy = new CoreCategoricalProgram({
            profile: 'fibred-transfd-1'
        });
        const legacyK = legacy.category('legacyK');
        const legacyB = legacy.displayedFamily('legacyB', legacyK);
        assert.throws(
            () => legacy.groupedSequentialContext(
                'k',
                legacyK,
                [
                    { name: 'b', family: legacyB },
                    { name: 'c', family: legacyB }
                ]
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'UNAVAILABLE_GROUPED_SEQUENTIAL'
        );

        const {
            emdash,
            K,
            B,
            C
        } = fixture();
        assert.throws(
            () => emdash.groupedSequentialContext(
                'k',
                K,
                [{ name: 'b', family: B }]
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'INVALID_GROUPED_SEQUENTIAL_CONTEXT'
        );
        assert.throws(
            () => emdash.groupedSequentialContext(
                'k',
                K,
                [
                    { name: 'b', family: B },
                    { name: 'b', family: C }
                ]
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'INVALID_GROUPED_SEQUENTIAL_CONTEXT'
        );

        const L = emdash.category('L');
        const foreignBase = emdash.displayedFamily('foreignBase', L);
        assert.throws(
            () => emdash.groupedSequentialContext(
                'k',
                K,
                [
                    { name: 'b', family: B },
                    { name: 'x', family: foreignBase }
                ]
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'DISPLAYED_BASE_MISMATCH'
        );
    });

    it('rejects values outside the planned fibres', () => {
        const {
            emdash,
            K,
            B,
            C
        } = fixture();
        const context = emdash.groupedSequentialContext(
            'k',
            K,
            [
                { name: 'b', family: B },
                { name: 'c', family: C }
            ]
        );
        const k = emdash.object('k0', K);
        const b = emdash.object('b0', emdash.fibre(B, k));
        const wrong = emdash.object('wrong', K);
        assert.throws(
            () => emdash.groupedSequentialObject(
                context,
                k,
                [b, wrong]
            ),
            error =>
                error instanceof CoreCategoricalProgramError &&
                error.code === 'EXPECTED_CATEGORY_OBJECT'
        );
    });
});
