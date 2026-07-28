/**
 * Runnable FIBRED-GROUPED-SEQUENTIAL-1 demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalGroupedSequentialDemo,
    runCoreCategoricalGroupedSequentialDemo
} from '../src/v3_2';

describe('TypeScript v3.2 grouped/sequential context demo', () => {
    it('executes both presentations through one dependency plan', () => {
        const result =
            runCoreCategoricalGroupedSequentialDemo();
        assert.equal(
            result.candidate,
            'emdash-v3.2-fibred-grouped-sequential-1'
        );
        assert.deepEqual(
            result.presentations.dependencyEdges,
            [[0, 1], [0, 2]]
        );
        assert.deepEqual(
            result.presentations.sequentialKinds,
            [
                'direct-sigma-extension',
                'pullback-then-sigma-extension'
            ]
        );
        assert.equal(
            result.presentations.groupedRelation,
            'shared-minimal-base-siblings'
        );
        assert.equal(
            result.comparisons.every(item => item.status === 'equal'),
            true
        );
        assert.equal(
            result.dependencyEdgeDiagnostic.code,
            'DEPENDENT_SIBLING_GROUP'
        );
        assert.equal(result.totalCategoryCompared, false);
        assert.equal(
            result.newLambdapiMathematicalOwnerOrRule,
            false
        );
        assert.equal(result.productionLambdapiDependency, false);
    });

    it('formats a deterministic self-contained report', () => {
        const output =
            formatCoreCategoricalGroupedSequentialDemo();
        assert.match(
            output,
            /^emdash-v3\.2-fibred-grouped-sequential-1/u
        );
        assert.match(
            output,
            /sequential: k : demo_K; b : demo_B\[k\]; c : demo_C\[k\]/u
        );
        assert.match(
            output,
            /grouped: k : demo_K; \(b,c\) : P\(demo_B,demo_C\)\[k\]/u
        );
        assert.match(output, /DEPENDENT_SIBLING_GROUP/u);
        assert.match(
            output,
            /total-category equality\/equivalence compared: no/u
        );
        assert.match(
            output,
            /new Lambdapi mathematical owner\/rule: no/u
        );
    });
});
