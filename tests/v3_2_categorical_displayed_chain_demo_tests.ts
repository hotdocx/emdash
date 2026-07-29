/**
 * Runnable DISPLAYED-CHAIN-1A end-user demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalDisplayedChainDemo,
    runCoreCategoricalDisplayedChainDemo
} from '../src/v3_2';

describe('TypeScript v3.2 displayed dependent-chain demo', () => {
    it('executes outer, inner, recursive, arrow, and reindexing evidence',
        () => {
            const result =
                runCoreCategoricalDisplayedChainDemo();
            assert.equal(
                result.candidate,
                'emdash-v3.2-displayed-chain-1a'
            );
            assert.deepEqual(
                result.examples.map(example => example.id),
                ['outer', 'inner', 'recursive']
            );
            assert.equal(
                result.computation.outerObjectStatus,
                'equal'
            );
            assert.equal(
                result.computation.innerObjectStatus,
                'equal'
            );
            assert.equal(
                result.computation.recursiveObjectStatus,
                'equal'
            );
            assert.equal(
                result.computation.arrowIndependenceStatus,
                'equal'
            );
            assert.equal(
                result.computation
                    .internalizedArrowNonCollapseStatus,
                'not-equal'
            );
            assert.equal(
                result.computation.reindexedOutputKind,
                'displayed-functor'
            );
            assert.equal(
                result.computation.runtimeRuleIds.includes(
                    'categorical.displayed-chain.' +
                        'section-pullback-direct-object'
                ),
                true
            );
            assert.equal(
                result.computation.runtimeRuleIds.includes(
                    'categorical.displayed-chain.' +
                        'section-pullback-direct-arrow'
                ),
                true
            );
            assert.equal(
                result.negativeDiagnostic.code,
                'DISPLAYED_BASE_MISMATCH'
            );
            assert.equal(result.newLambdapiMathematicalOwnerCount, 1);
            assert.equal(result.newLambdapiRuntimeRuleCount, 6);
            assert.equal(result.intrinsicCoreOwnerCount, 0);
            assert.equal(result.stringParserDependency, false);
            assert.equal(result.productionLambdapiDependency, false);
        }
    );

    it('formats a self-contained telescope, pipeline, and output report',
        () => {
            const output =
                formatCoreCategoricalDisplayedChainDemo();
            assert.match(
                output,
                /^emdash-v3\.2-displayed-chain-1a/u
            );
            assert.match(
                output,
                /k : K; a : A\[k\]; b : B\[\(k,a\)\]/u
            );
            assert.match(
                output,
                /displayedDependentContextLambda/u
            );
            assert.match(
                output,
                /recursive contextual occurrence compiler/u
            );
            assert.match(
                output,
                /section_pullback\(sigma_functord_sec\(id A\)\)/u
            );
            assert.match(
                output,
                /Internalized arrow does not collapse: not-equal/u
            );
            assert.match(
                output,
                /New Lambdapi mathematical owners\/rules: 1\/6/u
            );
            assert.match(
                output,
                /Production Lambdapi dependency: no/u
            );
        }
    );
});
