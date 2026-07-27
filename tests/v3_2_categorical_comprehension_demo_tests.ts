/**
 * Runnable FIBRED-COMPREHENSION-1A end-user demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalComprehensionDemo,
    runCoreCategoricalComprehensionDemo
} from '../src/v3_2';

describe(
    'TypeScript v3.2 fibred comprehension demo',
    () => {
        it('shows dependent objects, arrows, and a further family chain', () => {
            const result = runCoreCategoricalComprehensionDemo();
            assert.equal(
                result.candidate,
                'emdash-v3.2-fibred-comprehension-1a'
            );
            assert.deepEqual(
                result.examples.map(example => example.id),
                [
                    'dependent-pair',
                    'canonical-sigma-arrow',
                    'totalized-object-action',
                    'totalized-arrow-action',
                    'further-dependent-substitution'
                ]
            );
            assert.deepEqual(
                result.reductions.map(reduction => reduction.ruleId),
                [
                    'categorical.sigma-pullback-total.object',
                    'categorical.sigma-pullback-total.arrow'
                ]
            );
            assert.deepEqual(result.outputSummary, {
                objectAction: '(a,u) maps to (F[a],u)',
                arrowAction: '(p,alpha) maps to (F[p],alpha)',
                dependentChain:
                    'Q over Sigma(D) reindexes over Sigma(F*D)'
            });
            assert.equal(result.productionLambdapiDependency, false);
        });

        it('formats a deterministic, self-contained end-user report', () => {
            const output = formatCoreCategoricalComprehensionDemo();
            assert.match(
                output,
                /^emdash-v3\.2-fibred-comprehension-1a/u
            );
            assert.match(output, /inputs:/u);
            assert.match(output, /dependent-pair:/u);
            assert.match(
                output,
                /\(a,u\) maps to \(F\[a\],u\)/u
            );
            assert.match(
                output,
                /\(p,alpha\) maps to \(F\[p\],alpha\)/u
            );
            assert.match(
                output,
                /production Lambdapi dependency: false/u
            );
        });
    }
);
