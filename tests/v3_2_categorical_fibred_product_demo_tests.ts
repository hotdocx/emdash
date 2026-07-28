/**
 * Runnable FIBRED-PRODUCT-1A end-user demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalFibredProductDemo,
    runCoreCategoricalFibredProductDemo
} from '../src/v3_2';

describe(
    'TypeScript v3.2 fibred product demo',
    () => {
        it('shows pointwise fibres and shared-base arrow transport', () => {
            const result = runCoreCategoricalFibredProductDemo();
            assert.equal(
                result.candidate,
                'emdash-v3.2-fibred-product-1a'
            );
            assert.equal(
                result.familyPresentation,
                'uncurry(Product_cat_func) o Product_pair(B,C)'
            );
            assert.deepEqual(
                result.examples.map(example => example.id),
                [
                    'transparent-product-transport',
                    'componentwise-product-map'
                ]
            );
            assert.deepEqual(
                result.comparisons.map(comparison => [
                    comparison.id,
                    comparison.status,
                    comparison.steps
                ]),
                [
                    ['pointwise-fibre', 'equal', 12],
                    ['shared-base-transport', 'equal', 26]
                ]
            );
            assert.equal(
                result.comparisons[1].ruleIds.at(-1),
                'categorical.fibred-product.shared-base-arrow'
            );
            assert.deepEqual(result.outputSummary, {
                fibre: '(B x C)[x] computes to B[x] x C[x]',
                transport:
                    '(B x C)[p] computes to ' +
                    'Product_map_func(B[p],C[p])',
                sameBaseDiscriminator: true
            });
            assert.equal(result.productionLambdapiDependency, false);
        });

        it('formats a deterministic, self-contained end-user report', () => {
            const output = formatCoreCategoricalFibredProductDemo();
            assert.match(
                output,
                /^emdash-v3\.2-fibred-product-1a/u
            );
            assert.match(output, /inputs:/u);
            assert.match(
                output,
                /transparent-product-transport:/u
            );
            assert.match(
                output,
                /\(B x C\)\[x\] computes to B\[x\] x C\[x\]/u
            );
            assert.match(
                output,
                /Product_map_func\(B\[p\],C\[p\]\)/u
            );
            assert.match(
                output,
                /same literal base arrow required: true/u
            );
            assert.match(
                output,
                /production Lambdapi dependency: false/u
            );
        });
    }
);
