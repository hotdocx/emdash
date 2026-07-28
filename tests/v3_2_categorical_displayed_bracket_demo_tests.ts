/**
 * Runnable DISPLAYED-BRACKET-1A end-user demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalDisplayedBracketDemo,
    runCoreCategoricalDisplayedBracketDemo
} from '../src/v3_2';

describe('TypeScript v3.2 displayed contextual bracket demo', () => {
    it('executes five inputs plus object/arrow computation', () => {
        const result = runCoreCategoricalDisplayedBracketDemo();
        assert.equal(
            result.candidate,
            'emdash-v3.2-displayed-bracket-1a'
        );
        assert.deepEqual(
            result.examples.map(example => example.id),
            [
                'projection',
                'exchange',
                'contraction',
                'mapped-pair',
                'three-sibling'
            ]
        );
        assert.equal(
            result.projectionComputation.objectStatus,
            'equal'
        );
        assert.equal(
            result.projectionComputation.arrowStatus,
            'equal'
        );
        assert.equal(
            result.projectionComputation.runtimeRuleIds.includes(
                'categorical.fibred-structure.' +
                    'left-projection.point'
            ),
            true
        );
        assert.equal(
            result.negativeDiagnostic.code,
            'DISPLAYED_BASE_MISMATCH'
        );
        assert.match(
            result.examples[3].compilation.explicitCore,
            /generic-category-composition/u
        );
        assert.equal(
            result.examples[3].coreTypeSummary,
            'Functord(Product_catd(B,C),Product_catd(D,Q))'
        );
        assert.equal(result.newLambdapiOwnerOrRule, false);
        assert.equal(result.stringParserDependency, false);
        assert.equal(result.productionLambdapiDependency, false);
    });

    it('formats a deterministic self-contained report', () => {
        const output = formatCoreCategoricalDisplayedBracketDemo();
        assert.match(
            output,
            /^emdash-v3\.2-displayed-bracket-1a/u
        );
        assert.match(output, /λ \(b : B, c : C\) :\^fd\. b/u);
        assert.match(output, /fibrePair\(c,b\)/u);
        assert.match(
            output,
            /Core: displayed-product-pair\(right-projection,/u
        );
        assert.equal(output.includes('(owner "decode"'), false);
        assert.match(output, /Computed arrow input/u);
        assert.match(
            output,
            /Genuine dependent chains: deferred/u
        );
        assert.match(output, /New Lambdapi owner\/rule: no/u);
    });
});
