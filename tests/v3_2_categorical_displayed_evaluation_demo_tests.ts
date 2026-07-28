/**
 * Runnable DISPLAYED-EVAL-1A end-user demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalDisplayedEvaluationDemo,
    runCoreCategoricalDisplayedEvaluationDemo
} from '../src/v3_2';

describe('TypeScript v3.2 displayed evaluation demo', () => {
    it('executes varying, recursive, and fixed applications', () => {
        const result =
            runCoreCategoricalDisplayedEvaluationDemo();
        assert.equal(
            result.candidate,
            'emdash-v3.2-displayed-evaluation-1a'
        );
        assert.deepEqual(
            result.examples.map(example => example.id),
            ['varying', 'recursive', 'fixed']
        );
        assert.equal(result.computation.stableFibreStatus, 'equal');
        assert.equal(result.computation.pointOutputKind, 'functor');
        assert.equal(result.computation.arrowStatus, 'equal');
        assert.equal(
            result.computation.reindexedOutputKind,
            'displayed-functor'
        );
        assert.equal(
            result.computation.higherActionOutputKind,
            'functor'
        );
        assert.equal(
            result.computation.runtimeRuleIds.includes(
                'categorical.displayed-evaluation.' +
                    'stable-functor-family-fibre'
            ),
            true
        );
        assert.match(
            result.examples[1].compilation.explicitCore,
            /emdash\.categorical\.displayed-evaluation/u
        );
        assert.match(
            result.examples[2].compilation.explicitCore,
            /emdash\.categorical\.displayed-terminal/u
        );
        assert.equal(
            result.negativeDiagnostic.code,
            'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.equal(result.newLambdapiMathematicalOwnerCount, 2);
        assert.equal(result.newLambdapiRuntimeRuleCount, 2);
        assert.equal(result.intrinsicCoreOwnerCount, 0);
        assert.equal(result.stringParserDependency, false);
        assert.equal(result.productionLambdapiDependency, false);
    });

    it('formats a self-contained input/pipeline/Core report', () => {
        const output =
            formatCoreCategoricalDisplayedEvaluationDemo();
        assert.match(
            output,
            /^emdash-v3\.2-displayed-evaluation-1a/u
        );
        assert.match(output, /λ \(F : S, x : X\) :\^fd\. F x/u);
        assert.match(
            output,
            /apply\(apply\(H,e\),apply\(G,d\)\)/u
        );
        assert.match(
            output,
            /recursive typed-application tree/u
        );
        assert.match(output, /Eval_funcd ∘/u);
        assert.match(output, /New Lambdapi mathematical owners\/rules: 2\/2/u);
        assert.match(output, /Genuine dependent chains: deferred/u);
        assert.match(output, /Production Lambdapi dependency: no/u);
    });
});
