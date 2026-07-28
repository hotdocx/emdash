/**
 * Runnable FIBRED-BINDER-1 end-user demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalFibredBinderDemo,
    runCoreCategoricalFibredBinderDemo
} from '../src/v3_2';

describe('TypeScript v3.2 fibred binder demo', () => {
    it('executes identity, eta, composition, and classifier evidence', () => {
        const result = runCoreCategoricalFibredBinderDemo();
        assert.equal(
            result.candidate,
            'emdash-v3.2-fibred-binder-1'
        );
        assert.deepEqual(
            result.examples.map(example => example.id),
            ['identity', 'eta', 'composition']
        );
        assert.equal(result.compositionPoint.status, 'equal');
        assert.equal(
            result.compositionPoint.runtimeRuleIds.includes(
                'categorical.displayed-functor-composition.point'
            ),
            true
        );
        assert.equal(
            result.compositionPoint.runtimeRuleIds.includes(
                'categorical.functor-composition.object'
            ),
            true
        );
        assert.deepEqual(
            [
                result.classifierCompatibility.proofTime,
                result.classifierCompatibility.runtime
            ],
            ['solved', 'not-equal']
        );
        assert.equal(
            result.newLambdapiMathematicalOwnerOrRule,
            false
        );
        assert.equal(result.productionLambdapiDependency, false);
    });

    it('formats a deterministic self-contained report', () => {
        const output = formatCoreCategoricalFibredBinderDemo();
        assert.match(
            output,
            /^emdash-v3\.2-fibred-binder-1/u
        );
        assert.match(output, /λ a :\^fd demo_E\. a/u);
        assert.match(
            output,
            /demo_GG\[demo_FF\[a\]\]/u
        );
        assert.match(
            output,
            /proof-time comparison: solved/u
        );
        assert.match(
            output,
            /runtime conversion: not-equal/u
        );
        assert.match(
            output,
            /New Lambdapi mathematical owner\/rule: no/u
        );
    });
});
