/**
 * Runnable FIBRED-DEPENDENT-TARGET-1 demo evidence.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalFibredDependentTargetDemo,
    runCoreCategoricalFibredDependentTargetDemo
} from '../src/v3_2';

describe('FIBRED-DEPENDENT-TARGET-1 demo', () => {
    it('reports the computed Pi fibre and total-context eta', () => {
        const result =
            runCoreCategoricalFibredDependentTargetDemo();
        assert.equal(
            result.candidate,
            'emdash-v3.2-fibred-dependent-target-1'
        );
        assert.equal(result.fibre.runtimeStatus, 'equal');
        assert.equal(result.fibre.proofStatus, 'solved');
        assert.equal(
            result.fibre.runtimeRuleIds.includes(
                'categorical.dependent-target.' +
                    'section-functor-object'
            ),
            true
        );
        assert.equal(
            result.eta.compilation.explicitCore,
            '(free "demo_target_section")'
        );
        assert.equal(result.eta.callbackCount, 1);
        assert.equal(
            result.negativeDiagnostic.code,
            'EXPECTED_FUNCTOR'
        );
        assert.equal(
            result.newLambdapiMathematicalOwnerOrRule,
            false
        );
        assert.equal(result.stringParserDependency, false);

        const formatted =
            formatCoreCategoricalFibredDependentTargetDemo(result);
        assert.match(
            formatted,
            /^emdash-v3\.2-fibred-dependent-target-1/u
        );
        assert.match(
            formatted,
            /demo_B\[\(demo_k,demo_M\)\][\s\S]*Pi_cat/u
        );
        assert.match(
            formatted,
            /New Lambdapi mathematical owner\/rule: no/u
        );
    });
});
