/**
 * Runnable FIBRED-TRANSFD-1 end-user demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalFibredTransfdDemo,
    runCoreCategoricalFibredTransfdDemo
} from '../src/v3_2';

describe('TypeScript v3.2 fibred displayed-transfor demo', () => {
    it('executes eta, components, higher cell, and classifier evidence', () => {
        const result = runCoreCategoricalFibredTransfdDemo();
        assert.equal(
            result.candidate,
            'emdash-v3.2-fibred-transfd-1'
        );
        assert.deepEqual(
            result.examples.map(example => example.id),
            [
                'coherent-eta',
                'fibre-component',
                'point-component',
                'higher-cell',
                'composite-component'
            ]
        );
        assert.deepEqual(result.coherentAbstraction, {
            input: 'λ k :^nd demo_K. demo_eta[k]',
            output: 'demo_eta',
            callbackCount: 1,
            status: 'equal'
        });
        assert.deepEqual(
            [
                result.classifierCompatibility
                    .directOrdinaryRuntime,
                result.classifierCompatibility
                    .directOrdinaryProofTime,
                result.classifierCompatibility
                    .directOrdinaryObjectRuntime,
                result.classifierCompatibility
                    .directSigmaPiRuntime
            ],
            ['not-equal', 'solved', 'equal', 'equal']
        );
        assert.deepEqual(
            result.verticalComponentRuntimeRuleIds,
            [
                'categorical.transfd.component-composition.direct',
                'categorical.transfd.component-composition.ordinary'
            ]
        );
        assert.equal(
            result.newLambdapiMathematicalOwnerOrRule,
            false
        );
        assert.equal(result.productionLambdapiDependency, false);
    });

    it('formats a deterministic self-contained report', () => {
        const output = formatCoreCategoricalFibredTransfdDemo();
        assert.match(
            output,
            /^emdash-v3\.2-fibred-transfd-1/u
        );
        assert.match(output, /λ k :\^nd demo_K\. demo_eta\[k\]/u);
        assert.match(output, /demo_eta\[demo_p\]\[demo_u\]/u);
        assert.match(output, /direct\/ordinary runtime: not-equal/u);
        assert.match(output, /direct\/ordinary proof-time: solved/u);
        assert.match(
            output,
            /New Lambdapi mathematical owner\/rule: no/u
        );
    });
});
