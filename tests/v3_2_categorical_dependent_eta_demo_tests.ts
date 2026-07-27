/**
 * Runnable USABILITY-2A1 dependent categorical eta demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalDependentEtaDemo,
    runCoreCategoricalDependentEtaDemo
} from '../src/v3_2';

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe('TypeScript v3.2 dependent categorical eta demo', () => {
    it('checks and exposes the indexed section-eta witness', () => {
        const result = runCoreCategoricalDependentEtaDemo();
        assert.equal(
            result.surfaceInput,
            'λ k :^n demo_K. demo_s[k]'
        );
        assert.deepEqual(result.contextualClassifier, {
            tag: 'indexed-object',
            baseCategory: '(free "demo_K")',
            family: '(free "demo_E")',
            index: 0
        });
        assert.equal(result.explicitCore, '(free "demo_s")');
        assert.equal(result.inferredType, result.expectedType);
        assert.deepEqual(
            result.dependentPrerequisites,
            ['section-object-evaluation']
        );
        assert.equal(result.generalDependentBracketAvailable, false);
        assert.equal(result.stringParserDependency, false);
        assert.equal(result.productionLambdapiDependency, false);
        assertDeepFrozen(result);
    });

    it('reports the untransferred section-arrow boundary', () => {
        const diagnostic =
            runCoreCategoricalDependentEtaDemo().negativeDiagnostic;
        assert.equal(
            diagnostic.code,
            'UNAVAILABLE_DEPENDENT_ACTION'
        );
        assert.equal(diagnostic.phase, 'surface');
        assert.equal(
            diagnostic.location,
            'src/v3_2/categorical_dependent_eta_demo.ts:82:9'
        );
        assert.match(diagnostic.message, /piapp1_fapp0 transfer/u);
    });

    it('formats a deterministic end-user report', () => {
        const output = formatCoreCategoricalDependentEtaDemo();
        assert.match(
            output,
            /^emdash v3\.2 dependent categorical eta demo/u
        );
        assert.match(
            output,
            /λ k :\^n demo_K\. demo_s\[k\]/u
        );
        assert.match(
            output,
            /Explicit Core: \(free "demo_s"\)/u
        );
        assert.match(
            output,
            /section-object-evaluation/u
        );
        assert.match(output, /piapp1_fapp0 transfer/u);
        assert.match(
            output,
            /General dependent bracket abstraction: not yet/u
        );
        assert.match(output, /String parser dependency: no/u);
        assert.match(output, /Production Lambdapi dependency: no$/u);
    });
});
