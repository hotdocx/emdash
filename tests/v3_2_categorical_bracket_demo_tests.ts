/**
 * Runnable USABILITY-1D categorical bracket demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalBracketDemo,
    runCoreCategoricalBracketDemo
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

describe('TypeScript v3.2 categorical bracket demo', () => {
    it('checks the representative pointwise, diagonal, and exchange inputs', () => {
        const result = runCoreCategoricalBracketDemo();
        assert.equal(
            result.construction,
            'direct-typescript-categorical-program'
        );
        assert.deepEqual(
            result.examples.map(entry => entry.name),
            ['pointwise-application', 'diagonal', 'exchange']
        );
        assert.deepEqual(
            result.examples.map(entry =>
                entry.structuralPrerequisites
            ),
            [
                [
                    'identity-functor',
                    'functor-composition',
                    'product-category',
                    'product-pair',
                    'evaluation-functor'
                ],
                ['diagonal-functor-abstraction'],
                ['exchange-functor-abstraction']
            ]
        );
        for (const entry of result.examples) {
            assert.equal(
                entry.explicitCore.includes('emdash3_2'),
                false
            );
            assert.equal(
                entry.explicitCore.includes('_func'),
                false
            );
            assert.equal(
                entry.inferredType.includes('(owner "decode"'),
                true
            );
        }
        assert.equal(result.stringParserDependency, false);
        assert.equal(result.productionLambdapiDependency, false);
        assertDeepFrozen(result);
    });

    it('reports the wrong-category negative at the supplied source site', () => {
        const diagnostic =
            runCoreCategoricalBracketDemo().negativeDiagnostic;
        assert.equal(
            diagnostic.code,
            'CLASSIFIER_ARGUMENT_MISMATCH'
        );
        assert.equal(diagnostic.phase, 'surface');
        assert.equal(
            diagnostic.location,
            'src/v3_2/categorical_bracket_demo.ts:157:9'
        );
        assert.match(
            diagnostic.message,
            /neither an object nor an arrow/
        );
    });

    it('formats a deterministic end-user report', () => {
        const output = formatCoreCategoricalBracketDemo();
        assert.match(
            output,
            /^emdash v3\.2 categorical bracket demo/
        );
        assert.match(
            output,
            /λ x :\^f demo_A\. \(demo_H x\) \(demo_K x\)/
        );
        assert.match(
            output,
            /emdash\.categorical\.evaluation-functor/
        );
        assert.match(
            output,
            /CLASSIFIER_ARGUMENT_MISMATCH/
        );
        assert.match(output, /String parser dependency: no/);
        assert.match(output, /Production Lambdapi dependency: no$/);
    });
});
