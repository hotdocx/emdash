/**
 * Runnable USABILITY-DEPENDENT-1A section-composition demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalDependentCompositionDemo,
    runCoreCategoricalDependentCompositionDemo
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

describe(
    'TypeScript v3.2 dependent section-composition demo',
    () => {
        it('checks and exposes the non-eta displayed witness', () => {
            const result =
                runCoreCategoricalDependentCompositionDemo();
            assert.equal(
                result.surfaceInput,
                'λ k :^n demo_K. demo_FF[k](demo_s[k])'
            );
            assert.equal(
                result.contextualBody,
                'indexed-fibre-functor.object(index=0)'
            );
            assert.equal(
                result.lowering,
                'generic comp_fapp0 at Catd_cat demo_K'
            );
            assert.match(
                result.explicitCore,
                /generic-category-composition/u
            );
            assert.match(
                result.explicitCore,
                /displayed-category-category/u
            );
            assert.match(
                result.explicitCore,
                /constant-displayed-family/u
            );
            assert.deepEqual(
                result.dependentPrerequisites,
                [
                    'displayed-functor-fibre',
                    'section-object-evaluation',
                    'generic-category-composition',
                    'terminal-category',
                    'displayed-hom-classifier-reduction',
                    'section-object-classifier-reduction'
                ]
            );
            assert.equal(
                result.newLambdapiMathematicalOwnerOrRule,
                false
            );
            assert.equal(
                result.generalDependentBracketAvailable,
                false
            );
            assert.equal(result.stringParserDependency, false);
            assert.equal(
                result.productionLambdapiDependency,
                false
            );
            assertDeepFrozen(result);
        });

        it('reports a wrong displayed source family precisely', () => {
            const diagnostic =
                runCoreCategoricalDependentCompositionDemo()
                    .negativeDiagnostic;
            assert.equal(
                diagnostic.code,
                'CLASSIFIER_ARGUMENT_MISMATCH'
            );
            assert.equal(diagnostic.phase, 'surface');
            assert.equal(
                diagnostic.location,
                'src/v3_2/' +
                'categorical_dependent_composition_demo.ts:91:9'
            );
            assert.match(diagnostic.message, /source family/u);
        });

        it('formats a deterministic end-user report', () => {
            const output =
                formatCoreCategoricalDependentCompositionDemo();
            assert.match(
                output,
                /^emdash v3\.2 dependent section-composition demo/u
            );
            assert.match(
                output,
                /λ k :\^n demo_K\. demo_FF\[k\]\(demo_s\[k\]\)/u
            );
            assert.match(
                output,
                /generic comp_fapp0 at Catd_cat demo_K/u
            );
            assert.match(
                output,
                /generic-category-composition/u
            );
            assert.match(
                output,
                /Pointwise meaning: Fibre_func/u
            );
            assert.match(
                output,
                /CLASSIFIER_ARGUMENT_MISMATCH/u
            );
            assert.match(
                output,
                /New Lambdapi mathematical owner\/rule: no/u
            );
            assert.match(
                output,
                /General dependent bracket abstraction: not yet/u
            );
            assert.match(output, /String parser dependency: no/u);
            assert.match(
                output,
                /Production Lambdapi dependency: no$/u
            );
        });
    }
);
