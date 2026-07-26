/**
 * USABILITY-0B runnable directed dependent demo tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreDirectedDependentDemo,
    runCoreDirectedDependentDemo
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const assertDeepFrozen = (
    value: unknown
): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

describe('USABILITY-0B directed dependent demo', () => {
    it('builds, infers, and reduces without a parser or Lambdapi runtime', () => {
        const result = runCoreDirectedDependentDemo();

        assert.equal(
            result.construction,
            'direct-typescript-scoped-builder'
        );
        assert.equal(result.productionLambdapiDependency, false);
        assert.match(result.surfaceInput, /builder\.lam/);
        assert.match(result.surfaceInput, /piapp0/);
        assert.match(result.explicitCore, /piapp0/);
        assert.match(result.inferredType, /Sigma_cat/);
        assert.match(result.reducedType, /tapp0_fapp0/);
        assert.deepEqual(
            result.trace.map(entry => entry.reduction),
            [
                'beta',
                'directed.sigma-telescope-fibre.evaluate'
            ]
        );
        assert.match(result.reducedComputation, /tapp0_fapp0/);
        assertDeepFrozen(result);
    });

    it('reports one stable wrong-family dependent-pair diagnostic', () => {
        const result = runCoreDirectedDependentDemo();

        assert.equal(result.negativeDiagnostic.code, 'TYPE_MISMATCH');
        assert.match(
            result.negativeDiagnostic.summary,
            /belongs to displayed family S/
        );
        assert.match(
            result.negativeDiagnostic.message,
            /Core type mismatch/
        );
        assert.match(
            result.negativeDiagnostic.message,
            /examples\/v3_2_directed_dependent_demo\.ts/
        );
    });

    it('renders a deterministic product-facing walkthrough', () => {
        const rendered = formatCoreDirectedDependentDemo();

        assert.match(rendered, /^emdash v3\.2 directed dependent demo/m);
        assert.match(rendered, /^Input:/m);
        assert.match(rendered, /^Explicit Core:/m);
        assert.match(rendered, /^Inferred type:/m);
        assert.match(rendered, /^Reduced type:/m);
        assert.match(rendered, /^  1\. beta$/m);
        assert.match(
            rendered,
            /^  2\. directed\.sigma-telescope-fibre\.evaluate$/m
        );
        assert.match(rendered, /^Rejected wrong-family input:/m);
        assert.match(rendered, /^Production Lambdapi dependency: no$/m);
    });

    it('keeps the demo out of the deployed browser profile', () => {
        assert.equal(
            'runCoreDirectedDependentDemo' in browser,
            false
        );
    });
});
