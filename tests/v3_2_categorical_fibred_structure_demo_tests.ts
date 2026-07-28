/**
 * Runnable FIBRED-STRUCTURE-1A end-user demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalFibredStructureDemo,
    runCoreCategoricalFibredStructureDemo
} from '../src/v3_2';

describe(
    'TypeScript v3.2 fibred structure demo',
    () => {
        it('shows the structural and canonical-reindex closure', () => {
            const result = runCoreCategoricalFibredStructureDemo();
            assert.equal(
                result.candidate,
                'emdash-v3.2-fibred-structure-1a'
            );
            assert.deepEqual(
                result.examples.map(example => example.id),
                [
                    'left-projection-point',
                    'displayed-pairing-point',
                    'derived-swap-point',
                    'derived-diagonal-point',
                    'left-projection-full-action'
                ]
            );
            assert.deepEqual(
                result.comparisons.map(entry => [
                    entry.id,
                    entry.status
                ]),
                [
                    ['left-projection-computes', 'equal'],
                    ['pairing-computes', 'equal'],
                    ['swap-computes', 'equal'],
                    ['diagonal-computes', 'equal'],
                    ['full-capped-coherence', 'equal'],
                    ['canonical-grouped-reindex', 'equal']
                ]
            );
            assert.equal(
                result.comparisons[0].ruleIds.includes(
                    'categorical.fibred-structure.' +
                    'left-projection.point'
                ),
                true
            );
            assert.equal(
                result.outputSummary
                    .rawKernelReindexStillNonConvertible,
                true
            );
            assert.equal(result.productionLambdapiDependency, false);
        });

        it('formats a deterministic self-contained report', () => {
            const output =
                formatCoreCategoricalFibredStructureDemo();
            assert.match(
                output,
                /^emdash-v3\.2-fibred-structure-1a/u
            );
            assert.match(output, /projL_d\(B,C\)\[x\]/u);
            assert.match(output, /pair_d\(FF,GG\)\[x\]/u);
            assert.match(output, /swap_d\(B,C\)\[x\]/u);
            assert.match(output, /diag_d\(B\)\[x\]/u);
            assert.match(
                output,
                /reindex\(P\(B,C\),F\) emits/u
            );
            assert.match(
                output,
                /raw kernel pullback\/product conversion: false/u
            );
            assert.match(
                output,
                /production Lambdapi dependency: false/u
            );
        });
    }
);
