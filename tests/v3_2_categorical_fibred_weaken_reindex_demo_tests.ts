/**
 * Runnable FIBRED-WEAKEN-REINDEX-1 end-user demo contract.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    formatCoreCategoricalFibredWeakenReindexDemo,
    runCoreCategoricalFibredWeakenReindexDemo
} from '../src/v3_2';

describe('TypeScript v3.2 fibred weakening/reindexing demo', () => {
    it('executes both positive computations and the negative gate', () => {
        const result =
            runCoreCategoricalFibredWeakenReindexDemo();
        assert.equal(
            result.candidate,
            'emdash-v3.2-fibred-weaken-reindex-1'
        );
        assert.equal(result.weakening.pointStatus, 'equal');
        assert.equal(
            result.weakening.termTypeChecking,
            'runtime-object-classifier-join'
        );
        assert.deepEqual(result.weakening.classifierBridge, {
            runtime: 'not-equal',
            proofTime: 'solved',
            proofRuleId: 'stress.sigma-pi.uncurrying'
        });
        assert.equal(result.reindexing.pointStatus, 'equal');
        assert.equal(
            result.reindexing.runtimeRuleIds.includes(
                'categorical.weaken-reindex.' +
                    'pullback-hom-component'
            ),
            true
        );
        assert.equal(
            result.reindexing.abstractionBeforeAfterCoreEqual,
            true
        );
        assert.equal(
            result.negativeDiagnostic.code,
            'DISPLAYED_BASE_MISMATCH'
        );
        assert.equal(
            result.newLambdapiMathematicalOwnerOrRule,
            false
        );
        assert.equal(result.productionLambdapiDependency, false);
    });

    it('formats a deterministic self-contained report', () => {
        const output =
            formatCoreCategoricalFibredWeakenReindexDemo();
        assert.match(
            output,
            /^emdash-v3\.2-fibred-weaken-reindex-1/u
        );
        assert.match(output, /demo_s\[indexOf\(a\)\]/u);
        assert.match(
            output,
            /demo_sigma\^\*demo_FF/u
        );
        assert.match(
            output,
            /proof time: solved via stress\.sigma-pi\.uncurrying/u
        );
        assert.match(
            output,
            /New Lambdapi mathematical owner\/rule: no/u
        );
    });
});
