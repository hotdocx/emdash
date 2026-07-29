/**
 * Focused PRODUCT-DEMO-1B external-review report tests.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    assembleCoreProductReviewDemo,
    CORE_PRODUCT_REVIEW_DEMO_PANEL_IDS,
    CoreProductReviewDemoComponents,
    CoreProductReviewDemoError,
    CoreProductReviewDemoResult,
    formatCoreProductReviewDemo,
    runCoreProductReviewDemo
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

let cachedResult: CoreProductReviewDemoResult | undefined;

const result = (): CoreProductReviewDemoResult => {
    cachedResult ??= runCoreProductReviewDemo();
    return cachedResult;
};

describe('PRODUCT-DEMO-1B external-review report', () => {
    it('runs exactly the approved three existing structured panels', () => {
        const report = result();
        assert.deepEqual(
            report.panelIds,
            CORE_PRODUCT_REVIEW_DEMO_PANEL_IDS
        );
        assert.deepEqual(report.panelIds, [
            'outer-dependent-lf',
            'ordinary-functorial-binding',
            'displayed-dependent-binding'
        ]);
        assert.equal(
            report.components.outerDependentLf.profile,
            'emdash-v3.2-dttlf-directed-1'
        );
        assert.equal(
            report.components.ordinaryFunctorialBinding.candidate,
            'emdash-v3.2-usability-1d'
        );
        assert.equal(
            report.components.displayedDependentBinding.candidate,
            'emdash-v3.2-displayed-chain-1a'
        );
    });

    it('is stable readonly data and records zero product semantics', () => {
        const report = result();
        [
            report,
            report.panelIds,
            report.pipeline,
            report.components,
            report.productEffects,
            report.supportedEnvelope,
            report.deferred,
            report.advancedWitness
        ].forEach(value => assert.equal(Object.isFrozen(value), true));
        assert.deepEqual(report.productEffects, {
            newMathematicalOwnerCount: 0,
            newRuntimeRuleCount: 0,
            newCheckerOrEvaluatorBranchCount: 0,
            newParserDependencyCount: 0,
            browserPromotion: false,
            productionLambdapiDependency: false
        });
    });

    it('formats one coherent deterministic evidence report', () => {
        const report = result();
        const first = formatCoreProductReviewDemo(report);
        const second = formatCoreProductReviewDemo(report);
        assert.equal(first, second);
        [
            '=== 1. Outer dependent logical framework ===',
            'Explicit locally nameless Core:',
            'Computation: 1. beta -> ' +
                '2. directed.sigma-telescope-fibre.evaluate',
            '=== 2. Ordinary functorial binding ===',
            'λ x :^f demo_A. (demo_H x) (demo_K x)',
            'Combined structural basis:',
            '=== 3. Displayed dependent binding ===',
            'λ a :^fd A. λ b :^fd B(a). FF[a]',
            'internalized arrow does not collapse: not-equal',
            'new owners/rules/checker branches in this report: 0/0/0',
            'production Lambdapi dependency: no',
            './scripts/pnpmw run ' +
                'demo:categorical-displayed-nd-higher'
        ].forEach(fragment => assert.match(first, new RegExp(
            fragment.replace(/[.*+?^${}()|[\]\\]/gu, '\\$&'),
            'u'
        )));
    });

    it('fails closed when a reviewed component boundary drifts', () => {
        const report = result();
        const driftedOrdinary = {
            ...report.components.ordinaryFunctorialBinding,
            stringParserDependency: true
        };
        const drifted = {
            ...report.components,
            ordinaryFunctorialBinding: driftedOrdinary
        } as unknown as CoreProductReviewDemoComponents;
        assert.throws(
            () => assembleCoreProductReviewDemo(drifted),
            error =>
                error instanceof CoreProductReviewDemoError &&
                error.code ===
                    'PRODUCT_REVIEW_COMPONENT_BOUNDARY_DRIFT'
        );
    });

    it('stays out of the browser and imports no process oracle', () => {
        assert.equal(
            'runCoreProductReviewDemo' in browser,
            false
        );
        assert.equal(
            'formatCoreProductReviewDemo' in browser,
            false
        );
        const source = readFileSync(
            'src/v3_2/product_review_demo.ts',
            'utf8'
        );
        assert.doesNotMatch(
            source,
            /from ['"]node:child_process['"]|from ['"]child_process['"]/u
        );
        assert.equal(
            result().advancedWitness.includedByDefault,
            false
        );
    });
});
