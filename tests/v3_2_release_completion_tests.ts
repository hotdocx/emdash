/**
 * Focused RELEASE-1C completion, residual, and performance-boundary tests.
 */

import assert from 'node:assert';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_CHECKER_RUNTIME_COMPARISON_STEP_LIMIT,
    CORE_MVP_GRADUATION_REVIEW,
    CORE_MVP_RELEASE_COMPLETION,
    CORE_MVP_RELEASE_POLICY,
    CoreMvpReleaseCompletionError,
    CoreMvpReleaseCompletionInput,
    validateCoreMvpReleaseCompletion
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const repositoryRoot = resolve(__dirname, '..');

const readRepositoryFile = (path: string): string =>
    readFileSync(resolve(repositoryRoot, path), 'utf8');

const cloneCompletion = (): CoreMvpReleaseCompletionInput =>
    JSON.parse(JSON.stringify(CORE_MVP_RELEASE_COMPLETION));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    for (const child of Object.values(value as Record<string, unknown>)) {
        assertDeepFrozen(child);
    }
};

const expectCompletionError = (
    mutate: (completion: any) => void
): CoreMvpReleaseCompletionError => {
    const completion = cloneCompletion() as any;
    mutate(completion);
    try {
        validateCoreMvpReleaseCompletion(completion);
    } catch (error) {
        assert.ok(error instanceof CoreMvpReleaseCompletionError);
        assert.equal(
            error.code,
            'RELEASE_COMPLETION_BOUNDARY_MISMATCH'
        );
        return error;
    }
    assert.fail('Expected RELEASE_COMPLETION_BOUNDARY_MISMATCH');
};

describe('TypeScript v3.2 RELEASE-1C completion', () => {
    it('closes the three release slices for the exact approved profile', () => {
        const completion = CORE_MVP_RELEASE_COMPLETION;

        assert.equal(completion.revision, 'RELEASE-1C');
        assert.equal(
            completion.status,
            'release-ready-exact-profile'
        );
        assert.deepEqual(completion.completedReleaseSlices, [
            'RELEASE-1A',
            'RELEASE-1B',
            'RELEASE-1C'
        ]);
        assert.equal(
            completion.productProfile.manifestRevision,
            'emdash-v3.2-mvp-1'
        );
        assert.deepEqual(
            completion.productProfile.ownerIds,
            CORE_MVP_GRADUATION_REVIEW.ownerIds
        );
        assert.deepEqual(
            completion.productProfile.runtimeRuleIds,
            CORE_MVP_GRADUATION_REVIEW.runtimeRuleIds
        );
        assert.equal(completion.releaseReady, true);
        assert.equal(completion.nextSlice, null);
    });

    it('adds completion without rewriting historical non-ready records', () => {
        assert.equal(CORE_MVP_GRADUATION_REVIEW.releaseReady, false);
        assert.equal(CORE_MVP_RELEASE_POLICY.releaseReady, false);
        assert.equal(CORE_MVP_RELEASE_POLICY.nextSlice, 'RELEASE-1C');
        assert.equal(
            CORE_MVP_RELEASE_COMPLETION.releasePolicyRevision,
            CORE_MVP_RELEASE_POLICY.revision
        );
        assert.deepEqual(
            CORE_MVP_RELEASE_COMPLETION
                .lambdapiPolicy.acceptanceTriggers,
            CORE_MVP_RELEASE_POLICY.lambdapiPolicy.acceptanceTriggers
        );
    });

    it('makes the performance non-claim and future prerequisite exact', () => {
        const boundary =
            CORE_MVP_RELEASE_COMPLETION.performanceBoundary;

        assert.equal(
            boundary.checkerComparisonStepLimit,
            CORE_CHECKER_RUNTIME_COMPARISON_STEP_LIMIT
        );
        assert.equal(
            boundary.boundMeaning,
            'global-runtime-rewrite-step-budget'
        );
        assert.equal(boundary.wallClockGuarantee, 'none');
        assert.equal(boundary.latencyThroughputOrScaleSla, 'none');
        assert.equal(boundary.benchmarkRequiredForCurrentRelease, false);
        assert.equal(
            boundary.futurePerformanceClaimRequires,
            'representative-workload-measurement-and-separate-review'
        );
        assert.equal(boundary.observedValidationTimingIsSla, false);
    });

    it('has no release blockers while preserving conditional scope', () => {
        const residual =
            CORE_MVP_RELEASE_COMPLETION.residualBoundary;
        const masterPlan = readRepositoryFile(
            'docs/TYPESCRIPT_ELABORATOR_V3_2_MASTER_PLAN.md'
        );
        const coverageRows = masterPlan
            .split('\n')
            .filter(line => /^\| C-\d{2} \|/.test(line));

        assert.deepEqual(residual.releaseBlockers, []);
        assert.deepEqual(
            residual.conditionalFutureGates.map(gate => [
                gate.id,
                gate.state
            ]),
            [
                ['H-02', 'not-triggered'],
                ['H-06', 'not-triggered']
            ]
        );
        assert.equal(coverageRows.length, 21);
        for (const row of coverageRows) {
            assert.match(
                row.split('|')[3].trim(),
                /^complete/,
                `Expected completed coverage row: ${row}`
            );
        }
        assert.match(
            masterPlan,
            /^\| RELEASE-READY \| complete \|/m
        );
        assert.match(
            masterPlan,
            /^\| RELEASE-1C \| complete \|/m
        );
        assert.doesNotMatch(
            masterPlan,
            /^\| RELEASE-\d[A-Z] \| dependency-ready/m
        );
    });

    it('pins the final gates and keeps completion outside the browser API', () => {
        const validation = CORE_MVP_RELEASE_COMPLETION.validation;
        const rootReadme = readRepositoryFile('README.md');
        const handoff = readRepositoryFile(
            'docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md'
        );

        assert.equal(validation.allPassed, true);
        assert.equal(
            validation.conformanceCommand,
            './scripts/pnpmw run check:conformance'
        );
        assert.equal(
            validation.repositoryGateCommand,
            'EMDASH_TYPECHECK_TIMEOUT=60s ' +
                './scripts/pnpmw run check:all'
        );
        assert.match(rootReadme, /release-ready exact profile/i);
        assert.match(handoff, /RELEASE-READY is complete/);
        assert.equal(
            Object.prototype.hasOwnProperty.call(
                browser,
                'CORE_MVP_RELEASE_COMPLETION'
            ),
            false
        );
        assert.equal(
            browser.CORE_MVP_MANIFEST.revision,
            'emdash-v3.2-mvp-1'
        );
    });

    it('is deeply frozen and rejects every completion-boundary drift', () => {
        assertDeepFrozen(CORE_MVP_RELEASE_COMPLETION);
        assert.doesNotThrow(() =>
            validateCoreMvpReleaseCompletion(
                CORE_MVP_RELEASE_COMPLETION
            )
        );

        assert.match(
            expectCompletionError(drift => {
                drift.residualBoundary.releaseBlockers.push('parser');
            }).message,
            /exact RELEASE-1C/
        );
        assert.match(
            expectCompletionError(drift => {
                drift.performanceBoundary
                    .latencyThroughputOrScaleSla = 'fast';
            }).message,
            /exact RELEASE-1C/
        );
        assert.match(
            expectCompletionError(drift => {
                drift.claimBoundary.generalConfluence = 'authorized';
            }).message,
            /exact RELEASE-1C/
        );
        assert.match(
            expectCompletionError(drift => {
                drift.releaseReady = false;
            }).message,
            /exact RELEASE-1C/
        );
    });
});
