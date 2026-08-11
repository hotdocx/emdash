/** Focused tests for separate AGENT-EVAL-12B2 proposal review. */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_REVIEW,
    CoreLfProofAgentPublicSurface12b2Review,
    CoreLfProofAgentPublicSurface12b2ReviewError,
    cloneCoreLfProofAgentPublicSurface12b2Review,
    validateCoreLfProofAgentPublicSurface12b2Review
} from '../src/v3_2/lf_proof_agent_public_surface_review';

const repositoryRoot = resolve(__dirname, '..');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

describe('AGENT-EVAL-12B2 separate public-surface proposal review', () => {
    it('approves only checkpoint ba49705 and its exact proposal digest',
        () => {
            const review = validateCoreLfProofAgentPublicSurface12b2Review();
            assertDeepFrozen(review);
            assert.equal(review.proposalCheckpoint, 'ba49705');
            assert.equal(
                review.proposalSha256,
                'c820786bd4974313fff2eae5e3d459f29d46a2a18a5c97690047fe324364e759'
            );
            assert.equal(
                review.decision,
                'approved-for-AGENT-EVAL-12B2-bounded-implementation'
            );
            assert.equal(
                review.authority,
                'user-delegated-unattended-approval'
            );
            assert.equal(review.humanMaySupersede, true);
        });

    it('makes catalog, UTF-8, replay, and canonical output exact', () => {
        const conditions = new Map(
            CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_REVIEW
                .implementationConditions.map(entry => [entry.id, entry])
        );
        assert.match(
            conditions.get('canonical-compact-catalog')?.requirement ?? '',
            /contains no case text/u
        );
        assert.match(
            conditions.get('strict-run-file-boundary')?.requirement ?? '',
            /raw byte limit before fatal UTF-8 decode/u
        );
        assert.match(
            conditions.get('fresh-evaluation-and-canonical-output')
                ?.requirement ?? '',
            /strict run parser then fresh unchanged 12A/u
        );
    });

    it('requires isolated package entries and retains least authority', () => {
        const scope =
            CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_REVIEW
                .semanticAuthorization;
        assert.equal(scope.addBenchmarkPackageEntry, true);
        assert.equal(scope.updatePackageBuildAndConsumerGates, true);
        assert.equal(scope.updateExactReleasePreflightExports, true);
        assert.equal(scope.reexportFromExistingPackageEntries, false);
        assert.equal(scope.addNpmBinOrRuntimeDependency, false);
        assert.equal(scope.changePackageVersion, false);
        assert.equal(scope.publishOrRelease, false);
    });

    it('requires transitive browser gates and an inert page load', () => {
        const conditions = new Map(
            CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_REVIEW
                .implementationConditions.map(entry => [entry.id, entry])
        );
        assert.match(
            conditions.get('transitive-browser-budget')?.requirement ?? '',
            /complete initial static and benchmark dynamic closures/u
        );
        assert.match(
            conditions.get('browser-non-authority')?.requirement ?? '',
            /page load performs no corpus work/u
        );
        assert.equal(
            CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_REVIEW
                .semanticAuthorization.addLazyBrowserPresentation,
            true
        );
    });

    it('requires all packed consumer modes and no semantic widening', () => {
        const review = CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_REVIEW;
        assert.match(
            review.implementationConditions.find(entry =>
                entry.id === 'installed-consumer-matrix'
            )?.requirement ?? '',
            /ESM, CommonJS, strict NodeNext, and browser/u
        );
        assert.equal(review.semanticAuthorization.change12aEvaluator, false);
        assert.equal(
            review.semanticAuthorization.change12b1CorpusOrInterchange,
            false
        );
        assert.equal(review.semanticAuthorization.changeCoreOrChecker, false);
        assert.equal(review.semanticAuthorization.addRuntimeOrProofRule, false);
    });

    it('accepts focused evidence without rewriting the wrapper or aggregate',
        () => {
            const validation =
                CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_REVIEW
                    .validationAccepted;
            assert.equal(validation.proposalTests, 8);
            assert.equal(validation.rootTypecheckPassed, true);
            assert.equal(validation.currentPackageBuildPassed, true);
            assert.equal(validation.directBrowserBuildPassed, true);
            assert.equal(validation.prescribedBrowserWrapperPassed, false);
            assert.equal(
                validation.prescribedBrowserWrapperFailureRecorded,
                true
            );
            assert.equal(validation.longAggregateRun, false);
            assert.equal(validation.longAggregateClaimed, false);
        });

    it('rejects proposal, scope, and general review drift', () => {
        const proposal = cloneCoreLfProofAgentPublicSurface12b2Review();
        (proposal as { proposalCheckpoint: string }).proposalCheckpoint =
            'wrong';
        assert.throws(
            () => validateCoreLfProofAgentPublicSurface12b2Review(proposal),
            error => error instanceof
                CoreLfProofAgentPublicSurface12b2ReviewError &&
                error.code === 'PUBLIC_SURFACE_REVIEW_PROPOSAL_DRIFT'
        );

        const scope = cloneCoreLfProofAgentPublicSurface12b2Review();
        (scope.semanticAuthorization as {
            addNpmBinOrRuntimeDependency: boolean;
        }).addNpmBinOrRuntimeDependency = true;
        assert.throws(
            () => validateCoreLfProofAgentPublicSurface12b2Review(scope),
            error => error instanceof
                CoreLfProofAgentPublicSurface12b2ReviewError &&
                error.code === 'PUBLIC_SURFACE_REVIEW_SCOPE_DRIFT'
        );

        const general = cloneCoreLfProofAgentPublicSurface12b2Review();
        (general as { nextAfterImplementation: string })
            .nextAfterImplementation = 'other';
        assert.throws(
            () => validateCoreLfProofAgentPublicSurface12b2Review(general),
            error => error instanceof
                CoreLfProofAgentPublicSurface12b2ReviewError &&
                error.code === 'PUBLIC_SURFACE_REVIEW_RECORD_DRIFT'
        );
    });

    it('adds no public, package, browser, or runner dependency', () => {
        for (const relative of [
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'emdash-template/src/emdash_api.ts',
            'packages/emdash/package.json',
            'scripts/emdash'
        ]) {
            const source = readFileSync(resolve(repositoryRoot, relative),
                'utf8');
            assert.doesNotMatch(
                source,
                /lf_proof_agent_public_surface_(?:proposal|review)|package_benchmark/u,
                relative
            );
        }
        const clone = cloneCoreLfProofAgentPublicSurface12b2Review();
        assert.notEqual(
            clone as CoreLfProofAgentPublicSurface12b2Review,
            CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_REVIEW
        );
    });
});
