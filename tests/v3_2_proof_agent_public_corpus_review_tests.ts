/** Focused tests for separate AGENT-EVAL-12B1 proposal review. */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_REVIEW,
    CoreLfProofAgentPublicCorpus12b1Review,
    CoreLfProofAgentPublicCorpus12b1ReviewError,
    cloneCoreLfProofAgentPublicCorpus12b1Review,
    validateCoreLfProofAgentPublicCorpus12b1Review
} from '../src/v3_2/lf_proof_agent_public_corpus_review';

const repositoryRoot = resolve(__dirname, '..');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

describe('AGENT-EVAL-12B1 separate corpus proposal review', () => {
    it('approves only exact checkpoint a181885 and proposal digest', () => {
        const review = validateCoreLfProofAgentPublicCorpus12b1Review();
        assertDeepFrozen(review);
        assert.equal(review.proposalCheckpoint, 'a181885');
        assert.equal(
            review.proposalSha256,
            'ecbd67496a99775c13357d9175b623200e20e79346d62b00b8773bc5e7d08a60'
        );
        assert.equal(
            review.decision,
            'approved-for-AGENT-EVAL-12B1-internal-implementation'
        );
        assert.equal(review.authority, 'user-delegated-unattended-approval');
        assert.equal(review.humanMaySupersede, true);
    });

    it('requires executable integration rather than feature labels', () => {
        const conditions = new Map(
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_REVIEW
                .implementationConditions.map(entry => [entry.id, entry])
        );
        assert.match(
            conditions.get('reference-owner-integration')?.requirement ?? '',
            /generate one ordinary patch accepted by fresh unchanged 12A/u
        );
        assert.match(
            conditions.get('no-label-substitution')?.requirement ?? '',
            /cannot substitute/u
        );
        assert.match(
            conditions.get('ambiguity-honesty')?.requirement ?? '',
            /without an arbitrary hidden winner/u
        );
    });

    it('authorizes internal corpus/interchange modules and nothing later',
        () => {
            const scope =
                CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_REVIEW
                    .semanticAuthorization;
            assert.equal(scope.addCorpusModule, true);
            assert.equal(scope.addInterchangeModule, true);
            assert.equal(scope.addFocusedTests, true);
            assert.equal(scope.useExisting12aEvaluator, true);
            assert.equal(scope.change12aTaskKind, false);
            assert.equal(scope.changeCoreOrChecker, false);
            assert.equal(scope.addRuntimeOrProofRule, false);
            assert.equal(scope.exportPublicPackageBarrel, false);
            assert.equal(scope.addNodeRunner, false);
            assert.equal(scope.changePackageVersion, false);
            assert.equal(scope.publishOrRelease, false);
            assert.equal(scope.mutateSiblingRepository, false);
            assert.equal(scope.invokeModel, false);
            assert.equal(scope.mutateHostedState, false);
        });

    it('accepts focused evidence without inventing an aggregate pass', () => {
        const validation =
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_REVIEW.validationAccepted;
        assert.deepEqual(validation, {
            proposalTests: 8,
            nearestOwnerTests: 104,
            nearestOwnerSuites: 18,
            rootTypecheckPassed: true,
            focusedLintPassed: true,
            staticNonExportPassed: true,
            diffHygienePassed: true,
            longAggregateRun: false,
            longAggregateClaimed: false
        });
    });

    it('rejects proposal, scope, and general review drift', () => {
        const proposal = cloneCoreLfProofAgentPublicCorpus12b1Review();
        (proposal as { proposalCheckpoint: string }).proposalCheckpoint =
            'wrong';
        assert.throws(
            () => validateCoreLfProofAgentPublicCorpus12b1Review(proposal),
            error => error instanceof
                CoreLfProofAgentPublicCorpus12b1ReviewError &&
                error.code === 'PUBLIC_CORPUS_REVIEW_PROPOSAL_DRIFT'
        );

        const scope = cloneCoreLfProofAgentPublicCorpus12b1Review();
        (scope.semanticAuthorization as {
            exportPublicPackageBarrel: boolean;
        }).exportPublicPackageBarrel = true;
        assert.throws(
            () => validateCoreLfProofAgentPublicCorpus12b1Review(scope),
            error => error instanceof
                CoreLfProofAgentPublicCorpus12b1ReviewError &&
                error.code === 'PUBLIC_CORPUS_REVIEW_SCOPE_DRIFT'
        );

        const general = cloneCoreLfProofAgentPublicCorpus12b1Review();
        (general as { nextAfterImplementation: string })
            .nextAfterImplementation = 'other';
        assert.throws(
            () => validateCoreLfProofAgentPublicCorpus12b1Review(general),
            error => error instanceof
                CoreLfProofAgentPublicCorpus12b1ReviewError &&
                error.code === 'PUBLIC_CORPUS_REVIEW_RECORD_DRIFT'
        );
    });

    it('adds no public, package, browser, or runner dependency', () => {
        for (const relative of [
            'src/v3_2/index.ts',
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/browser.ts',
            'packages/emdash/package.json'
        ]) {
            const source = readFileSync(resolve(repositoryRoot, relative),
                'utf8');
            assert.doesNotMatch(
                source,
                /lf_proof_agent_public_corpus_(?:proposal|review)/u,
                relative
            );
        }
        const clone = cloneCoreLfProofAgentPublicCorpus12b1Review();
        assert.notEqual(
            clone as CoreLfProofAgentPublicCorpus12b1Review,
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_REVIEW
        );
    });
});
