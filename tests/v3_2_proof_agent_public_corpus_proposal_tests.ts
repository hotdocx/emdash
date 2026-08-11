/** Focused tests for the non-authorizing AGENT-EVAL-12B1 proposal. */

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL,
    CoreLfProofAgentPublicCorpus12b1Proposal,
    CoreLfProofAgentPublicCorpus12b1ProposalError,
    cloneCoreLfProofAgentPublicCorpus12b1Proposal,
    validateCoreLfProofAgentPublicCorpus12b1Proposal
} from '../src/v3_2/lf_proof_agent_public_corpus_proposal';

const repositoryRoot = resolve(__dirname, '..');

const sha256 = (relative: string): string => createHash('sha256')
    .update(readFileSync(resolve(repositoryRoot, relative)))
    .digest('hex');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

describe('AGENT-EVAL-12B1 public corpus/interchange proposal', () => {
    it('pins the exact completed evaluator, package, host, and library state',
        () => {
            const proposal =
                validateCoreLfProofAgentPublicCorpus12b1Proposal();
            assertDeepFrozen(proposal);
            assert.equal(
                proposal.revision,
                'AGENT-EVAL-12B1-PROPOSAL-1'
            );
            assert.equal(proposal.status, 'ready-for-separate-review');
            assert.deepEqual(proposal.parent, {
                governingPlanCheckpoint: '7aeb783',
                synchronizedAuditLedgerCheckpoint: '858126a',
                evaluatorSemanticCheckpoint: 'f46ff9a',
                publicPackageVersion: '0.2.0',
                publicPackageReleaseCheckpoint: 'ab513f7',
                hostedTypescriptConsumerCheckpoint: 'bd4146b',
                hostedGoalViewConsumerCheckpoint: '5c0d0c1',
                pathoutGraduationProposalCheckpoint: '85b560e',
                pathoutGraduationReviewCheckpoint: 'd7d7428',
                pathoutGraduationLedgerCheckpoint: '3135747',
                lean4SourceCheckpoint:
                    'f29e9e488ea8242c875806e4b0564820c2d553b2'
            });
        });

    it('pins every local owner by current file digest', () => {
        const proposal =
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL;
        assert.equal(proposal.pinnedSources.length, 13);
        for (const source of proposal.pinnedSources) {
            assert.equal(sha256(source.path), source.sha256, source.id);
        }
    });

    it('selects six tracks and ten unique cases without shrinking the gate',
        () => {
            const proposal =
                CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL;
            assert.equal(proposal.tracks.length, 6);
            assert.equal(proposal.caseMatrix.length, 10);
            assert.equal(
                new Set(proposal.caseMatrix.map(entry => entry.id)).size,
                10
            );
            for (const track of proposal.tracks) {
                assert.ok(
                    proposal.caseMatrix.filter(entry =>
                        entry.track === track.id
                    ).length >= track.minimumCases,
                    track.id
                );
            }
            assert.equal(
                proposal.caseMatrix.filter(entry =>
                    entry.origin === 'lean4-manual-translation'
                ).length,
                1
            );
            assert.ok(proposal.caseMatrix.some(entry =>
                entry.expectedReferenceOutcome === 'abstained'
            ));
        });

    it('covers proof management, automation, maintenance, and class sharing',
        () => {
            const features = new Set<string>(
                CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL
                    .caseMatrix.flatMap(entry => entry.features)
            );
            for (const required of [
                'contextual-have',
                'typed-placeholder',
                'direct-goal-coupling',
                'bounded-candidates',
                'backward-transport',
                'ancestor-sharing',
                'equal-priority-ambiguity',
                'previous-current-source',
                'explicit-dictionary-erasure'
            ]) {
                assert.equal(features.has(required), true, required);
            }
        });

    it('keeps PathOut and every authority/public effect outside 12B1', () => {
        const proposal =
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL;
        assert.equal(proposal.taskBoundary.pathoutPresentationIsCase, false);
        assert.equal(
            proposal.taskBoundary.semanticProgramTaskFamilyAdded,
            false
        );
        assert.equal(proposal.taskBoundary.newCoreNodeCount, 0);
        assert.equal(proposal.taskBoundary.newCheckerBranchCount, 0);
        assert.equal(proposal.taskBoundary.newRuleCount, 0);
        assert.equal(proposal.semanticEffects.corpusCreated, false);
        assert.equal(proposal.semanticEffects.parserCreated, false);
        assert.equal(proposal.semanticEffects.publicBarrelChanged, false);
        assert.equal(proposal.semanticEffects.packageVersionChanged, false);
        assert.equal(proposal.semanticEffects.siblingRepositoryChanged, false);
        assert.equal(proposal.semanticEffects.modelInvoked, false);
        assert.equal(proposal.decision.proposalIsSelfAuthorizing, false);
        assert.equal(
            proposal.decision.separateImmutableReviewRequired,
            true
        );
    });

    it('pins additive canonical APIs and external provenance evidence', () => {
        const proposal =
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL;
        assert.equal(
            proposal.plannedApi.createCorpus,
            'createCoreLfProofAgentPublicCorpus'
        );
        assert.equal(
            proposal.plannedApi.parseRun,
            'parseCoreLfProofAgentBenchmarkRunText'
        );
        assert.equal(proposal.interchange.unknownFieldPolicy, 'reject');
        assert.equal(proposal.interchange.canonicalByteIdentity, true);
        assert.equal(proposal.interchange.deepFrozen, true);
        assert.equal(
            proposal.externalEvidence.lean4.sourcePath,
            'tests/elab/diamond1.lean'
        );
        assert.equal(proposal.externalEvidence.lean4.license, 'Apache-2.0');
        assert.equal(
            proposal.externalEvidence.closerfans.mutationAuthorizedIn12B1,
            false
        );
    });

    it('rejects prerequisite, representativeness, authority, and general drift',
        () => {
            const prerequisite =
                cloneCoreLfProofAgentPublicCorpus12b1Proposal();
            (prerequisite.parent as {
                evaluatorSemanticCheckpoint: string;
            }).evaluatorSemanticCheckpoint = 'wrong';
            assert.throws(
                () => validateCoreLfProofAgentPublicCorpus12b1Proposal(
                    prerequisite
                ),
                error => error instanceof
                    CoreLfProofAgentPublicCorpus12b1ProposalError &&
                    error.code === 'PUBLIC_CORPUS_PREREQUISITE_DRIFT'
            );

            const representativeness =
                cloneCoreLfProofAgentPublicCorpus12b1Proposal();
            (representativeness.caseMatrix as unknown as unknown[]).pop();
            assert.throws(
                () => validateCoreLfProofAgentPublicCorpus12b1Proposal(
                    representativeness
                ),
                error => error instanceof
                    CoreLfProofAgentPublicCorpus12b1ProposalError &&
                    error.code === 'PUBLIC_CORPUS_REPRESENTATIVENESS_DRIFT'
            );

            const authority =
                cloneCoreLfProofAgentPublicCorpus12b1Proposal();
            (authority.taskBoundary as {
                pathoutPresentationIsCase: boolean;
            }).pathoutPresentationIsCase = true;
            assert.throws(
                () => validateCoreLfProofAgentPublicCorpus12b1Proposal(
                    authority
                ),
                error => error instanceof
                    CoreLfProofAgentPublicCorpus12b1ProposalError &&
                    error.code === 'PUBLIC_CORPUS_AUTHORITY_DRIFT'
            );

            const general =
                cloneCoreLfProofAgentPublicCorpus12b1Proposal();
            (general.plannedApi as { corpusModule: string }).corpusModule =
                'different.ts';
            assert.throws(
                () => validateCoreLfProofAgentPublicCorpus12b1Proposal(
                    general
                ),
                error => error instanceof
                    CoreLfProofAgentPublicCorpus12b1ProposalError &&
                    error.code === 'PUBLIC_CORPUS_PROPOSAL_DRIFT'
            );
        });

    it('adds no behavior or barrel/package dependency', () => {
        const source = readFileSync(resolve(
            repositoryRoot,
            'src/v3_2/lf_proof_agent_public_corpus_proposal.ts'
        ), 'utf8');
        assert.doesNotMatch(source, /^import\s/mu);
        for (const relative of [
            'src/v3_2/index.ts',
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/browser.ts',
            'packages/emdash/package.json'
        ]) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, relative), 'utf8'),
                /lf_proof_agent_public_corpus/u,
                relative
            );
        }
        const clone = cloneCoreLfProofAgentPublicCorpus12b1Proposal();
        assert.notEqual(
            clone as CoreLfProofAgentPublicCorpus12b1Proposal,
            CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_12B1_PROPOSAL
        );
    });
});
