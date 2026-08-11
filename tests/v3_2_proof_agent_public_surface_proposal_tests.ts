/** Focused tests for the non-authorizing AGENT-EVAL-12B2 proposal. */

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL,
    CoreLfProofAgentPublicSurface12b2Proposal,
    CoreLfProofAgentPublicSurface12b2ProposalError,
    cloneCoreLfProofAgentPublicSurface12b2Proposal,
    validateCoreLfProofAgentPublicSurface12b2Proposal
} from '../src/v3_2/lf_proof_agent_public_surface_proposal';

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

describe('AGENT-EVAL-12B2 public benchmark-surface proposal', () => {
    it('pins the exact completed 12B1 and current package predecessor', () => {
        const proposal =
            validateCoreLfProofAgentPublicSurface12b2Proposal();
        assertDeepFrozen(proposal);
        assert.equal(proposal.revision, 'AGENT-EVAL-12B2-PROPOSAL-1');
        assert.equal(proposal.status, 'ready-for-separate-review');
        assert.equal(proposal.parent.corpusSemanticCheckpoint, 'd0d3764');
        assert.equal(proposal.parent.corpusLedgerCheckpoint, '3e3fcf8');
        assert.equal(proposal.parent.publicPackageVersion, '0.2.0');
        assert.equal(
            proposal.parent.nextPackageVersionAndReleaseOwner,
            'AGENT-EVAL-12B3'
        );
    });

    it('retains all seventeen approved predecessor owners and proposal digest',
        () => {
        const proposal =
            CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL;
        assert.equal(proposal.pinnedSources.length, 17);
        assert.equal(
            new Set(proposal.pinnedSources.map(source => source.id)).size,
            17
        );
        for (const source of proposal.pinnedSources) {
            assert.match(source.sha256, /^[0-9a-f]{64}$/u, source.id);
        }
        assert.equal(
            sha256('src/v3_2/lf_proof_agent_public_surface_proposal.ts'),
            'c820786bd4974313fff2eae5e3d459f29d46a2a18a5c97690047fe324364e759'
        );
    });

    it('measures the payload and freezes a genuinely lazy browser gate',
        () => {
            const proposal =
                CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL;
            assert.equal(
                proposal.measuredBoundary.canonicalCorpusUtf8Bytes,
                5884285
            );
            assert.equal(
                proposal.measuredBoundary.standaloneBrowserClosure.gzipBytes,
                136817
            );
            assert.equal(
                proposal.browserPresentation.userTriggeredOnly,
                true
            );
            assert.equal(
                proposal.browserPresentation
                    .automaticallyBuildsCorpusOnPageLoad,
                false
            );
            assert.equal(
                proposal.browserPresentation.initialChunkContainsCorpusRevision,
                false
            );
            assert.equal(
                proposal.browserPresentation.lazyChunkContainsCorpusRevision,
                true
            );
        });

    it('adds one isolated browser-safe package subpath and no npm CLI', () => {
        const surface =
            CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL
                .publicPackageSurface;
        assert.equal(surface.newSubpath, '@hotdocx/emdash/benchmark');
        assert.deepEqual(surface.existingExportOrder, [
            '.',
            './authoring',
            './workspace',
            './benchmark',
            './package.json'
        ]);
        assert.equal(surface.rootReexportsBenchmark, false);
        assert.equal(surface.authoringReexportsBenchmark, false);
        assert.equal(surface.workspaceReexportsBenchmark, false);
        assert.equal(surface.nodeBuiltinDependency, false);
        assert.equal(surface.npmBinAdded, false);
        assert.equal(surface.installHookAdded, false);
        assert.equal(surface.runtimeDependencyAdded, false);
        assert.equal(surface.releasePreflightRetainsNoBinPolicy, true);
    });

    it('defines a stateless artifact runner rather than a provider server',
        () => {
            const runner =
                CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL.nodeRunner;
            assert.deepEqual(
                runner.commands.map(command => command.id),
                ['catalog', 'case', 'corpus', 'reference', 'evaluate']
            );
            assert.equal(runner.evaluateUsesStrictRunParser, true);
            assert.equal(runner.evaluateFreshlyReplays, true);
            assert.equal(runner.readsExactlyOneRunFile, true);
            assert.equal(runner.scansDirectories, false);
            assert.equal(runner.writesFiles, false);
            assert.equal(runner.spawnsProvider, false);
            assert.equal(runner.invokesModel, false);
            assert.equal(runner.accessesNetwork, false);
            assert.equal(runner.enforcesReportedResourceLimits, false);
            assert.equal(runner.retainsSessionState, false);
            assert.equal(runner.publishedAsNpmBin, false);
        });

    it('requires the full public, browser, and installed-consumer gates',
        () => {
            const validation =
                CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL.validation;
            assert.equal(validation.workspaceCheck, true);
            assert.equal(validation.typecheck, true);
            assert.equal(validation.browserTypecheckAndBuild, true);
            assert.equal(validation.packageBuild, true);
            assert.equal(validation.packedEsmConsumer, true);
            assert.equal(validation.packedCjsConsumer, true);
            assert.equal(validation.packedStrictNodeNextConsumer, true);
            assert.equal(validation.packedBrowserConsumer, true);
            assert.equal(
                validation.packageCoreOnlyExcludesBenchmarkClosure,
                true
            );
            assert.equal(validation.checkTsRequiredAbsentHumanWaiver, true);
            assert.equal(
                validation.directStandingLongAggregateWaiverApplies,
                true
            );
            assert.equal(validation.checkAll, false);
            assert.equal(validation.lambdapi, false);
        });

    it('rejects prerequisite, package, runner, browser, authority, and drift',
        () => {
            const cases: readonly [
                CoreLfProofAgentPublicSurface12b2Proposal,
                CoreLfProofAgentPublicSurface12b2ProposalError['code']
            ][] = [
                (() => {
                    const value =
                        cloneCoreLfProofAgentPublicSurface12b2Proposal();
                    (value.parent as {
                        corpusSemanticCheckpoint: string;
                    }).corpusSemanticCheckpoint = 'wrong';
                    return value;
                })(),
                (() => {
                    const value =
                        cloneCoreLfProofAgentPublicSurface12b2Proposal();
                    (value.publicPackageSurface as {
                        npmBinAdded: boolean;
                    }).npmBinAdded = true;
                    return value;
                })(),
                (() => {
                    const value =
                        cloneCoreLfProofAgentPublicSurface12b2Proposal();
                    (value.nodeRunner as {
                        spawnsProvider: boolean;
                    }).spawnsProvider = true;
                    return value;
                })(),
                (() => {
                    const value =
                        cloneCoreLfProofAgentPublicSurface12b2Proposal();
                    (value.browserPresentation as {
                        automaticallyBuildsCorpusOnPageLoad: boolean;
                    }).automaticallyBuildsCorpusOnPageLoad = true;
                    return value;
                })(),
                (() => {
                    const value =
                        cloneCoreLfProofAgentPublicSurface12b2Proposal();
                    (value.semanticEffects as {
                        packageReleased: boolean;
                    }).packageReleased = true;
                    return value;
                })(),
                (() => {
                    const value =
                        cloneCoreLfProofAgentPublicSurface12b2Proposal();
                    (value.publicPackageSurface as {
                        sourceEntry: string;
                    }).sourceEntry = 'different.ts';
                    return value;
                })()
            ].map((value, index) => [value, [
                'PUBLIC_SURFACE_PREREQUISITE_DRIFT',
                'PUBLIC_SURFACE_PACKAGE_DRIFT',
                'PUBLIC_SURFACE_RUNNER_DRIFT',
                'PUBLIC_SURFACE_BROWSER_DRIFT',
                'PUBLIC_SURFACE_AUTHORITY_DRIFT',
                'PUBLIC_SURFACE_PROPOSAL_DRIFT'
            ][index] as CoreLfProofAgentPublicSurface12b2ProposalError['code']]);

            for (const [proposal, code] of cases) {
                assert.throws(
                    () => validateCoreLfProofAgentPublicSurface12b2Proposal(
                        proposal
                    ),
                    error => error instanceof
                        CoreLfProofAgentPublicSurface12b2ProposalError &&
                        error.code === code,
                    code
                );
            }
        });

    it('keeps the historical planning record outside runtime owners', () => {
        const source = readFileSync(resolve(
            repositoryRoot,
            'src/v3_2/lf_proof_agent_public_surface_proposal.ts'
        ), 'utf8');
        assert.doesNotMatch(source, /^import\s/mu);
        for (const relative of [
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/package_benchmark.ts',
            'src/v3_2/lf_proof_agent_benchmark_cli.ts',
            'emdash-template/src/emdash_api.ts',
            'packages/emdash/package.json'
        ]) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, relative), 'utf8'),
                /lf_proof_agent_public_surface_(?:proposal|review)/u,
                relative
            );
        }
        const clone = cloneCoreLfProofAgentPublicSurface12b2Proposal();
        assert.notEqual(
            clone as CoreLfProofAgentPublicSurface12b2Proposal,
            CORE_LF_PROOF_AGENT_PUBLIC_SURFACE_12B2_PROPOSAL
        );
    });
});
