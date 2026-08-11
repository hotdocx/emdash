/** Focused AGENT-EVAL-12B2 stateless benchmark-adapter tests. */

import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    createCoreLfProofAgentBenchmarkRun,
    serializeCoreLfProofAgentBenchmarkReport,
    serializeCoreLfProofAgentBenchmarkRun
} from '../src/v3_2/lf_proof_agent_benchmark';
import {
    parseCoreLfProofAgentBenchmarkCaseText,
    parseCoreLfProofAgentBenchmarkReportText
} from '../src/v3_2/lf_proof_agent_interchange';
import {
    CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE,
    CoreLfProofAgentBenchmarkCatalog,
    CoreLfProofAgentBenchmarkCliErrorCode,
    createCoreLfProofAgentBenchmarkCatalog,
    runCoreLfProofAgentBenchmarkCli,
    serializeCoreLfProofAgentBenchmarkCatalog
} from '../src/v3_2/lf_proof_agent_benchmark_cli';
import {
    createCoreLfProofAgentPublicCorpus,
    parseCoreLfProofAgentPublicCorpusText,
    serializeCoreLfProofAgentPublicCorpus
} from '../src/v3_2/lf_proof_agent_public_corpus';

const repositoryRoot = resolve(__dirname, '..');

interface CliResult {
    readonly exitCode: number;
    readonly stdout: string;
    readonly stderr: string;
    readonly reads: readonly string[];
}

const runCli = (
    argv: readonly string[],
    bytes?: Uint8Array | (() => Uint8Array)
): CliResult => {
    let stdout = '';
    let stderr = '';
    const reads: string[] = [];
    const exitCode = runCoreLfProofAgentBenchmarkCli(argv, {
        cwd: () => '/benchmark-project',
        readFileBytes: absolutePath => {
            reads.push(absolutePath);
            if (typeof bytes === 'function') return bytes();
            if (bytes !== undefined) return bytes;
            throw new Error('missing fixture');
        },
        stdout: text => { stdout += text; },
        stderr: text => { stderr += text; }
    });
    return { exitCode, stdout, stderr, reads };
};

const parseError = (result: CliResult): {
    readonly code: CoreLfProofAgentBenchmarkCliErrorCode;
    readonly command: string | null;
    readonly includesStack: false;
    readonly includesArtifactContents: false;
} => JSON.parse(result.stderr) as {
    readonly code: CoreLfProofAgentBenchmarkCliErrorCode;
    readonly command: string | null;
    readonly includesStack: false;
    readonly includesArtifactContents: false;
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

describe('AGENT-EVAL-12B2 stateless proof-agent benchmark adapter', () => {
    it('derives a canonical deeply frozen catalog with no task text', () => {
        const catalog = createCoreLfProofAgentBenchmarkCatalog();
        assertDeepFrozen(catalog);
        assert.equal(
            catalog.revision,
            'emdash-lf-proof-agent-benchmark-catalog-v1'
        );
        assert.equal(catalog.tracks.length, 6);
        assert.equal(catalog.entries.length, 10);
        assert.deepEqual(catalog.referenceOutcomes, {
            abstained: 1,
            acceptedComplete: 9,
            acceptedIncomplete: 0,
            rejected: 0
        });
        assert.equal(catalog.caseTextIncluded, false);
        assert.equal(catalog.artifactIsBenchmarkTask, false);
        assert.equal(catalog.artifactIsProofAuthority, false);
        assert.equal(catalog.referenceAttemptsAreProofAuthority, false);
        assert.equal(catalog.modelPerformanceClaimed, false);
        const text = serializeCoreLfProofAgentBenchmarkCatalog(catalog);
        assert.equal(text.endsWith('\n'), true);
        assert.doesNotMatch(text, /previousSourceText|currentSourceText/u);
        assert.doesNotMatch(text, /reportText/u);
    });

    it('emits exact catalog and selected-case JSONL or bounded text', () => {
        const catalog = runCli(['catalog']);
        assert.equal(catalog.exitCode, 0);
        assert.equal(catalog.stderr, '');
        assert.equal(catalog.reads.length, 0);
        const record = JSON.parse(catalog.stdout) as
            CoreLfProofAgentBenchmarkCatalog;
        assert.equal(record.entries.length, 10);
        assert.equal(
            catalog.stdout,
            serializeCoreLfProofAgentBenchmarkCatalog(record)
        );

        const caseResult = runCli([
            'case',
            '--case',
            'native.apply.explicit-premise'
        ]);
        assert.equal(caseResult.exitCode, 0);
        assert.equal(caseResult.stderr, '');
        assert.equal(
            parseCoreLfProofAgentBenchmarkCaseText(caseResult.stdout).id,
            'native.apply.explicit-premise'
        );

        const text = runCli([
            'case',
            '--case=native.apply.explicit-premise',
            '--format=text'
        ]);
        assert.equal(text.exitCode, 0);
        assert.match(text.stdout, /goal:/u);
        assert.match(text.stdout, /not the canonical benchmark case/u);
        assert.doesNotMatch(text.stdout, /previousSourceText/u);
    });

    it('emits exact canonical full-corpus and reference-report artifacts',
        () => {
            const corpusResult = runCli(['corpus']);
            assert.equal(corpusResult.exitCode, 0);
            assert.equal(corpusResult.stderr, '');
            const corpus = parseCoreLfProofAgentPublicCorpusText(
                corpusResult.stdout
            );
            assert.equal(
                corpusResult.stdout,
                serializeCoreLfProofAgentPublicCorpus(corpus)
            );

            const reference = runCli(['reference']);
            assert.equal(reference.exitCode, 0);
            assert.equal(reference.stderr, '');
            const report = parseCoreLfProofAgentBenchmarkReportText(
                reference.stdout
            );
            assert.deepEqual(report.metrics.outcomes, {
                abstained: 1,
                acceptedComplete: 9,
                acceptedIncomplete: 0,
                rejected: 0
            });
            assert.equal(
                reference.stdout,
                serializeCoreLfProofAgentBenchmarkReport(report)
            );
        });

    it('reads one explicit run, strictly parses it, and freshly evaluates',
        () => {
            const corpus = createCoreLfProofAgentPublicCorpus();
            const runText = serializeCoreLfProofAgentBenchmarkRun(
                corpus.referenceReport.run
            );
            const result = runCli(
                ['evaluate', '--run-file', 'run.json'],
                Buffer.from(runText, 'utf8')
            );
            assert.equal(result.exitCode, 0);
            assert.equal(result.stderr, '');
            assert.deepEqual(result.reads, ['/benchmark-project/run.json']);
            const report = parseCoreLfProofAgentBenchmarkReportText(
                result.stdout
            );
            assert.deepEqual(report.metrics.outcomes, {
                abstained: 1,
                acceptedComplete: 9,
                acceptedIncomplete: 0,
                rejected: 0
            });
            assert.equal(report.artifactCurrent, false);
            assert.equal(report.materializesUpdatedSource, false);
        });

    it('checks raw size and fatal UTF-8 before canonical run parsing', () => {
        const oversized = runCli(
            ['evaluate', '--run-file=large.json'],
            () => new Uint8Array(
                CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE
                    .maximumRunInputBytes + 1
            )
        );
        assert.equal(oversized.exitCode, 2);
        assert.equal(oversized.stdout, '');
        assert.deepEqual(oversized.reads, ['/benchmark-project/large.json']);
        assert.equal(parseError(oversized).code, 'RUN_INPUT_TOO_LARGE');

        const invalidUtf8 = runCli(
            ['evaluate', '--run-file', 'invalid.json'],
            Uint8Array.from([0xff])
        );
        assert.equal(invalidUtf8.exitCode, 2);
        assert.equal(parseError(invalidUtf8).code, 'RUN_INPUT_INVALID_UTF8');

        const corpus = createCoreLfProofAgentPublicCorpus();
        const noncanonical = serializeCoreLfProofAgentBenchmarkRun(
            corpus.referenceReport.run
        ).trimEnd();
        const invalidArtifact = runCli(
            ['evaluate', '--run-file', 'run.json'],
            Buffer.from(noncanonical, 'utf8')
        );
        assert.equal(invalidArtifact.exitCode, 2);
        assert.equal(parseError(invalidArtifact).code, 'RUN_ARTIFACT_INVALID');
    });

    it('reports stable content-free usage, case, file, and evaluation errors',
        () => {
            const invalid = runCli(['unknown']);
            assert.equal(invalid.exitCode, 2);
            assert.equal(invalid.stdout, '');
            assert.equal(parseError(invalid).code, 'INVALID_ARGUMENT');

            const unknownCase = runCli(['case', '--case', 'missing']);
            assert.equal(unknownCase.exitCode, 2);
            assert.equal(parseError(unknownCase).code, 'UNKNOWN_CASE');

            const unreadable = runCli(['evaluate', '--run-file', 'none']);
            assert.equal(unreadable.exitCode, 2);
            assert.equal(parseError(unreadable).code, 'RUN_FILE_READ_FAILED');

            const corpus = createCoreLfProofAgentPublicCorpus();
            const incompleteRun = createCoreLfProofAgentBenchmarkRun({
                revision: 'partial-evaluation-run-1',
                provider: { id: 'partial', revision: 'partial-1' },
                allowedProfiles: ['explicit'],
                seed: 'fixed',
                attempts: [corpus.referenceReport.run.attempts[0]]
            });
            const failedEvaluation = runCli(
                ['evaluate', '--run-file', 'partial.json'],
                Buffer.from(
                    serializeCoreLfProofAgentBenchmarkRun(incompleteRun),
                    'utf8'
                )
            );
            assert.equal(failedEvaluation.exitCode, 2);
            assert.equal(
                parseError(failedEvaluation).code,
                'BENCHMARK_EVALUATION_FAILED'
            );

            for (const result of [
                invalid,
                unknownCase,
                unreadable,
                failedEvaluation
            ]) {
                const error = parseError(result);
                assert.equal(error.includesStack, false);
                assert.equal(error.includesArtifactContents, false);
                assert.doesNotMatch(result.stderr, /previousSourceText|at /u);
            }
        });

    it('keeps the public entry browser-safe and the Node adapter outer', () => {
        const packageEntry = readFileSync(resolve(
            repositoryRoot,
            'src/v3_2/package_benchmark.ts'
        ), 'utf8');
        const cli = readFileSync(resolve(
            repositoryRoot,
            'src/v3_2/lf_proof_agent_benchmark_cli.ts'
        ), 'utf8');
        const dispatcher = readFileSync(resolve(
            repositoryRoot,
            'scripts/emdash'
        ), 'utf8');
        assert.doesNotMatch(packageEntry, /node:/u);
        assert.doesNotMatch(packageEntry, /benchmark_cli/u);
        assert.match(cli, /from 'node:fs'/u);
        assert.match(dispatcher, /v3_2_proof_agent_benchmark_cli\.ts/u);
        assert.equal(
            CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.publishedAsNpmBin,
            false
        );
        assert.equal(
            CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.spawnsProvider,
            false
        );
        assert.equal(
            CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.invokesModel,
            false
        );
        assert.equal(
            CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.retainsSessionState,
            false
        );
    });

    it('dispatches the explicit repository command without an npm bin', () => {
        const result = spawnSync(
            resolve(repositoryRoot, 'scripts/emdash'),
            ['benchmark', 'catalog', '--format', 'text'],
            {
                cwd: repositoryRoot,
                encoding: 'utf8'
            }
        );
        assert.equal(result.status, 0, result.stderr);
        assert.equal(result.stderr, '');
        assert.match(result.stdout, /proof-agent benchmark: 10 cases/u);
        assert.match(result.stdout, /tracks: 6/u);
        assert.match(
            result.stdout,
            /reference baseline: 9 accepted-complete, 1 abstained/u
        );
        assert.match(result.stdout, /not proofs/u);
    });
});
