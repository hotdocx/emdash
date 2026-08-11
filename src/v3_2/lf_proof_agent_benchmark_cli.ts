/** Stateless Node adapter for the public LF proof-agent benchmark. */

import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import {
    CoreLfProofAgentBenchmarkCase,
    CoreLfProofAgentBenchmarkReport,
    evaluateCoreLfProofAgentBenchmarkRun,
    serializeCoreLfProofAgentBenchmarkCase,
    serializeCoreLfProofAgentBenchmarkReport
} from './lf_proof_agent_benchmark';
import {
    CoreLfProofAgentInterchangeError,
    parseCoreLfProofAgentBenchmarkRunText
} from './lf_proof_agent_interchange';
import {
    CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE,
    CoreLfProofAgentPublicCorpus,
    CoreLfProofAgentPublicCorpusEntry,
    CoreLfProofAgentPublicCorpusError,
    createCoreLfProofAgentPublicCorpus,
    serializeCoreLfProofAgentPublicCorpus
} from './lf_proof_agent_public_corpus';
import {
    CoreLfProofAgentBenchmarkError
} from './lf_proof_agent_benchmark';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE = Object.freeze({
    revision: 'emdash-lf-proof-agent-benchmark-cli-v1' as const,
    catalogRevision:
        'emdash-lf-proof-agent-benchmark-catalog-v1' as const,
    errorRevision:
        'emdash-lf-proof-agent-benchmark-cli-error-v1' as const,
    command: 'benchmark' as const,
    defaultFormat: 'jsonl' as const,
    maximumRunInputBytes: 33554432,
    performsFileIo: true as const,
    writesFiles: false as const,
    scansDirectories: false as const,
    spawnsProvider: false as const,
    invokesModel: false as const,
    accessesNetwork: false as const,
    retainsSessionState: false as const,
    enforcesReportedResourceLimits: false as const,
    publishedAsNpmBin: false as const
});

export type CoreLfProofAgentBenchmarkCliFormat = 'jsonl' | 'text';

export type CoreLfProofAgentBenchmarkCliCommand =
    | 'catalog'
    | 'case'
    | 'corpus'
    | 'reference'
    | 'evaluate';

export type CoreLfProofAgentBenchmarkCliErrorCode =
    | 'INVALID_ARGUMENT'
    | 'UNKNOWN_CASE'
    | 'RUN_FILE_READ_FAILED'
    | 'RUN_INPUT_TOO_LARGE'
    | 'RUN_INPUT_INVALID_UTF8'
    | 'RUN_ARTIFACT_INVALID'
    | 'BENCHMARK_EVALUATION_FAILED'
    | 'INTERNAL_ERROR';

export interface CoreLfProofAgentBenchmarkCliErrorRecord {
    readonly revision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.errorRevision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.revision;
    readonly code: CoreLfProofAgentBenchmarkCliErrorCode;
    readonly command: CoreLfProofAgentBenchmarkCliCommand | null;
    readonly message: string;
    readonly includesStack: false;
    readonly includesArtifactContents: false;
}

export interface CoreLfProofAgentBenchmarkCatalogEntry {
    readonly id: string;
    readonly track: CoreLfProofAgentPublicCorpusEntry['track'];
    readonly origin: CoreLfProofAgentPublicCorpusEntry['origin'];
    readonly sourceOwner: string;
    readonly referenceOwner: string;
    readonly features: readonly string[];
    readonly expectedReferenceOutcome:
        CoreLfProofAgentPublicCorpusEntry['expectedReferenceOutcome'];
    readonly actualReferenceOutcome:
        CoreLfProofAgentPublicCorpusEntry['actualReferenceOutcome'];
    readonly ownerEvidenceKind:
        CoreLfProofAgentPublicCorpusEntry['ownerEvidence']['kind'];
    readonly ownerRevision: string;
}

export interface CoreLfProofAgentBenchmarkCatalog {
    readonly revision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.catalogRevision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.revision;
    readonly corpusRevision:
        typeof CORE_LF_PROOF_AGENT_PUBLIC_CORPUS_PROFILE.revision;
    readonly tracks: CoreLfProofAgentPublicCorpus['tracks'];
    readonly entries: readonly CoreLfProofAgentBenchmarkCatalogEntry[];
    readonly referenceOutcomes:
        CoreLfProofAgentBenchmarkReport['metrics']['outcomes'];
    readonly caseTextIncluded: false;
    readonly artifactIsBenchmarkTask: false;
    readonly artifactIsProofAuthority: false;
    readonly referenceAttemptsAreProofAuthority: false;
    readonly modelPerformanceClaimed: false;
    readonly meaning:
        'compact-derived-catalog-not-benchmark-input-or-proof-authority';
}

export interface CoreLfProofAgentBenchmarkCliIo {
    readonly cwd?: () => string;
    readonly readFileBytes?: (absolutePath: string) => Uint8Array;
    readonly stdout?: (text: string) => void;
    readonly stderr?: (text: string) => void;
}

interface ParsedCommand {
    readonly command: CoreLfProofAgentBenchmarkCliCommand;
    readonly format: CoreLfProofAgentBenchmarkCliFormat;
    readonly caseId: string | null;
    readonly runFile: string | null;
}

export const CORE_LF_PROOF_AGENT_BENCHMARK_CLI_USAGE = [
    'usage:',
    '  ./scripts/emdash benchmark catalog [--format jsonl|text]',
    '  ./scripts/emdash benchmark case --case ID [--format jsonl|text]',
    '  ./scripts/emdash benchmark corpus [--format jsonl|text]',
    '  ./scripts/emdash benchmark reference [--format jsonl|text]',
    '  ./scripts/emdash benchmark evaluate --run-file PATH ' +
        '[--format jsonl|text]'
].join('\n');

const deepFreeze = <T>(value: T): T => {
    if (value !== null && typeof value === 'object') {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        if (!Object.isFrozen(value)) Object.freeze(value);
    }
    return value;
};

const cliErrorMessages: Readonly<
Record<CoreLfProofAgentBenchmarkCliErrorCode, string>
> = Object.freeze({
    INVALID_ARGUMENT: 'The benchmark command arguments are invalid',
    UNKNOWN_CASE: 'The requested benchmark case does not exist',
    RUN_FILE_READ_FAILED: 'The canonical run file could not be read',
    RUN_INPUT_TOO_LARGE: 'The canonical run file exceeds the byte limit',
    RUN_INPUT_INVALID_UTF8: 'The canonical run file is not valid UTF-8',
    RUN_ARTIFACT_INVALID: 'The canonical run artifact is invalid or stale',
    BENCHMARK_EVALUATION_FAILED:
        'The benchmark run could not be freshly evaluated',
    INTERNAL_ERROR: 'The benchmark command failed internally'
});

class CliFailure extends Error {
    constructor(
        public readonly code: CoreLfProofAgentBenchmarkCliErrorCode,
        public readonly command: CoreLfProofAgentBenchmarkCliCommand | null
    ) {
        super(cliErrorMessages[code]);
        this.name = 'CoreLfProofAgentBenchmarkCliFailure';
    }
}

const fail = (
    code: CoreLfProofAgentBenchmarkCliErrorCode,
    command: CoreLfProofAgentBenchmarkCliCommand | null
): never => {
    throw new CliFailure(code, command);
};

const parseFormat = (
    value: string,
    command: CoreLfProofAgentBenchmarkCliCommand
): CoreLfProofAgentBenchmarkCliFormat => {
    if (value === 'jsonl' || value === 'text') return value;
    return fail('INVALID_ARGUMENT', command);
};

const optionValue = (
    argv: readonly string[],
    index: number,
    command: CoreLfProofAgentBenchmarkCliCommand
): string => {
    const value = argv[index + 1];
    if (value === undefined || value.length === 0 || value.startsWith('--')) {
        return fail('INVALID_ARGUMENT', command);
    }
    return value;
};

const parseCommand = (argv: readonly string[]): ParsedCommand => {
    const command = argv[0];
    if (
        command !== 'catalog' &&
        command !== 'case' &&
        command !== 'corpus' &&
        command !== 'reference' &&
        command !== 'evaluate'
    ) {
        return fail('INVALID_ARGUMENT', null);
    }
    let format: CoreLfProofAgentBenchmarkCliFormat =
        CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.defaultFormat;
    let caseId: string | null = null;
    let runFile: string | null = null;
    let formatSeen = false;
    for (let index = 1; index < argv.length; index++) {
        const argument = argv[index];
        if (argument === '--format') {
            if (formatSeen) return fail('INVALID_ARGUMENT', command);
            format = parseFormat(
                optionValue(argv, index, command),
                command
            );
            formatSeen = true;
            index++;
            continue;
        }
        if (argument.startsWith('--format=')) {
            if (formatSeen) return fail('INVALID_ARGUMENT', command);
            format = parseFormat(
                argument.slice('--format='.length),
                command
            );
            formatSeen = true;
            continue;
        }
        if (argument === '--case') {
            if (caseId !== null) return fail('INVALID_ARGUMENT', command);
            caseId = optionValue(argv, index, command);
            index++;
            continue;
        }
        if (argument.startsWith('--case=')) {
            if (caseId !== null) return fail('INVALID_ARGUMENT', command);
            caseId = argument.slice('--case='.length);
            if (caseId.length === 0) return fail('INVALID_ARGUMENT', command);
            continue;
        }
        if (argument === '--run-file') {
            if (runFile !== null) return fail('INVALID_ARGUMENT', command);
            runFile = optionValue(argv, index, command);
            index++;
            continue;
        }
        if (argument.startsWith('--run-file=')) {
            if (runFile !== null) return fail('INVALID_ARGUMENT', command);
            runFile = argument.slice('--run-file='.length);
            if (runFile.length === 0) {
                return fail('INVALID_ARGUMENT', command);
            }
            continue;
        }
        return fail('INVALID_ARGUMENT', command);
    }
    if (
        (command === 'case') !== (caseId !== null) ||
        (command === 'evaluate') !== (runFile !== null)
    ) {
        return fail('INVALID_ARGUMENT', command);
    }
    return Object.freeze({ command, format, caseId, runFile });
};

/** Derive the compact, non-authoritative catalog from a freshly built corpus. */
export function createCoreLfProofAgentBenchmarkCatalog(
    corpus: CoreLfProofAgentPublicCorpus =
        createCoreLfProofAgentPublicCorpus()
): CoreLfProofAgentBenchmarkCatalog {
    return deepFreeze({
        revision:
            CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.catalogRevision,
        profileRevision:
            CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.revision,
        corpusRevision: corpus.revision,
        tracks: corpus.tracks,
        entries: corpus.entries.map(entry => ({
            id: entry.id,
            track: entry.track,
            origin: entry.origin,
            sourceOwner: entry.sourceOwner,
            referenceOwner: entry.referenceOwner,
            features: entry.features,
            expectedReferenceOutcome: entry.expectedReferenceOutcome,
            actualReferenceOutcome: entry.actualReferenceOutcome,
            ownerEvidenceKind: entry.ownerEvidence.kind,
            ownerRevision: entry.ownerEvidence.ownerRevision
        })),
        referenceOutcomes: corpus.referenceReport.metrics.outcomes,
        caseTextIncluded: false as const,
        artifactIsBenchmarkTask: false as const,
        artifactIsProofAuthority: false as const,
        referenceAttemptsAreProofAuthority: false as const,
        modelPerformanceClaimed: false as const,
        meaning:
            'compact-derived-catalog-not-benchmark-input-or-proof-authority' as const
    });
}

export const serializeCoreLfProofAgentBenchmarkCatalog = (
    catalog: CoreLfProofAgentBenchmarkCatalog
): string => serializeCoreLfWorkspaceCanonicalJson(
    catalog,
    'proofAgentBenchmarkCatalog'
);

export const createCoreLfProofAgentBenchmarkCliError = (
    code: CoreLfProofAgentBenchmarkCliErrorCode,
    command: CoreLfProofAgentBenchmarkCliCommand | null
): CoreLfProofAgentBenchmarkCliErrorRecord => deepFreeze({
    revision: CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.errorRevision,
    profileRevision: CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.revision,
    code,
    command,
    message: cliErrorMessages[code],
    includesStack: false as const,
    includesArtifactContents: false as const
});

export const serializeCoreLfProofAgentBenchmarkCliError = (
    error: CoreLfProofAgentBenchmarkCliErrorRecord
): string => serializeCoreLfWorkspaceCanonicalJson(
    error,
    'proofAgentBenchmarkCliError'
);

const formatCatalog = (catalog: CoreLfProofAgentBenchmarkCatalog): string => {
    const outcomes = catalog.referenceOutcomes;
    const lines = [
        `emdash proof-agent benchmark: ${catalog.entries.length} cases`,
        `tracks: ${catalog.tracks.length}`,
        'reference baseline: ' +
            `${outcomes.acceptedComplete} accepted-complete, ` +
            `${outcomes.abstained} abstained`,
        'authority: derived catalog and reference attempts are not proofs',
        ''
    ];
    catalog.entries.forEach(entry => {
        lines.push(`${entry.id} [${entry.track}]`);
        lines.push(
            `  ${entry.actualReferenceOutcome}; ${entry.ownerEvidenceKind}`
        );
    });
    return `${lines.join('\n')}\n`;
};

const formatCase = (
    benchmarkCase: CoreLfProofAgentBenchmarkCase,
    entry: CoreLfProofAgentBenchmarkCatalogEntry
): string => [
    `case: ${benchmarkCase.id}`,
    `track: ${entry.track}`,
    `origin: ${entry.origin}`,
    `proof: ${benchmarkCase.proof.moduleId}.${benchmarkCase.proof.declarationId}`,
    `goal: ${benchmarkCase.goalId}`,
    `relevant premises: ${benchmarkCase.relevantPremises.length}`,
    'authority: this text view is not the canonical benchmark case',
    ''
].join('\n');

const formatReport = (report: CoreLfProofAgentBenchmarkReport): string => {
    const outcomes = report.metrics.outcomes;
    return [
        `provider: ${report.run.provider.id}@${report.run.provider.revision}`,
        `cases: ${report.metrics.cases}`,
        `accepted-complete: ${outcomes.acceptedComplete}`,
        `accepted-incomplete: ${outcomes.acceptedIncomplete}`,
        `rejected: ${outcomes.rejected}`,
        `abstained: ${outcomes.abstained}`,
        'authority: freshly evaluated attempts; source was not committed',
        ''
    ].join('\n');
};

const defaultCwd = (): string => process.cwd();
const defaultReadFileBytes = (absolutePath: string): Uint8Array =>
    readFileSync(absolutePath);
const defaultStdout = (text: string): void => { process.stdout.write(text); };
const defaultStderr = (text: string): void => { process.stderr.write(text); };

const decodeRunFile = (
    runFile: string,
    command: CoreLfProofAgentBenchmarkCliCommand,
    io: Required<Pick<CoreLfProofAgentBenchmarkCliIo, 'cwd' | 'readFileBytes'>>
): string => {
    let bytes: Uint8Array;
    try {
        bytes = io.readFileBytes(resolve(io.cwd(), runFile));
    } catch {
        return fail('RUN_FILE_READ_FAILED', command);
    }
    if (
        bytes.byteLength >
            CORE_LF_PROOF_AGENT_BENCHMARK_CLI_PROFILE.maximumRunInputBytes
    ) {
        return fail('RUN_INPUT_TOO_LARGE', command);
    }
    try {
        return new TextDecoder('utf-8', { fatal: true }).decode(bytes);
    } catch {
        return fail('RUN_INPUT_INVALID_UTF8', command);
    }
};

const findCase = (
    corpus: CoreLfProofAgentPublicCorpus,
    caseId: string,
    command: CoreLfProofAgentBenchmarkCliCommand
): {
    readonly benchmarkCase: CoreLfProofAgentBenchmarkCase;
    readonly entry: CoreLfProofAgentBenchmarkCatalogEntry;
} => {
    const benchmarkCase = corpus.referenceReport.suite.cases.find(entry =>
        entry.id === caseId
    );
    const catalogEntry = createCoreLfProofAgentBenchmarkCatalog(corpus)
        .entries.find(entry => entry.id === caseId);
    if (benchmarkCase === undefined || catalogEntry === undefined) {
        return fail('UNKNOWN_CASE', command);
    }
    return { benchmarkCase, entry: catalogEntry };
};

const execute = (
    parsed: ParsedCommand,
    io: Required<Pick<CoreLfProofAgentBenchmarkCliIo, 'cwd' | 'readFileBytes'>>
): string => {
    if (parsed.command === 'evaluate') {
        const text = decodeRunFile(parsed.runFile as string, parsed.command, io);
        let run;
        try {
            run = parseCoreLfProofAgentBenchmarkRunText(text);
        } catch (error: unknown) {
            if (error instanceof CoreLfProofAgentInterchangeError) {
                return fail('RUN_ARTIFACT_INVALID', parsed.command);
            }
            throw error;
        }
        let report: CoreLfProofAgentBenchmarkReport;
        try {
            const corpus = createCoreLfProofAgentPublicCorpus();
            report = evaluateCoreLfProofAgentBenchmarkRun({
                suite: corpus.referenceReport.suite,
                run
            });
        } catch (error: unknown) {
            if (
                error instanceof CoreLfProofAgentBenchmarkError ||
                error instanceof CoreLfProofAgentPublicCorpusError
            ) {
                return fail('BENCHMARK_EVALUATION_FAILED', parsed.command);
            }
            throw error;
        }
        return parsed.format === 'jsonl'
            ? serializeCoreLfProofAgentBenchmarkReport(report)
            : formatReport(report);
    }

    const corpus = createCoreLfProofAgentPublicCorpus();
    if (parsed.command === 'catalog') {
        const catalog = createCoreLfProofAgentBenchmarkCatalog(corpus);
        return parsed.format === 'jsonl'
            ? serializeCoreLfProofAgentBenchmarkCatalog(catalog)
            : formatCatalog(catalog);
    }
    if (parsed.command === 'case') {
        const selected = findCase(
            corpus,
            parsed.caseId as string,
            parsed.command
        );
        return parsed.format === 'jsonl'
            ? serializeCoreLfProofAgentBenchmarkCase(selected.benchmarkCase)
            : formatCase(selected.benchmarkCase, selected.entry);
    }
    if (parsed.command === 'corpus') {
        return parsed.format === 'jsonl'
            ? serializeCoreLfProofAgentPublicCorpus(corpus)
            : formatCatalog(createCoreLfProofAgentBenchmarkCatalog(corpus));
    }
    return parsed.format === 'jsonl'
        ? serializeCoreLfProofAgentBenchmarkReport(corpus.referenceReport)
        : formatReport(corpus.referenceReport);
};

/** Execute one explicit artifact command without invoking an agent/provider. */
export function runCoreLfProofAgentBenchmarkCli(
    argv: readonly string[],
    io: CoreLfProofAgentBenchmarkCliIo = {}
): number {
    const writeStdout = io.stdout ?? defaultStdout;
    const writeStderr = io.stderr ?? defaultStderr;
    let command: CoreLfProofAgentBenchmarkCliCommand | null = null;
    try {
        const parsed = parseCommand(argv);
        command = parsed.command;
        const output = execute(parsed, {
            cwd: io.cwd ?? defaultCwd,
            readFileBytes: io.readFileBytes ?? defaultReadFileBytes
        });
        writeStdout(output);
        return 0;
    } catch (error: unknown) {
        const failure = error instanceof CliFailure
            ? error
            : new CliFailure('INTERNAL_ERROR', command);
        writeStderr(serializeCoreLfProofAgentBenchmarkCliError(
            createCoreLfProofAgentBenchmarkCliError(
                failure.code,
                failure.command
            )
        ));
        return 2;
    }
}
