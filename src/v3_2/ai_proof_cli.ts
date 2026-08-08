/** Node-owned local command adapter for the first AI-native proof module. */

import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import {
    CORE_AI_PROOF_DEMO_SOURCE_PATH,
    compileCoreAiProofDemo,
    createCoreAiProofDemoFingerprint
} from './ai_proof_demo';
import {
    assertCoreProofArtifactCurrent,
    formatCoreProofArtifact,
    serializeCoreProofArtifactJsonl,
    serializeCoreProofDocumentProfile
} from './proof_document';

export type CoreAiProofCliCommand = 'check' | 'goals';
export type CoreAiProofCliFormat = 'jsonl' | 'text';

export interface CoreAiProofCliIo {
    readonly readText?: (absolutePath: string) => string;
    readonly stdout?: (text: string) => void;
    readonly stderr?: (text: string) => void;
}

interface ParsedCommand {
    readonly command: CoreAiProofCliCommand;
    readonly declarationId: string;
    readonly format: CoreAiProofCliFormat;
}

export const CORE_AI_PROOF_CLI_USAGE =
    'usage: ./scripts/emdash ' +
    '<check|goals> [declaration] [--format jsonl|text]';

export const coreAiProofSha256 = (value: string): string =>
    'sha256:' + createHash('sha256').update(value).digest('hex');

const parseFormat = (value: string): CoreAiProofCliFormat => {
    if (value === 'jsonl' || value === 'text') return value;
    throw new Error(
        `Unknown AI proof output format '${value}'; expected jsonl or text`
    );
};

const parseCommand = (argv: readonly string[]): ParsedCommand => {
    const command = argv[0];
    if (command !== 'check' && command !== 'goals') {
        throw new Error(CORE_AI_PROOF_CLI_USAGE);
    }

    let declarationId = command === 'check'
        ? 'complete_identity'
        : 'open_identity';
    let declarationSupplied = false;
    let format: CoreAiProofCliFormat = 'jsonl';

    for (let index = 1; index < argv.length; index++) {
        const argument = argv[index];
        if (argument === '--format') {
            const value = argv[index + 1];
            if (!value) throw new Error('Missing value after --format');
            format = parseFormat(value);
            index++;
            continue;
        }
        if (argument.startsWith('--format=')) {
            format = parseFormat(argument.slice('--format='.length));
            continue;
        }
        if (argument.startsWith('-')) {
            throw new Error(`Unknown AI proof option '${argument}'`);
        }
        if (declarationSupplied) {
            throw new Error(
                `Unexpected extra AI proof declaration '${argument}'`
            );
        }
        declarationId = argument;
        declarationSupplied = true;
    }

    return Object.freeze({ command, declarationId, format });
};

const defaultReadText = (absolutePath: string): string =>
    readFileSync(absolutePath, 'utf8');

const defaultStdout = (text: string): void => {
    process.stdout.write(text);
};

const defaultStderr = (text: string): void => {
    process.stderr.write(text);
};

/**
 * Run one command without retaining the checker session or writing artifacts.
 * The return value is suitable for `process.exitCode`.
 */
export function runCoreAiProofCli(
    argv: readonly string[],
    io: CoreAiProofCliIo = {}
): number {
    const readText = io.readText ?? defaultReadText;
    const writeStdout = io.stdout ?? defaultStdout;
    const writeStderr = io.stderr ?? defaultStderr;

    try {
        const parsed = parseCommand(argv);
        const repositoryRoot = path.resolve(__dirname, '../..');
        const sourcePath = path.join(
            repositoryRoot,
            CORE_AI_PROOF_DEMO_SOURCE_PATH
        );
        const sourceSha256 = coreAiProofSha256(readText(sourcePath));
        const profileSha256 = coreAiProofSha256(
            serializeCoreProofDocumentProfile()
        );
        const fingerprint = createCoreAiProofDemoFingerprint(
            sourceSha256,
            profileSha256
        );
        const compilation = compileCoreAiProofDemo(
            parsed.declarationId,
            fingerprint
        );
        assertCoreProofArtifactCurrent(
            compilation.artifact,
            fingerprint
        );

        const output = parsed.format === 'jsonl'
            ? serializeCoreProofArtifactJsonl(compilation.artifact)
            : `${formatCoreProofArtifact(compilation.artifact)}\n`;
        writeStdout(output);

        if (
            parsed.command === 'check' &&
            compilation.artifact.state.status !== 'complete'
        ) {
            writeStderr(
                `${compilation.artifact.moduleId}.` +
                `${compilation.artifact.declarationId}: ` +
                'proof is incomplete\n'
            );
            return 1;
        }
        return 0;
    } catch (error: unknown) {
        const message = error instanceof Error
            ? error.message
            : String(error);
        writeStderr(`emdash: ${message}\n`);
        return 2;
    }
}
