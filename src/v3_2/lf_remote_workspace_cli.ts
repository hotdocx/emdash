/** Node-owned local command adapter for mounted remote LF workspaces. */

import {
    CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE,
    CoreLfMountedRemoteWorkspaceResult,
    materializeCoreLfMountedRemoteWorkspace,
    materializeCoreLfMountedRemoteWorkspaceOffline
} from './lf_remote_workspace_store';

export const CORE_LF_REMOTE_WORKSPACE_CLI_PROFILE = Object.freeze({
    revision: 'emdash-lf-remote-workspace-cli-v1' as const,
    recordRevision: 'emdash-lf-workspace-check-record-v1' as const,
    command: 'workspace check' as const,
    backend:
        CORE_LF_MOUNTED_REMOTE_WORKSPACE_STORE_PROFILE.backend,
    defaultFormat: 'jsonl' as const,
    requiresExplicitRoots: true as const,
    supportsOffline: true as const,
    supportsBackendSelection: false as const,
    performsRootDiscovery: false as const,
    regeneratesLocks: false as const,
    performsTransport: false as const,
    invokesLambdapi: false as const
});

export type CoreLfRemoteWorkspaceCliFormat = 'jsonl' | 'text';

export interface CoreLfRemoteWorkspaceCliIo {
    readonly stdout?: (text: string) => void;
    readonly stderr?: (text: string) => void;
}

export interface CoreLfRemoteWorkspaceCheckRecord {
    readonly revision:
        typeof CORE_LF_REMOTE_WORKSPACE_CLI_PROFILE.recordRevision;
    readonly kind: 'workspace-check';
    readonly status: 'verified';
    readonly backend:
        typeof CORE_LF_REMOTE_WORKSPACE_CLI_PROFILE.backend;
    readonly mode: CoreLfMountedRemoteWorkspaceResult['mode'];
    readonly cacheDisposition:
        CoreLfMountedRemoteWorkspaceResult['cacheDisposition'];
    readonly logicalWorkspaceId: string;
    readonly workspaceRevision: string;
    readonly moduleIds: readonly string[];
    readonly sourceSha256: string;
    readonly compiledSha256: string;
    readonly cacheKey: string;
}

interface ParsedWorkspaceCommand {
    readonly projectRoot: string;
    readonly dataRoot: string;
    readonly offline: boolean;
    readonly format: CoreLfRemoteWorkspaceCliFormat;
}

export const CORE_LF_REMOTE_WORKSPACE_CLI_USAGE =
    'usage: ./scripts/emdash workspace check ' +
    '--project-root ABSOLUTE_PATH --data-root ABSOLUTE_PATH ' +
    '[--offline] [--format jsonl|text]';

const parseFormat = (value: string): CoreLfRemoteWorkspaceCliFormat => {
    if (value === 'jsonl' || value === 'text') return value;
    throw new Error(
        `Unknown workspace output format '${value}'; expected jsonl or text`
    );
};

const optionValue = (
    argv: readonly string[],
    index: number,
    option: string
): string => {
    const value = argv[index + 1];
    if (value === undefined || value.length === 0 || value.startsWith('--')) {
        throw new Error(`Missing value after ${option}`);
    }
    return value;
};

const parseCommand = (
    argv: readonly string[]
): ParsedWorkspaceCommand => {
    if (argv[0] !== 'check') {
        throw new Error(CORE_LF_REMOTE_WORKSPACE_CLI_USAGE);
    }

    let projectRoot: string | undefined;
    let dataRoot: string | undefined;
    let offline = false;
    let format: CoreLfRemoteWorkspaceCliFormat =
        CORE_LF_REMOTE_WORKSPACE_CLI_PROFILE.defaultFormat;
    let formatSeen = false;

    for (let index = 1; index < argv.length; index++) {
        const argument = argv[index];
        if (argument === '--project-root') {
            if (projectRoot !== undefined) {
                throw new Error('Duplicate --project-root option');
            }
            projectRoot = optionValue(argv, index, argument);
            index++;
            continue;
        }
        if (argument.startsWith('--project-root=')) {
            if (projectRoot !== undefined) {
                throw new Error('Duplicate --project-root option');
            }
            projectRoot = argument.slice('--project-root='.length);
            if (projectRoot.length === 0) {
                throw new Error('Missing value after --project-root');
            }
            continue;
        }
        if (argument === '--data-root') {
            if (dataRoot !== undefined) {
                throw new Error('Duplicate --data-root option');
            }
            dataRoot = optionValue(argv, index, argument);
            index++;
            continue;
        }
        if (argument.startsWith('--data-root=')) {
            if (dataRoot !== undefined) {
                throw new Error('Duplicate --data-root option');
            }
            dataRoot = argument.slice('--data-root='.length);
            if (dataRoot.length === 0) {
                throw new Error('Missing value after --data-root');
            }
            continue;
        }
        if (argument === '--offline') {
            if (offline) throw new Error('Duplicate --offline option');
            offline = true;
            continue;
        }
        if (argument === '--format') {
            if (formatSeen) throw new Error('Duplicate --format option');
            format = parseFormat(optionValue(argv, index, argument));
            formatSeen = true;
            index++;
            continue;
        }
        if (argument.startsWith('--format=')) {
            if (formatSeen) throw new Error('Duplicate --format option');
            format = parseFormat(argument.slice('--format='.length));
            formatSeen = true;
            continue;
        }
        throw new Error(`Unknown workspace option '${argument}'`);
    }

    if (projectRoot === undefined || dataRoot === undefined) {
        throw new Error(CORE_LF_REMOTE_WORKSPACE_CLI_USAGE);
    }
    return Object.freeze({
        projectRoot,
        dataRoot,
        offline,
        format
    });
};

/** Project one verified materialization into compact path-free machine data. */
export function createCoreLfRemoteWorkspaceCheckRecord(
    result: CoreLfMountedRemoteWorkspaceResult
): CoreLfRemoteWorkspaceCheckRecord {
    const artifact = result.materialized.lock.artifact;
    return Object.freeze({
        revision: CORE_LF_REMOTE_WORKSPACE_CLI_PROFILE.recordRevision,
        kind: 'workspace-check' as const,
        status: 'verified' as const,
        backend: CORE_LF_REMOTE_WORKSPACE_CLI_PROFILE.backend,
        mode: result.mode,
        cacheDisposition: result.cacheDisposition,
        logicalWorkspaceId: artifact.logicalWorkspaceId,
        workspaceRevision: artifact.workspaceRevision,
        moduleIds: Object.freeze([
            ...result.materialized.source.plan.order
        ]),
        sourceSha256: artifact.sourceSha256,
        compiledSha256: artifact.compiledSha256,
        cacheKey: result.cacheKey
    });
}

export const serializeCoreLfRemoteWorkspaceCheckRecord = (
    record: CoreLfRemoteWorkspaceCheckRecord
): string => `${JSON.stringify(record)}\n`;

export const formatCoreLfRemoteWorkspaceCheckRecord = (
    record: CoreLfRemoteWorkspaceCheckRecord
): string => [
    `${record.logicalWorkspaceId}@${record.workspaceRevision}: verified`,
    `backend ${record.backend}`,
    `modules ${record.moduleIds.length}: ${record.moduleIds.join(', ')}`,
    `cache ${record.mode}/${record.cacheDisposition}: ${record.cacheKey}`
].join('\n') + '\n';

const defaultStdout = (text: string): void => {
    process.stdout.write(text);
};

const defaultStderr = (text: string): void => {
    process.stderr.write(text);
};

/** Run one workspace check without retaining state or discovering roots. */
export async function runCoreLfRemoteWorkspaceCli(
    argv: readonly string[],
    io: CoreLfRemoteWorkspaceCliIo = {}
): Promise<number> {
    const writeStdout = io.stdout ?? defaultStdout;
    const writeStderr = io.stderr ?? defaultStderr;

    try {
        const parsed = parseCommand(argv);
        const roots = {
            projectRoot: parsed.projectRoot,
            dataRoot: parsed.dataRoot
        };
        const result = parsed.offline
            ? await materializeCoreLfMountedRemoteWorkspaceOffline(roots)
            : await materializeCoreLfMountedRemoteWorkspace(roots);
        const record = createCoreLfRemoteWorkspaceCheckRecord(result);
        writeStdout(parsed.format === 'jsonl'
            ? serializeCoreLfRemoteWorkspaceCheckRecord(record)
            : formatCoreLfRemoteWorkspaceCheckRecord(record));
        return 0;
    } catch (error: unknown) {
        const message = error instanceof Error
            ? error.message
            : String(error);
        writeStderr(`emdash: ${message}\n`);
        return 2;
    }
}
