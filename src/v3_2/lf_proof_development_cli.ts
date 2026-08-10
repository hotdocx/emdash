/** Stateless Node command adapter for canonical proof developments. */

import {
    CoreProofPlanGoalSnapshot
} from './proof_plan';
import {
    CoreLfWorkspaceProofArtifact
} from './lf_workspace_proof';
import {
    CoreLfCompiledProofDevelopment,
    CoreLfProofDevelopmentArtifact,
    compileCoreLfProofDevelopment
} from './lf_proof_development';
import {
    CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE,
    CoreLfMountedProofDevelopmentResult,
    materializeCoreLfMountedProofDevelopment
} from './lf_proof_development_store';

export const CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE = Object.freeze({
    revision: 'emdash-lf-proof-development-cli-v2' as const,
    summaryRevision:
        'emdash-lf-proof-development-summary-v2' as const,
    goalRevision: 'emdash-lf-proof-development-goal-v2' as const,
    buildRevision: 'emdash-lf-proof-development-build-v2' as const,
    mountedProfileRevision:
        CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE.revision,
    commandNamespace: 'development' as const,
    commands: Object.freeze(['check', 'goals', 'build'] as const),
    backend: CORE_LF_MOUNTED_PROOF_DEVELOPMENT_PROFILE.backend,
    defaultFormat: 'jsonl' as const,
    requiresExplicitProjectRoot: true as const,
    retainsCheckerSession: false as const,
    performsRootDiscovery: false as const,
    acceptsBackendSelection: false as const,
    writesArtifacts: false as const,
    invokesLambdapi: false as const
});

export type CoreLfProofDevelopmentCliCommand =
    typeof CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE.commands[number];
export type CoreLfProofDevelopmentCliFormat = 'jsonl' | 'text';
export type CoreLfProofDevelopmentCliScope = 'development' | 'proof';

export interface CoreLfProofDevelopmentCliIo {
    readonly stdout?: (text: string) => void;
    readonly stderr?: (text: string) => void;
}

interface ParsedCommand {
    readonly command: CoreLfProofDevelopmentCliCommand;
    readonly projectRoot: string;
    readonly moduleId?: string;
    readonly declarationId?: string;
    readonly format: CoreLfProofDevelopmentCliFormat;
}

export interface CoreLfProofDevelopmentSummaryRecord {
    readonly revision:
        typeof CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE.summaryRevision;
    readonly kind: 'proof-development-summary';
    readonly command: CoreLfProofDevelopmentCliCommand;
    readonly backend:
        typeof CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE.backend;
    readonly scope: CoreLfProofDevelopmentCliScope;
    readonly status: 'complete' | 'incomplete';
    readonly sourceSha256: string;
    readonly developmentRevision: string;
    readonly moduleIds: readonly string[];
    readonly proofCount: number;
    readonly openGoalCount: number;
    readonly moduleId?: string;
    readonly declarationId?: string;
}

export interface CoreLfProofDevelopmentGoalRecord {
    readonly revision:
        typeof CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE.goalRevision;
    readonly kind: 'proof-development-goal';
    readonly moduleId: string;
    readonly declarationId: string;
    readonly goal: CoreProofPlanGoalSnapshot;
}

export interface CoreLfProofDevelopmentBuildRecord {
    readonly revision:
        typeof CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE.buildRevision;
    readonly kind: 'proof-development-build';
    readonly backend:
        typeof CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE.backend;
    readonly scope: CoreLfProofDevelopmentCliScope;
    readonly status: 'complete' | 'incomplete';
    readonly sourceSha256: string;
    readonly developmentRevision: string;
    readonly moduleId?: string;
    readonly declarationId?: string;
    readonly artifact:
        CoreLfProofDevelopmentArtifact | CoreLfWorkspaceProofArtifact;
}

interface SelectedDevelopment {
    readonly summary: CoreLfProofDevelopmentSummaryRecord;
    readonly goals: readonly CoreLfProofDevelopmentGoalRecord[];
    readonly artifact:
        CoreLfProofDevelopmentArtifact | CoreLfWorkspaceProofArtifact;
}

export const CORE_LF_PROOF_DEVELOPMENT_CLI_USAGE =
    'usage: ./scripts/emdash development <check|goals|build> ' +
    '--project-root ABSOLUTE_PATH ' +
    '[--module MODULE_ID --declaration DECLARATION_ID] ' +
    '[--format jsonl|text]';

const parseFormat = (value: string): CoreLfProofDevelopmentCliFormat => {
    if (value === 'jsonl' || value === 'text') return value;
    throw new Error(
        `Unknown proof-development output format '${value}'; ` +
            'expected jsonl or text'
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

const parseCommand = (argv: readonly string[]): ParsedCommand => {
    const command = argv[0];
    if (
        command !== 'check' &&
        command !== 'goals' &&
        command !== 'build'
    ) {
        throw new Error(CORE_LF_PROOF_DEVELOPMENT_CLI_USAGE);
    }

    let projectRoot: string | undefined;
    let moduleId: string | undefined;
    let declarationId: string | undefined;
    let format: CoreLfProofDevelopmentCliFormat =
        CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE.defaultFormat;
    let formatSeen = false;

    const assign = (
        option: '--project-root' | '--module' | '--declaration',
        value: string
    ): void => {
        if (value.length === 0) throw new Error(`Missing value after ${option}`);
        switch (option) {
            case '--project-root':
                if (projectRoot !== undefined) {
                    throw new Error('Duplicate --project-root option');
                }
                projectRoot = value;
                return;
            case '--module':
                if (moduleId !== undefined) {
                    throw new Error('Duplicate --module option');
                }
                moduleId = value;
                return;
            case '--declaration':
                if (declarationId !== undefined) {
                    throw new Error('Duplicate --declaration option');
                }
                declarationId = value;
                return;
            default: {
                const exhaustive: never = option;
                return exhaustive;
            }
        }
    };

    for (let index = 1; index < argv.length; index++) {
        const argument = argv[index];
        if (
            argument === '--project-root' ||
            argument === '--module' ||
            argument === '--declaration'
        ) {
            assign(argument, optionValue(argv, index, argument));
            index++;
            continue;
        }
        const valued = [
            '--project-root',
            '--module',
            '--declaration'
        ] as const;
        const match = valued.find(option =>
            argument.startsWith(`${option}=`)
        );
        if (match !== undefined) {
            assign(match, argument.slice(match.length + 1));
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
        throw new Error(`Unknown proof-development option '${argument}'`);
    }

    if (projectRoot === undefined) {
        throw new Error(CORE_LF_PROOF_DEVELOPMENT_CLI_USAGE);
    }
    if ((moduleId === undefined) !== (declarationId === undefined)) {
        throw new Error(
            '--module and --declaration must be supplied together'
        );
    }
    return Object.freeze({
        command,
        projectRoot,
        moduleId,
        declarationId,
        format
    });
};

const goalRecord = (
    moduleId: string,
    declarationId: string,
    goal: CoreProofPlanGoalSnapshot
): CoreLfProofDevelopmentGoalRecord => Object.freeze({
    revision: CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE.goalRevision,
    kind: 'proof-development-goal' as const,
    moduleId,
    declarationId,
    goal
});

const selectDevelopment = (
    command: CoreLfProofDevelopmentCliCommand,
    mounted: CoreLfMountedProofDevelopmentResult,
    development: CoreLfCompiledProofDevelopment,
    moduleId?: string,
    declarationId?: string
): SelectedDevelopment => {
    if (moduleId !== undefined && declarationId !== undefined) {
        const proof = development.proof(moduleId, declarationId);
        if (proof === undefined) {
            throw new Error(
                `Unknown proof '${moduleId}.${declarationId}'`
            );
        }
        const proofArtifact = proof.artifact.proofArtifact;
        const goals = Object.freeze(proofArtifact.state.goals.map(goal =>
            goalRecord(moduleId, declarationId, goal)
        ));
        return Object.freeze({
            summary: Object.freeze({
                revision:
                    CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE.summaryRevision,
                kind: 'proof-development-summary' as const,
                command,
                backend: mounted.backend,
                scope: 'proof' as const,
                status: proofArtifact.state.status,
                sourceSha256: mounted.sourceSha256,
                developmentRevision: development.plan.revision,
                moduleIds: Object.freeze([...proof.artifact.closure.order]),
                proofCount: 1,
                openGoalCount: goals.length,
                moduleId,
                declarationId
            }),
            goals,
            artifact: proof.artifact
        });
    }

    const goals = Object.freeze(development.goals.map(entry => goalRecord(
        entry.moduleId,
        entry.declarationId,
        entry.goal
    )));
    return Object.freeze({
        summary: Object.freeze({
            revision:
                CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE.summaryRevision,
            kind: 'proof-development-summary' as const,
            command,
            backend: mounted.backend,
            scope: 'development' as const,
            status: development.artifact.status,
            sourceSha256: mounted.sourceSha256,
            developmentRevision: development.plan.revision,
            moduleIds: Object.freeze([
                ...development.artifact.workspace.order
            ]),
            proofCount: development.proofs.length,
            openGoalCount: goals.length
        }),
        goals,
        artifact: development.artifact
    });
};

const createCoreLfProofDevelopmentBuildRecord = (
    selected: SelectedDevelopment
): CoreLfProofDevelopmentBuildRecord => Object.freeze({
    revision: CORE_LF_PROOF_DEVELOPMENT_CLI_PROFILE.buildRevision,
    kind: 'proof-development-build' as const,
    backend: selected.summary.backend,
    scope: selected.summary.scope,
    status: selected.summary.status,
    sourceSha256: selected.summary.sourceSha256,
    developmentRevision: selected.summary.developmentRevision,
    ...(selected.summary.moduleId === undefined
        ? {}
        : {
            moduleId: selected.summary.moduleId,
            declarationId: selected.summary.declarationId
        }),
    artifact: selected.artifact
});

const serializeRecords = (records: readonly object[]): string =>
    `${records.map(record => JSON.stringify(record)).join('\n')}\n`;

export const formatCoreLfProofDevelopmentSummary = (
    summary: CoreLfProofDevelopmentSummaryRecord
): string => {
    const identity = summary.scope === 'development'
        ? summary.developmentRevision
        : `${summary.moduleId}.${summary.declarationId}`;
    return [
        `${summary.scope} ${identity}: ${summary.status}`,
        `backend ${summary.backend}`,
        `source ${summary.sourceSha256}`,
        `modules ${summary.moduleIds.length}: ${summary.moduleIds.join(', ')}`,
        `proofs ${summary.proofCount}; open goals ${summary.openGoalCount}`
    ].join('\n') + '\n';
};

const formatGoal = (record: CoreLfProofDevelopmentGoalRecord): string =>
    `Goal ${record.moduleId}.${record.declarationId}.${record.goal.id} ` +
    `[depth ${record.goal.contextDepth}]\n` +
    `  |- ${record.goal.target}\n`;

const defaultStdout = (text: string): void => {
    process.stdout.write(text);
};

const defaultStderr = (text: string): void => {
    process.stderr.write(text);
};

/** Acquire and freshly check one development without retaining state. */
export async function runCoreLfProofDevelopmentCli(
    argv: readonly string[],
    io: CoreLfProofDevelopmentCliIo = {}
): Promise<number> {
    const writeStdout = io.stdout ?? defaultStdout;
    const writeStderr = io.stderr ?? defaultStderr;
    try {
        const parsed = parseCommand(argv);
        const mounted = await materializeCoreLfMountedProofDevelopment({
            projectRoot: parsed.projectRoot
        });
        const development = compileCoreLfProofDevelopment(
            mounted.reconstruction.plan
        );
        const selected = selectDevelopment(
            parsed.command,
            mounted,
            development,
            parsed.moduleId,
            parsed.declarationId
        );

        if (parsed.format === 'jsonl') {
            const records = parsed.command === 'build'
                ? [createCoreLfProofDevelopmentBuildRecord(selected)]
                : parsed.command === 'goals'
                    ? [selected.summary, ...selected.goals]
                    : [selected.summary];
            writeStdout(serializeRecords(records));
        } else {
            writeStdout(
                formatCoreLfProofDevelopmentSummary(selected.summary) +
                (parsed.command === 'goals'
                    ? selected.goals.map(formatGoal).join('')
                    : '')
            );
        }

        if (
            parsed.command !== 'goals' &&
            selected.summary.status === 'incomplete'
        ) {
            const identity = selected.summary.scope === 'proof'
                ? `${selected.summary.moduleId}.` +
                    `${selected.summary.declarationId}`
                : selected.summary.developmentRevision;
            writeStderr(`emdash: ${identity}: proof is incomplete\n`);
            return 1;
        }
        return 0;
    } catch (error: unknown) {
        const message = error instanceof Error ? error.message : String(error);
        writeStderr(`emdash: ${message}\n`);
        return 2;
    }
}
