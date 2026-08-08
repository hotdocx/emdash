/** Stateless command projection of the source-visible AI-native contract. */

import {
    CORE_AI_NATIVE_CAPABILITIES,
    CoreAiNativeCapabilityRecord,
    serializeCoreAiNativeCapabilities
} from './ai_native_capabilities';

export const CORE_AI_NATIVE_CAPABILITIES_CLI_PROFILE = Object.freeze({
    revision: 'emdash-ai-native-capabilities-cli-v1' as const,
    command: 'capabilities' as const,
    defaultFormat: 'jsonl' as const,
    performsFileIo: false as const,
    performsSemanticChecks: false as const,
    supportsBackendSelection: false as const,
    invokesLambdapi: false as const
});

export type CoreAiNativeCapabilitiesCliFormat = 'jsonl' | 'text';

export interface CoreAiNativeCapabilitiesCliIo {
    readonly stdout?: (text: string) => void;
    readonly stderr?: (text: string) => void;
}

export const CORE_AI_NATIVE_CAPABILITIES_CLI_USAGE =
    'usage: ./scripts/emdash capabilities [--format jsonl|text]';

const parseFormat = (value: string): CoreAiNativeCapabilitiesCliFormat => {
    if (value === 'jsonl' || value === 'text') return value;
    throw new Error(
        `Unknown capabilities output format '${value}'; ` +
        'expected jsonl or text'
    );
};

const parseCommand = (
    argv: readonly string[]
): CoreAiNativeCapabilitiesCliFormat => {
    let format: CoreAiNativeCapabilitiesCliFormat =
        CORE_AI_NATIVE_CAPABILITIES_CLI_PROFILE.defaultFormat;
    let formatSeen = false;
    for (let index = 0; index < argv.length; index++) {
        const argument = argv[index];
        if (argument === '--format') {
            if (formatSeen) throw new Error('Duplicate --format option');
            const value = argv[index + 1];
            if (value === undefined || value.startsWith('--')) {
                throw new Error('Missing value after --format');
            }
            format = parseFormat(value);
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
        throw new Error(CORE_AI_NATIVE_CAPABILITIES_CLI_USAGE);
    }
    return format;
};

export const formatCoreAiNativeCapabilities = (
    record: CoreAiNativeCapabilityRecord = CORE_AI_NATIVE_CAPABILITIES
): string => {
    const lines = [
        `emdash AI-native: ${record.status}`,
        `backend: ${record.backend}`,
        'proof authority: checked backend-neutral explicit Core',
        'Lambdapi: optional development conformance; not production runtime',
        '',
        'Commands:'
    ];
    record.commands.forEach(command => {
        lines.push(`  ${command.syntax}`);
        lines.push(`    scope: ${command.scope}`);
    });
    lines.push('', 'Implemented profiles:');
    record.implementedProfiles.forEach(profile => {
        lines.push(
            `  ${profile.id}@${profile.revision} — ${profile.scope}`
        );
    });
    lines.push('', 'Deferred:');
    record.deferred.forEach(capability => {
        lines.push(
            `  ${capability.id} (${capability.state}) — ` +
                capability.prerequisite
        );
    });
    return `${lines.join('\n')}\n`;
};

const defaultStdout = (text: string): void => {
    process.stdout.write(text);
};

const defaultStderr = (text: string): void => {
    process.stderr.write(text);
};

/** Render the immutable record without checking or acquiring anything. */
export function runCoreAiNativeCapabilitiesCli(
    argv: readonly string[],
    io: CoreAiNativeCapabilitiesCliIo = {}
): number {
    const writeStdout = io.stdout ?? defaultStdout;
    const writeStderr = io.stderr ?? defaultStderr;
    try {
        const format = parseCommand(argv);
        writeStdout(format === 'jsonl'
            ? serializeCoreAiNativeCapabilities()
            : formatCoreAiNativeCapabilities());
        return 0;
    } catch (error: unknown) {
        const message = error instanceof Error
            ? error.message
            : String(error);
        writeStderr(`emdash: ${message}\n`);
        return 2;
    }
}
