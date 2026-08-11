/** Stateless CLI adapter for the finite PathOut presentation vocabulary. */

import {
    CORE_PATHOUT_PRESENTATION_1F_MANIFEST,
    CorePathoutPresentationFormId,
    createCorePathoutQualificationReport,
    formatCorePathoutQualificationReport,
    parseCorePathoutPresentationText
} from './pathout_presentation';

export const CORE_PATHOUT_PRESENTATION_1F_CLI_PROFILE = Object.freeze({
    revision: 'PATHOUT-LIBRARY-PRESENTATION-1F-CLI-1' as const,
    commandNamespace: 'pathout' as const,
    commands: Object.freeze(['catalog', 'parse', 'check'] as const),
    defaultFormat: 'text' as const,
    catalogLoadsSemanticTransfer: false as const,
    parseLoadsSemanticTransfer: false as const,
    checkLoadsSemanticTransferOnExplicitRequest: true as const,
    retainsCheckerSession: false as const,
    invokesLambdapi: false as const
});

export type CorePathoutPresentationCliCommand =
    typeof CORE_PATHOUT_PRESENTATION_1F_CLI_PROFILE.commands[number];
export type CorePathoutPresentationCliFormat = 'text' | 'json';

export interface CorePathoutPresentationCliIo {
    readonly stdout?: (text: string) => void;
    readonly stderr?: (text: string) => void;
}

export type CorePathoutPresentationSemanticModule = Pick<
    typeof import('./pathout_presentation_check'),
    'checkCorePathoutPresentationRequest' | 'formatCorePathoutFreshCheck'
>;

export interface CorePathoutPresentationCliDependencies {
    readonly loadSemanticCheck?:
        () => Promise<CorePathoutPresentationSemanticModule>;
}

interface ParsedCommand {
    readonly command: CorePathoutPresentationCliCommand;
    readonly formId?: CorePathoutPresentationFormId;
    readonly source?: string;
    readonly format: CorePathoutPresentationCliFormat;
}

export const CORE_PATHOUT_PRESENTATION_CLI_USAGE =
    'usage: ./scripts/emdash pathout ' +
    '<catalog|parse|check> [EXAMPLE] ' +
    '[--source EXPRESSION] [--format text|json]';

export const CORE_PATHOUT_PRESENTATION_COLD_CHECK_NOTICE =
    'emdash: explicit PathOut semantic check requested; the first ' +
    'TypeScript transfer assembly in this process may take several minutes.\n';

const parseFormat = (value: string): CorePathoutPresentationCliFormat => {
    if (value === 'text' || value === 'json') return value;
    throw new Error(
        `Unknown PathOut output format '${value}'; expected text or json`
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

const parseFormId = (value: string): CorePathoutPresentationFormId => {
    const form = CORE_PATHOUT_PRESENTATION_1F_MANIFEST.forms.find(
        candidate => candidate.id === value
    );
    if (form === undefined) {
        throw new Error(
            `Unknown PathOut example '${value}'; run ` +
            "'./scripts/emdash pathout catalog' to list examples"
        );
    }
    return form.id;
};

const parseCommand = (argv: readonly string[]): ParsedCommand => {
    const command = argv[0];
    if (
        command !== 'catalog' &&
        command !== 'parse' &&
        command !== 'check'
    ) {
        throw new Error(CORE_PATHOUT_PRESENTATION_CLI_USAGE);
    }

    let formId: CorePathoutPresentationFormId | undefined;
    let source: string | undefined;
    let format: CorePathoutPresentationCliFormat =
        CORE_PATHOUT_PRESENTATION_1F_CLI_PROFILE.defaultFormat;
    let formatSeen = false;

    for (let index = 1; index < argv.length; index++) {
        const argument = argv[index] as string;
        if (argument === '--source') {
            if (source !== undefined) {
                throw new Error('Duplicate --source option');
            }
            source = optionValue(argv, index, argument);
            index++;
            continue;
        }
        if (argument.startsWith('--source=')) {
            if (source !== undefined) {
                throw new Error('Duplicate --source option');
            }
            source = argument.slice('--source='.length);
            if (source.length === 0) {
                throw new Error('Missing value after --source');
            }
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
        if (argument.startsWith('--')) {
            throw new Error(`Unknown PathOut option '${argument}'`);
        }
        if (formId !== undefined) {
            throw new Error(`Unexpected PathOut argument '${argument}'`);
        }
        formId = parseFormId(argument);
    }

    if (command === 'catalog') {
        if (formId !== undefined || source !== undefined) {
            throw new Error(
                'PathOut catalog does not accept an example or --source'
            );
        }
    } else if (formId === undefined) {
        throw new Error(CORE_PATHOUT_PRESENTATION_CLI_USAGE);
    }

    return Object.freeze({ command, formId, source, format });
};

const formatCatalog = (): string => [
    CORE_PATHOUT_PRESENTATION_1F_MANIFEST.title,
    'Evidence: qualified at pinned checkpoints; not rerun by catalog.',
    '',
    ...CORE_PATHOUT_PRESENTATION_1F_MANIFEST.forms.flatMap(form => [
        `${form.id}: ${form.label}`,
        `  ${form.canonicalSource}`,
        `  target ${form.semanticTarget}; result ${form.resultKind}`
    ]),
    '',
    'Use `pathout parse` for a static qualification report or `pathout ' +
        'check` for an explicit fresh TypeScript semantic check.'
].join('\n') + '\n';

const defaultStdout = (text: string): void => {
    process.stdout.write(text);
};

const defaultStderr = (text: string): void => {
    process.stderr.write(text);
};

const defaultLoadSemanticCheck = async ():
Promise<CorePathoutPresentationSemanticModule> =>
    import('./pathout_presentation_check.js');

/**
 * Run one finite PathOut presentation command.
 *
 * Catalog and parse are browser-safe and never call the semantic loader.
 * Check is the only command that dynamically acquires the Node adapter.
 */
export async function runCorePathoutPresentationCli(
    argv: readonly string[],
    io: CorePathoutPresentationCliIo = {},
    dependencies: CorePathoutPresentationCliDependencies = {}
): Promise<number> {
    const writeStdout = io.stdout ?? defaultStdout;
    const writeStderr = io.stderr ?? defaultStderr;
    try {
        const parsed = parseCommand(argv);
        if (parsed.command === 'catalog') {
            writeStdout(parsed.format === 'json'
                ? `${JSON.stringify(
                    CORE_PATHOUT_PRESENTATION_1F_MANIFEST,
                    null,
                    2
                )}\n`
                : formatCatalog());
            return 0;
        }

        const form = CORE_PATHOUT_PRESENTATION_1F_MANIFEST.forms.find(
            candidate => candidate.id === parsed.formId
        );
        if (form === undefined) {
            throw new Error(`Unknown PathOut example '${parsed.formId}'`);
        }
        const request = parseCorePathoutPresentationText(
            parsed.source ?? form.canonicalSource,
            '<pathout-cli>'
        );
        if (request.formId !== form.id) {
            throw new Error(
                `Example '${form.id}' does not match parsed form ` +
                `'${request.formId}'`
            );
        }

        if (parsed.command === 'parse') {
            const report = createCorePathoutQualificationReport(request);
            writeStdout(parsed.format === 'json'
                ? `${JSON.stringify(report, null, 2)}\n`
                : `${formatCorePathoutQualificationReport(report)}\n`);
            return 0;
        }

        writeStderr(CORE_PATHOUT_PRESENTATION_COLD_CHECK_NOTICE);
        const semantic = await (
            dependencies.loadSemanticCheck ?? defaultLoadSemanticCheck
        )();
        const result = semantic.checkCorePathoutPresentationRequest(request);
        writeStdout(parsed.format === 'json'
            ? `${JSON.stringify(result, null, 2)}\n`
            : `${semantic.formatCorePathoutFreshCheck(result)}\n`);
        return 0;
    } catch (error: unknown) {
        const message = error instanceof Error ? error.message : String(error);
        writeStderr(`emdash: ${message}\n`);
        return 2;
    }
}
