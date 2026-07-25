/**
 * Small fail-closed checked acquisition adapter for SCALE-ACQUIRE-1.
 *
 * This selects exact top-level commands from a pinned canonical Lambdapi
 * export. It deliberately does not parse terms or patterns and grants no
 * semantic policy.
 */

import { createHash } from 'node:crypto';
import {
    CanonicalLambdapiCommand,
    CanonicalLambdapiCommandKind,
    CanonicalLambdapiExportInventory,
    CanonicalLambdapiSymbolModifier,
    parseCanonicalLambdapiExport
} from './lambdapi_export_inventory';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';

interface CoreLfCanonicalCommandExpectationBase {
    readonly id: string;
    readonly ordinal: number;
    readonly kind: CanonicalLambdapiCommandKind;
    readonly textSha256: string;
}

export type CoreLfCanonicalCommandExpectation =
    | CoreLfCanonicalCommandExpectationBase & {
        readonly kind: 'require';
        readonly open: boolean;
        readonly modules: readonly string[];
    }
    | CoreLfCanonicalCommandExpectationBase & {
        readonly kind: 'flag';
    }
    | CoreLfCanonicalCommandExpectationBase & {
        readonly kind: 'symbol';
        readonly name: string;
        readonly modifiers:
            readonly CanonicalLambdapiSymbolModifier[];
        readonly hasBody: boolean;
    }
    | CoreLfCanonicalCommandExpectationBase & {
        readonly kind: 'inductive';
        readonly name: string;
        readonly constructorCount: number;
    }
    | CoreLfCanonicalCommandExpectationBase & {
        readonly kind: 'rule';
        readonly clauseCount: number;
    }
    | CoreLfCanonicalCommandExpectationBase & {
        readonly kind: 'unif_rule';
    }
    | CoreLfCanonicalCommandExpectationBase & {
        readonly kind: 'builtin';
    }
    | CoreLfCanonicalCommandExpectationBase & {
        readonly kind: 'notation';
    }
    | CoreLfCanonicalCommandExpectationBase & {
        readonly kind: 'opaque';
        readonly symbols: readonly string[];
    };

export interface CoreLfCanonicalSelectionContractInput {
    readonly revision: string;
    readonly moduleId: string;
    readonly authorityPath: string;
    readonly sourceSha256: string;
    readonly canonicalExport: {
        readonly exporterVersion: string;
        readonly sha256: string;
        readonly imports: readonly string[];
    };
    readonly commands:
        readonly CoreLfCanonicalCommandExpectation[];
}

export type CoreLfCanonicalSelectionContract =
    CoreLfCanonicalSelectionContractInput;

export interface CoreLfCanonicalAcquisitionInput {
    readonly sourceText: string;
    readonly canonicalExportText: string;
    readonly observedExporterVersion: string;
}

export interface CoreLfAcquiredCanonicalCommand {
    readonly id: string;
    readonly textSha256: string;
    readonly command: CanonicalLambdapiCommand;
}

export interface CoreLfCanonicalCommandSelection {
    readonly revision: string;
    readonly moduleId: string;
    readonly authorityPath: string;
    readonly sourceSha256: string;
    readonly canonicalExport: {
        readonly exporterVersion: string;
        readonly sha256: string;
        readonly imports: readonly string[];
        readonly commandCount: number;
    };
    readonly commands: readonly CoreLfAcquiredCanonicalCommand[];
}

export type CoreLfCanonicalAcquisitionErrorCode =
    | 'INVALID_SELECTION_CONTRACT'
    | 'SOURCE_HASH_MISMATCH'
    | 'EXPORTER_VERSION_MISMATCH'
    | 'EXPORT_HASH_MISMATCH'
    | 'IMPORT_DRIFT'
    | 'COMMAND_MISSING'
    | 'COMMAND_DRIFT';

export class CoreLfCanonicalAcquisitionError extends Error {
    constructor(
        public readonly code: CoreLfCanonicalAcquisitionErrorCode,
        message: string,
        public readonly path: string
    ) {
        super(message);
        this.name = 'CoreLfCanonicalAcquisitionError';
    }
}

const fail = (
    code: CoreLfCanonicalAcquisitionErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfCanonicalAcquisitionError(code, message, path);
};

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        Object.freeze(value);
    }
    return value;
};

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

const sha256 = (source: string): string =>
    'sha256:' + createHash('sha256').update(source).digest('hex');

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const validModuleId = (moduleId: string): boolean =>
    /^[\p{L}\p{N}_]+(?:\.[\p{L}\p{N}_]+)*$/u.test(moduleId);

const validRevisionOrId = (value: string): boolean =>
    /^[\p{L}\p{N}_][\p{L}\p{N}_.-]*$/u.test(value);

const validSha256 = (value: string): boolean =>
    /^sha256:[0-9a-f]{64}$/u.test(value);

const commandKinds = new Set<CanonicalLambdapiCommandKind>([
    'require',
    'flag',
    'symbol',
    'inductive',
    'rule',
    'unif_rule',
    'builtin',
    'notation',
    'opaque'
]);

const symbolModifiers =
    new Set<CanonicalLambdapiSymbolModifier>([
        'constant',
        'injective',
        'protected',
        'private',
        'opaque'
    ]);

const validateAuthorityPath = (authorityPath: string): void => {
    if (
        authorityPath.length === 0 ||
        authorityPath.startsWith('/') ||
        authorityPath.includes('\\') ||
        !/^[\p{L}\p{N}_.\-/]+$/u.test(authorityPath) ||
        authorityPath.split('/').some(
            segment =>
                segment.length === 0 ||
                segment === '.' ||
                segment === '..'
        )
    ) {
        fail(
            'INVALID_SELECTION_CONTRACT',
            'contract.authorityPath',
            'Canonical acquisition authority path must be normalized and ' +
                'repository-relative'
        );
    }
};

const validateNonnegativeInteger = (
    value: number,
    path: string
): void => {
    if (!Number.isSafeInteger(value) || value < 0) {
        fail(
            'INVALID_SELECTION_CONTRACT',
            path,
            'Canonical acquisition count or ordinal must be a ' +
                'nonnegative safe integer'
        );
    }
};

const validateExpectationShape = (
    expectation: CoreLfCanonicalCommandExpectation,
    path: string
): void => {
    const commonKeys = ['id', 'ordinal', 'kind', 'textSha256'];
    const specificKeys: Readonly<
        Record<CanonicalLambdapiCommandKind, readonly string[]>
    > = {
        require: ['open', 'modules'],
        flag: [],
        symbol: ['name', 'modifiers', 'hasBody'],
        inductive: ['name', 'constructorCount'],
        rule: ['clauseCount'],
        unif_rule: [],
        builtin: [],
        notation: [],
        opaque: ['symbols']
    };
    if (!commandKinds.has(expectation.kind)) {
        fail(
            'INVALID_SELECTION_CONTRACT',
            `${path}.kind`,
            'Canonical command expectation has an unsupported kind'
        );
    }
    const expectedKeys = [
        ...commonKeys,
        ...specificKeys[expectation.kind]
    ].sort();
    const actualKeys = Object.keys(expectation).sort();
    if (!sameData(actualKeys, expectedKeys)) {
        fail(
            'INVALID_SELECTION_CONTRACT',
            path,
            'Canonical command expectation has missing or unsupported fields'
        );
    }
    switch (expectation.kind) {
        case 'require':
            if (
                typeof expectation.open !== 'boolean' ||
                expectation.modules.length === 0 ||
                expectation.modules.some(
                    moduleId => !validModuleId(moduleId)
                ) ||
                new Set(expectation.modules).size !==
                    expectation.modules.length
            ) {
                fail(
                    'INVALID_SELECTION_CONTRACT',
                    `${path}.modules`,
                    'Required modules must be nonempty valid module IDs'
                );
            }
            return;
        case 'symbol':
            if (
                expectation.name.length === 0 ||
                /\s/u.test(expectation.name) ||
                typeof expectation.hasBody !== 'boolean' ||
                new Set(expectation.modifiers).size !==
                    expectation.modifiers.length ||
                expectation.modifiers.some(
                    modifier => !symbolModifiers.has(modifier)
                )
            ) {
                fail(
                    'INVALID_SELECTION_CONTRACT',
                    path,
                    'Symbol expectation has an invalid name or duplicate ' +
                        'modifier'
                );
            }
            return;
        case 'inductive':
            if (
                expectation.name.length === 0 ||
                /\s/u.test(expectation.name)
            ) {
                fail(
                    'INVALID_SELECTION_CONTRACT',
                    `${path}.name`,
                    'Inductive expectation requires a name'
                );
            }
            validateNonnegativeInteger(
                expectation.constructorCount,
                `${path}.constructorCount`
            );
            return;
        case 'rule':
            validateNonnegativeInteger(
                expectation.clauseCount,
                `${path}.clauseCount`
            );
            if (expectation.clauseCount === 0) {
                fail(
                    'INVALID_SELECTION_CONTRACT',
                    `${path}.clauseCount`,
                    'Runtime rule expectation requires at least one clause'
                );
            }
            return;
        case 'opaque':
            if (
                expectation.symbols.length === 0 ||
                expectation.symbols.some(
                    symbol =>
                        symbol.length === 0 ||
                        /\s/u.test(symbol)
                ) ||
                new Set(expectation.symbols).size !==
                    expectation.symbols.length
            ) {
                fail(
                    'INVALID_SELECTION_CONTRACT',
                    `${path}.symbols`,
                    'Opacity expectation requires at least one symbol'
                );
            }
            return;
        case 'flag':
        case 'unif_rule':
        case 'builtin':
        case 'notation':
            return;
        default:
            return fail(
                'INVALID_SELECTION_CONTRACT',
                `${path}.kind`,
                'Canonical command expectation has an unsupported kind'
            );
    }
};

const validateContract = (
    input: CoreLfCanonicalSelectionContractInput
): void => {
    if (!validRevisionOrId(input.revision)) {
        fail(
            'INVALID_SELECTION_CONTRACT',
            'contract.revision',
            'Canonical acquisition contract has an invalid revision'
        );
    }
    if (!validModuleId(input.moduleId)) {
        fail(
            'INVALID_SELECTION_CONTRACT',
            'contract.moduleId',
            'Canonical acquisition contract has an invalid module ID'
        );
    }
    validateAuthorityPath(input.authorityPath);
    if (!validSha256(input.sourceSha256)) {
        fail(
            'INVALID_SELECTION_CONTRACT',
            'contract.sourceSha256',
            'Canonical acquisition contract requires a prefixed SHA-256'
        );
    }
    if (
        input.canonicalExport.exporterVersion.trim() !==
            input.canonicalExport.exporterVersion ||
        input.canonicalExport.exporterVersion.length === 0 ||
        !validSha256(input.canonicalExport.sha256)
    ) {
        fail(
            'INVALID_SELECTION_CONTRACT',
            'contract.canonicalExport',
            'Canonical export evidence requires an exact version and ' +
                'prefixed SHA-256'
        );
    }
    if (
        input.canonicalExport.imports.some(
            moduleId => !validModuleId(moduleId)
        ) ||
        new Set(input.canonicalExport.imports).size !==
            input.canonicalExport.imports.length
    ) {
        fail(
            'INVALID_SELECTION_CONTRACT',
            'contract.canonicalExport.imports',
            'Canonical export imports must be unique valid module IDs'
        );
    }
    if (input.commands.length === 0) {
        fail(
            'INVALID_SELECTION_CONTRACT',
            'contract.commands',
            'Canonical acquisition contract must select at least one command'
        );
    }

    const ids = new Set<string>();
    const ordinals = new Set<number>();
    let previousOrdinal = -1;
    input.commands.forEach((expectation, index) => {
        const path = `contract.commands[${index}]`;
        if (
            !validRevisionOrId(expectation.id) ||
            ids.has(expectation.id)
        ) {
            fail(
                'INVALID_SELECTION_CONTRACT',
                `${path}.id`,
                'Canonical command selection IDs must be valid and unique'
            );
        }
        validateNonnegativeInteger(
            expectation.ordinal,
            `${path}.ordinal`
        );
        if (
            ordinals.has(expectation.ordinal) ||
            expectation.ordinal <= previousOrdinal
        ) {
            fail(
                'INVALID_SELECTION_CONTRACT',
                `${path}.ordinal`,
                'Canonical command ordinals must be unique and strictly ' +
                    'increasing'
            );
        }
        if (!validSha256(expectation.textSha256)) {
            fail(
                'INVALID_SELECTION_CONTRACT',
                `${path}.textSha256`,
                'Canonical command expectation requires a prefixed SHA-256'
            );
        }
        validateExpectationShape(expectation, path);
        ids.add(expectation.id);
        ordinals.add(expectation.ordinal);
        previousOrdinal = expectation.ordinal;
    });
};

export function createCoreLfCanonicalSelectionContract(
    input: CoreLfCanonicalSelectionContractInput
): CoreLfCanonicalSelectionContract {
    validateCoreLfScaleEngineReview();
    validateContract(input);
    return deepFreeze(cloneData(input));
}

const commandFacts = (
    command: CanonicalLambdapiCommand
): Record<string, unknown> => {
    switch (command.kind) {
        case 'require':
            return {
                open: command.open,
                modules: command.modules
            };
        case 'symbol':
            return {
                name: command.name,
                modifiers: command.modifiers,
                hasBody: command.hasBody
            };
        case 'inductive':
            return {
                name: command.name,
                constructorCount: command.constructorCount
            };
        case 'rule':
            return { clauseCount: command.clauseCount };
        case 'opaque':
            return { symbols: command.symbols };
        case 'flag':
        case 'unif_rule':
        case 'builtin':
        case 'notation':
            return {};
        default: {
            const exhaustive: never = command;
            return exhaustive;
        }
    }
};

const expectationFacts = (
    expectation: CoreLfCanonicalCommandExpectation
): Record<string, unknown> => {
    switch (expectation.kind) {
        case 'require':
            return {
                open: expectation.open,
                modules: expectation.modules
            };
        case 'symbol':
            return {
                name: expectation.name,
                modifiers: expectation.modifiers,
                hasBody: expectation.hasBody
            };
        case 'inductive':
            return {
                name: expectation.name,
                constructorCount: expectation.constructorCount
            };
        case 'rule':
            return { clauseCount: expectation.clauseCount };
        case 'opaque':
            return { symbols: expectation.symbols };
        case 'flag':
        case 'unif_rule':
        case 'builtin':
        case 'notation':
            return {};
        default: {
            const exhaustive: never = expectation;
            return exhaustive;
        }
    }
};

const selectCommand = (
    inventory: CanonicalLambdapiExportInventory,
    expectation: CoreLfCanonicalCommandExpectation,
    index: number
): CoreLfAcquiredCanonicalCommand => {
    const path = `contract.commands[${index}]`;
    const command = inventory.commands[expectation.ordinal];
    if (command === undefined) {
        return fail(
            'COMMAND_MISSING',
            `${path}.ordinal`,
            `Canonical export has no command at ordinal ` +
                expectation.ordinal
        );
    }
    if (
        command.kind !== expectation.kind ||
        sha256(command.text) !== expectation.textSha256 ||
        !sameData(
            commandFacts(command),
            expectationFacts(expectation)
        )
    ) {
        return fail(
            'COMMAND_DRIFT',
            path,
            `Canonical command '${expectation.id}' differs from its exact ` +
                'kind, metadata, or text digest'
        );
    }
    return deepFreeze({
        id: expectation.id,
        textSha256: expectation.textSha256,
        command
    });
};

export function acquireCoreLfCanonicalCommands(
    contractInput: CoreLfCanonicalSelectionContractInput,
    input: CoreLfCanonicalAcquisitionInput
): CoreLfCanonicalCommandSelection {
    validateCoreLfScaleEngineReview();
    const contract = createCoreLfCanonicalSelectionContract(
        contractInput
    );
    if (sha256(input.sourceText) !== contract.sourceSha256) {
        return fail(
            'SOURCE_HASH_MISMATCH',
            'input.sourceText',
            `Active source for '${contract.moduleId}' differs from the ` +
                'reviewed source digest'
        );
    }
    if (
        input.observedExporterVersion !==
            contract.canonicalExport.exporterVersion
    ) {
        return fail(
            'EXPORTER_VERSION_MISMATCH',
            'input.observedExporterVersion',
            `Observed canonical exporter version differs from the reviewed ` +
                `version for '${contract.moduleId}'`
        );
    }
    if (
        sha256(input.canonicalExportText) !==
            contract.canonicalExport.sha256
    ) {
        return fail(
            'EXPORT_HASH_MISMATCH',
            'input.canonicalExportText',
            `Canonical export for '${contract.moduleId}' differs from the ` +
                'reviewed export digest'
        );
    }

    const inventory = parseCanonicalLambdapiExport(
        contract.moduleId,
        input.canonicalExportText
    );
    if (
        !sameData(
            inventory.imports,
            contract.canonicalExport.imports
        )
    ) {
        return fail(
            'IMPORT_DRIFT',
            'contract.canonicalExport.imports',
            `Canonical imports for '${contract.moduleId}' differ from the ` +
                'reviewed dependency order'
        );
    }
    const commands = contract.commands.map(
        (expectation, index) =>
            selectCommand(inventory, expectation, index)
    );

    return deepFreeze({
        revision: contract.revision,
        moduleId: contract.moduleId,
        authorityPath: contract.authorityPath,
        sourceSha256: contract.sourceSha256,
        canonicalExport: {
            exporterVersion:
                contract.canonicalExport.exporterVersion,
            sha256: contract.canonicalExport.sha256,
            imports: [...inventory.imports],
            commandCount: inventory.commands.length
        },
        commands
    });
}
