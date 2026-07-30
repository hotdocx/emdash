/**
 * Node-only fail-closed checked acquisition adapter for SCALE-ACQUIRE-1.
 *
 * Browser-safe selection-contract creation lives in the adjacent contract
 * module and is re-exported here for compatibility. This adapter alone
 * hashes active source/export text and parses canonical export commands.
 */

import { createHash } from 'node:crypto';
import {
    CanonicalLambdapiCommand,
    CanonicalLambdapiExportInventory,
    parseCanonicalLambdapiExport
} from './lambdapi_export_inventory';
import {
    CoreLfCanonicalAcquisitionError,
    createCoreLfCanonicalSelectionContract
} from './lf_transfer_acquisition_contract';
import type {
    CoreLfCanonicalAcquisitionErrorCode,
    CoreLfCanonicalCommandExpectation,
    CoreLfCanonicalSelectionContractInput
} from './lf_transfer_acquisition_contract';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';

export * from './lf_transfer_acquisition_contract';

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

const sha256 = (source: string): string =>
    'sha256:' + createHash('sha256').update(source).digest('hex');

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

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
