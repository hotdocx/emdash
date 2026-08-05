/**
 * Focused SCALE-STRESS-3B protected/evidence acquisition audit.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { basename, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_STRESS_3B_ACQUISITION_AUDIT,
    CORE_LF_SCALE_STRESS_3B_EVIDENCE_PROPERTY_ACQUISITION,
    CORE_LF_SCALE_STRESS_3B_PROTECTED_HOM_ACTION_ACQUISITION,
    CanonicalLambdapiCommand,
    CoreLfCanonicalCommandSelection,
    CoreLfCanonicalSelectionContract,
    acquireCoreLfCanonicalCommands,
    compileCoreLfScaleStress3a2bRepresentation,
    parseCanonicalLambdapiExport
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const repositoryRoot = resolve(__dirname, '..');
const lambdapiRoot = resolve(repositoryRoot, 'emdash2');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const runLambdapi = (args: readonly string[]): string => {
    const result = spawnSync('lambdapi', [...args], {
        cwd: lambdapiRoot,
        encoding: 'utf8',
        timeout: 60_000,
        maxBuffer: 64 * 1024 * 1024
    });
    assert.equal(result.error, undefined, result.error?.message);
    assert.equal(
        result.status,
        0,
        `lambdapi ${args.join(' ')} failed:\n${result.stderr}`
    );
    return result.stdout;
};

const acquire = (
    contract: CoreLfCanonicalSelectionContract,
    canonicalExportText: string,
    exporterVersion: string
): CoreLfCanonicalCommandSelection =>
    acquireCoreLfCanonicalCommands(contract, {
        sourceText: readFileSync(
            resolve(repositoryRoot, contract.authorityPath),
            'utf8'
        ),
        canonicalExportText,
        observedExporterVersion: exporterVersion
    });

const identifiers = (source: string): ReadonlySet<string> =>
    new Set(source.match(/[\p{L}\p{N}\p{M}_]+|=/gu) ?? []);

const producerNames = (
    command: CanonicalLambdapiCommand
): readonly string[] => {
    if (command.kind === 'symbol') return [command.name];
    if (command.kind !== 'inductive') return [];
    return [
        command.name,
        `ind_${command.name}`,
        ...[...command.text.matchAll(
            /\|\s*([^\s:(),;]+)/gu
        )].map(match => match[1])
    ];
};

const assertRootPrerequisiteAudit = (
    rootCanonicalExportText: string,
    selections: readonly CoreLfCanonicalCommandSelection[]
): void => {
    const root = parseCanonicalLambdapiExport(
        'emdash.emdash3_2',
        rootCanonicalExportText
    );
    const producers = root.commands.filter(command =>
        command.kind === 'symbol' ||
        command.kind === 'inductive'
    );
    const byName = new Map(
        producers.flatMap(command =>
            producerNames(command).map(name => [
                name,
                command
            ] as const)
        )
    );
    const directNames = new Set<string>();
    selections.forEach(selection =>
        selection.commands.forEach(entry =>
            identifiers(entry.command.text).forEach(name => {
                if (byName.has(name)) directNames.add(name);
            })
        )
    );

    const closure = new Map<number, CanonicalLambdapiCommand>();
    const visit = (name: string): void => {
        const command = byName.get(name);
        if (
            command === undefined ||
            closure.has(command.ordinal)
        ) {
            return;
        }
        const ownNames = new Set(producerNames(command));
        identifiers(command.text).forEach(dependencyName => {
            const dependency = byName.get(dependencyName);
            if (
                !ownNames.has(dependencyName) &&
                dependency !== undefined &&
                dependency.ordinal < command.ordinal
            ) {
                visit(dependencyName);
            }
        });
        closure.set(command.ordinal, command);
    };
    directNames.forEach(visit);

    const compiled =
        compileCoreLfScaleStress3a2bRepresentation()
            .compiled.declarations;
    const availability = (
        command: CanonicalLambdapiCommand
    ): readonly boolean[] =>
        producerNames(command).map(name =>
            compiled.declaration({
                moduleId: 'emdash.emdash3_2',
                name
            }) !== undefined
        );
    const commands = [...closure.values()].sort(
        (left, right) => left.ordinal - right.ordinal
    );
    const consumerAvailable = commands.filter(command =>
        availability(command).some(Boolean)
    );
    const partial = consumerAvailable.filter(command => {
        const available = availability(command);
        return available.some(Boolean) &&
            available.some(value => !value);
    });
    const missing = commands.filter(command =>
        availability(command).every(value => !value)
    );
    const audit =
        CORE_LF_SCALE_STRESS_3B_ACQUISITION_AUDIT
            .rootPrerequisite;

    assert.equal(directNames.size, audit.directlyReferencedNameCount);
    assert.equal(commands.length, audit.sourcePriorCommandCount);
    assert.equal(
        consumerAvailable.length,
        audit.consumerAvailableCommandCount
    );
    assert.deepEqual(
        partial.map(command =>
            command.kind === 'inductive'
                ? command.name
                : command.kind
        ),
        audit.partiallyAvailableInductiveCommands
    );
    assert.equal(missing.length, audit.missingCommandCount);
    assert.equal(
        missing.filter(command => command.kind === 'symbol').length,
        audit.missingSymbolCommandCount
    );
    assert.equal(
        missing.filter(command => command.kind === 'inductive').length,
        audit.missingInductiveCommandCount
    );
    assert.equal(
        missing.filter(command =>
            command.kind === 'symbol' && command.hasBody
        ).length,
        audit.missingExplicitTermCommandCount
    );
    assert.equal(
        missing.filter(command =>
            command.kind === 'symbol' && !command.hasBody
        ).length,
        audit.missingAbsentBodyCommandCount
    );
    assert.equal(
        missing.reduce(
            (total, command) =>
                total + Buffer.byteLength(command.text),
            0
        ),
        audit.missingCanonicalCommandBytes
    );
    assert.deepEqual(
        missing
            .filter(
                (
                    command
                ): command is CanonicalLambdapiCommand & {
                    readonly kind: 'inductive';
                    readonly name: string;
                } => command.kind === 'inductive'
            )
            .map(command => command.name),
        audit.missingInductiveCommands
    );
};

const assertDependencyClosed = (
    contract: CoreLfCanonicalSelectionContract,
    selection: CoreLfCanonicalCommandSelection,
    canonicalExportText: string
): void => {
    const inventory = parseCanonicalLambdapiExport(
        contract.moduleId,
        canonicalExportText
    );
    const allLocalSymbols = inventory.commands
        .filter(command => command.kind === 'symbol')
        .map(command => command.name);
    const selected = new Map(
        selection.commands.map(entry => {
            assert.equal(entry.command.kind, 'symbol');
            if (entry.command.kind !== 'symbol') {
                throw new Error('Expected a selected symbol command');
            }
            return [entry.command.name, entry.command.ordinal];
        })
    );

    selection.commands.forEach(entry => {
        const command = entry.command;
        assert.equal(command.kind, 'symbol');
        if (command.kind !== 'symbol') return;
        const tokens = identifiers(command.text);
        allLocalSymbols.forEach(name => {
            if (
                name !== command.name &&
                tokens.has(name)
            ) {
                const dependencyOrdinal = selected.get(name);
                assert.notEqual(
                    dependencyOrdinal,
                    undefined,
                    `${command.name} omits local dependency ${name}`
                );
                assert.ok(
                    dependencyOrdinal !== undefined &&
                    dependencyOrdinal < command.ordinal,
                    `${command.name} has a non-prior dependency ${name}`
                );
            }
        });
    });
};

describe(
    'TypeScript v3.2 SCALE-STRESS-3B acquisition audit',
    () => {
        it('pins the exact protected and proof-heavy closures', () => {
            const protectedContract =
                CORE_LF_SCALE_STRESS_3B_PROTECTED_HOM_ACTION_ACQUISITION;
            const evidenceContract =
                CORE_LF_SCALE_STRESS_3B_EVIDENCE_PROPERTY_ACQUISITION;

            assert.equal(protectedContract.commands.length, 58);
            assert.deepEqual(
                protectedContract.commands.map(command =>
                    command.ordinal
                ),
                [
                    ...Array.from(
                        { length: 56 },
                        (_value, index) => index + 1
                    ),
                    58,
                    59
                ]
            );
            assert.equal(
                protectedContract.commands.filter(command =>
                    command.kind === 'symbol' &&
                    command.modifiers.includes('protected')
                ).length,
                56
            );
            const protectedTarget =
                protectedContract.commands.at(-1);
            assert.equal(
                protectedTarget?.kind,
                'symbol'
            );
            assert.equal(
                protectedTarget?.kind === 'symbol'
                    ? protectedTarget.name
                    : undefined,
                'groupoidal_core_homwise'
            );

            assert.equal(evidenceContract.commands.length, 25);
            assert.deepEqual(
                evidenceContract.commands.map(command =>
                    command.ordinal
                ),
                [
                    2, 3, 4, 5, 6, 7, 8, 9, 28,
                    38, 39, 40, 41, 42, 43, 44, 45, 46,
                    47, 48, 49, 50, 51, 52, 53
                ]
            );
            const evidenceTarget =
                evidenceContract.commands.at(-1);
            assert.equal(
                evidenceTarget?.kind === 'symbol'
                    ? evidenceTarget.name
                    : undefined,
                'omega_equiv_along_evidence_is_prop'
            );
            assert.deepEqual(
                evidenceContract.canonicalExport.imports,
                [
                    'emdash.emdash3_2',
                    'emdash.emdash3_2_eq1_hom_action'
                ]
            );
            assertDeepFrozen(protectedContract);
            assertDeepFrozen(evidenceContract);
            assertDeepFrozen(
                CORE_LF_SCALE_STRESS_3B_ACQUISITION_AUDIT
            );
        });

        it(
            'matches live exports and verifies dependency closure',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_SCALE_MODULE_STRESS_PROBES !==
                    '1'
            },
            () => {
                const exporterVersion =
                    runLambdapi(['--version']).trim();
                const contracts = [
                    CORE_LF_SCALE_STRESS_3B_PROTECTED_HOM_ACTION_ACQUISITION,
                    CORE_LF_SCALE_STRESS_3B_EVIDENCE_PROPERTY_ACQUISITION
                ];
                const selections = contracts.map(contract => {
                    const canonicalExportText = runLambdapi([
                        'export',
                        '-o',
                        'lp',
                        basename(contract.authorityPath)
                    ]);
                    const selection = acquire(
                        contract,
                        canonicalExportText,
                        exporterVersion
                    );
                    assertDependencyClosed(
                        contract,
                        selection,
                        canonicalExportText
                    );
                    return selection;
                });
                const rootCanonicalExportText = runLambdapi([
                    'export',
                    '-o',
                    'lp',
                    'emdash3_2.lp'
                ]);
                assertRootPrerequisiteAudit(
                    rootCanonicalExportText,
                    selections
                );

                const protectedSelection = selections[0];
                const protectedBytes =
                    protectedSelection.commands.reduce(
                        (total, entry) =>
                            total + Buffer.byteLength(entry.command.text),
                        0
                    );
                const tacticNames = protectedSelection.commands
                    .filter(entry =>
                        entry.command.kind === 'symbol' &&
                        /\bbegin\b/u.test(entry.command.text)
                    )
                    .map(entry => entry.command.kind === 'symbol'
                        ? entry.command.name
                        : '')
                    .sort();
                assert.equal(
                    protectedBytes,
                    CORE_LF_SCALE_STRESS_3B_ACQUISITION_AUDIT
                        .protectedHomAction.canonicalCommandBytes
                );
                assert.deepEqual(
                    tacticNames,
                    [
                        'eq1_adjusted_component_agrees',
                        'eq1_fapp1_left_right_law'
                    ]
                );

                const evidenceBytes = selections[1].commands.reduce(
                    (total, entry) =>
                        total + Buffer.byteLength(entry.command.text),
                    0
                );
                assert.equal(
                    evidenceBytes,
                    CORE_LF_SCALE_STRESS_3B_ACQUISITION_AUDIT
                        .evidenceProperty.canonicalCommandBytes
                );
            }
        );

        it('keeps acquisition and visibility machinery out of the browser', () => {
            assert.equal(
                'CORE_LF_SCALE_STRESS_3B_ACQUISITION_AUDIT' in browser,
                false
            );
            assert.equal(
                'createCoreLfCompiledModuleInterface' in browser,
                false
            );
        });
    }
);
