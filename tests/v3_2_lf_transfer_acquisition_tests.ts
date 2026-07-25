/**
 * Focused reviewed H-DTTLF-SCALE-02 and SCALE-ACQUIRE-1A tests.
 */

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { basename, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_ENGINE_REVIEW,
    CORE_LF_SCALE_STRESS_1_ACQUISITION_CONTRACTS,
    CORE_LF_SCALE_STRESS_1B_CORE_ACQUISITION,
    CORE_LF_SCALE_STRESS_1_CORE_ACQUISITION,
    CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION,
    CanonicalLambdapiCommand,
    CoreLfCanonicalAcquisitionError,
    CoreLfCanonicalCommandExpectation,
    CoreLfCanonicalSelectionContractInput,
    CoreLfScaleEngineReviewError,
    CoreLfScaleEngineReviewInput,
    acquireCoreLfCanonicalCommands,
    createCoreLfCanonicalSelectionContract,
    parseCanonicalLambdapiExport,
    validateCoreLfScaleEngineReview
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const repositoryRoot = resolve(__dirname, '..');
const lambdapiRoot = resolve(repositoryRoot, 'emdash2');

const fixtureSource = 'fixture canonical acquisition authority\n';
const fixtureExport = `
require open fixture.base;
flag "eta_equality" on;
injective symbol sample : TYPE;
inductive pair (A : TYPE) : TYPE ≔
| make_pair : A → A → pair A;
rule sample $x ↪ $x
with sample $x $y ↪ $y;
unif_rule sample $x ≡ sample $y ↪ [ $x ≡ $y ];
builtin "sample" ≔ sample;
notation sample prefix 10;
opaque sample;
`;
const fixtureVersion = 'fixture-exporter-1';

const sha256 = (source: string): string =>
    'sha256:' + createHash('sha256').update(source).digest('hex');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const commandExpectation = (
    command: CanonicalLambdapiCommand
): CoreLfCanonicalCommandExpectation => {
    const base = {
        id: `fixture.command-${command.ordinal}`,
        ordinal: command.ordinal,
        kind: command.kind,
        textSha256: sha256(command.text)
    };
    switch (command.kind) {
        case 'require':
            return {
                ...base,
                kind: command.kind,
                open: command.open,
                modules: command.modules
            };
        case 'symbol':
            return {
                ...base,
                kind: command.kind,
                name: command.name,
                modifiers: command.modifiers,
                hasBody: command.hasBody
            };
        case 'inductive':
            return {
                ...base,
                kind: command.kind,
                name: command.name,
                constructorCount: command.constructorCount
            };
        case 'rule':
            return {
                ...base,
                kind: command.kind,
                clauseCount: command.clauseCount
            };
        case 'opaque':
            return {
                ...base,
                kind: command.kind,
                symbols: command.symbols
            };
        case 'flag':
        case 'unif_rule':
        case 'builtin':
        case 'notation':
            return {
                ...base,
                kind: command.kind
            };
        default: {
            const exhaustive: never = command;
            return exhaustive;
        }
    }
};

const fixtureContractInput =
(): CoreLfCanonicalSelectionContractInput => {
    const inventory = parseCanonicalLambdapiExport(
        'fixture.acquisition',
        fixtureExport
    );
    return {
        revision: 'fixture-acquisition-1',
        moduleId: inventory.moduleId,
        authorityPath: 'tests/fixtures/acquisition.lp',
        sourceSha256: sha256(fixtureSource),
        canonicalExport: {
            exporterVersion: fixtureVersion,
            sha256: sha256(fixtureExport),
            imports: inventory.imports
        },
        commands: inventory.commands.map(commandExpectation)
    };
};

const fixtureAcquisitionInput = () => ({
    sourceText: fixtureSource,
    canonicalExportText: fixtureExport,
    observedExporterVersion: fixtureVersion
});

const cloneContract = (
    contract: CoreLfCanonicalSelectionContractInput
): CoreLfCanonicalSelectionContractInput =>
    JSON.parse(JSON.stringify(contract)) as
        CoreLfCanonicalSelectionContractInput;

const expectAcquisitionError = (
    action: () => unknown,
    code: CoreLfCanonicalAcquisitionError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfCanonicalAcquisitionError &&
            error.code === code
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

describe(
    'TypeScript v3.2 reviewed SCALE engine and checked acquisition',
    () => {
        it('records exact H-DTTLF-SCALE-02 approval without semantics', () => {
            const review = CORE_LF_SCALE_ENGINE_REVIEW;
            assert.equal(review.gate, 'H-DTTLF-SCALE-02');
            assert.equal(review.decision, 'D-DTTLF-SCALE-002');
            assert.equal(review.status, 'approved');
            assert.equal(review.approvedOn, '2026-07-25');
            assert.equal(
                review.defaultAcquisition.extraction,
                'small-fail-closed-checked-adapters'
            );
            assert.equal(
                review.generatedArtifactPolicy
                    .productionLambdapiDependency,
                false
            );
            assert.ok(
                review.authorizes.includes(
                    'representative-stress-work'
                )
            );
            assert.ok(
                review.doesNotAuthorize.includes(
                    'active-runtime-rule'
                )
            );
            assert.ok(
                review.doesNotAuthorize.includes(
                    'mechanical-transfer-qualification'
                )
            );
            assertDeepFrozen(review);
            assert.doesNotThrow(() =>
                validateCoreLfScaleEngineReview()
            );
        });

        it('rejects drift from the exact reviewed engine decision', () => {
            const review = JSON.parse(JSON.stringify(
                CORE_LF_SCALE_ENGINE_REVIEW
            )) as CoreLfScaleEngineReviewInput;
            const changed = {
                ...review,
                authorizes: [
                    ...review.authorizes,
                    'active-runtime-rule'
                ]
            } as unknown as CoreLfScaleEngineReviewInput;
            assert.throws(
                () => validateCoreLfScaleEngineReview(changed),
                error =>
                    error instanceof CoreLfScaleEngineReviewError &&
                    error.code === 'REVIEW_DRIFT'
            );
        });

        it('selects every top-level command kind exactly and immutably', () => {
            const contract = createCoreLfCanonicalSelectionContract(
                fixtureContractInput()
            );
            const selection = acquireCoreLfCanonicalCommands(
                contract,
                fixtureAcquisitionInput()
            );

            assert.deepEqual(
                selection.commands.map(entry => entry.command.kind),
                [
                    'require',
                    'flag',
                    'symbol',
                    'inductive',
                    'rule',
                    'unif_rule',
                    'builtin',
                    'notation',
                    'opaque'
                ]
            );
            assert.deepEqual(
                selection.commands.map(entry =>
                    entry.command.ordinal
                ),
                [0, 1, 2, 3, 4, 5, 6, 7, 8]
            );
            assert.equal(selection.canonicalExport.commandCount, 9);
            assert.deepEqual(
                selection.canonicalExport.imports,
                ['fixture.base']
            );
            assertDeepFrozen(contract);
            assertDeepFrozen(selection);
        });

        it('fails closed on artifact, import, and command drift', () => {
            const contract = fixtureContractInput();
            const input = fixtureAcquisitionInput();

            expectAcquisitionError(
                () => acquireCoreLfCanonicalCommands(
                    contract,
                    {
                        ...input,
                        sourceText: input.sourceText + 'drift'
                    }
                ),
                'SOURCE_HASH_MISMATCH'
            );
            expectAcquisitionError(
                () => acquireCoreLfCanonicalCommands(
                    contract,
                    {
                        ...input,
                        observedExporterVersion: 'other-exporter'
                    }
                ),
                'EXPORTER_VERSION_MISMATCH'
            );
            expectAcquisitionError(
                () => acquireCoreLfCanonicalCommands(
                    contract,
                    {
                        ...input,
                        canonicalExportText:
                            input.canonicalExportText + '\n'
                    }
                ),
                'EXPORT_HASH_MISMATCH'
            );

            const importDrift = cloneContract(contract);
            expectAcquisitionError(
                () => acquireCoreLfCanonicalCommands(
                    {
                        ...importDrift,
                        canonicalExport: {
                            ...importDrift.canonicalExport,
                            imports: ['fixture.other']
                        }
                    },
                    input
                ),
                'IMPORT_DRIFT'
            );

            const commandDrift = cloneContract(contract);
            expectAcquisitionError(
                () => acquireCoreLfCanonicalCommands(
                    {
                        ...commandDrift,
                        commands: commandDrift.commands.map(
                            (command, index) =>
                                index === 0
                                    ? {
                                        ...command,
                                        textSha256:
                                            'sha256:' + '0'.repeat(64)
                                    }
                                    : command
                        )
                    },
                    input
                ),
                'COMMAND_DRIFT'
            );

            const missing = cloneContract(contract);
            const last = missing.commands.at(-1);
            assert.notEqual(last, undefined);
            if (last === undefined) return;
            expectAcquisitionError(
                () => acquireCoreLfCanonicalCommands(
                    {
                        ...missing,
                        commands: [
                            ...missing.commands.slice(0, -1),
                            {
                                ...last,
                                ordinal: 99
                            }
                        ]
                    },
                    input
                ),
                'COMMAND_MISSING'
            );
        });

        it('rejects malformed or ambiguous selection contracts', () => {
            const contract = fixtureContractInput();
            expectAcquisitionError(
                () => createCoreLfCanonicalSelectionContract({
                    ...contract,
                    commands: [
                        contract.commands[0],
                        {
                            ...contract.commands[1],
                            id: contract.commands[0].id
                        }
                    ]
                }),
                'INVALID_SELECTION_CONTRACT'
            );
            expectAcquisitionError(
                () => createCoreLfCanonicalSelectionContract({
                    ...contract,
                    authorityPath: '../outside.lp'
                }),
                'INVALID_SELECTION_CONTRACT'
            );
            expectAcquisitionError(
                () => createCoreLfCanonicalSelectionContract({
                    ...contract,
                    canonicalExport: {
                        ...contract.canonicalExport,
                        sha256: 'not-a-hash'
                    }
                }),
                'INVALID_SELECTION_CONTRACT'
            );
        });

        it('pins the first stress command corpus without promotion', () => {
            assert.equal(
                CORE_LF_SCALE_STRESS_1_ACQUISITION_CONTRACTS.length,
                2
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_1_CORE_ACQUISITION.commands
                    .map(command => command.id),
                [
                    'outer-j.declaration',
                    'outer-j.reflexivity-beta',
                    'sigma.decoded-inductive',
                    'sigma.eliminator',
                    'sigma.eliminator-beta',
                    'pi.decoded-classifier',
                    'pi.decoding-beta'
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION.commands
                    .map(command => command.id),
                [
                    'nat.import-core',
                    'nat.addition',
                    'nat.addition-grouped-recursion'
                ]
            );
            CORE_LF_SCALE_STRESS_1_ACQUISITION_CONTRACTS.forEach(
                contract => {
                    const activeSource = readFileSync(
                        resolve(repositoryRoot, contract.authorityPath),
                        'utf8'
                    );
                    assert.equal(
                        sha256(activeSource),
                        contract.sourceSha256
                    );
                    assertDeepFrozen(contract);
                }
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_1B_CORE_ACQUISITION.commands.map(
                    command => command.ordinal
                ),
                [10, 12, 13, 14, 38, 39, 40, 54, 63, 64, 74, 75]
            );
            assertDeepFrozen(
                CORE_LF_SCALE_STRESS_1B_CORE_ACQUISITION
            );

            const implementation = readFileSync(
                resolve(
                    repositoryRoot,
                    'src/v3_2/lf_transfer_acquisition.ts'
                ),
                'utf8'
            );
            assert.doesNotMatch(
                implementation,
                /ind_eqr|Pi_grpd|τΣ_|nat_add/u
            );
            assert.doesNotMatch(
                implementation,
                /spawnSync|lambdapi\s+export/u
            );
            assert.equal(
                'acquireCoreLfCanonicalCommands' in browser,
                false
            );
            assert.equal(
                'CORE_LF_SCALE_ENGINE_REVIEW' in browser,
                false
            );
        });

        it(
            'selects the live J, Pi, Sigma, and grouped-Nat commands',
            {
                skip:
                    process.env.EMDASH_RUN_LAMBDAPI_SCALE_PROBES !== '1'
            },
            () => {
                const version = runLambdapi(['--version']).trim();
                CORE_LF_SCALE_STRESS_1_ACQUISITION_CONTRACTS.forEach(
                    contract => {
                        const sourceText = readFileSync(
                            resolve(
                                repositoryRoot,
                                contract.authorityPath
                            ),
                            'utf8'
                        );
                        const canonicalExportText = runLambdapi([
                            'export',
                            '-o',
                            'lp',
                            basename(contract.authorityPath)
                        ]);
                        const selection =
                            acquireCoreLfCanonicalCommands(
                                contract,
                                {
                                    sourceText,
                                    canonicalExportText,
                                    observedExporterVersion: version
                                }
                            );
                        assert.equal(
                            selection.commands.length,
                            contract.commands.length
                        );
                        assert.deepEqual(
                            selection.commands.map(entry => entry.id),
                            contract.commands.map(entry => entry.id)
                        );
                    }
                );

                const coreExport = runLambdapi([
                    'export',
                    '-o',
                    'lp',
                    'emdash3_2.lp'
                ]);
                const coreSelection = acquireCoreLfCanonicalCommands(
                    CORE_LF_SCALE_STRESS_1_CORE_ACQUISITION,
                    {
                        sourceText: readFileSync(
                            resolve(
                                repositoryRoot,
                                CORE_LF_SCALE_STRESS_1_CORE_ACQUISITION
                                    .authorityPath
                            ),
                            'utf8'
                        ),
                        canonicalExportText: coreExport,
                        observedExporterVersion: version
                    }
                );
                const proposalSelection =
                    acquireCoreLfCanonicalCommands(
                        CORE_LF_SCALE_STRESS_1B_CORE_ACQUISITION,
                        {
                            sourceText: readFileSync(
                                resolve(
                                    repositoryRoot,
                                    CORE_LF_SCALE_STRESS_1B_CORE_ACQUISITION
                                        .authorityPath
                                ),
                                'utf8'
                            ),
                            canonicalExportText: coreExport,
                            observedExporterVersion: version
                        }
                    );
                assert.equal(
                    proposalSelection.commands.length,
                    12
                );
                assert.deepEqual(
                    proposalSelection.commands.map(
                        entry => entry.command.ordinal
                    ),
                    [
                        10, 12, 13, 14, 38, 39,
                        40, 54, 63, 64, 74, 75
                    ]
                );
                const outerJ = coreSelection.commands.find(
                    entry => entry.id === 'outer-j.reflexivity-beta'
                );
                const pi = coreSelection.commands.find(
                    entry => entry.id === 'pi.decoding-beta'
                );
                assert.notEqual(outerJ, undefined);
                assert.notEqual(pi, undefined);
                assert.match(outerJ?.command.text ?? '', /_ \$u \$y/u);
                assert.match(
                    outerJ?.command.text ?? '',
                    /@eq_refl \$a \$y/u
                );
                assert.match(pi?.command.text ?? '', /↪ Π/u);

                const natExport = runLambdapi([
                    'export',
                    '-o',
                    'lp',
                    'emdash3_2_nat_arithmetic.lp'
                ]);
                const natSelection = acquireCoreLfCanonicalCommands(
                    CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION,
                    {
                        sourceText: readFileSync(
                            resolve(
                                repositoryRoot,
                                CORE_LF_SCALE_STRESS_1_NAT_ACQUISITION
                                    .authorityPath
                            ),
                            'utf8'
                        ),
                        canonicalExportText: natExport,
                        observedExporterVersion: version
                    }
                );
                const grouped = natSelection.commands.find(
                    entry =>
                        entry.id ===
                            'nat.addition-grouped-recursion'
                )?.command;
                assert.equal(grouped?.kind, 'rule');
                if (grouped?.kind !== 'rule') return;
                assert.equal(grouped.clauseCount, 3);
                assert.equal(
                    grouped.text.match(/\bwith\b/gu)?.length,
                    2
                );
            }
        );
    }
);
