/**
 * Focused SCALE-STRESS-3A1 acquisition, opacity, and transparent-delta
 * evidence for the first profunctor boundary.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { basename, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_STRESS_3A1_BOUNDARY,
    CORE_LF_SCALE_STRESS_3A1_LINKAGE,
    CORE_LF_SCALE_STRESS_3A1_MODULE,
    CORE_LF_SCALE_STRESS_3A1_POLICY,
    CORE_LF_SCALE_STRESS_3A1_SYMBOLS,
    CORE_LF_SCALE_STRESS_3_PROFUNCTOR_BOUNDARY_ACQUISITION,
    CoreLfCompiledDeclarationModule,
    CoreLfQualifiedSymbol,
    acquireCoreLfCanonicalCommands,
    checkLambdapiProbe,
    compileCoreLfScaleStress3a1Representation,
    coreLfDefinitionalCompare,
    kernelApplication,
    kernelCall,
    kernelFree,
    provenance
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

const freeDeclarationName = (
    compiled: CoreLfCompiledDeclarationModule,
    symbol: CoreLfQualifiedSymbol
): string => {
    const declaration = compiled.declaration(symbol);
    assert.notEqual(declaration, undefined);
    assert.equal(declaration?.link.kind, 'free-declaration');
    if (
        declaration === undefined ||
        declaration.link.kind !== 'free-declaration'
    ) {
        throw new Error('Expected a compiled free declaration');
    }
    return declaration.link.coreName;
};

describe(
    'TypeScript v3.2 SCALE-STRESS-3A1 profunctor boundary',
    () => {
        it('pins the exact non-contiguous command and policy order', () => {
            const contract =
                CORE_LF_SCALE_STRESS_3_PROFUNCTOR_BOUNDARY_ACQUISITION;
            assert.deepEqual(
                contract.commands.map(command => command.ordinal),
                [578, 1229, 1233, 1263, 1293]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_3A1_MODULE.declarations.map(
                    declaration => declaration.symbol.name
                ),
                [
                    'DefIso',
                    'Prof_cat',
                    'Prof',
                    'ProfComparison',
                    'Prof_tensor'
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_3A1_POLICY.entries.map(
                    entry => entry.policy
                ),
                [
                    'opaque-signature',
                    'opaque-signature',
                    'checked-transparent-definition',
                    'checked-transparent-definition',
                    'opaque-signature'
                ]
            );
            assert.equal(
                CORE_LF_SCALE_STRESS_3A1_LINKAGE.entries.length,
                9
            );
            assertDeepFrozen(contract);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_3A1_MODULE);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_3A1_POLICY);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_3A1_LINKAGE);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_3A1_BOUNDARY);
        });

        it('checks the deep transparent chain and preserves opacity', () => {
            const compilation =
                compileCoreLfScaleStress3a1Representation();
            const compiled = compilation.compiled;
            const symbols = CORE_LF_SCALE_STRESS_3A1_SYMBOLS;

            assert.deepEqual(
                compiled.declarations.map(declaration => [
                    declaration.symbol.name,
                    declaration.status
                ]),
                [
                    ['DefIso', 'installed-opaque'],
                    ['Prof_cat', 'installed-opaque'],
                    ['Prof', 'installed-transparent'],
                    ['ProfComparison', 'installed-transparent'],
                    ['Prof_tensor', 'installed-opaque']
                ]
            );
            assert.equal(compiled.initialDeclarationCount, 9);
            assert.equal(compiled.environment.declarations.length, 14);
            compiled.createChecker().validateEnvironment();

            const source = provenance(
                'derived',
                'SCALE-STRESS-3A1 transparent-delta witness'
            );
            const A = kernelFree('stress3a1_A', source);
            const B = kernelFree('stress3a1_B', source);
            const X = kernelFree('stress3a1_X', source);
            const P = kernelFree('stress3a1_P', source);
            const Q = kernelFree('stress3a1_Q', source);
            const S = kernelFree('stress3a1_S', source);

            const profCategory = kernelCall(
                kernelFree(
                    freeDeclarationName(
                        compiled,
                        symbols.profunctorCategory
                    ),
                    source
                ),
                [
                    { plicity: 'explicit', value: A },
                    { plicity: 'explicit', value: B }
                ],
                source
            );
            const prof = kernelCall(
                kernelFree(
                    freeDeclarationName(
                        compiled,
                        symbols.profunctorClassifier
                    ),
                    source
                ),
                [
                    { plicity: 'explicit', value: A },
                    { plicity: 'explicit', value: B }
                ],
                source
            );
            const objectOfProfCategory = kernelApplication(
                'object-classifier',
                [{ value: profCategory }],
                source
            );
            const profDelta = coreLfDefinitionalCompare(
                compiled.environment,
                prof,
                objectOfProfCategory,
                16
            );
            assert.equal(profDelta.status, 'equal');
            assert.equal(
                profDelta.trace.some(entry =>
                    entry.reduction.kind === 'delta' &&
                    entry.reduction.declarationName ===
                        freeDeclarationName(
                            compiled,
                            symbols.profunctorClassifier
                        )
                ),
                true
            );

            const comparison = kernelCall(
                kernelFree(
                    freeDeclarationName(
                        compiled,
                        symbols.profunctorComparison
                    ),
                    source
                ),
                [
                    { plicity: 'implicit', value: A },
                    { plicity: 'implicit', value: B },
                    { plicity: 'explicit', value: P },
                    { plicity: 'explicit', value: Q }
                ],
                source
            );
            const definition = kernelCall(
                kernelFree(
                    freeDeclarationName(
                        compiled,
                        symbols.definitionalIsomorphism
                    ),
                    source
                ),
                [
                    { plicity: 'implicit', value: profCategory },
                    { plicity: 'explicit', value: P },
                    { plicity: 'explicit', value: Q }
                ],
                source
            );
            const comparisonDelta = coreLfDefinitionalCompare(
                compiled.environment,
                comparison,
                definition,
                16
            );
            assert.equal(comparisonDelta.status, 'equal');
            assert.equal(
                comparisonDelta.trace.some(entry =>
                    entry.reduction.kind === 'delta' &&
                    entry.reduction.declarationName ===
                        freeDeclarationName(
                            compiled,
                            symbols.profunctorComparison
                        )
                ),
                true
            );

            const tensor = kernelCall(
                kernelFree(
                    freeDeclarationName(
                        compiled,
                        symbols.profunctorTensor
                    ),
                    source
                ),
                [
                    { plicity: 'implicit', value: A },
                    { plicity: 'implicit', value: B },
                    { plicity: 'implicit', value: X },
                    { plicity: 'explicit', value: P },
                    { plicity: 'explicit', value: S }
                ],
                source
            );
            const opaque = coreLfDefinitionalCompare(
                compiled.environment,
                tensor,
                P,
                16
            );
            assert.equal(opaque.status, 'not-equal');
            assert.equal(
                opaque.trace.some(entry =>
                    entry.reduction.kind === 'delta' &&
                    entry.reduction.declarationName ===
                        freeDeclarationName(
                            compiled,
                            symbols.profunctorTensor
                        )
                ),
                false
            );
        });

        it(
            'matches live acquisition and Lambdapi opacity',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_SCALE_PROFUNCTOR_STRESS_PROBES !==
                    '1'
            },
            () => {
                const contract =
                    CORE_LF_SCALE_STRESS_3_PROFUNCTOR_BOUNDARY_ACQUISITION;
                const selection = acquireCoreLfCanonicalCommands(
                    contract,
                    {
                        sourceText: readFileSync(
                            resolve(
                                repositoryRoot,
                                contract.authorityPath
                            ),
                            'utf8'
                        ),
                        canonicalExportText: runLambdapi([
                            'export',
                            '-o',
                            'lp',
                            basename(contract.authorityPath)
                        ]),
                        observedExporterVersion:
                            runLambdapi(['--version']).trim()
                    }
                );
                assert.deepEqual(
                    selection.commands.map(entry =>
                        entry.command.ordinal
                    ),
                    contract.commands.map(command => command.ordinal)
                );

                const header = [
                    'require open emdash.emdash3_2;',
                    'symbol stress3a1_A : Cat;',
                    'symbol stress3a1_B : Cat;',
                    'symbol stress3a1_X : Cat;',
                    'symbol stress3a1_P : τ ' +
                        '(Prof stress3a1_A stress3a1_B);',
                    'symbol stress3a1_Q : τ ' +
                        '(Prof stress3a1_A stress3a1_B);',
                    'symbol stress3a1_S : τ ' +
                        '(Prof stress3a1_B stress3a1_X);',
                    'symbol stress3a1_T : τ ' +
                        '(Prof stress3a1_A stress3a1_X);'
                ];
                const tensor = [
                    '@Prof_tensor stress3a1_A stress3a1_B',
                    'stress3a1_X stress3a1_P stress3a1_S'
                ].join(' ');
                const positive = checkLambdapiProbe(
                    {
                        source: [
                            ...header,
                            'assert ⊢ Prof stress3a1_A stress3a1_B ≡ ' +
                                'Obj (Prof_cat stress3a1_A stress3a1_B);',
                            'assert ⊢ @ProfComparison stress3a1_A ' +
                                'stress3a1_B stress3a1_P stress3a1_Q ≡ ' +
                                '@DefIso (Prof_cat stress3a1_A ' +
                                'stress3a1_B) stress3a1_P stress3a1_Q;',
                            `assertnot ⊢ ${tensor} ≡ stress3a1_T;`
                        ].join('\n'),
                        sourceMap: []
                    },
                    {
                        packageRoot: lambdapiRoot,
                        timeoutMs: 30_000
                    }
                );
                assert.equal(
                    positive.accepted,
                    true,
                    positive.diagnostics
                );
                assert.equal(positive.timedOut, false);

                const negative = checkLambdapiProbe(
                    {
                        source: [
                            ...header,
                            `assert ⊢ ${tensor} ≡ stress3a1_T;`
                        ].join('\n'),
                        sourceMap: []
                    },
                    {
                        packageRoot: lambdapiRoot,
                        timeoutMs: 30_000
                    }
                );
                assert.equal(negative.accepted, false);
                assert.equal(negative.timedOut, false);
                assert.match(
                    negative.diagnostics,
                    /Assertion failed/u
                );
            }
        );

        it('keeps the slice local and generic engines owner-free', () => {
            assert.equal(
                'CORE_LF_SCALE_STRESS_3A1_MODULE' in browser,
                false
            );
            assert.equal(
                'compileCoreLfScaleStress3a1Representation' in browser,
                false
            );
            const authorityText = readFileSync(
                resolve(
                    repositoryRoot,
                    CORE_LF_SCALE_STRESS_3A1_MODULE.authorityPath
                ),
                'utf8'
            );
            CORE_LF_SCALE_STRESS_3A1_MODULE.declarations.forEach(
                declaration => {
                    assert.ok(
                        authorityText.includes(
                            declaration.provenance.sourceFragment
                        ),
                        declaration.provenance.sourceFragment
                    );
                }
            );

            const genericSources = [
                'src/v3_2/lf_transfer_compiler.ts',
                'src/v3_2/lf_transfer_runtime.ts',
                'src/v3_2/lf_transfer_mixed.ts'
            ].map(path => readFileSync(
                resolve(repositoryRoot, path),
                'utf8'
            ));
            [
                'ProfComparison',
                'Prof_tensor',
                'profunctor'
            ].forEach(ownerName => {
                genericSources.forEach(sourceText => {
                    assert.equal(
                        sourceText.includes(ownerName),
                        false,
                        ownerName
                    );
                });
            });
        });
    }
);
