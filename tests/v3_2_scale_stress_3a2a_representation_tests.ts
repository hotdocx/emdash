/**
 * Focused SCALE-STRESS-3A2A profunctor comparison-action qualification.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { basename, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_STRESS_3A2A_BOUNDARY,
    CORE_LF_SCALE_STRESS_3A2A_LINKAGE,
    CORE_LF_SCALE_STRESS_3A2A_MODULE,
    CORE_LF_SCALE_STRESS_3A2A_INTRINSIC_DEFINITIONS,
    CORE_LF_SCALE_STRESS_3A2A_PLAN,
    CORE_LF_SCALE_STRESS_3A2A_POLICY,
    CORE_LF_SCALE_STRESS_3A2A_SYMBOLS,
    CORE_LF_SCALE_STRESS_3A1_SYMBOLS,
    CORE_LF_SCALE_STRESS_3_PROFUNCTOR_COMPARISON_ACQUISITION,
    CoreLfCompiledMixedModule,
    CoreLfQualifiedSymbol,
    acquireCoreLfCanonicalCommands,
    checkLambdapiProbe,
    compileCoreLfScaleStress3a2aRepresentation,
    coreLfCombinedWeakHead,
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
    compiled: CoreLfCompiledMixedModule,
    symbol: CoreLfQualifiedSymbol
): string => {
    const declaration = compiled.declarations.declaration(symbol);
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
    'TypeScript v3.2 SCALE-STRESS-3A2A profunctor comparison action',
    () => {
        it('pins source order, policy, intrinsic delta, and mixed phases', () => {
            const contract =
                CORE_LF_SCALE_STRESS_3_PROFUNCTOR_COMPARISON_ACQUISITION;
            assert.deepEqual(
                contract.commands.map(command => command.ordinal),
                [230, 232, 406, 407, 547, 579, 580, 1235, 1264, 1265]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_3A2A_MODULE.declarations.map(
                    declaration => declaration.symbol.name
                ),
                [
                    'Hom',
                    'id',
                    'id_func',
                    'hom_postcomp_fapp0',
                    'defiso_to',
                    'defiso_from',
                    'ProfMap',
                    'prof_comparison_push',
                    'prof_comparison_pull'
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_3A2A_POLICY.entries.map(
                    entry => entry.policy
                ),
                [
                    'checked-transparent-definition',
                    'opaque-signature',
                    'checked-transparent-definition',
                    'runtime-rewrite',
                    'opaque-signature',
                    'opaque-signature',
                    'opaque-signature',
                    'checked-transparent-definition',
                    'checked-transparent-definition',
                    'checked-transparent-definition'
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_3A2A_PLAN.phases.map(
                    phase => phase.kind
                ),
                [
                    'declaration',
                    'declaration',
                    'declaration',
                    'runtime',
                    'declaration',
                    'declaration',
                    'declaration',
                    'declaration',
                    'declaration',
                    'declaration'
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_3A2A_INTRINSIC_DEFINITIONS.map(
                    definition => [
                        definition.acquisitionId,
                        definition.sourceSymbol.name,
                        definition.targetOwner,
                        definition.sourceDependencies.map(
                            dependency => dependency.name
                        ),
                        definition.consumer.name
                    ]
                ),
                [[
                    'profunctor-comparison.hom-classifier',
                    'Hom',
                    'hom-classifier',
                    ['Obj', 'Hom_cat'],
                    'ProfMap'
                ]]
            );
            assert.equal(
                CORE_LF_SCALE_STRESS_3A2A_LINKAGE.entries.length,
                21
            );
            [
                contract,
                CORE_LF_SCALE_STRESS_3A2A_MODULE,
                CORE_LF_SCALE_STRESS_3A2A_POLICY,
                CORE_LF_SCALE_STRESS_3A2A_PLAN,
                CORE_LF_SCALE_STRESS_3A2A_LINKAGE,
                CORE_LF_SCALE_STRESS_3A2A_INTRINSIC_DEFINITIONS,
                CORE_LF_SCALE_STRESS_3A2A_BOUNDARY
            ].forEach(assertDeepFrozen);
        });

        it('checks all declarations and executes the nested identity action', () => {
            const compilation =
                compileCoreLfScaleStress3a2aRepresentation();
            const compiled = compilation.compiled;
            const symbols = CORE_LF_SCALE_STRESS_3A2A_SYMBOLS;
            const declarations = compiled.declarations.modules.flatMap(
                module => module.declarations
            );
            assert.deepEqual(
                declarations.map(declaration => [
                    declaration.symbol.name,
                    declaration.status
                ]),
                [
                    ['Hom', 'intrinsic-transparent'],
                    ['id', 'installed-opaque'],
                    ['id_func', 'installed-transparent'],
                    ['hom_postcomp_fapp0', 'installed-opaque'],
                    ['defiso_to', 'installed-opaque'],
                    ['defiso_from', 'installed-opaque'],
                    ['ProfMap', 'installed-transparent'],
                    ['prof_comparison_push', 'installed-transparent'],
                    ['prof_comparison_pull', 'installed-transparent']
                ]
            );
            assert.deepEqual(
                compiled.latestRuntime?.runtime.ruleIds.slice(-1),
                ['stress.profunctor-comparison.identity-object']
            );

            const source = provenance(
                'derived',
                'SCALE-STRESS-3A2A comparison-action witness'
            );
            const A = kernelFree('stress3a2a_A', source);
            const B = kernelFree('stress3a2a_B', source);
            const P = kernelFree('stress3a2a_P', source);
            const Q = kernelFree('stress3a2a_Q', source);
            const base = kernelCall(
                kernelFree(
                    freeDeclarationName(
                        compiled,
                        CORE_LF_SCALE_STRESS_3A1_SYMBOLS
                            .profunctorCategory
                    ),
                    source
                ),
                [
                    { plicity: 'explicit', value: A },
                    { plicity: 'explicit', value: B }
                ],
                source
            );
            const profunctorMap = kernelCall(
                kernelFree(
                    freeDeclarationName(
                        compiled,
                        symbols.profunctorMap
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
            const foldedHom = kernelApplication(
                'hom-classifier',
                [
                    { value: base },
                    { value: P },
                    { value: Q }
                ],
                source
            );
            const folded = coreLfDefinitionalCompare(
                compiled.declarations.environment,
                profunctorMap,
                foldedHom,
                16,
                undefined,
                compiled.latestRuntime?.runtime
            );
            assert.equal(folded.status, 'equal');
            assert.equal(
                folded.trace.some(entry =>
                    entry.reduction.kind === 'delta' &&
                    entry.reduction.declarationName ===
                        freeDeclarationName(
                            compiled,
                            symbols.profunctorMap
                        )
                ),
                true
            );

            const homBody = kernelApplication(
                'object-classifier',
                [{
                    value: kernelApplication(
                        'hom-category',
                        [
                            { value: base },
                            { value: P },
                            { value: Q }
                        ],
                        source
                    )
                }],
                source
            );
            const intrinsicHom = coreLfDefinitionalCompare(
                compiled.declarations.environment,
                foldedHom,
                homBody,
                8,
                undefined,
                compiled.latestRuntime?.runtime
            );
            assert.equal(intrinsicHom.status, 'equal');
            assert.deepEqual(
                intrinsicHom.trace.map(
                    entry => entry.reduction.kind
                ),
                ['delta', 'beta', 'beta', 'beta']
            );
            assert.equal(
                intrinsicHom.trace[0].reduction.kind === 'delta'
                    ? intrinsicHom.trace[0].reduction.declarationName
                    : undefined,
                'emdash.emdash3_2.Hom'
            );

            const identityFunctor = kernelCall(
                kernelFree(
                    freeDeclarationName(
                        compiled,
                        symbols.identityFunctor
                    ),
                    source
                ),
                [{ plicity: 'implicit', value: base }],
                source
            );
            const identityApplication = kernelApplication(
                'functor-object',
                [
                    { value: base },
                    { value: base },
                    { value: identityFunctor },
                    { value: P }
                ],
                source
            );
            const identity = coreLfDefinitionalCompare(
                compiled.declarations.environment,
                P,
                identityApplication,
                16,
                undefined,
                compiled.latestRuntime?.runtime
            );
            assert.equal(identity.status, 'equal');
            assert.deepEqual(
                identity.trace.map(entry => entry.reduction.kind),
                ['delta', 'beta', 'runtime']
            );
            assert.equal(
                identity.trace[2].reduction.kind === 'runtime'
                    ? identity.trace[2].reduction.ruleId
                    : undefined,
                'stress.profunctor-comparison.identity-object'
            );
        });

        it('delta-reduces push and pull to the opaque generic action', () => {
            const compilation =
                compileCoreLfScaleStress3a2aRepresentation();
            const compiled = compilation.compiled;
            const symbols = CORE_LF_SCALE_STRESS_3A2A_SYMBOLS;
            const source = provenance(
                'derived',
                'SCALE-STRESS-3A2A push/pull delta witness'
            );
            const values = {
                A: kernelFree('stress3a2a_delta_A', source),
                B: kernelFree('stress3a2a_delta_B', source),
                P: kernelFree('stress3a2a_delta_P', source),
                Q: kernelFree('stress3a2a_delta_Q', source),
                i: kernelFree('stress3a2a_delta_i', source),
                R: kernelFree('stress3a2a_delta_R', source),
                incoming: kernelFree(
                    'stress3a2a_delta_incoming',
                    source
                )
            };
            const arguments_ = [
                { plicity: 'implicit' as const, value: values.A },
                { plicity: 'implicit' as const, value: values.B },
                { plicity: 'implicit' as const, value: values.P },
                { plicity: 'implicit' as const, value: values.Q },
                { plicity: 'explicit' as const, value: values.i },
                { plicity: 'implicit' as const, value: values.R },
                {
                    plicity: 'explicit' as const,
                    value: values.incoming
                }
            ];
            [
                symbols.comparisonPush,
                symbols.comparisonPull
            ].forEach(symbol => {
                const reduction = coreLfCombinedWeakHead(
                    compiled.declarations.environment,
                    kernelCall(
                        kernelFree(
                            freeDeclarationName(compiled, symbol),
                            source
                        ),
                        arguments_,
                        source
                    ),
                    16,
                    undefined,
                    compiled.latestRuntime?.runtime
                );
                assert.equal(reduction.status, 'weak-head-normal');
                assert.deepEqual(
                    reduction.trace.map(entry => entry.kind),
                    [
                        'delta',
                        'beta',
                        'beta',
                        'beta',
                        'beta',
                        'beta',
                        'beta',
                        'beta'
                    ]
                );
                assert.equal(reduction.expression.tag, 'call');
                if (reduction.expression.tag !== 'call') {
                    throw new Error('Expected opaque postcomposition call');
                }
                assert.equal(
                    reduction.expression.callee.tag,
                    'reference'
                );
                assert.equal(
                    reduction.expression.callee.tag === 'reference'
                        ? reduction.expression.callee.name
                        : undefined,
                    freeDeclarationName(
                        compiled,
                        symbols.postcompositionAction
                    )
                );
            });
        });

        it(
            'matches live acquisition and push/pull typing',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_SCALE_PROFUNCTOR_STRESS_PROBES !==
                    '1'
            },
            () => {
                const contract =
                    CORE_LF_SCALE_STRESS_3_PROFUNCTOR_COMPARISON_ACQUISITION;
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
                    'symbol stress3a2a_A : Cat;',
                    'symbol stress3a2a_B : Cat;',
                    'symbol stress3a2a_P : ' +
                        'τ (Prof stress3a2a_A stress3a2a_B);',
                    'symbol stress3a2a_Q : ' +
                        'τ (Prof stress3a2a_A stress3a2a_B);',
                    'symbol stress3a2a_R : ' +
                        'τ (Prof stress3a2a_A stress3a2a_B);',
                    'symbol stress3a2a_i : τ (@ProfComparison ' +
                        'stress3a2a_A stress3a2a_B ' +
                        'stress3a2a_P stress3a2a_Q);',
                    'symbol stress3a2a_r : τ (@ProfMap ' +
                        'stress3a2a_A stress3a2a_B ' +
                        'stress3a2a_R stress3a2a_P);',
                    'symbol stress3a2a_s : τ (@ProfMap ' +
                        'stress3a2a_A stress3a2a_B ' +
                        'stress3a2a_R stress3a2a_Q);'
                ];
                const push = '@prof_comparison_push ' +
                    'stress3a2a_A stress3a2a_B ' +
                    'stress3a2a_P stress3a2a_Q stress3a2a_i ' +
                    'stress3a2a_R stress3a2a_r';
                const pull = '@prof_comparison_pull ' +
                    'stress3a2a_A stress3a2a_B ' +
                    'stress3a2a_P stress3a2a_Q stress3a2a_i ' +
                    'stress3a2a_R stress3a2a_s';
                const positive = checkLambdapiProbe(
                    {
                        source: [
                            ...header,
                            'symbol stress3a2a_push : τ (@ProfMap ' +
                                'stress3a2a_A stress3a2a_B ' +
                                'stress3a2a_R stress3a2a_Q) ' +
                                `≔ ${push};`,
                            'symbol stress3a2a_pull : τ (@ProfMap ' +
                                'stress3a2a_A stress3a2a_B ' +
                                'stress3a2a_R stress3a2a_P) ' +
                                `≔ ${pull};`
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
                            'symbol stress3a2a_bad : τ (@ProfMap ' +
                                'stress3a2a_A stress3a2a_B ' +
                                'stress3a2a_R stress3a2a_P) ' +
                                `≔ ${push};`
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
            }
        );

        it('keeps the representation isolated and generic engines owner-free', () => {
            assert.equal(
                'CORE_LF_SCALE_STRESS_3A2A_MODULE' in browser,
                false
            );
            assert.equal(
                'compileCoreLfScaleStress3a2aRepresentation' in browser,
                false
            );
            const authorityText = readFileSync(
                resolve(
                    repositoryRoot,
                    CORE_LF_SCALE_STRESS_3A2A_MODULE.authorityPath
                ),
                'utf8'
            );
            CORE_LF_SCALE_STRESS_3A2A_MODULE.declarations.forEach(
                declaration => assert.ok(
                    authorityText.includes(
                        declaration.provenance.sourceFragment
                    ),
                    declaration.provenance.sourceFragment
                )
            );
            assert.ok(authorityText.includes(
                CORE_LF_SCALE_STRESS_3A2A_INTRINSIC_DEFINITIONS[0]
                    .sourceBody
            ));

            const genericSources = [
                'src/v3_2/lf_transfer_compiler.ts',
                'src/v3_2/lf_transfer_runtime.ts',
                'src/v3_2/lf_transfer_mixed.ts',
                'src/v3_2/lf_conversion.ts'
            ].map(path => readFileSync(
                resolve(repositoryRoot, path),
                'utf8'
            ));
            [
                'ProfMap',
                'prof_comparison_push',
                'profunctor-comparison'
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
