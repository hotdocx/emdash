/**
 * Focused SCALE-STRESS-2B2 acquisition, runtime-lineage, and internal-Pi
 * base-arrow-action representation evidence.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { basename, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_STRESS_2B2_BOUNDARY,
    CORE_LF_SCALE_STRESS_2B2_MODULE,
    CORE_LF_SCALE_STRESS_2B2_PLAN,
    CORE_LF_SCALE_STRESS_2B2_POLICY,
    CORE_LF_SCALE_STRESS_2B2_SYMBOLS,
    CORE_LF_SCALE_STRESS_2_PI_BASE_ACTION_ACQUISITION,
    CoreLfCompiledRuntimeProgram,
    KernelExpression,
    acquireCoreLfCanonicalCommands,
    checkLambdapiProbe,
    compileCoreLfScaleStress2b2Representation,
    kernelExpressionEquals,
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

const localRuntimePrograms = (
    compilation:
        ReturnType<typeof compileCoreLfScaleStress2b2Representation>
): readonly CoreLfCompiledRuntimeProgram[] =>
    compilation.compiled.phases
        .filter(phase => phase.kind === 'runtime')
        .map(phase => phase.runtime.localProgram);

const flipFirstPlicity = (
    expression: KernelExpression
): KernelExpression => {
    if (
        expression.tag !== 'application' &&
        expression.tag !== 'call'
    ) {
        throw new Error('Expected an applied runtime redex');
    }
    return {
        ...expression,
        arguments: expression.arguments.map((argument, index) =>
            index === 0
                ? {
                    ...argument,
                    plicity:
                        argument.plicity === 'explicit'
                            ? 'implicit'
                            : 'explicit'
                }
                : argument
        )
    };
};

describe(
    'TypeScript v3.2 SCALE-STRESS-2B2 Pi base-arrow action',
    () => {
        it('pins the exact minimal command and phase order', () => {
            const contract =
                CORE_LF_SCALE_STRESS_2_PI_BASE_ACTION_ACQUISITION;
            assert.deepEqual(
                contract.commands.map(command => command.ordinal),
                [512, 927, 1098, 1099, 1119, 1218, 1226, 1227]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2B2_MODULE.declarations.map(
                    declaration => declaration.symbol.name
                ),
                [
                    'Terminal_cat',
                    'Fibre_cat',
                    'functord_transport_lhs_func',
                    'functord_transport_rhs_func',
                    'fdapp1_int_cell',
                    'section_pullback_func'
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2B2_MODULE.runtimeRules.map(
                    rule => rule.order
                ),
                [6, 7]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2B2_PLAN.phases.map(phase => [
                    phase.kind,
                    phase.sourceOrders
                ]),
                [
                    ['declaration', [0]],
                    ['declaration', [1]],
                    ['declaration', [2]],
                    ['declaration', [3]],
                    ['declaration', [4]],
                    ['declaration', [5]],
                    ['runtime', [6]],
                    ['runtime', [7]]
                ]
            );
            assert.equal(
                CORE_LF_SCALE_STRESS_2B2_POLICY.entries.length,
                8
            );
            assertDeepFrozen(contract);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_2B2_MODULE);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_2B2_PLAN);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_2B2_BOUNDARY);
        });

        it('extends the exact 2B1 runtime and preserves body boundaries', () => {
            const compilation =
                compileCoreLfScaleStress2b2Representation();
            const prior = compilation.prerequisite
                .compiled.latestRuntime?.runtime.ruleIds;
            assert.notEqual(prior, undefined);
            if (prior === undefined) return;
            assert.equal(prior.length, 19);
            assert.deepEqual(
                compilation.compiled.latestRuntime?.runtime.ruleIds,
                [
                    ...prior,
                    'stress.internal-pi.base-action',
                    'stress.internal-pi.pullback-base-action'
                ]
            );

            const programs = localRuntimePrograms(compilation);
            assert.deepEqual(
                programs.map(program => {
                    const rule = program.rules[0];
                    return [
                        rule.id,
                        rule.subjectValidation.kind,
                        rule.checkedWithEarlierRuleIds.length
                    ];
                }),
                [
                    [
                        'stress.internal-pi.base-action',
                        'external-oracle-required',
                        19
                    ],
                    [
                        'stress.internal-pi.pullback-base-action',
                        'external-oracle-required',
                        20
                    ]
                ]
            );

            const context = compilation.compiled.declarations;
            assert.equal(
                context.declaration(
                    CORE_LF_SCALE_STRESS_2B2_SYMBOLS.fibreCategory
                )?.status,
                'installed-transparent'
            );
            [
                CORE_LF_SCALE_STRESS_2B2_SYMBOLS
                    .displayedTransportLeft,
                CORE_LF_SCALE_STRESS_2B2_SYMBOLS
                    .displayedTransportRight
            ].forEach(symbol => {
                assert.equal(
                    context.declaration(symbol)?.status,
                    'installed-opaque'
                );
            });
        });

        it('executes both clauses and rejects a plicity near miss', () => {
            const compilation =
                compileCoreLfScaleStress2b2Representation();
            const runtime = compilation.compiled.latestRuntime?.runtime;
            assert.notEqual(runtime, undefined);
            if (runtime === undefined) return;

            const witnessSource = provenance(
                'derived',
                'SCALE-STRESS-2B2 runtime witness'
            );
            const programs = localRuntimePrograms(compilation);
            programs.forEach((program, programIndex) => {
                const rule = program.rules[0];
                const bindings = rule.variables.map((variable, index) =>
                    kernelFree(
                        `stress2b2_${programIndex}_${index}_` +
                            variable.name,
                        witnessSource
                    )
                );
                const redex = program.instantiateRuleLeft(
                    rule,
                    bindings,
                    witnessSource
                );
                const result = runtime.rewriteHead(redex);
                assert.equal(result.status, 'rewritten');
                if (result.status !== 'rewritten') return;
                assert.equal(result.ruleId, rule.id);
                assert.equal(
                    kernelExpressionEquals(result.before, redex),
                    true
                );
            });

            const lastProgram = programs[programs.length - 1];
            const lastRule = lastProgram.rules[0];
            const bindings = lastRule.variables.map((variable, index) =>
                kernelFree(
                    `stress2b2_near_${index}_${variable.name}`,
                    witnessSource
                )
            );
            const redex = lastProgram.instantiateRuleLeft(
                lastRule,
                bindings,
                witnessSource
            );
            assert.equal(
                runtime.rewriteHead(flipFirstPlicity(redex)).status,
                'irreducible'
            );
        });

        it(
            'matches live acquisition and Lambdapi base-arrow action',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_SCALE_TELESCOPE_STRESS_PROBES !==
                    '1'
            },
            () => {
                const contract =
                    CORE_LF_SCALE_STRESS_2_PI_BASE_ACTION_ACQUISITION;
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
                    'symbol stress2b2_A : Cat;',
                    'symbol stress2b2_B : Cat;',
                    'symbol stress2b2_F : ' +
                        'τ (Functor stress2b2_A stress2b2_B);',
                    'symbol stress2b2_E0 : τ (Catd stress2b2_B);',
                    'symbol stress2b2_b : τ (Obj stress2b2_B);',
                    'symbol stress2b2_bad : ' +
                        'τ (Functor ' +
                        '(@Functord_cat stress2b2_B ' +
                        '(@Const_catd stress2b2_B Terminal_cat) ' +
                        'stress2b2_E0) ' +
                        '(@Functord_cat stress2b2_A ' +
                        '(@Const_catd stress2b2_A Terminal_cat) ' +
                        '(@Pullback_catd stress2b2_A stress2b2_B ' +
                        'stress2b2_E0 stress2b2_F)));',
                    'symbol stress2b2_K : Cat;',
                    'symbol stress2b2_G : ' +
                        'τ (Functor stress2b2_K ' +
                        '(Op_cat Cat_cat));',
                    'symbol stress2b2_x : τ (Obj stress2b2_K);',
                    'symbol stress2b2_y : τ (Obj stress2b2_K);',
                    'symbol stress2b2_p : ' +
                        'τ (Hom stress2b2_K ' +
                        'stress2b2_x stress2b2_y);',
                    'symbol stress2b2_E : ' +
                        'τ (Catd (@fapp0 stress2b2_K ' +
                        '(Op_cat Cat_cat) stress2b2_G ' +
                        'stress2b2_x));'
                ];
                const positive = checkLambdapiProbe(
                    {
                        source: [
                            ...header,
                            'assert ⊢ @Fibre_cat stress2b2_B ' +
                                'stress2b2_E0 stress2b2_b ≡ ' +
                                '@fapp0 stress2b2_B Cat_cat ' +
                                'stress2b2_E0 stress2b2_b;',
                            'assert ⊢ @fdapp1_int_cell ' +
                                '(Op_cat Cat_cat) Catd_cat_func ' +
                                '(@Const_catd ' +
                                '(Op_cat Cat_cat) Cat_cat) ' +
                                'Pi_int_funcd stress2b2_B ' +
                                'stress2b2_A stress2b2_F ' +
                                'stress2b2_E0 ≡ ' +
                                '@section_pullback_func ' +
                                'stress2b2_A stress2b2_B ' +
                                'stress2b2_F stress2b2_E0;',
                            'assert ⊢ @fdapp1_int_cell ' +
                                'stress2b2_K ' +
                                '(@Pullback_catd stress2b2_K ' +
                                '(Op_cat Cat_cat) Catd_cat_func ' +
                                'stress2b2_G) ' +
                                '(@Const_catd stress2b2_K Cat_cat) ' +
                                '(@Pi_pullback_funcd ' +
                                'stress2b2_K stress2b2_G) ' +
                                'stress2b2_x stress2b2_y ' +
                                'stress2b2_p stress2b2_E ≡ ' +
                                '@section_pullback_func ' +
                                '(@fapp0 stress2b2_K ' +
                                '(Op_cat Cat_cat) stress2b2_G ' +
                                'stress2b2_y) ' +
                                '(@fapp0 stress2b2_K ' +
                                '(Op_cat Cat_cat) stress2b2_G ' +
                                'stress2b2_x) ' +
                                '(@fapp1_fapp0 stress2b2_K ' +
                                '(Op_cat Cat_cat) stress2b2_G ' +
                                'stress2b2_x stress2b2_y ' +
                                'stress2b2_p) stress2b2_E;',
                            'assertnot ⊢ @fdapp1_int_cell ' +
                                '(Op_cat Cat_cat) Catd_cat_func ' +
                                '(@Const_catd ' +
                                '(Op_cat Cat_cat) Cat_cat) ' +
                                'Pi_int_funcd stress2b2_B ' +
                                'stress2b2_A stress2b2_F ' +
                                'stress2b2_E0 ≡ stress2b2_bad;'
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
                            'assert ⊢ @fdapp1_int_cell ' +
                                '(Op_cat Cat_cat) Catd_cat_func ' +
                            '(@Const_catd ' +
                                '(Op_cat Cat_cat) Cat_cat) ' +
                                'Pi_int_funcd stress2b2_B ' +
                                'stress2b2_A stress2b2_F ' +
                                'stress2b2_E0 ≡ stress2b2_bad;'
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
                'CORE_LF_SCALE_STRESS_2B2_MODULE' in browser,
                false
            );
            assert.equal(
                'compileCoreLfScaleStress2b2Representation' in browser,
                false
            );
            const authorityText = readFileSync(
                resolve(
                    repositoryRoot,
                    CORE_LF_SCALE_STRESS_2B2_MODULE.authorityPath
                ),
                'utf8'
            );
            [
                ...CORE_LF_SCALE_STRESS_2B2_MODULE.declarations,
                ...CORE_LF_SCALE_STRESS_2B2_MODULE.runtimeRules
            ].forEach(entry => {
                assert.ok(
                    authorityText.includes(
                        entry.provenance.sourceFragment
                    ),
                    entry.provenance.sourceFragment
                );
            });

            const genericSources = [
                'src/v3_2/lf_transfer_compiler.ts',
                'src/v3_2/lf_transfer_runtime.ts',
                'src/v3_2/lf_transfer_mixed.ts'
            ].map(path => readFileSync(
                resolve(repositoryRoot, path),
                'utf8'
            )).join('\n');
            [
                'fdapp1_int_cell',
                'section_pullback_func',
                'functord_transport_lhs_func'
            ].forEach(name => {
                assert.equal(genericSources.includes(name), false);
            });
        });
    }
);
