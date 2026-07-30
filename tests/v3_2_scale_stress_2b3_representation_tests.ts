/**
 * Focused SCALE-STRESS-2B3 acquisition, runtime-lineage, and Sigma-total
 * displayed-transfor uncurrying evidence.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { basename, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_STRESS_2B3_BOUNDARY,
    CORE_LF_SCALE_STRESS_2B3_MODULE,
    CORE_LF_SCALE_STRESS_2B3_PLAN,
    CORE_LF_SCALE_STRESS_2B3_POLICY,
    CORE_LF_SCALE_STRESS_2B3_SYMBOLS,
    CORE_LF_SCALE_STRESS_2_SIGMA_TRANSFOR_ACQUISITION,
    CoreLfCompiledRuntimeProgram,
    KernelExpression,
    acquireCoreLfCanonicalCommands,
    checkLambdapiProbe,
    compileCoreLfScaleStress2b3Representation,
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
        ReturnType<typeof compileCoreLfScaleStress2b3Representation>
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
    'TypeScript v3.2 SCALE-STRESS-2B3 Sigma transfor uncurrying',
    () => {
        it('pins the exact command and phase order', () => {
            const contract =
                CORE_LF_SCALE_STRESS_2_SIGMA_TRANSFOR_ACQUISITION;
            assert.deepEqual(
                contract.commands.map(command => command.ordinal),
                [401, 402, 1028, 1029, 1031, 1080, 1082, 1092]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2B3_MODULE.declarations.map(
                    declaration => declaration.symbol.name
                ),
                [
                    'Transfd_cat',
                    'Transfd',
                    'Sigma_transfd_funcd',
                    'Fibre_func',
                    'tdapp0_fapp0'
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2B3_MODULE.runtimeRules.map(
                    rule => rule.order
                ),
                [5]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2B3_PLAN.phases.map(phase => [
                    phase.kind,
                    phase.sourceOrders
                ]),
                [
                    ['declaration', [0]],
                    ['declaration', [1]],
                    ['declaration', [2]],
                    ['declaration', [3]],
                    ['declaration', [4]],
                    ['runtime', [5]]
                ]
            );
            assert.equal(
                CORE_LF_SCALE_STRESS_2B3_POLICY.entries.length,
                6
            );
            assertDeepFrozen(contract);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_2B3_MODULE);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_2B3_PLAN);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_2B3_BOUNDARY);
        });

        it('extends the exact 2B2 runtime and records one body boundary', () => {
            const compilation =
                compileCoreLfScaleStress2b3Representation();
            const prior = compilation.prerequisite
                .compiled.latestRuntime?.runtime.ruleIds;
            assert.notEqual(prior, undefined);
            if (prior === undefined) return;
            assert.equal(prior.length, 21);
            assert.deepEqual(
                compilation.compiled.latestRuntime?.runtime.ruleIds,
                [
                    ...prior,
                    'stress.sigma-transfor.object-component'
                ]
            );

            const programs = localRuntimePrograms(compilation);
            assert.equal(programs.length, 1);
            const rule = programs[0].rules[0];
            assert.equal(
                rule.id,
                'stress.sigma-transfor.object-component'
            );
            assert.equal(
                rule.subjectValidation.kind,
                'external-oracle-required'
            );
            assert.equal(rule.checkedWithEarlierRuleIds.length, 21);
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2B3_BOUNDARY
                    .runtimeSubjectOracleRuleIds,
                [rule.id]
            );

            const context = compilation.compiled.declarations;
            assert.equal(
                context.declaration(
                    CORE_LF_SCALE_STRESS_2B3_SYMBOLS
                        .displayedTransformationClassifier
                )?.status,
                'installed-transparent'
            );
            assert.equal(
                context.declaration(
                    CORE_LF_SCALE_STRESS_2B3_SYMBOLS.fibreFunctor
                )?.status,
                'installed-opaque'
            );
        });

        it('executes the selected clause and rejects a plicity near miss', () => {
            const compilation =
                compileCoreLfScaleStress2b3Representation();
            const runtime = compilation.compiled.latestRuntime?.runtime;
            assert.notEqual(runtime, undefined);
            if (runtime === undefined) return;

            const program = localRuntimePrograms(compilation)[0];
            const rule = program.rules[0];
            const witnessSource = provenance(
                'derived',
                'SCALE-STRESS-2B3 runtime witness'
            );
            const bindings = rule.variables.map((variable, index) =>
                kernelFree(
                    `stress2b3_${index}_${variable.name}`,
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
            assert.equal(
                runtime.rewriteHead(flipFirstPlicity(redex)).status,
                'irreducible'
            );
        });

        it(
            'matches live acquisition and Lambdapi Sigma uncurrying',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_SCALE_TELESCOPE_STRESS_PROBES !==
                    '1'
            },
            () => {
                const contract =
                    CORE_LF_SCALE_STRESS_2_SIGMA_TRANSFOR_ACQUISITION;
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
                    'symbol stress2b3_K : Cat;',
                    'symbol stress2b3_R : τ (Catd stress2b3_K);',
                    'symbol stress2b3_S : τ (Functord ' +
                        'stress2b3_R (@Const_catd ' +
                        'stress2b3_K Cat_cat));',
                    'symbol stress2b3_T : τ (Functord ' +
                        'stress2b3_R (@Const_catd ' +
                        'stress2b3_K Cat_cat));',
                    'symbol stress2b3_eta : τ (@Transfd ' +
                        'stress2b3_K stress2b3_R ' +
                        '(@Const_catd stress2b3_K Cat_cat) ' +
                        'stress2b3_S stress2b3_T);',
                    'symbol stress2b3_k : τ (Obj stress2b3_K);',
                    'symbol stress2b3_r : τ (Obj ' +
                        '(Fibre_cat stress2b3_R stress2b3_k));',
                    'constant symbol stress2b3_bad : τ (@Hom ' +
                        'Cat_cat ' +
                        '(@fapp0 (Fibre_cat stress2b3_R ' +
                        'stress2b3_k) Cat_cat ' +
                        '(@Fibre_func stress2b3_K stress2b3_R ' +
                        '(@Const_catd stress2b3_K Cat_cat) ' +
                        'stress2b3_S stress2b3_k) stress2b3_r) ' +
                        '(@fapp0 (Fibre_cat stress2b3_R ' +
                        'stress2b3_k) Cat_cat ' +
                        '(@Fibre_func stress2b3_K stress2b3_R ' +
                        '(@Const_catd stress2b3_K Cat_cat) ' +
                        'stress2b3_T stress2b3_k) stress2b3_r));'
                ];
                const left = [
                    '@tapp0_fapp0',
                    '(@Sigma_cat stress2b3_K stress2b3_R)',
                    'Cat_cat',
                    '(@Sigma_catd_functord_catd stress2b3_K',
                    'stress2b3_R stress2b3_S)',
                    '(@Sigma_catd_functord_catd stress2b3_K',
                    'stress2b3_R stress2b3_T)',
                    '(Struct_sigma stress2b3_k stress2b3_r)',
                    '(@Sigma_transfd_funcd stress2b3_K',
                    'stress2b3_R stress2b3_S stress2b3_T',
                    'stress2b3_eta)'
                ].join(' ');
                const right = [
                    '@tapp0_fapp0',
                    '(Fibre_cat stress2b3_R stress2b3_k)',
                    'Cat_cat',
                    '(@Fibre_func stress2b3_K stress2b3_R',
                    '(@Const_catd stress2b3_K Cat_cat)',
                    'stress2b3_S stress2b3_k)',
                    '(@Fibre_func stress2b3_K stress2b3_R',
                    '(@Const_catd stress2b3_K Cat_cat)',
                    'stress2b3_T stress2b3_k)',
                    'stress2b3_r',
                    '(@tdapp0_fapp0 stress2b3_K stress2b3_R',
                    '(@Const_catd stress2b3_K Cat_cat)',
                    'stress2b3_S stress2b3_T stress2b3_k',
                    'stress2b3_eta)'
                ].join(' ');

                const positive = checkLambdapiProbe(
                    {
                        source: [
                            ...header,
                            'assert ⊢ @Transfd stress2b3_K ' +
                                'stress2b3_R (@Const_catd ' +
                                'stress2b3_K Cat_cat) ' +
                                'stress2b3_S stress2b3_T ≡ ' +
                                'Obj (@Transfd_cat stress2b3_K ' +
                                'stress2b3_R (@Const_catd ' +
                                'stress2b3_K Cat_cat) ' +
                                'stress2b3_S stress2b3_T);',
                            'assert ⊢ @Fibre_func stress2b3_K ' +
                                'stress2b3_R (@Const_catd ' +
                                'stress2b3_K Cat_cat) ' +
                                'stress2b3_S stress2b3_k ≡ ' +
                                '@tapp0_fapp0 stress2b3_K ' +
                                'Cat_cat stress2b3_R ' +
                                '(@Const_catd stress2b3_K Cat_cat) ' +
                                'stress2b3_k stress2b3_S;',
                            `assert ⊢ ${left} ≡ ${right};`,
                            `assertnot ⊢ ${left} ≡ stress2b3_bad;`
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
                            `assert ⊢ ${left} ≡ stress2b3_bad;`
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
                'CORE_LF_SCALE_STRESS_2B3_MODULE' in browser,
                false
            );
            assert.equal(
                'compileCoreLfScaleStress2b3Representation' in browser,
                false
            );
            const authorityText = readFileSync(
                resolve(
                    repositoryRoot,
                    CORE_LF_SCALE_STRESS_2B3_MODULE.authorityPath
                ),
                'utf8'
            );
            [
                ...CORE_LF_SCALE_STRESS_2B3_MODULE.declarations,
                ...CORE_LF_SCALE_STRESS_2B3_MODULE.runtimeRules
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
                'Sigma_transfd_funcd',
                'tdapp0_fapp0',
                'Transfd_cat'
            ].forEach(name => {
                assert.equal(genericSources.includes(name), false);
            });
        });
    }
);
