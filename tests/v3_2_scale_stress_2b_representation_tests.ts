/**
 * Focused SCALE-STRESS-2B1 acquisition, mixed-runtime-lineage, and
 * internal/pullback dependent-Pi representation evidence.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { basename, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_STRESS_2B1_BOUNDARY,
    CORE_LF_SCALE_STRESS_2B1_MODULE,
    CORE_LF_SCALE_STRESS_2B1_PLAN,
    CORE_LF_SCALE_STRESS_2B1_POLICY,
    CORE_LF_SCALE_STRESS_2B1_SYMBOLS,
    CORE_LF_SCALE_STRESS_2_INTERNAL_PI_ACQUISITION,
    CoreLfCompiledRuntimeProgram,
    KernelExpression,
    acquireCoreLfCanonicalCommands,
    checkLambdapiProbe,
    compileCoreLfScaleStress2b1Representation,
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
        ReturnType<typeof compileCoreLfScaleStress2b1Representation>
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
    'TypeScript v3.2 SCALE-STRESS-2B1 internal dependent Pi',
    () => {
        it('pins the exact additional command and source-phase order', () => {
            const contract =
                CORE_LF_SCALE_STRESS_2_INTERNAL_PI_ACQUISITION;
            assert.deepEqual(
                contract.commands.map(command => command.ordinal),
                [
                    236, 238, 394, 538, 928, 929, 932, 933, 938,
                    941, 943, 985, 986, 988, 989, 990, 991, 992
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2B1_MODULE.declarations.map(
                    declaration => declaration.symbol.name
                ),
                [
                    'Op_cat',
                    'Functord',
                    'Catd_cat_func',
                    'Pullback_catd',
                    'Pullback_catd_func',
                    'Pi_func',
                    'Pi_int_funcd',
                    'Pi_pullback_funcd'
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2B1_MODULE.runtimeRules.map(
                    rule => rule.order
                ),
                [1, 5, 7, 8, 9, 11, 13, 15, 16]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2B1_PLAN.phases.map(phase => [
                    phase.kind,
                    phase.sourceOrders
                ]),
                [
                    ['declaration', [0]],
                    ['runtime', [1]],
                    ['declaration', [2]],
                    ['declaration', [3]],
                    ['declaration', [4]],
                    ['runtime', [5]],
                    ['declaration', [6]],
                    ['runtime', [7]],
                    ['runtime', [8]],
                    ['runtime', [9]],
                    ['declaration', [10]],
                    ['runtime', [11]],
                    ['declaration', [12]],
                    ['runtime', [13]],
                    ['declaration', [14]],
                    ['runtime', [15]],
                    ['runtime', [16]]
                ]
            );
            assert.equal(
                CORE_LF_SCALE_STRESS_2B1_POLICY.entries.length,
                17
            );
            assertDeepFrozen(contract);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_2B1_MODULE);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_2B1_PLAN);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_2B1_BOUNDARY);
        });

        it('composes the reviewed runtime and classifies exact subjects', () => {
            const compilation =
                compileCoreLfScaleStress2b1Representation();
            const expectedPrior = [
                'directed.category-object.decode',
                'directed.displayed-family.decode',
                'directed.displayed-functor.decode',
                'directed.category-hom.decode',
                'directed.sigma-object.decode',
                'directed.sigma-first-projection.evaluate',
                'directed.sigma-telescope-fibre.evaluate',
                'projection.functor-hom.evaluate',
                'projection.transfor-component.evaluate',
                'projection.transfor-hom.evaluate'
            ];
            const expectedLocal =
                CORE_LF_SCALE_STRESS_2B1_MODULE.runtimeRules.map(
                    rule => rule.id
                );
            assert.deepEqual(
                compilation.continuationRuntime.runtime.ruleIds,
                expectedPrior
            );
            assert.deepEqual(
                compilation.compiled.latestRuntime?.runtime.ruleIds,
                [...expectedPrior, ...expectedLocal]
            );

            const programs = localRuntimePrograms(compilation);
            const validations = programs.map(program => {
                const rule = program.rules[0];
                return [
                    rule.id,
                    rule.subjectValidation.kind,
                    rule.checkedWithEarlierRuleIds.length
                ];
            });
            assert.deepEqual(
                validations.map(entry => entry[1]),
                [
                    'typescript-checked',
                    'typescript-checked',
                    'typescript-checked',
                    'typescript-checked',
                    'typescript-checked',
                    'typescript-checked',
                    'external-oracle-required',
                    'external-oracle-required',
                    'external-oracle-required'
                ]
            );
            assert.deepEqual(
                validations.map(entry => entry[2]),
                [10, 11, 12, 13, 14, 15, 16, 17, 18]
            );
            assert.deepEqual(
                programs
                    .filter(program =>
                        program.rules[0].subjectValidation.kind ===
                            'external-oracle-required'
                    )
                    .map(program => program.rules[0].id),
                CORE_LF_SCALE_STRESS_2B1_BOUNDARY
                    .runtimeSubjectOracleRuleIds
            );

            const context = compilation.compiled.declarations;
            assert.equal(
                context.declaration(
                    CORE_LF_SCALE_STRESS_2B1_SYMBOLS
                        .displayedFunctorClassifier
                )?.status,
                'installed-transparent'
            );
            assert.equal(
                context.declaration(
                    CORE_LF_SCALE_STRESS_2B1_SYMBOLS
                        .displayedCategoryFunctor
                )?.status,
                'installed-opaque'
            );
        });

        it('executes every selected clause and rejects a plicity near miss', () => {
            const compilation =
                compileCoreLfScaleStress2b1Representation();
            const runtime = compilation.compiled.latestRuntime?.runtime;
            assert.notEqual(runtime, undefined);
            if (runtime === undefined) return;

            const witnessSource = provenance(
                'derived',
                'SCALE-STRESS-2B1 runtime witness'
            );
            const programs = localRuntimePrograms(compilation);
            programs.forEach((program, programIndex) => {
                const rule = program.rules[0];
                const bindings = rule.variables.map((variable, index) =>
                    kernelFree(
                        `stress2b1_${programIndex}_${index}_` +
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
                    `stress2b1_near_${index}_${variable.name}`,
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
            'matches live acquisition and Lambdapi positive/negative use',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_SCALE_TELESCOPE_STRESS_PROBES !==
                    '1'
            },
            () => {
                const contract =
                    CORE_LF_SCALE_STRESS_2_INTERNAL_PI_ACQUISITION;
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
                    'symbol stress2b_K : Cat;',
                    'symbol stress2b_E : τ (Catd stress2b_K);',
                    'symbol stress2b_D : τ (Catd stress2b_K);',
                    'symbol stress2b_G : ' +
                        'τ (Functor stress2b_K (Op_cat Cat_cat));',
                    'symbol stress2b_x : τ (Obj stress2b_K);'
                ];
                const positive = checkLambdapiProbe(
                    {
                        source: [
                            ...header,
                            'assert ⊢ Obj (Op_cat stress2b_K) ' +
                                '≡ Obj stress2b_K;',
                            'assert ⊢ @fapp0 stress2b_K Cat_cat ' +
                                '(@Const_catd stress2b_K Cat_cat) ' +
                                'stress2b_x ≡ Cat_cat;',
                            'assert ⊢ @fapp0 (@Catd_cat stress2b_K) ' +
                                'Cat_cat (@Pi_func stress2b_K) ' +
                                'stress2b_E ≡ ' +
                                '@Pi_cat stress2b_K stress2b_E;',
                            'assert ⊢ @tapp0_fapp0 ' +
                                '(Op_cat Cat_cat) Cat_cat ' +
                                'Catd_cat_func ' +
                                '(@Const_catd ' +
                                '(Op_cat Cat_cat) Cat_cat) ' +
                                'stress2b_K Pi_int_funcd ' +
                                '≡ @Pi_func stress2b_K;',
                            'assert ⊢ @fapp1_fapp0 ' +
                                '(@Catd_cat (Op_cat Cat_cat)) ' +
                                '(@Catd_cat stress2b_K) ' +
                                '(@Pullback_catd_func stress2b_K ' +
                                '(Op_cat Cat_cat) stress2b_G) ' +
                                'Catd_cat_func ' +
                                '(@Const_catd ' +
                                '(Op_cat Cat_cat) Cat_cat) ' +
                                'Pi_int_funcd ≡ ' +
                                '@Pi_pullback_funcd ' +
                                'stress2b_K stress2b_G;',
                            'assert ⊢ @tapp0_fapp0 ' +
                                'stress2b_K Cat_cat ' +
                                '(@Pullback_catd stress2b_K ' +
                                '(Op_cat Cat_cat) Catd_cat_func ' +
                                'stress2b_G) ' +
                                '(@Const_catd stress2b_K Cat_cat) ' +
                                'stress2b_x ' +
                            '(@Pi_pullback_funcd ' +
                                'stress2b_K stress2b_G) ≡ ' +
                                '@Pi_func (@fapp0 stress2b_K ' +
                                '(Op_cat Cat_cat) stress2b_G ' +
                                'stress2b_x);',
                            'assertnot ⊢ @fapp0 ' +
                                '(@Catd_cat stress2b_K) Cat_cat ' +
                                '(@Pi_func stress2b_K) stress2b_E ' +
                                '≡ @Pi_cat stress2b_K stress2b_D;'
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
                            'assert ⊢ @fapp0 ' +
                                '(@Catd_cat stress2b_K) Cat_cat ' +
                                '(@Pi_func stress2b_K) stress2b_E ' +
                                '≡ @Pi_cat stress2b_K stress2b_D;'
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

        it('keeps representation local and generic engines owner-free', () => {
            assert.equal(
                'CORE_LF_SCALE_STRESS_2B1_MODULE' in browser,
                false
            );
            assert.equal(
                'compileCoreLfScaleStress2b1Representation' in browser,
                false
            );
            const authorityText = readFileSync(
                resolve(
                    repositoryRoot,
                    CORE_LF_SCALE_STRESS_2B1_MODULE.authorityPath
                ),
                'utf8'
            );
            [
                ...CORE_LF_SCALE_STRESS_2B1_MODULE.declarations,
                ...CORE_LF_SCALE_STRESS_2B1_MODULE.runtimeRules
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
                'Pi_int_funcd',
                'Pi_pullback_funcd',
                'Catd_cat_func'
            ].forEach(name => {
                assert.equal(genericSources.includes(name), false);
            });
        });
    }
);
