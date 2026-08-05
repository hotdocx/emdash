/**
 * Focused SCALE-STRESS-3A2B product/tensor-action qualification.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { basename, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_STRESS_3A1_SYMBOLS,
    CORE_LF_SCALE_STRESS_3A2A_SYMBOLS,
    CORE_LF_SCALE_STRESS_3A2B_BOUNDARY,
    CORE_LF_SCALE_STRESS_3A2B_LINKAGE,
    CORE_LF_SCALE_STRESS_3A2B_MODULE,
    CORE_LF_SCALE_STRESS_3A2B_PLAN,
    CORE_LF_SCALE_STRESS_3A2B_POLICY,
    CORE_LF_SCALE_STRESS_3A2B_SYMBOLS,
    CORE_LF_SCALE_STRESS_3_PROFUNCTOR_TENSOR_ACTION_ACQUISITION,
    CoreLfCompiledMixedModule,
    CoreLfQualifiedSymbol,
    KernelExpression,
    acquireCoreLfCanonicalCommands,
    binderMode,
    checkLambdapiProbe,
    compileCoreLfScaleStress3a2bRepresentation,
    coreDirectedContinuationTransferSymbol,
    coreLfCombinedWeakHead,
    coreLfDefinitionalCompare,
    kernelApplication,
    kernelBinder,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
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

const freeCall = (
    compiled: CoreLfCompiledMixedModule,
    symbol: CoreLfQualifiedSymbol,
    arguments_: readonly {
        readonly plicity: 'explicit' | 'implicit';
        readonly value: KernelExpression;
    }[],
    source: ReturnType<typeof provenance>
): KernelExpression => kernelCall(
    kernelFree(freeDeclarationName(compiled, symbol), source),
    arguments_,
    source
);

const decode = (
    classifier: KernelExpression,
    source: ReturnType<typeof provenance>
): KernelExpression => kernelApplication(
    'decode',
    [{ value: classifier }],
    source
);

const objectClassifier = (
    category: KernelExpression,
    source: ReturnType<typeof provenance>
): KernelExpression => kernelApplication(
    'object-classifier',
    [{ value: category }],
    source
);

const homCategory = (
    category: KernelExpression,
    sourceObject: KernelExpression,
    targetObject: KernelExpression,
    source: ReturnType<typeof provenance>
): KernelExpression => kernelApplication(
    'hom-category',
    [
        { value: category },
        { value: sourceObject },
        { value: targetObject }
    ],
    source
);

const constantFamily = (
    leftClassifier: KernelExpression,
    rightClassifier: KernelExpression,
    source: ReturnType<typeof provenance>
): KernelExpression => kernelLambda(
    kernelBinder(
        'ignored',
        decode(leftClassifier, source),
        binderMode('explicit', 'functorial'),
        source
    ),
    rightClassifier,
    source
);

const productCategory = (
    compiled: CoreLfCompiledMixedModule,
    left: KernelExpression,
    right: KernelExpression,
    source: ReturnType<typeof provenance>
): KernelExpression => freeCall(
    compiled,
    CORE_LF_SCALE_STRESS_3A2B_SYMBOLS.productCategory,
    [
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
    ],
    source
);

const productComponents = (
    compiled: CoreLfCompiledMixedModule,
    leftCategory: KernelExpression,
    rightCategory: KernelExpression,
    pair: KernelExpression,
    source: ReturnType<typeof provenance>
) => {
    const leftClassifier = objectClassifier(leftCategory, source);
    const rightClassifier = objectClassifier(rightCategory, source);
    const family = constantFamily(
        leftClassifier,
        rightClassifier,
        source
    );
    const arguments_ = [
        { plicity: 'implicit' as const, value: leftClassifier },
        { plicity: 'implicit' as const, value: family },
        { plicity: 'explicit' as const, value: pair }
    ];
    return {
        first: freeCall(
            compiled,
            CORE_LF_SCALE_STRESS_3A2B_SYMBOLS.sigmaFirst,
            arguments_,
            source
        ),
        second: freeCall(
            compiled,
            CORE_LF_SCALE_STRESS_3A2B_SYMBOLS.sigmaSecond,
            arguments_,
            source
        )
    };
};

const profunctorCategory = (
    compiled: CoreLfCompiledMixedModule,
    A: KernelExpression,
    B: KernelExpression,
    source: ReturnType<typeof provenance>
): KernelExpression => freeCall(
    compiled,
    CORE_LF_SCALE_STRESS_3A1_SYMBOLS.profunctorCategory,
    [
        { plicity: 'explicit', value: A },
        { plicity: 'explicit', value: B }
    ],
    source
);

describe(
    'TypeScript v3.2 SCALE-STRESS-3A2B profunctor tensor action',
    () => {
        it('pins the exact dependency closure, policy, and phases', () => {
            const contract =
                CORE_LF_SCALE_STRESS_3_PROFUNCTOR_TENSOR_ACTION_ACQUISITION;
            assert.deepEqual(
                contract.commands.map(command => command.ordinal),
                [59, 61, 184, 185, 668, 670, 687, 1354, 1355, 1356, 1357]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_3A2B_MODULE.declarations.map(
                    declaration => declaration.symbol.name
                ),
                [
                    'sigma_Fst',
                    'sigma_Snd',
                    'Product_grpd',
                    'Product_cat',
                    'Prof_tensor_map',
                    'Prof_tensor_func'
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_3A2B_POLICY.entries.map(
                    entry => entry.policy
                ),
                [
                    'opaque-signature',
                    'opaque-signature',
                    'opaque-signature',
                    'runtime-rewrite',
                    'opaque-signature',
                    'runtime-rewrite',
                    'runtime-rewrite',
                    'opaque-signature',
                    'opaque-signature',
                    'runtime-rewrite',
                    'runtime-rewrite'
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_3A2B_PLAN.phases.map(
                    phase => phase.kind
                ),
                [
                    'declaration',
                    'declaration',
                    'declaration',
                    'runtime',
                    'declaration',
                    'runtime',
                    'runtime',
                    'declaration',
                    'declaration',
                    'runtime',
                    'runtime'
                ]
            );
            assert.equal(
                CORE_LF_SCALE_STRESS_3A2B_LINKAGE.entries.length,
                20
            );
            [
                contract,
                CORE_LF_SCALE_STRESS_3A2B_MODULE,
                CORE_LF_SCALE_STRESS_3A2B_POLICY,
                CORE_LF_SCALE_STRESS_3A2B_PLAN,
                CORE_LF_SCALE_STRESS_3A2B_LINKAGE,
                CORE_LF_SCALE_STRESS_3A2B_BOUNDARY
            ].forEach(assertDeepFrozen);
        });

        it('checks all signatures and executes product decoding', () => {
            const compilation =
                compileCoreLfScaleStress3a2bRepresentation();
            const compiled = compilation.compiled;
            const declarations = compiled.declarations.modules.flatMap(
                module => module.declarations
            );
            assert.deepEqual(
                declarations.map(declaration => [
                    declaration.symbol.name,
                    declaration.status
                ]),
                [
                    ['sigma_Fst', 'installed-opaque'],
                    ['sigma_Snd', 'installed-opaque'],
                    ['Product_grpd', 'installed-opaque'],
                    ['Product_cat', 'installed-opaque'],
                    ['Prof_tensor_map', 'installed-opaque'],
                    ['Prof_tensor_func', 'installed-opaque']
                ]
            );
            assert.equal(
                compiled.declarations.declaration(
                    CORE_LF_SCALE_STRESS_3A2A_SYMBOLS.homClassifier
                )?.status,
                'intrinsic-transparent'
            );
            assert.deepEqual(
                compiled.latestRuntime?.runtime.ruleIds.slice(-5),
                CORE_LF_SCALE_STRESS_3A2B_BOUNDARY
                    .selectedRuntimeRuleIds
            );

            const source = provenance(
                'derived',
                'SCALE-STRESS-3A2B product witness'
            );
            const A = kernelFree('stress3a2b_product_A', source);
            const B = kernelFree('stress3a2b_product_B', source);
            const product = productCategory(
                compiled,
                A,
                B,
                source
            );
            const objectReduction = coreLfCombinedWeakHead(
                compiled.declarations.environment,
                objectClassifier(product, source),
                1,
                undefined,
                compiled.latestRuntime?.runtime
            );
            assert.equal(objectReduction.status, 'weak-head-normal');
            assert.equal(objectReduction.steps, 1);
            assert.equal(
                objectReduction.trace[0].kind === 'runtime'
                    ? objectReduction.trace[0].ruleId
                    : undefined,
                'stress.profunctor-tensor.product-object'
            );

            const productGroupoid = freeCall(
                compiled,
                CORE_LF_SCALE_STRESS_3A2B_SYMBOLS.productGroupoid,
                [
                    {
                        plicity: 'explicit',
                        value: objectClassifier(A, source)
                    },
                    {
                        plicity: 'explicit',
                        value: objectClassifier(B, source)
                    }
                ],
                source
            );
            assert.equal(
                kernelExpressionEquals(
                    objectReduction.expression,
                    productGroupoid
                ),
                true
            );

            const family = constantFamily(
                objectClassifier(A, source),
                objectClassifier(B, source),
                source
            );
            const decodedPair = freeCall(
                compiled,
                coreDirectedContinuationTransferSymbol(
                    'decoded-dependent-pair'
                ),
                [
                    {
                        plicity: 'implicit',
                        value: objectClassifier(A, source)
                    },
                    { plicity: 'explicit', value: family }
                ],
                source
            );
            const nested = coreLfDefinitionalCompare(
                compiled.declarations.environment,
                decode(objectClassifier(product, source), source),
                decodedPair,
                8,
                undefined,
                compiled.latestRuntime?.runtime
            );
            assert.equal(nested.status, 'equal');
            assert.deepEqual(
                nested.trace
                    .filter(entry =>
                        entry.reduction.kind === 'runtime'
                    )
                    .map(entry =>
                        entry.reduction.kind === 'runtime'
                            ? entry.reduction.ruleId
                            : undefined
                    ),
                [
                    'stress.profunctor-tensor.product-object',
                    'stress.profunctor-tensor.product-groupoid-decode'
                ]
            );
        });

        it('executes tensor object and capped-arrow action', () => {
            const compilation =
                compileCoreLfScaleStress3a2bRepresentation();
            const compiled = compilation.compiled;
            const source = provenance(
                'derived',
                'SCALE-STRESS-3A2B tensor action witness'
            );
            const A = kernelFree('stress3a2b_A', source);
            const B = kernelFree('stress3a2b_B', source);
            const X = kernelFree('stress3a2b_X', source);
            const PQ = kernelFree('stress3a2b_PQ', source);
            const nextPQ = kernelFree('stress3a2b_PQ_next', source);
            const rs = kernelFree('stress3a2b_rs', source);
            const leftCategory = profunctorCategory(
                compiled,
                A,
                B,
                source
            );
            const rightCategory = profunctorCategory(
                compiled,
                B,
                X,
                source
            );
            const sourceCategory = productCategory(
                compiled,
                leftCategory,
                rightCategory,
                source
            );
            const targetCategory = profunctorCategory(
                compiled,
                A,
                X,
                source
            );
            const tensorFunctor = freeCall(
                compiled,
                CORE_LF_SCALE_STRESS_3A2B_SYMBOLS
                    .profunctorTensorFunctor,
                [
                    { plicity: 'implicit', value: A },
                    { plicity: 'implicit', value: B },
                    { plicity: 'implicit', value: X }
                ],
                source
            );
            const components = productComponents(
                compiled,
                leftCategory,
                rightCategory,
                PQ,
                source
            );
            const objectAction = kernelApplication(
                'functor-object',
                [
                    { value: sourceCategory },
                    { value: targetCategory },
                    { value: tensorFunctor },
                    { value: PQ }
                ],
                source
            );
            const objectResult = coreLfCombinedWeakHead(
                compiled.declarations.environment,
                objectAction,
                1,
                undefined,
                compiled.latestRuntime?.runtime
            );
            const expectedObject = freeCall(
                compiled,
                CORE_LF_SCALE_STRESS_3A1_SYMBOLS.profunctorTensor,
                [
                    { plicity: 'implicit', value: A },
                    { plicity: 'implicit', value: B },
                    { plicity: 'implicit', value: X },
                    { plicity: 'explicit', value: components.first },
                    { plicity: 'explicit', value: components.second }
                ],
                source
            );
            assert.equal(objectResult.status, 'weak-head-normal');
            assert.equal(objectResult.steps, 1);
            assert.equal(
                kernelExpressionEquals(
                    objectResult.expression,
                    expectedObject
                ),
                true
            );

            const nextComponents = productComponents(
                compiled,
                leftCategory,
                rightCategory,
                nextPQ,
                source
            );
            const leftHomClassifier = objectClassifier(
                homCategory(
                    leftCategory,
                    components.first,
                    nextComponents.first,
                    source
                ),
                source
            );
            const rightHomClassifier = objectClassifier(
                homCategory(
                    rightCategory,
                    components.second,
                    nextComponents.second,
                    source
                ),
                source
            );
            const arrowFamily = constantFamily(
                leftHomClassifier,
                rightHomClassifier,
                source
            );
            const arrowProjectionArguments = [
                {
                    plicity: 'implicit' as const,
                    value: leftHomClassifier
                },
                {
                    plicity: 'implicit' as const,
                    value: arrowFamily
                },
                { plicity: 'explicit' as const, value: rs }
            ];
            const r = freeCall(
                compiled,
                CORE_LF_SCALE_STRESS_3A2B_SYMBOLS.sigmaFirst,
                arrowProjectionArguments,
                source
            );
            const s = freeCall(
                compiled,
                CORE_LF_SCALE_STRESS_3A2B_SYMBOLS.sigmaSecond,
                arrowProjectionArguments,
                source
            );
            const arrowAction = kernelApplication(
                'functor-hom-capped',
                [
                    { value: sourceCategory },
                    { value: targetCategory },
                    { value: tensorFunctor },
                    { value: PQ },
                    { value: nextPQ },
                    { value: rs }
                ],
                source
            );
            const arrowResult = coreLfCombinedWeakHead(
                compiled.declarations.environment,
                arrowAction,
                1,
                undefined,
                compiled.latestRuntime?.runtime
            );
            const expectedArrow = freeCall(
                compiled,
                CORE_LF_SCALE_STRESS_3A2B_SYMBOLS.profunctorTensorMap,
                [
                    { plicity: 'implicit', value: A },
                    { plicity: 'implicit', value: B },
                    { plicity: 'implicit', value: X },
                    {
                        plicity: 'implicit',
                        value: components.first
                    },
                    {
                        plicity: 'implicit',
                        value: nextComponents.first
                    },
                    {
                        plicity: 'implicit',
                        value: components.second
                    },
                    {
                        plicity: 'implicit',
                        value: nextComponents.second
                    },
                    { plicity: 'explicit', value: r },
                    { plicity: 'explicit', value: s }
                ],
                source
            );
            assert.equal(arrowResult.status, 'weak-head-normal');
            assert.equal(arrowResult.steps, 1);
            assert.equal(
                arrowResult.trace[0].kind === 'runtime'
                    ? arrowResult.trace[0].ruleId
                    : undefined,
                'stress.profunctor-tensor.arrow-action'
            );
            assert.equal(
                kernelExpressionEquals(
                    arrowResult.expression,
                    expectedArrow
                ),
                true
            );

            const wrongFunctor = kernelFree(
                'stress3a2b_wrong_functor',
                source
            );
            const nonReduction = coreLfCombinedWeakHead(
                compiled.declarations.environment,
                kernelApplication(
                    'functor-object',
                    [
                        { value: sourceCategory },
                        { value: targetCategory },
                        { value: wrongFunctor },
                        { value: PQ }
                    ],
                    source
                ),
                1,
                undefined,
                compiled.latestRuntime?.runtime
            );
            assert.equal(nonReduction.status, 'weak-head-normal');
            assert.equal(nonReduction.steps, 0);
        });

        it(
            'matches live acquisition and Lambdapi tensor action',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_SCALE_PROFUNCTOR_STRESS_PROBES !==
                    '1'
            },
            () => {
                const contract =
                    CORE_LF_SCALE_STRESS_3_PROFUNCTOR_TENSOR_ACTION_ACQUISITION;
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

                const source = [
                    'require open emdash.emdash3_2;',
                    'symbol stress3a2b_A : Cat;',
                    'symbol stress3a2b_B : Cat;',
                    'symbol stress3a2b_X : Cat;',
                    'symbol stress3a2b_PQ : τ (Obj (Product_cat ' +
                        '(Prof_cat stress3a2b_A stress3a2b_B) ' +
                        '(Prof_cat stress3a2b_B stress3a2b_X)));',
                    'symbol stress3a2b_PQ2 : τ (Obj (Product_cat ' +
                        '(Prof_cat stress3a2b_A stress3a2b_B) ' +
                        '(Prof_cat stress3a2b_B stress3a2b_X)));',
                    'symbol stress3a2b_rs : τ (Hom ' +
                        '(Product_cat ' +
                        '(Prof_cat stress3a2b_A stress3a2b_B) ' +
                        '(Prof_cat stress3a2b_B stress3a2b_X)) ' +
                        'stress3a2b_PQ stress3a2b_PQ2);',
                    'assert ⊢ @fapp0 _ _ (@Prof_tensor_func ' +
                        'stress3a2b_A stress3a2b_B stress3a2b_X) ' +
                        'stress3a2b_PQ ≡ @Prof_tensor ' +
                        'stress3a2b_A stress3a2b_B stress3a2b_X ' +
                        '(sigma_Fst stress3a2b_PQ) ' +
                        '(sigma_Snd stress3a2b_PQ);',
                    'assert ⊢ @fapp1_fapp0 _ _ (@Prof_tensor_func ' +
                        'stress3a2b_A stress3a2b_B stress3a2b_X) ' +
                        'stress3a2b_PQ stress3a2b_PQ2 stress3a2b_rs ≡ ' +
                        '@Prof_tensor_map stress3a2b_A stress3a2b_B ' +
                        'stress3a2b_X ' +
                        '(sigma_Fst stress3a2b_PQ) ' +
                        '(sigma_Fst stress3a2b_PQ2) ' +
                        '(sigma_Snd stress3a2b_PQ) ' +
                        '(sigma_Snd stress3a2b_PQ2) ' +
                        '(sigma_Fst stress3a2b_rs) ' +
                        '(sigma_Snd stress3a2b_rs);'
                ].join('\n');
                const positive = checkLambdapiProbe(
                    {
                        source,
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
                        source: source.replace(
                            '(sigma_Snd stress3a2b_rs);',
                            '(sigma_Fst stress3a2b_rs);'
                        ),
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

        it('keeps the slice isolated and generic engines owner-free', () => {
            assert.equal(
                'CORE_LF_SCALE_STRESS_3A2B_MODULE' in browser,
                false
            );
            assert.equal(
                'compileCoreLfScaleStress3a2bRepresentation' in browser,
                false
            );
            const authorityText = readFileSync(
                resolve(
                    repositoryRoot,
                    CORE_LF_SCALE_STRESS_3A2B_MODULE.authorityPath
                ),
                'utf8'
            );
            CORE_LF_SCALE_STRESS_3A2B_MODULE.declarations.forEach(
                declaration => assert.ok(
                    authorityText.includes(
                        declaration.provenance.sourceFragment
                    ),
                    declaration.provenance.sourceFragment
                )
            );

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
                'Prof_tensor_map',
                'Prof_tensor_func',
                'Product_grpd'
            ].forEach(ownerName => {
                genericSources.forEach(sourceText => {
                    assert.equal(
                        sourceText.includes(ownerName),
                        false,
                        `${ownerName} leaked into a generic engine`
                    );
                });
            });
        });
    }
);
