/**
 * Focused SCALE-STRESS-2A acquisition, representation, and proof-time
 * uncurrying evidence. The exact active rule remains an isolated
 * qualification program and is not a product/browser registration.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { basename, resolve } from 'node:path';
import { spawnSync } from 'node:child_process';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_STRESS_2A_MODULE,
    CORE_LF_SCALE_STRESS_2A_PLAN,
    CORE_LF_SCALE_STRESS_2A_POLICY,
    CORE_LF_SCALE_STRESS_2A_TYPING_ORACLE,
    CORE_LF_SCALE_STRESS_2_UNCURRYING_ACQUISITION,
    CoreLfProofCompilerError,
    acquireCoreLfCanonicalCommands,
    checkLambdapiProbe,
    compileCoreLfScaleStress2aRepresentation,
    coreDirectedContinuationTransferSymbol,
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

const executableTerms = () => {
    const compilation =
        compileCoreLfScaleStress2aRepresentation();
    const compiled = compilation.compiled;
    const proof = compiled.proofProgram;
    assert.notEqual(proof, undefined);
    if (proof === undefined) {
        throw new Error('Missing SCALE-STRESS-2A proof program');
    }

    const localSymbol =
        CORE_LF_SCALE_STRESS_2A_MODULE.declarations[1].symbol;
    const localPhase = compiled.phases.find(phase =>
        phase.kind === 'declaration' &&
        phase.declarations.declaration(localSymbol) !== undefined
    );
    assert.equal(localPhase?.kind, 'declaration');
    if (localPhase?.kind !== 'declaration') {
        throw new Error('Missing Sigma projection declaration phase');
    }

    const sigmaCategory =
        coreDirectedContinuationTransferSymbol('sigma-category');
    const sectionCategory =
        coreDirectedContinuationTransferSymbol('section-category');
    const displayedFunctorCategory =
        coreDirectedContinuationTransferSymbol(
            'displayed-functor-category'
        );
    const categoryOfCategories =
        coreDirectedContinuationTransferSymbol(
            'category-of-categories'
        );
    const constantDisplayedFamily =
        coreDirectedContinuationTransferSymbol(
            'constant-displayed-family'
        );
    const displayedCategoryCategory =
        coreDirectedContinuationTransferSymbol(
            'displayed-category-category'
        );
    const nodeProvenance = provenance(
        'derived',
        'SCALE-STRESS-2A proof comparison witness'
    );
    const K = compilation.initialDeclarations.application(
        categoryOfCategories,
        [],
        nodeProvenance
    );
    const R = compilation.initialDeclarations.application(
        constantDisplayedFamily,
        [K, K],
        nodeProvenance
    );
    const D = R;
    const D2 = compilation.initialDeclarations.application(
        constantDisplayedFamily,
        [
            K,
            compilation.initialDeclarations.application(
                displayedCategoryCategory,
                [K],
                nodeProvenance
            )
        ],
        nodeProvenance
    );
    const sigmaTotal =
        compilation.initialDeclarations.application(
            sigmaCategory,
            [K, R],
            nodeProvenance
        );
    const pullback = localPhase.declarations.application(
        localSymbol,
        [K, R, D],
        nodeProvenance
    );
    const left = compilation.initialDeclarations.application(
        sectionCategory,
        [sigmaTotal, pullback],
        nodeProvenance
    );
    const right = compilation.initialDeclarations.application(
        displayedFunctorCategory,
        [K, R, D],
        nodeProvenance
    );
    const wrong = compilation.initialDeclarations.application(
        displayedFunctorCategory,
        [K, R, D2],
        nodeProvenance
    );
    return {
        compilation,
        proof,
        left,
        right,
        wrong
    };
};

describe(
    'TypeScript v3.2 SCALE-STRESS-2A proof-time uncurrying',
    () => {
        it('pins the exact active command selection and source order', () => {
            const contract =
                CORE_LF_SCALE_STRESS_2_UNCURRYING_ACQUISITION;
            assert.deepEqual(
                contract.commands.map(command => command.ordinal),
                [389, 393, 961, 981, 991, 995]
            );
            assert.deepEqual(
                contract.commands.map(command => command.id),
                [
                    'uncurrying.displayed-family-classifier',
                    'uncurrying.displayed-functor-category',
                    'uncurrying.section-category',
                    'uncurrying.sigma-category',
                    'uncurrying.sigma-projection-pullback',
                    'uncurrying.sigma-section-comparison'
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2A_PLAN.phases.map(phase => [
                    phase.kind,
                    phase.sourceOrders
                ]),
                [
                    ['declaration', [0]],
                    ['declaration', [1]],
                    ['proof', [2]]
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2A_POLICY.entries.map(
                    entry => entry.policy
                ),
                [
                    'checked-transparent-definition',
                    'opaque-signature',
                    'proof-unification'
                ]
            );
            assert.deepEqual(
                CORE_LF_SCALE_STRESS_2A_MODULE.proofRules[0]
                    .generatedConstraints.map(constraint => [
                        constraint.left,
                        constraint.right
                    ]).map(pair => pair.map(expression =>
                        expression.tag === 'capture'
                            ? expression.name
                            : expression.tag
                    )),
                [
                    ['K', 'K2'],
                    ['R', 'R2'],
                    ['D', 'D2']
                ]
            );
            assertDeepFrozen(contract);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_2A_MODULE);
            assertDeepFrozen(CORE_LF_SCALE_STRESS_2A_PLAN);
        });

        it('fails closed without the exact dependent typing oracle', () => {
            assert.throws(
                () =>
                    compileCoreLfScaleStress2aRepresentation(false),
                error =>
                    error instanceof CoreLfProofCompilerError &&
                    error.code === 'INVALID_PROOF_RULE_TYPE' &&
                    /K2.*K|K.*K2/u.test(error.message)
            );
        });

        it('compiles only an isolated proof program with explicit evidence', () => {
            const { compiled } =
                compileCoreLfScaleStress2aRepresentation();
            assert.deepEqual(
                compiled.phases.map(phase => phase.kind),
                ['declaration', 'declaration', 'proof']
            );
            assert.deepEqual(
                compiled.proofProgram?.ruleIds,
                ['stress.sigma-pi.uncurrying']
            );
            const rule = compiled.proofProgram?.rule(
                'stress.sigma-pi.uncurrying'
            );
            assert.deepEqual(
                rule?.typingValidation,
                {
                    kind: 'external-oracle-required',
                    authorityPath:
                        CORE_LF_SCALE_STRESS_2A_TYPING_ORACLE
                            .authorityPath,
                    evidence:
                        CORE_LF_SCALE_STRESS_2A_TYPING_ORACLE
                            .evidence,
                    diagnostic:
                        "Core type mismatch: free name " +
                        "'proof_2_3_K2' differs from free name " +
                        "'proof_2_0_K'"
                }
            );
            assert.equal(compiled.latestRuntime, undefined);
            assert.equal(
                compiled.semanticStatus,
                'compiled-selected-policy'
            );
            assert.ok(
                compiled.doesNotProvide.includes(
                    'active-policy-selection'
                )
            );
        });

        it('executes forward/symmetric matching and ordered constraints', () => {
            const { proof, left, right, wrong } = executableTerms();
            const forward = proof.compare(left, right);
            assert.equal(forward.status, 'solved');
            assert.deepEqual(
                forward.ruleApplications.map(application => [
                    application.ruleId,
                    application.orientation,
                    application.generatedProblems.length
                ]),
                [['stress.sigma-pi.uncurrying', 'forward', 3]]
            );
            assert.deepEqual(forward.resolutionOrder, [0, 1, 2, 3]);

            const symmetric = proof.compare(right, left);
            assert.equal(symmetric.status, 'solved');
            assert.equal(
                symmetric.ruleApplications[0]?.orientation,
                'symmetric'
            );

            const negative = proof.compare(left, wrong);
            assert.equal(negative.status, 'stuck');
            if (negative.status !== 'stuck') return;
            assert.equal(negative.reason, 'no-proof-rule');
            assert.deepEqual(negative.resolutionOrder, [0, 1, 2]);
            assert.equal(
                negative.ruleApplications[0]?.generatedProblems.length,
                3
            );
        });

        it(
            'matches live acquisition and Lambdapi positive/negative use',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_SCALE_PROOF_STRESS_PROBES !==
                    '1'
            },
            () => {
                const contract =
                    CORE_LF_SCALE_STRESS_2_UNCURRYING_ACQUISITION;
                const version = runLambdapi(['--version']).trim();
                const canonicalExportText = runLambdapi([
                    'export',
                    '-o',
                    'lp',
                    basename(contract.authorityPath)
                ]);
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
                        canonicalExportText,
                        observedExporterVersion: version
                    }
                );
                assert.deepEqual(
                    selection.commands.map(entry =>
                        entry.command.ordinal
                    ),
                    [389, 393, 961, 981, 991, 995]
                );

                const header = [
                    'require open emdash.emdash3_2;',
                    'symbol stress2_K : Cat;',
                    'symbol stress2_R : τ (Catd stress2_K);',
                    'symbol stress2_D : τ (Catd stress2_K);',
                    'symbol stress2_D2 : τ (Catd stress2_K);'
                ];
                const left =
                    '@Pi_cat ' +
                    '(@Sigma_cat stress2_K stress2_R) ' +
                    '(@Sigma_proj1_pullback_catd ' +
                    'stress2_K stress2_R stress2_D)';
                const positive = checkLambdapiProbe(
                    {
                        source: [
                            ...header,
                            `symbol stress2_s : τ (Obj (${left}));`,
                            'symbol stress2_positive : ' +
                                'τ (Obj (@Functord_cat stress2_K ' +
                                'stress2_R stress2_D)) ≔ stress2_s;'
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
                            `symbol stress2_s : τ (Obj (${left}));`,
                            'symbol stress2_negative : ' +
                                'τ (Obj (@Functord_cat stress2_K ' +
                                'stress2_R stress2_D2)) ≔ stress2_s;'
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
                    /stress2_D2 ≡ stress2_D/u
                );
            }
        );

        it('stays out of the browser and owner-generic engines', () => {
            assert.equal(
                'CORE_LF_SCALE_STRESS_2A_MODULE' in browser,
                false
            );
            assert.equal(
                'compileCoreLfScaleStress2aRepresentation' in browser,
                false
            );
            const proofEngine = readFileSync(
                resolve(
                    repositoryRoot,
                    'src/v3_2/lf_transfer_proof.ts'
                ),
                'utf8'
            );
            const mixedEngine = readFileSync(
                resolve(
                    repositoryRoot,
                    'src/v3_2/lf_transfer_mixed.ts'
                ),
                'utf8'
            );
            assert.doesNotMatch(
                proofEngine,
                /Sigma_proj1_pullback_catd|stress\.sigma-pi/u
            );
            assert.doesNotMatch(
                mixedEngine,
                /Sigma_proj1_pullback_catd|stress\.sigma-pi/u
            );
        });
    }
);
