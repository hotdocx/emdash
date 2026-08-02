/**
 * Focused DISPLAYED-ND-HIGHER-1B dependency and consumer audit.
 */

import assert from 'node:assert/strict';
import {
    spawnSync
} from 'node:child_process';
import {
    readFileSync
} from 'node:fs';
import {
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_ACQUISITION,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT,
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY,
    CoreCategoricalDisplayedNdHigherAuditError,
    acquireCoreLfCanonicalCommands,
    validateCoreCategoricalDisplayedNdHigherAudit
} from '../src/v3_2';

const repositoryRoot = resolve(__dirname, '..');
const lambdapiRoot = resolve(repositoryRoot, 'emdash2');

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

const assertAuditError = (
    mutate: (audit: any) => void,
    expected: CoreCategoricalDisplayedNdHigherAuditError['code']
): void => {
    const audit = clone();
    mutate(audit);
    assert.throws(
        () => validateCoreCategoricalDisplayedNdHigherAudit(audit),
        error =>
            error instanceof
                CoreCategoricalDisplayedNdHigherAuditError &&
            error.code === expected
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

describe('DISPLAYED-ND-HIGHER-1B dependency-first audit', () => {
    it('starts from the completed ND-1A checkpoint and current transfer',
        () => {
            const prerequisite =
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
                    .prerequisite;
            assert.equal(
                prerequisite.displayedNd1aImplementationCheckpoint,
                'd8b450222273167ab326701c76fff03f0f539b18'
            );
            assert.deepEqual(
                [
                    prerequisite.currentTransfdDeclarationCount,
                    prerequisite.currentTransfdRuntimeRuleCount,
                    prerequisite.semanticImplementationAuthorized
                ],
                [7, 10, false]
            );
        });

    it('pins the exact 16-declaration and two-rule source closure', () => {
        const audit =
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT;
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_ACQUISITION
                .commands.length,
            18
        );
        assert.deepEqual(
            audit.measuredClosure.foundationDeclarations,
            [
                'id',
                'comp_catd_fapp0',
                'Op_func',
                'Op_catd_func',
                'hom_int',
                'Op_catd',
                'Op_funcd',
                'Functor_catd_func',
                'Edge_catd_func',
                'Presheaf_catd_func',
                'HomPresheaf_catd_func',
                'Homd_target_catd',
                'homd_int'
            ]
        );
        assert.deepEqual(
            audit.measuredClosure.targetDeclarations,
            [
                'tdapp1_int_func_transfd',
                'tdapp1_int_fapp0_transfd',
                'tdapp1_int_fapp1_func_transfd'
            ]
        );
        assert.deepEqual(
            [
                audit.measuredClosure.totalDeclarationCount,
                audit.measuredClosure.totalRuntimeRuleCount,
                audit.measuredClosure.targetOnlyTransferIsClosed
            ],
            [16, 2, false]
        );
        assert.deepEqual(
            audit.dependencyBoundary.reusablePriorRepresentation,
            {
                sourceRow: 'SCALE-STRESS-3A2A',
                symbol: 'id',
                coreName: 'emdash_v3_2_scale_stress_3a2a_id',
                policy: 'opaque-signature',
                presentInInitialEnvironment: false,
                importWholeProfileRequired: false,
                interpretation:
                    'reuse-or-extract-the-existing-exact-id-' +
                    'representation;do-not-import-the-unrelated-' +
                    'profunctor-profile'
            }
        );
        assert.notEqual(
            audit.measuredClosure.canonicalExportEvidence
                .observedSha256,
            audit.measuredClosure.canonicalExportEvidence
                .historicalScaleContractSha256
        );
    });

    it('confirms only relocated id is present in the current transfer',
        () => {
            const source = readFileSync(
                resolve(repositoryRoot, 'emdash2/emdash3_2.lp'),
                'utf8'
            );
            const names = [
                ...CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
                    .measuredClosure.foundationDeclarations,
                ...CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
                    .measuredClosure.targetDeclarations
            ];
            for (const name of names) {
                assert.match(
                    source,
                    new RegExp(`(?:injective )?symbol ${name}\\b`, 'u')
                );
                assert.equal(
                    (
                        CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
                            .declarationNames as readonly string[]
                    ).includes(name),
                    name === 'id'
                );
            }
            assert.match(
                source,
                /rule fapp0 \(@tdapp1_int_func_transfd/u
            );
            assert.match(
                source,
                /rule @fapp1_func _ _ \(@tdapp1_int_func_transfd/u
            );
        });

    it('freezes a concrete next-hom consumer without another checker',
        () => {
            const audit =
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT;
            assert.match(
                audit.concreteConsumer.source,
                /Hom\(Transfd_cat/u
            );
            assert.match(
                audit.concreteConsumer.cappedAction,
                /tdapp1_int_fapp1_func_transfd/u
            );
            assert.equal(
                audit.concreteConsumer.requiresNewKernelSemantics,
                false
            );
            assert.deepEqual(
                [
                    audit.surfaceAssessment.secondCheckerRequired,
                    audit.surfaceAssessment.rawExprOrParserRequired,
                    audit.surfaceAssessment.contextualIrNodeRequired,
                    audit.surfaceAssessment.newBinderModeRequired,
                    audit.surfaceAssessment
                        .ownerSpecificLfCheckerBranchRequired
                ],
                [false, false, false, false, false]
            );
            const fixture = readFileSync(
                resolve(repositoryRoot, audit.concreteConsumer.fixture),
                'utf8'
            );
            assert.match(
                fixture,
                /fapp0\s+\(@fapp1_func[\s\S]*tdapp1_int_func_transfd/u
            );
            assert.match(
                fixture,
                /≡\s+fapp0\s+\(@tdapp1_int_fapp1_func_transfd/u
            );
        });

    it('selects only the dependency-first foundation for D-019', () => {
        const continuation =
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
                .recommendedContinuation;
        assert.equal(
            continuation.row,
            'DISPLAYED-ND-HIGHER-FOUNDATION-1A'
        );
        assert.equal(
            continuation.decision,
            'D-DTTLF-USABILITY-019'
        );
        assert.deepEqual(
            [
                continuation.exactDeclarations.length,
                continuation.checkedTransparentDefinitionCount,
                continuation.opaqueSignatureCount,
                continuation.exactRuntimeRules.length,
                continuation.exactProofRules.length
            ],
            [13, 5, 8, 0, 0]
        );
        assert.deepEqual(
            [
                continuation.newMathematicalOwnerCount,
                continuation.newMathematicalRuntimeRuleCount,
                continuation.newMathematicalProofRuleCount,
                continuation.intrinsicCoreOwnerDelta,
                continuation.ownerSpecificCheckerBranchDelta,
                continuation.surfaceMethodDelta,
                continuation.browserPromotionDelta
            ],
            [0, 0, 0, 0, 0, 0, 0]
        );
    });

    it('is deeply frozen, fail-closed, and absent from the browser', () => {
        assert.doesNotThrow(
            () => validateCoreCategoricalDisplayedNdHigherAudit()
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
        );
        assertAuditError(
            audit => {
                audit.prerequisite
                    .displayedNd1aImplementationCheckpoint = 'drift';
            },
            'DISPLAYED_ND_HIGHER_PREREQUISITE_DRIFT'
        );
        assertAuditError(
            audit => {
                audit.measuredClosure.targetDeclarations.pop();
            },
            'DISPLAYED_ND_HIGHER_AUTHORITY_DRIFT'
        );
        assertAuditError(
            audit => {
                audit.measuredClosure.canonicalExportEvidence
                    .historicalScaleContractSha256 = 'drift';
            },
            'DISPLAYED_ND_HIGHER_AUTHORITY_DRIFT'
        );
        assertAuditError(
            audit => {
                audit.surfaceAssessment.secondCheckerRequired = true;
            },
            'DISPLAYED_ND_HIGHER_BOUNDARY_DRIFT'
        );
        assertAuditError(
            audit => {
                audit.dependencyBoundary
                    .alreadyAvailableFreeDeclarationLinks.pop();
            },
            'DISPLAYED_ND_HIGHER_BOUNDARY_DRIFT'
        );
        assertAuditError(
            audit => {
                audit.dependencyBoundary
                    .transparentDefinitionsMustRemainChecked.pop();
            },
            'DISPLAYED_ND_HIGHER_BOUNDARY_DRIFT'
        );
        assertAuditError(
            audit => {
                audit.recommendedContinuation.surfaceMethodDelta = 1;
            },
            'DISPLAYED_ND_HIGHER_PROPOSAL_DRIFT'
        );
        const browser = readFileSync(
            resolve(repositoryRoot, 'src/v3_2/browser.ts'),
            'utf8'
        );
        assert.doesNotMatch(
            browser,
            /categorical_displayed_nd_higher|DISPLAYED-ND-HIGHER/u
        );
    });

    it(
        'matches live canonical acquisition and the bounded consumer',
        {
            skip:
                process.env
                    .EMDASH_RUN_LAMBDAPI_DISPLAYED_ND_HIGHER_PROBES !==
                '1'
        },
        () => {
            const contract =
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_ACQUISITION;
            const canonicalExportText = runLambdapi([
                'export',
                '-o',
                'lp',
                'emdash3_2.lp'
            ]);
            assert.equal(
                runLambdapi([
                    'export',
                    '-o',
                    'lp',
                    'emdash3_2.lp'
                ]),
                canonicalExportText
            );
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
                    observedExporterVersion:
                        runLambdapi(['--version']).trim()
                }
            );
            assert.deepEqual(
                selection.commands.map(entry => entry.command.ordinal),
                contract.commands.map(command => command.ordinal)
            );
            runLambdapi([
                'check',
                '-w',
                `--map-dir=emdash:${lambdapiRoot}`,
                '--map-dir=emdash_tests:' +
                    resolve(repositoryRoot, 'tests/fixtures'),
                resolve(
                    repositoryRoot,
                    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
                        .concreteConsumer.fixture
                )
            ]);
        }
    );
});
