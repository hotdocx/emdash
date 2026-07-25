/**
 * Reviewed DIRECTED-1C section evaluation and combined graduation consumer.
 */

import assert from 'node:assert/strict';
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
    CORE_DIRECTED_1A_PRIMITIVE_NAMES,
    CORE_DIRECTED_1B_PRIMITIVE_NAMES,
    CORE_DIRECTED_1C_PRIMITIVE_NAMES,
    CORE_MVP_MANIFEST,
    CORE_OWNER_SCHEMAS,
    CoreCheckerError,
    CoreDirected1aCatalogError,
    CoreDirected1bCatalogError,
    CoreDirected1cCatalog,
    CoreDirected1cCatalogError,
    CoreLfDeclarationEnvironment,
    CoreLfScopedBuilder,
    KernelExpression,
    LAMBDAPI_V32_OWNER_BINDINGS,
    binderMode,
    checkLambdapiProbe,
    coreConstantDisplayedFamily,
    coreDisplayedFamilyType,
    coreLfDefinitionalCompare,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    provenance,
    serializeCoreLfKernelProbe,
    sourceSpan
} from '../src/v3_2';

const fixturePath = 'tests/fixtures/v3_2_directed_1c.surface.ts';

const at = (
    line: number,
    startColumn = 1,
    endColumn = startColumn + 1
) => sourceSpan(
    fixturePath,
    line,
    startColumn,
    line,
    endColumn
);

const because = (
    line: number,
    detail: string
) => provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');

const owner = (
    name: Parameters<typeof kernelApplication>[0],
    arguments_: readonly KernelExpression[] = [],
    line = 1
): KernelExpression => kernelApplication(
    name,
    arguments_.map(value => ({ value })),
    because(line, `DIRECTED-1C owner ${name}`)
);

const categoryUniverse = (
    line: number
): KernelExpression => owner('category-universe', [], line);

const categoryOfCategories = (
    line: number
): KernelExpression => owner('category-of-categories', [], line);

const objectClassifier = (
    category: KernelExpression,
    line: number
): KernelExpression => owner('object-classifier', [category], line);

const decode = (
    classifier: KernelExpression,
    line: number
): KernelExpression => owner('decode', [classifier], line);

const objectType = (
    category: KernelExpression,
    line: number
): KernelExpression => decode(objectClassifier(category, line), line);

const sectionCategory = (
    base: KernelExpression,
    family: KernelExpression,
    line: number
): KernelExpression => owner(
    'section-category',
    [base, family],
    line
);

const fibre = (
    base: KernelExpression,
    family: KernelExpression,
    point: KernelExpression,
    line: number
): KernelExpression => owner(
    'functor-object',
    [base, categoryOfCategories(line), family, point],
    line
);

const familyObjectType = (
    base: KernelExpression,
    family: KernelExpression,
    point: KernelExpression,
    line: number
): KernelExpression => objectType(
    fibre(base, family, point, line),
    line
);

const encodedPairFamily = (
    base: KernelExpression,
    family: KernelExpression,
    line: number
): KernelExpression => {
    const nodeProvenance = because(
        line,
        'DIRECTED-1C encoded pair family'
    );
    const pairIndex = kernelBound(
        0,
        because(line, 'DIRECTED-1C encoded pair index')
    );
    return kernelLambda(
        kernelBinder(
            'pairIndex',
            objectType(base, line),
            explicitFunctorial,
            nodeProvenance
        ),
        objectClassifier(
            fibre(base, family, pairIndex, line),
            line
        ),
        nodeProvenance
    );
};

const telescopePointFunctor = (
    base: KernelExpression,
    family: KernelExpression,
    telescope: KernelExpression,
    point: KernelExpression,
    line: number
): KernelExpression => owner(
    'transfor-component-capped',
    [
        base,
        categoryOfCategories(line),
        family,
        coreConstantDisplayedFamily(
            base,
            categoryOfCategories(line),
            because(line, 'DIRECTED-1C constant Cat family')
        ),
        point,
        telescope
    ],
    line
);

interface Directed1cFixture {
    readonly catalog: CoreDirected1cCatalog;
    readonly environment: CoreLfDeclarationEnvironment;
    readonly K: KernelExpression;
    readonly R: KernelExpression;
    readonly FF: KernelExpression;
    readonly k: KernelExpression;
    readonly r: KernelExpression;
    readonly telescopeCategory: KernelExpression;
    readonly sigmaBase: KernelExpression;
    readonly telescopeFamily: KernelExpression;
    readonly pair: KernelExpression;
    readonly sectionType: KernelExpression;
    readonly section: KernelExpression;
    readonly evaluation: KernelExpression;
    readonly rawEvaluationType: KernelExpression;
    readonly reducedEvaluationType: KernelExpression;
    readonly outerEvaluation: KernelExpression;
    readonly combinedTypeRedex: KernelExpression;
}

const directedFixture = (): Directed1cFixture => {
    const catalog = CoreDirected1cCatalog.create(
        because(1, 'DIRECTED-1C reviewed primitive catalog')
    );
    let environment = catalog.environment;
    const assume = (
        name: string,
        type: KernelExpression,
        line: number
    ): void => {
        environment = environment.extend({
            name,
            type,
            mode: explicitFunctorial,
            provenance: because(line, `DIRECTED-1C assumption ${name}`)
        });
    };

    assume('directed1c_K', categoryUniverse(2), 2);
    const K = kernelFree('directed1c_K', because(3, 'DIRECTED-1C K'));
    assume(
        'directed1c_R',
        coreDisplayedFamilyType(
            K,
            because(4, 'DIRECTED-1C R type')
        ),
        4
    );
    const R = kernelFree('directed1c_R', because(5, 'DIRECTED-1C R'));
    const constantCategoryFamily = coreConstantDisplayedFamily(
        K,
        categoryOfCategories(6),
        because(6, 'DIRECTED-1C constant Cat family')
    );
    const telescopeCategory =
        catalog.directed1b.directed1a.displayedFunctorCategory(
            K,
            R,
            constantCategoryFamily,
            because(7, 'DIRECTED-1C telescope category')
        );
    assume('directed1c_FF', objectType(telescopeCategory, 8), 8);
    const FF = kernelFree(
        'directed1c_FF',
        because(9, 'DIRECTED-1C FF')
    );
    assume('directed1c_k', objectType(K, 10), 10);
    const k = kernelFree('directed1c_k', because(11, 'DIRECTED-1C k'));
    assume(
        'directed1c_r',
        familyObjectType(K, R, k, 12),
        12
    );
    const r = kernelFree('directed1c_r', because(13, 'DIRECTED-1C r'));

    const sigmaBase =
        catalog.directed1b.directed1a.sigmaCategory(
            K,
            R,
            because(14, 'DIRECTED-1C Sigma base')
        );
    const telescopeFamily =
        catalog.directed1b.directed1a.sigmaTelescopeFamily(
            K,
            R,
            FF,
            because(15, 'DIRECTED-1C telescope family')
        );
    const pair = catalog.directed1b.dependentPair(
        objectClassifier(K, 16),
        encodedPairFamily(K, R, 16),
        k,
        r,
        because(16, 'DIRECTED-1C dependent pair')
    );
    const sectionType = objectType(
        sectionCategory(sigmaBase, telescopeFamily, 17),
        17
    );
    assume('directed1c_s', sectionType, 18);
    const section = kernelFree(
        'directed1c_s',
        because(19, 'DIRECTED-1C section')
    );
    const evaluation = catalog.sectionObjectEvaluation(
        sigmaBase,
        telescopeFamily,
        section,
        pair,
        because(20, 'DIRECTED-1C section evaluation')
    );
    const rawEvaluationType = objectType(
        fibre(sigmaBase, telescopeFamily, pair, 21),
        21
    );
    const reducedEvaluationType = objectType(
        owner(
            'functor-object',
            [
                fibre(K, R, k, 22),
                categoryOfCategories(22),
                telescopePointFunctor(K, R, FF, k, 22),
                r
            ],
            22
        ),
        22
    );

    const boundSection = kernelBound(
        0,
        because(23, 'DIRECTED-1C bound section')
    );
    const outerLambda = kernelLambda(
        kernelBinder(
            'section',
            sectionType,
            explicitFunctorial,
            because(23, 'DIRECTED-1C outer evaluator binder')
        ),
        catalog.sectionObjectEvaluation(
            sigmaBase,
            telescopeFamily,
            boundSection,
            pair,
            because(23, 'DIRECTED-1C bound section evaluation')
        ),
        because(23, 'DIRECTED-1C outer evaluator')
    );
    const outerEvaluation = kernelCall(
        outerLambda,
        [{
            plicity: 'explicit',
            value: section
        }],
        because(24, 'DIRECTED-1C outer application')
    );

    /*
     * A type-level witness makes the composition visible in one conversion
     * trace: beta exposes the raw telescope fibre, then the reviewed
     * DIRECTED-1B rule computes that fibre at the dependent pair.
     */
    const combinedTypeRedex = kernelCall(
        kernelLambda(
            kernelBinder(
                'section',
                sectionType,
                explicitFunctorial,
                because(25, 'DIRECTED-1C combined type binder')
            ),
            rawEvaluationType,
            because(25, 'DIRECTED-1C combined type abstraction')
        ),
        [{
            plicity: 'explicit',
            value: section
        }],
        because(25, 'DIRECTED-1C combined type redex')
    );

    return {
        catalog,
        environment,
        K,
        R,
        FF,
        k,
        r,
        telescopeCategory,
        sigmaBase,
        telescopeFamily,
        pair,
        sectionType,
        section,
        evaluation,
        rawEvaluationType,
        reducedEvaluationType,
        outerEvaluation,
        combinedTypeRedex
    };
};

const comparisonSteps = (
    comparison: ReturnType<typeof coreLfDefinitionalCompare>
): readonly string[] => comparison.trace.map(entry =>
    entry.reduction.kind === 'runtime'
        ? entry.reduction.ruleId
        : entry.reduction.kind
);

describe('TypeScript v3.2 reviewed DIRECTED-1C catalog', () => {
    it('adds exactly one opaque body-free section evaluator', () => {
        const fixture = directedFixture();
        assert.equal(
            fixture.catalog.environment.declarations.length,
            9
        );
        assert.deepEqual(
            fixture.catalog.environment.declarations.slice(-1).map(
                declaration => [
                    declaration.name,
                    declaration.transparency,
                    declaration.body === undefined
                        ? 'body-free'
                        : 'checked-body'
                ]
            ),
            [['dttlf_piapp0', 'opaque', 'body-free']]
        );
        assert.deepEqual(
            fixture.catalog.primitives.map(primitive => [
                primitive.owner,
                primitive.coreName,
                primitive.backendName,
                primitive.disposition,
                primitive.activeAuthority
            ]),
            [[
                'section-object-evaluation',
                'dttlf_piapp0',
                'piapp0',
                'opaque-import',
                'transparent-definition'
            ]]
        );
        assert.doesNotThrow(() =>
            fixture.catalog.createChecker().validateEnvironment()
        );
        assert.doesNotThrow(() =>
            fixture.catalog.createChecker(
                fixture.environment
            ).validateEnvironment()
        );
    });

    it('reuses the exact seven-rule DIRECTED-1B runtime by identity', () => {
        const fixture = directedFixture();
        assert.equal(
            fixture.catalog.runtimeProgram,
            fixture.catalog.directed1b.runtimeProgram
        );
        assert.deepEqual(fixture.catalog.runtimeProgram.ruleIds, [
            'directed.category-object.decode',
            'directed.displayed-family.decode',
            'directed.displayed-functor.decode',
            'directed.category-hom.decode',
            'directed.sigma-object.decode',
            'directed.sigma-first-projection.evaluate',
            'directed.sigma-telescope-fibre.evaluate'
        ]);
    });

    it('types section evaluation at the raw and computed telescope fibres', () => {
        const fixture = directedFixture();
        const checker = fixture.catalog.createChecker(
            fixture.environment
        );
        assert.doesNotThrow(() => checker.check(
            checker.rootContext,
            fixture.evaluation,
            fixture.reducedEvaluationType
        ));
        const inferred = checker.infer(
            checker.rootContext,
            fixture.evaluation
        );
        assert.equal(
            coreLfDefinitionalCompare(
                fixture.environment,
                inferred.type as KernelExpression,
                fixture.rawEvaluationType,
                16,
                undefined,
                fixture.catalog.runtimeProgram
            ).status,
            'equal'
        );
        const reduced = coreLfDefinitionalCompare(
            fixture.environment,
            inferred.type as KernelExpression,
            fixture.reducedEvaluationType,
            16,
            undefined,
            fixture.catalog.runtimeProgram
        );
        assert.equal(reduced.status, 'equal');
        assert.deepEqual(
            comparisonSteps(reduced),
            ['directed.sigma-telescope-fibre.evaluate']
        );
    });

    it('composes outer beta with directed telescope-fibre computation', () => {
        const fixture = directedFixture();
        const checker = fixture.catalog.createChecker(
            fixture.environment
        );
        assert.doesNotThrow(() => checker.check(
            checker.rootContext,
            fixture.outerEvaluation,
            fixture.reducedEvaluationType
        ));

        const outerBeta = coreLfDefinitionalCompare(
            fixture.environment,
            fixture.outerEvaluation,
            fixture.evaluation,
            16,
            undefined,
            fixture.catalog.runtimeProgram
        );
        assert.equal(outerBeta.status, 'equal');
        assert.deepEqual(comparisonSteps(outerBeta), ['beta']);

        const combined = coreLfDefinitionalCompare(
            fixture.environment,
            fixture.combinedTypeRedex,
            fixture.reducedEvaluationType,
            16,
            undefined,
            fixture.catalog.runtimeProgram
        );
        assert.equal(combined.status, 'equal');
        assert.deepEqual(comparisonSteps(combined), [
            'beta',
            'directed.sigma-telescope-fibre.evaluate'
        ]);
    });

    it('lowers the combined evaluator through the scoped builder', () => {
        const fixture = directedFixture();
        const builder = new CoreLfScopedBuilder(
            because(50, 'DIRECTED-1C scoped surface')
        );
        const builtLambda = builder.lam(
            'section',
            builder.embed(fixture.sectionType),
            sectionToken => fixture.catalog.builderApplication(
                builder,
                'section-object-evaluation',
                [
                    builder.embed(fixture.sigmaBase),
                    builder.embed(fixture.telescopeFamily),
                    sectionToken,
                    builder.embed(fixture.pair)
                ],
                because(51, 'DIRECTED-1C built section evaluation')
            ),
            explicitFunctorial,
            because(51, 'DIRECTED-1C built outer evaluator')
        );
        const builtApplication = builder.apply(
            builtLambda,
            builder.embed(fixture.section),
            'explicit',
            because(52, 'DIRECTED-1C built outer application')
        );
        assert.equal(
            kernelExpressionEquals(
                builder.lower(builtApplication),
                fixture.outerEvaluation
            ),
            true
        );
    });

    it('rejects mismatched telescope families and dependent pairs', () => {
        const fixture = directedFixture();
        let environment = fixture.environment;
        const assume = (
            name: string,
            type: KernelExpression,
            line: number
        ): KernelExpression => {
            environment = environment.extend({
                name,
                type,
                mode: explicitFunctorial,
                provenance: because(
                    line,
                    `DIRECTED-1C negative assumption ${name}`
                )
            });
            return kernelFree(
                name,
                because(line, `DIRECTED-1C negative ${name}`)
            );
        };

        const GG = assume(
            'directed1c_GG',
            objectType(fixture.telescopeCategory, 60),
            60
        );
        const wrongTelescopeFamily =
            fixture.catalog.directed1b.directed1a.sigmaTelescopeFamily(
                fixture.K,
                fixture.R,
                GG,
                because(61, 'DIRECTED-1C wrong telescope family')
            );
        const wrongFamilyEvaluation =
            fixture.catalog.sectionObjectEvaluation(
                fixture.sigmaBase,
                wrongTelescopeFamily,
                fixture.section,
                fixture.pair,
                because(62, 'DIRECTED-1C mismatched family evaluation')
            );

        const S = assume(
            'directed1c_S',
            coreDisplayedFamilyType(
                fixture.K,
                because(63, 'DIRECTED-1C S type')
            ),
            63
        );
        const q = assume(
            'directed1c_q',
            familyObjectType(fixture.K, S, fixture.k, 64),
            64
        );
        const wrongPair = fixture.catalog.directed1b.dependentPair(
            objectClassifier(fixture.K, 65),
            encodedPairFamily(fixture.K, S, 65),
            fixture.k,
            q,
            because(65, 'DIRECTED-1C wrong-family pair')
        );
        const wrongPairEvaluation =
            fixture.catalog.sectionObjectEvaluation(
                fixture.sigmaBase,
                fixture.telescopeFamily,
                fixture.section,
                wrongPair,
                because(66, 'DIRECTED-1C mismatched pair evaluation')
            );

        const checker = fixture.catalog.createChecker(environment);
        assert.throws(
            () => checker.infer(
                checker.rootContext,
                wrongFamilyEvaluation
            ),
            error => error instanceof CoreCheckerError
        );
        assert.throws(
            () => checker.infer(
                checker.rootContext,
                wrongPairEvaluation
            ),
            error => error instanceof CoreCheckerError
        );
    });

    it('rejects malformed arity and a foreign LF environment', () => {
        const fixture = directedFixture();
        assert.throws(
            () => fixture.catalog.application(
                'section-object-evaluation',
                [fixture.K],
                because(70, 'DIRECTED-1C malformed arity')
            ),
            error =>
                error instanceof CoreDirected1cCatalogError &&
                error.code === 'INVALID_CANDIDATE_ARITY'
        );
        assert.throws(
            () => fixture.catalog.createChecker(
                CoreLfDeclarationEnvironment.empty()
            ),
            error =>
                (
                    error instanceof CoreDirected1cCatalogError ||
                    error instanceof CoreDirected1bCatalogError ||
                    error instanceof CoreDirected1aCatalogError
                ) &&
                error.code === 'FOREIGN_CANDIDATE_ENVIRONMENT'
        );
    });

    it('keeps default LF, MVP, browser, and base owner catalogs unchanged', () => {
        const fixture = directedFixture();
        assert.equal(
            'section-object-evaluation' in CORE_OWNER_SCHEMAS,
            false
        );
        assert.equal(
            'section-object-evaluation' in LAMBDAPI_V32_OWNER_BINDINGS,
            false
        );
        assert.equal(
            CORE_MVP_MANIFEST.owners.some(
                entry => entry.owner === 'section-object-evaluation'
            ),
            false
        );
        for (const ownerId of [
            ...Object.keys(CORE_DIRECTED_1A_PRIMITIVE_NAMES),
            ...Object.keys(CORE_DIRECTED_1B_PRIMITIVE_NAMES),
            ...Object.keys(CORE_DIRECTED_1C_PRIMITIVE_NAMES)
        ]) {
            assert.equal(ownerId in CORE_OWNER_SCHEMAS, false);
        }
        for (const ruleId of fixture.catalog.runtimeProgram.ruleIds) {
            assert.equal(
                CORE_MVP_MANIFEST.rules.some(
                    entry => entry.id === ruleId
                ),
                false
            );
        }
        assert.doesNotMatch(
            readFileSync('src/v3_2/browser.ts', 'utf8'),
            /directed_1c|CoreDirected1c|dttlf_piapp0/
        );
    });

    it('serializes piapp0 and every prerequisite without shadows', () => {
        const fixture = directedFixture();
        const serialized = serializeCoreLfKernelProbe({
            environment: fixture.environment,
            externalFreeReferences:
                fixture.catalog.externalFreeReferences,
            externalTransparentDefinitions:
                fixture.catalog.externalTransparentDefinitions,
            assertions: [{
                label: 'DIRECTED-1C combined section evaluation',
                term: fixture.outerEvaluation,
                type: fixture.reducedEvaluationType,
                span: at(80, 1, 80)
            }],
            conversions: [
                {
                    label: 'DIRECTED-1C outer evaluator beta',
                    left: fixture.outerEvaluation,
                    right: fixture.evaluation,
                    span: at(81, 1, 80)
                },
                {
                    label: 'DIRECTED-1C telescope fibre computation',
                    left: fixture.rawEvaluationType,
                    right: fixture.reducedEvaluationType,
                    span: at(82, 1, 80)
                }
            ]
        });
        assert.doesNotMatch(serialized.source, /symbol dttlf_/);
        assert.doesNotMatch(serialized.source, /dttlf_/);
        assert.match(serialized.source, /@piapp0/);
        assert.match(serialized.source, /@Functord_cat/);
        assert.match(serialized.source, /@Sigma_cat/);
        assert.match(serialized.source, /@Sigma_catd_functord_catd/);
        assert.match(serialized.source, /@Struct_sigma/);
        assert.equal(
            serialized.sourceMap.filter(
                entry => entry.kind === 'declaration'
            ).length,
            6
        );
    });

    it(
        'has the generated combined consumer accepted by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const fixture = directedFixture();
            const serialized = serializeCoreLfKernelProbe({
                environment: fixture.environment,
                externalFreeReferences:
                    fixture.catalog.externalFreeReferences,
                externalTransparentDefinitions:
                    fixture.catalog.externalTransparentDefinitions,
                assertions: [{
                    label: 'DIRECTED-1C combined section evaluation',
                    term: fixture.outerEvaluation,
                    type: fixture.reducedEvaluationType,
                    span: at(90, 1, 80)
                }],
                conversions: [
                    {
                        label: 'DIRECTED-1C outer evaluator beta',
                        left: fixture.outerEvaluation,
                        right: fixture.evaluation,
                        span: at(91, 1, 80)
                    },
                    {
                        label: 'DIRECTED-1C telescope fibre computation',
                        left: fixture.rawEvaluationType,
                        right: fixture.reducedEvaluationType,
                        span: at(92, 1, 80)
                    }
                ]
            });
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });
            assert.equal(
                result.accepted,
                true,
                `Expected DIRECTED-1C acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );

    it(
        'has a mismatched section family rejected by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const fixture = directedFixture();
            let environment = fixture.environment.extend({
                name: 'directed1c_oracle_GG',
                type: objectType(fixture.telescopeCategory, 100),
                mode: explicitFunctorial,
                provenance: because(
                    100,
                    'DIRECTED-1C oracle negative GG'
                )
            });
            const GG = kernelFree(
                'directed1c_oracle_GG',
                because(101, 'DIRECTED-1C oracle GG')
            );
            const wrongFamily =
                fixture.catalog.directed1b.directed1a
                    .sigmaTelescopeFamily(
                        fixture.K,
                        fixture.R,
                        GG,
                        because(102, 'DIRECTED-1C oracle wrong family')
                    );
            const wrongEvaluation =
                fixture.catalog.sectionObjectEvaluation(
                    fixture.sigmaBase,
                    wrongFamily,
                    fixture.section,
                    fixture.pair,
                    because(103, 'DIRECTED-1C oracle wrong evaluation')
                );
            const serialized = serializeCoreLfKernelProbe({
                environment,
                externalFreeReferences:
                    fixture.catalog.externalFreeReferences,
                externalTransparentDefinitions:
                    fixture.catalog.externalTransparentDefinitions,
                assertions: [{
                    label: 'DIRECTED-1C mismatched section family',
                    term: wrongEvaluation,
                    type: fixture.rawEvaluationType,
                    span: at(103, 1, 80)
                }]
            });
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });
            assert.equal(result.accepted, false);
            assert.equal(result.timedOut, false);
        }
    );
});
