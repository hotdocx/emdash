/**
 * Reviewed DIRECTED-1B dependent-pair, projection, and transport slice.
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
    CORE_MVP_MANIFEST,
    CORE_OWNER_SCHEMAS,
    CoreCheckerError,
    CoreDirected1aCatalogError,
    CoreDirected1bCatalog,
    CoreDirected1bCatalogError,
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
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    provenance,
    serializeCoreLfKernelProbe,
    sourceSpan
} from '../src/v3_2';

const fixturePath = 'tests/fixtures/v3_2_directed_1b.surface.ts';

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
    because(line, `DIRECTED-1B owner ${name}`)
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

const homType = (
    category: KernelExpression,
    source: KernelExpression,
    target: KernelExpression,
    line: number
): KernelExpression => decode(owner(
    'hom-classifier',
    [category, source, target],
    line
), line);

const functorType = (
    source: KernelExpression,
    target: KernelExpression,
    line: number
): KernelExpression => decode(owner(
    'functor-classifier',
    [source, target],
    line
), line);

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
        'DIRECTED-1B encoded pair family'
    );
    const pairIndex = kernelBound(
        0,
        because(line, 'DIRECTED-1B encoded pair index')
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

const transportedObject = (
    base: KernelExpression,
    family: KernelExpression,
    source: KernelExpression,
    target: KernelExpression,
    arrow: KernelExpression,
    value: KernelExpression,
    line: number
): KernelExpression => {
    const sourceFibre = fibre(base, family, source, line);
    const targetFibre = fibre(base, family, target, line);
    const action = owner(
        'functor-hom-capped',
        [
            base,
            categoryOfCategories(line),
            family,
            source,
            target,
            arrow
        ],
        line
    );
    return owner(
        'functor-object',
        [sourceFibre, targetFibre, action, value],
        line
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
            because(line, 'DIRECTED-1B constant Cat family')
        ),
        point,
        telescope
    ],
    line
);

interface Directed1bFixture {
    readonly catalog: CoreDirected1bCatalog;
    readonly environment: CoreLfDeclarationEnvironment;
    readonly K: KernelExpression;
    readonly R: KernelExpression;
    readonly FF: KernelExpression;
    readonly k: KernelExpression;
    readonly l: KernelExpression;
    readonly p: KernelExpression;
    readonly r: KernelExpression;
    readonly sigmaBase: KernelExpression;
    readonly telescopeFamily: KernelExpression;
    readonly pairX: KernelExpression;
    readonly pairY: KernelExpression;
    readonly telescopeSource: KernelExpression;
    readonly telescopeTarget: KernelExpression;
    readonly telescopeTransport: KernelExpression;
    readonly telescopeTransportType: KernelExpression;
    readonly expandedTelescopeTransport: KernelExpression;
}

const directedFixture = (): Directed1bFixture => {
    const catalog = CoreDirected1bCatalog.create(
        because(1, 'DIRECTED-1B reviewed primitive catalog')
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
            provenance: because(line, `DIRECTED-1B assumption ${name}`)
        });
    };

    assume('directed1b_K', categoryUniverse(2), 2);
    const K = kernelFree('directed1b_K', because(3, 'DIRECTED-1B K'));
    assume(
        'directed1b_R',
        coreDisplayedFamilyType(
            K,
            because(4, 'DIRECTED-1B R type')
        ),
        4
    );
    const R = kernelFree('directed1b_R', because(5, 'DIRECTED-1B R'));
    const constantCategoryFamily = coreConstantDisplayedFamily(
        K,
        categoryOfCategories(6),
        because(6, 'DIRECTED-1B constant Cat family')
    );
    const telescopeCategory =
        catalog.directed1a.displayedFunctorCategory(
            K,
            R,
            constantCategoryFamily,
            because(7, 'DIRECTED-1B telescope category')
        );
    assume('directed1b_FF', objectType(telescopeCategory, 8), 8);
    const FF = kernelFree(
        'directed1b_FF',
        because(9, 'DIRECTED-1B FF')
    );
    assume('directed1b_k', objectType(K, 10), 10);
    const k = kernelFree('directed1b_k', because(11, 'DIRECTED-1B k'));
    assume('directed1b_l', objectType(K, 12), 12);
    const l = kernelFree('directed1b_l', because(13, 'DIRECTED-1B l'));
    assume('directed1b_p', homType(K, k, l, 14), 14);
    const p = kernelFree('directed1b_p', because(15, 'DIRECTED-1B p'));
    assume(
        'directed1b_r',
        familyObjectType(K, R, k, 16),
        16
    );
    const r = kernelFree('directed1b_r', because(17, 'DIRECTED-1B r'));

    const sigmaBase = catalog.directed1a.sigmaCategory(
        K,
        R,
        because(18, 'DIRECTED-1B Sigma base')
    );
    const telescopeFamily =
        catalog.directed1a.sigmaTelescopeFamily(
            K,
            R,
            FF,
            because(19, 'DIRECTED-1B telescope family')
        );
    const pairFamily = encodedPairFamily(K, R, 20);
    const pairX = catalog.dependentPair(
        objectClassifier(K, 20),
        pairFamily,
        k,
        r,
        because(20, 'DIRECTED-1B source pair')
    );
    const transportedR = transportedObject(
        K,
        R,
        k,
        l,
        p,
        r,
        21
    );
    const pairY = catalog.dependentPair(
        objectClassifier(K, 21),
        pairFamily,
        l,
        transportedR,
        because(21, 'DIRECTED-1B target pair')
    );
    const telescopeSource = fibre(
        sigmaBase,
        telescopeFamily,
        pairX,
        22
    );
    const telescopeTarget = fibre(
        sigmaBase,
        telescopeFamily,
        pairY,
        23
    );
    const telescopeTransport = catalog.sigmaTelescopeTransport(
        K,
        R,
        FF,
        k,
        l,
        p,
        r,
        because(24, 'DIRECTED-1B telescope transport')
    );
    const telescopeTransportType = functorType(
        telescopeSource,
        telescopeTarget,
        25
    );
    const canonicalSigmaTransport = catalog.sigmaTransportArrow(
        K,
        R,
        k,
        l,
        p,
        r,
        because(26, 'DIRECTED-1B canonical Sigma transport')
    );
    const expandedTelescopeTransport = owner(
        'functor-hom-capped',
        [
            sigmaBase,
            categoryOfCategories(27),
            telescopeFamily,
            pairX,
            pairY,
            canonicalSigmaTransport
        ],
        27
    );

    return {
        catalog,
        environment,
        K,
        R,
        FF,
        k,
        l,
        p,
        r,
        sigmaBase,
        telescopeFamily,
        pairX,
        pairY,
        telescopeSource,
        telescopeTarget,
        telescopeTransport,
        telescopeTransportType,
        expandedTelescopeTransport
    };
};

describe('TypeScript v3.2 reviewed DIRECTED-1B catalog', () => {
    it('compiles eight ordered candidate owners with the reviewed transparency boundary', () => {
        const fixture = directedFixture();
        assert.deepEqual(
            fixture.catalog.environment.declarations.map(
                declaration => [
                    declaration.name,
                    declaration.transparency,
                    declaration.body === undefined
                        ? 'body-free'
                        : 'checked-body'
                ]
            ),
            [
                ...Object.values(CORE_DIRECTED_1A_PRIMITIVE_NAMES).map(
                    name => [name, 'opaque', 'body-free']
                ),
                [
                    'dttlf_decoded_sigma',
                    'opaque',
                    'body-free'
                ],
                [
                    'dttlf_Struct_sigma',
                    'opaque',
                    'body-free'
                ],
                [
                    'dttlf_Sigma_proj1_func',
                    'opaque',
                    'body-free'
                ],
                [
                    'dttlf_sigma_transport_arrow',
                    'opaque',
                    'body-free'
                ],
                [
                    'dttlf_Sigma_catd_transport_func',
                    'transparent',
                    'checked-body'
                ]
            ]
        );
        assert.deepEqual(
            fixture.catalog.primitives.map(primitive => [
                primitive.owner,
                primitive.coreName,
                primitive.backendName,
                primitive.disposition
            ]),
            [
                [
                    'decoded-dependent-pair',
                    'dttlf_decoded_sigma',
                    'τΣ_',
                    'opaque-import'
                ],
                [
                    'dependent-pair',
                    'dttlf_Struct_sigma',
                    'Struct_sigma',
                    'opaque-import'
                ],
                [
                    'sigma-first-projection',
                    'dttlf_Sigma_proj1_func',
                    'Sigma_proj1_func',
                    'opaque-import'
                ],
                [
                    'sigma-transport-arrow',
                    'dttlf_sigma_transport_arrow',
                    'sigma_transport_arrow',
                    'opaque-import'
                ],
                [
                    'sigma-telescope-transport',
                    'dttlf_Sigma_catd_transport_func',
                    'Sigma_catd_transport_func',
                    'transparent-checked-definition'
                ]
            ]
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

    it('runs the exact seven-rule component in reviewed order', () => {
        const fixture = directedFixture();
        const runtime = fixture.catalog.runtimeProgram;
        assert.equal(
            runtime.revision,
            'DIRECTED-FOUNDATION-1+DIRECTED-FOUNDATION-2+' +
            'DIRECTED-1B-REVIEWED'
        );
        assert.deepEqual(runtime.ruleIds, [
            'directed.category-object.decode',
            'directed.displayed-family.decode',
            'directed.displayed-functor.decode',
            'directed.category-hom.decode',
            'directed.sigma-object.decode',
            'directed.sigma-first-projection.evaluate',
            'directed.sigma-telescope-fibre.evaluate'
        ]);
        assert.equal(Object.isFrozen(runtime), true);
        assert.equal(Object.isFrozen(runtime.ruleIds), true);

        const pairClassifier = fixture.catalog.decodedDependentPair(
            objectClassifier(fixture.K, 30),
            encodedPairFamily(fixture.K, fixture.R, 30),
            because(30, 'DIRECTED-1B decoded pair classifier')
        );
        const sigmaDecode = runtime.rewriteHead(
            objectType(fixture.sigmaBase, 31)
        );
        assert.equal(sigmaDecode.status, 'rewritten');
        if (sigmaDecode.status === 'rewritten') {
            assert.equal(sigmaDecode.ruleIndex, 4);
            assert.equal(
                kernelExpressionEquals(
                    sigmaDecode.after,
                    pairClassifier
                ),
                true
            );
        }

        const catHom = runtime.rewriteHead(homType(
            categoryOfCategories(32),
            fixture.sigmaBase,
            fixture.K,
            32
        ));
        assert.equal(catHom.status, 'rewritten');
        if (catHom.status === 'rewritten') {
            assert.equal(catHom.ruleIndex, 3);
            assert.equal(
                catHom.ruleId,
                'directed.category-hom.decode'
            );
        }
    });

    it('types dependent pairs and evaluates the Sigma first projection', () => {
        const fixture = directedFixture();
        const checker = fixture.catalog.createChecker(
            fixture.environment
        );
        assert.doesNotThrow(() => checker.check(
            checker.rootContext,
            fixture.pairX,
            objectType(fixture.sigmaBase, 40)
        ));

        const projection = owner(
            'functor-object',
            [
                fixture.sigmaBase,
                fixture.K,
                fixture.catalog.sigmaFirstProjection(
                    fixture.K,
                    fixture.R,
                    because(41, 'DIRECTED-1B first projection')
                ),
                fixture.pairX
            ],
            41
        );
        const comparison = coreLfDefinitionalCompare(
            fixture.environment,
            projection,
            fixture.k,
            16,
            undefined,
            fixture.catalog.runtimeProgram
        );
        assert.equal(comparison.status, 'equal');
        assert.deepEqual(
            comparison.trace.map(entry =>
                entry.reduction.kind === 'runtime'
                    ? entry.reduction.ruleId
                    : entry.reduction.kind
            ),
            ['directed.sigma-first-projection.evaluate']
        );
    });

    it('evaluates the nested telescope fibre at a dependent pair', () => {
        const fixture = directedFixture();
        const expected = owner(
            'functor-object',
            [
                fibre(
                    fixture.K,
                    fixture.R,
                    fixture.k,
                    50
                ),
                categoryOfCategories(50),
                telescopePointFunctor(
                    fixture.K,
                    fixture.R,
                    fixture.FF,
                    fixture.k,
                    50
                ),
                fixture.r
            ],
            50
        );
        const comparison = coreLfDefinitionalCompare(
            fixture.environment,
            fixture.telescopeSource,
            expected,
            16,
            undefined,
            fixture.catalog.runtimeProgram
        );
        assert.equal(comparison.status, 'equal');
        assert.deepEqual(
            comparison.trace.map(entry =>
                entry.reduction.kind === 'runtime'
                    ? entry.reduction.ruleId
                    : entry.reduction.kind
            ),
            ['directed.sigma-telescope-fibre.evaluate']
        );
    });

    it('checks total telescope transport and its transparent definition', () => {
        const fixture = directedFixture();
        const checker = fixture.catalog.createChecker(
            fixture.environment
        );
        assert.doesNotThrow(() => checker.check(
            checker.rootContext,
            fixture.telescopeTransport,
            fixture.telescopeTransportType
        ));
        const inferred = checker.infer(
            checker.rootContext,
            fixture.telescopeTransport
        );
        assert.equal(
            coreLfDefinitionalCompare(
                fixture.environment,
                inferred.type as KernelExpression,
                fixture.telescopeTransportType,
                32,
                undefined,
                fixture.catalog.runtimeProgram
            ).status,
            'equal'
        );

        const unfolded = coreLfDefinitionalCompare(
            fixture.environment,
            fixture.telescopeTransport,
            fixture.expandedTelescopeTransport,
            32,
            undefined,
            fixture.catalog.runtimeProgram
        );
        assert.equal(unfolded.status, 'equal');
        assert.equal(
            unfolded.trace.some(
                entry => entry.reduction.kind === 'delta'
            ),
            true
        );
        assert.equal(
            unfolded.trace.filter(
                entry => entry.reduction.kind === 'beta'
            ).length,
            7
        );
    });

    it('lowers the transport consumer through the scoped builder', () => {
        const fixture = directedFixture();
        const builder = new CoreLfScopedBuilder(
            because(60, 'DIRECTED-1B scoped surface')
        );
        const built = fixture.catalog.builderApplication(
            builder,
            'sigma-telescope-transport',
            [
                builder.embed(fixture.K),
                builder.embed(fixture.R),
                builder.embed(fixture.FF),
                builder.embed(fixture.k),
                builder.embed(fixture.l),
                builder.embed(fixture.p),
                builder.embed(fixture.r)
            ],
            because(61, 'DIRECTED-1B built telescope transport')
        );
        assert.equal(
            kernelExpressionEquals(
                builder.lower(built),
                fixture.telescopeTransport
            ),
            true
        );
    });

    it('rejects wrong bases, family endpoints, and malformed arity', () => {
        const fixture = directedFixture();
        const checker = fixture.catalog.createChecker(
            fixture.environment
        );
        const wrongPair = fixture.catalog.dependentPair(
            objectClassifier(fixture.K, 70),
            encodedPairFamily(fixture.K, fixture.R, 70),
            fixture.l,
            fixture.r,
            because(70, 'DIRECTED-1B wrong pair endpoint')
        );
        assert.throws(
            () => checker.infer(checker.rootContext, wrongPair),
            error => error instanceof CoreCheckerError
        );

        const wrongFamilyPair = fixture.catalog.dependentPair(
            objectClassifier(fixture.K, 71),
            encodedPairFamily(
                fixture.K,
                coreConstantDisplayedFamily(
                    fixture.K,
                    categoryOfCategories(71),
                    because(71, 'DIRECTED-1B wrong pair family')
                ),
                71
            ),
            fixture.k,
            fixture.r,
            because(71, 'DIRECTED-1B wrong-family pair')
        );
        assert.throws(
            () => checker.infer(
                checker.rootContext,
                wrongFamilyPair
            ),
            error => error instanceof CoreCheckerError
        );

        const wrongTransport =
            fixture.catalog.sigmaTelescopeTransport(
                fixture.K,
                fixture.R,
                fixture.FF,
                fixture.l,
                fixture.k,
                fixture.p,
                fixture.r,
                because(71, 'DIRECTED-1B reversed endpoints')
            );
        assert.throws(
            () => checker.infer(
                checker.rootContext,
                wrongTransport
            ),
            error => error instanceof CoreCheckerError
        );

        const wrongBaseProjection =
            fixture.catalog.sigmaFirstProjection(
                categoryOfCategories(73),
                fixture.R,
                because(73, 'DIRECTED-1B wrong base')
            );
        assert.throws(
            () => checker.infer(
                checker.rootContext,
                wrongBaseProjection
            ),
            error => error instanceof CoreCheckerError
        );

        assert.throws(
            () => fixture.catalog.application(
                'dependent-pair',
                [fixture.K],
                because(74, 'DIRECTED-1B malformed arity')
            ),
            error =>
                error instanceof CoreDirected1bCatalogError &&
                error.code === 'INVALID_CANDIDATE_ARITY'
        );
    });

    it('rejects ambiguous and unchecked external mirror mappings', () => {
        const fixture = directedFixture();
        const assertion = {
            label: 'DIRECTED-1B mirror boundary',
            term: fixture.telescopeTransport,
            type: fixture.telescopeTransportType,
            span: at(85, 1, 80)
        };
        assert.throws(
            () => serializeCoreLfKernelProbe({
                environment: fixture.environment,
                externalFreeReferences:
                    fixture.catalog.externalFreeReferences,
                externalTransparentDefinitions: {
                    ...fixture.catalog
                        .externalTransparentDefinitions,
                    dttlf_decoded_sigma: 'τΣ_'
                },
                assertions: [assertion]
            }),
            /cannot be both an opaque import and a transparent mirror/
        );

        const opaqueReferences = {
            ...fixture.catalog.externalFreeReferences
        };
        delete opaqueReferences.dttlf_decoded_sigma;
        assert.throws(
            () => serializeCoreLfKernelProbe({
                environment: fixture.environment,
                externalFreeReferences: opaqueReferences,
                externalTransparentDefinitions: {
                    ...fixture.catalog
                        .externalTransparentDefinitions,
                    dttlf_decoded_sigma: 'τΣ_'
                },
                assertions: [assertion]
            }),
            /must have a checked transparent body/
        );
    });

    it('keeps default LF, MVP, browser, and base owner catalogs unchanged', () => {
        const fixture = directedFixture();
        const pairClassifier = fixture.catalog.decodedDependentPair(
            objectClassifier(fixture.K, 80),
            encodedPairFamily(fixture.K, fixture.R, 80),
            because(80, 'DIRECTED-1B opt-in pair classifier')
        );
        assert.equal(
            coreLfDefinitionalCompare(
                fixture.environment,
                objectType(fixture.sigmaBase, 80),
                pairClassifier,
                8
            ).status,
            'not-equal'
        );
        for (const ownerId of Object.keys(
            CORE_DIRECTED_1B_PRIMITIVE_NAMES
        )) {
            assert.equal(ownerId in CORE_OWNER_SCHEMAS, false);
            assert.equal(ownerId in LAMBDAPI_V32_OWNER_BINDINGS, false);
            assert.equal(
                CORE_MVP_MANIFEST.owners.some(
                    entry => entry.owner === ownerId
                ),
                false
            );
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
            /directed_1b|CoreDirected1b|dttlf_/
        );
    });

    it('rejects a foreign LF environment', () => {
        const fixture = directedFixture();
        assert.throws(
            () => fixture.catalog.createChecker(
                CoreLfDeclarationEnvironment.empty()
            ),
            error =>
                (
                    error instanceof CoreDirected1bCatalogError ||
                    error instanceof CoreDirected1aCatalogError
                ) &&
                error.code === 'FOREIGN_CANDIDATE_ENVIRONMENT'
        );
    });

    it('serializes active owners without opaque or transparent shadows', () => {
        const fixture = directedFixture();
        const pairClassifier = fixture.catalog.decodedDependentPair(
            objectClassifier(fixture.K, 89),
            encodedPairFamily(fixture.K, fixture.R, 89),
            because(89, 'DIRECTED-1B serialized pair classifier')
        );
        const firstProjection = owner(
            'functor-object',
            [
                fixture.sigmaBase,
                fixture.K,
                fixture.catalog.sigmaFirstProjection(
                    fixture.K,
                    fixture.R,
                    because(89, 'DIRECTED-1B serialized projection')
                ),
                fixture.pairX
            ],
            89
        );
        const serialized = serializeCoreLfKernelProbe({
            environment: fixture.environment,
            externalFreeReferences:
                fixture.catalog.externalFreeReferences,
            externalTransparentDefinitions:
                fixture.catalog.externalTransparentDefinitions,
            assertions: [
                {
                    label: 'DIRECTED-1B dependent pair',
                    term: fixture.pairX,
                    type: pairClassifier,
                    span: at(89, 1, 80)
                },
                {
                    label: 'DIRECTED-1B first projection',
                    term: firstProjection,
                    type: objectType(fixture.K, 90),
                    span: at(90, 1, 80)
                },
                {
                    label: 'DIRECTED-1B total telescope transport',
                    term: fixture.telescopeTransport,
                    type: fixture.telescopeTransportType,
                    span: at(91, 1, 80)
                }
            ],
            conversions: [{
                label: 'DIRECTED-1B checked transparent transport body',
                left: fixture.telescopeTransport,
                right: fixture.expandedTelescopeTransport,
                span: at(92, 1, 80)
            }]
        });
        assert.doesNotMatch(serialized.source, /symbol dttlf_/);
        assert.doesNotMatch(serialized.source, /dttlf_/);
        assert.match(serialized.source, /@τΣ_/);
        assert.match(serialized.source, /@Struct_sigma/);
        assert.match(serialized.source, /@Sigma_proj1_func/);
        assert.match(serialized.source, /@sigma_transport_arrow/);
        assert.match(
            serialized.source,
            /@Sigma_catd_transport_func/
        );
        assert.equal(
            serialized.sourceMap.filter(
                entry => entry.kind === 'declaration'
            ).length,
            7
        );
    });

    it(
        'has the generated total transport accepted by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const fixture = directedFixture();
            const pairClassifier =
                fixture.catalog.decodedDependentPair(
                    objectClassifier(fixture.K, 99),
                    encodedPairFamily(
                        fixture.K,
                        fixture.R,
                        99
                    ),
                    because(
                        99,
                        'DIRECTED-1B oracle pair classifier'
                    )
                );
            const firstProjection = owner(
                'functor-object',
                [
                    fixture.sigmaBase,
                    fixture.K,
                    fixture.catalog.sigmaFirstProjection(
                        fixture.K,
                        fixture.R,
                        because(
                            100,
                            'DIRECTED-1B oracle projection'
                        )
                    ),
                    fixture.pairX
                ],
                100
            );
            const serialized = serializeCoreLfKernelProbe({
                environment: fixture.environment,
                externalFreeReferences:
                    fixture.catalog.externalFreeReferences,
                externalTransparentDefinitions:
                    fixture.catalog.externalTransparentDefinitions,
                assertions: [
                    {
                        label: 'DIRECTED-1B dependent pair',
                        term: fixture.pairX,
                        type: pairClassifier,
                        span: at(99, 1, 80)
                    },
                    {
                        label: 'DIRECTED-1B first projection',
                        term: firstProjection,
                        type: objectType(fixture.K, 100),
                        span: at(100, 1, 80)
                    },
                    {
                        label: 'DIRECTED-1B total telescope transport',
                        term: fixture.telescopeTransport,
                        type: fixture.telescopeTransportType,
                        span: at(101, 1, 80)
                    }
                ],
                conversions: [{
                    label:
                        'DIRECTED-1B checked transparent transport body',
                    left: fixture.telescopeTransport,
                    right: fixture.expandedTelescopeTransport,
                    span: at(102, 1, 80)
                }]
            });
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });
            assert.equal(
                result.accepted,
                true,
                `Expected DIRECTED-1B acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );
});
