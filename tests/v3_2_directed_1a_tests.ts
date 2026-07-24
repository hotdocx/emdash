/**
 * Reviewed DIRECTED-1A isolated LF primitive catalog and first consumer.
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
    CORE_DIRECTED_1A_REVIEW,
    CORE_MVP_MANIFEST,
    CORE_OWNER_SCHEMAS,
    CoreCheckerError,
    CoreDirected1aCatalog,
    CoreDirected1aCatalogError,
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
    kernelExpressionEquals,
    kernelFree,
    provenance,
    serializeCoreLfKernelProbe,
    sourceSpan
} from '../src/v3_2';

const fixturePath = 'tests/fixtures/v3_2_directed_1a.surface.ts';

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

const categoryUniverse = (
    line: number
): KernelExpression => kernelApplication(
    'category-universe',
    [],
    because(line, 'DIRECTED-1A category universe')
);

const categoryOfCategories = (
    line: number
): KernelExpression => kernelApplication(
    'category-of-categories',
    [],
    because(line, 'DIRECTED-1A category of categories')
);

const objectType = (
    category: KernelExpression,
    line: number
): KernelExpression => kernelApplication('decode', [{
    value: kernelApplication('object-classifier', [{
        value: category
    }], because(line, 'DIRECTED-1A object classifier'))
}], because(line, 'DIRECTED-1A decoded object type'));

interface Directed1aFixture {
    readonly catalog: CoreDirected1aCatalog;
    readonly environment: CoreLfDeclarationEnvironment;
    readonly K: KernelExpression;
    readonly R: KernelExpression;
    readonly FF: KernelExpression;
    readonly sigmaBase: KernelExpression;
    readonly telescopeFamily: KernelExpression;
    readonly expectedFamilyType: KernelExpression;
}

const directedFixture = (): Directed1aFixture => {
    const catalog = CoreDirected1aCatalog.create(
        because(1, 'DIRECTED-1A reviewed primitive catalog')
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
            provenance: because(line, `DIRECTED-1A assumption ${name}`)
        });
    };

    assume('directed_K', categoryUniverse(2), 2);
    const K = kernelFree('directed_K', because(3, 'DIRECTED-1A K'));
    assume('directed_R', coreDisplayedFamilyType(
        K,
        because(4, 'DIRECTED-1A R type')
    ), 4);
    const R = kernelFree('directed_R', because(5, 'DIRECTED-1A R'));
    const constantCategoryFamily = coreConstantDisplayedFamily(
        K,
        categoryOfCategories(6),
        because(6, 'DIRECTED-1A constant Cat family')
    );
    const telescopeCategory = catalog.displayedFunctorCategory(
        K,
        R,
        constantCategoryFamily,
        because(7, 'DIRECTED-1A displayed telescope category')
    );
    assume('directed_FF', objectType(telescopeCategory, 8), 8);
    const FF = kernelFree('directed_FF', because(9, 'DIRECTED-1A FF'));
    const sigmaBase = catalog.sigmaCategory(
        K,
        R,
        because(10, 'DIRECTED-1A Sigma base')
    );
    const telescopeFamily = catalog.sigmaTelescopeFamily(
        K,
        R,
        FF,
        because(11, 'DIRECTED-1A uncurried telescope family')
    );
    const expectedFamilyType = coreDisplayedFamilyType(
        sigmaBase,
        because(12, 'DIRECTED-1A expected family type')
    );

    return {
        catalog,
        environment,
        K,
        R,
        FF,
        sigmaBase,
        telescopeFamily,
        expectedFamilyType
    };
};

describe('TypeScript v3.2 reviewed DIRECTED-1A catalog', () => {
    it('compiles the three reviewed signatures as ordered opaque LF primitives', () => {
        const fixture = directedFixture();
        assert.deepEqual(
            fixture.catalog.primitives.map(primitive => [
                primitive.owner,
                primitive.coreName,
                primitive.backendName
            ]),
            [
                [
                    'displayed-functor-category',
                    'dttlf_Functord_cat',
                    'Functord_cat'
                ],
                [
                    'sigma-category',
                    'dttlf_Sigma_cat',
                    'Sigma_cat'
                ],
                [
                    'sigma-telescope-family',
                    'dttlf_Sigma_catd_functord_catd',
                    'Sigma_catd_functord_catd'
                ]
            ]
        );
        assert.deepEqual(
            fixture.catalog.environment.declarations.map(declaration => [
                declaration.name,
                declaration.transparency,
                declaration.body
            ]),
            Object.values(CORE_DIRECTED_1A_PRIMITIVE_NAMES).map(name => [
                name,
                'opaque',
                undefined
            ])
        );
        assert.doesNotThrow(() =>
            fixture.catalog.createChecker().validateEnvironment()
        );
    });

    it('checks the first nested Cat-valued telescope end to end', () => {
        const fixture = directedFixture();
        const checker = fixture.catalog.createChecker(
            fixture.environment
        );
        const inferred = checker.infer(
            checker.rootContext,
            fixture.telescopeFamily
        );
        assert.equal(
            kernelExpressionEquals(
                inferred.type as KernelExpression,
                fixture.expectedFamilyType
            ),
            true
        );
        assert.doesNotThrow(() => checker.check(
            checker.rootContext,
            fixture.telescopeFamily,
            fixture.expectedFamilyType
        ));
    });

    it('lowers the same consumer through the approved scoped builder', () => {
        const fixture = directedFixture();
        const builder = new CoreLfScopedBuilder(
            because(20, 'DIRECTED-1A scoped surface')
        );
        const K = builder.embed(fixture.K);
        const R = builder.embed(fixture.R);
        const FF = builder.embed(fixture.FF);
        const built = fixture.catalog.builderApplication(
            builder,
            'sigma-telescope-family',
            [K, R, FF],
            because(21, 'DIRECTED-1A surface telescope')
        );
        assert.equal(
            kernelExpressionEquals(
                builder.lower(built),
                fixture.telescopeFamily
            ),
            true
        );
    });

    it('rejects a telescope from the wrong displayed family', () => {
        const fixture = directedFixture();
        let environment = fixture.environment.extend({
            name: 'directed_S',
            type: coreDisplayedFamilyType(
                fixture.K,
                because(30, 'DIRECTED-1A S type')
            ),
            mode: explicitFunctorial,
            provenance: because(30, 'DIRECTED-1A S')
        });
        const S = kernelFree('directed_S', because(31, 'DIRECTED-1A S use'));
        const constantCategoryFamily = coreConstantDisplayedFamily(
            fixture.K,
            categoryOfCategories(32),
            because(32, 'DIRECTED-1A wrong constant Cat family')
        );
        const wrongTelescopeCategory =
            fixture.catalog.displayedFunctorCategory(
                fixture.K,
                S,
                constantCategoryFamily,
                because(33, 'DIRECTED-1A wrong telescope category')
            );
        environment = environment.extend({
            name: 'directed_GG',
            type: objectType(wrongTelescopeCategory, 34),
            mode: explicitFunctorial,
            provenance: because(34, 'DIRECTED-1A GG')
        });
        const wrong = fixture.catalog.sigmaTelescopeFamily(
            fixture.K,
            fixture.R,
            kernelFree(
                'directed_GG',
                because(35, 'DIRECTED-1A wrong GG use')
            ),
            because(35, 'DIRECTED-1A wrong-family application')
        );
        const checker = fixture.catalog.createChecker(environment);
        assert.throws(
            () => checker.infer(checker.rootContext, wrong),
            error => error instanceof CoreCheckerError
        );
    });

    it('rejects a wrong base and preserves constant-family non-collapse', () => {
        const fixture = directedFixture();
        let environment = fixture.environment.extend({
            name: 'directed_L',
            type: categoryUniverse(40),
            mode: explicitFunctorial,
            provenance: because(40, 'DIRECTED-1A L')
        });
        const L = kernelFree('directed_L', because(41, 'DIRECTED-1A L use'));
        environment = environment.extend({
            name: 'directed_D',
            type: coreDisplayedFamilyType(
                L,
                because(42, 'DIRECTED-1A D type')
            ),
            mode: explicitFunctorial,
            provenance: because(42, 'DIRECTED-1A D')
        });
        const D = kernelFree('directed_D', because(43, 'DIRECTED-1A D use'));
        const wrongBaseType = coreDisplayedFamilyType(
            fixture.catalog.sigmaCategory(
                L,
                D,
                because(44, 'DIRECTED-1A wrong Sigma base')
            ),
            because(44, 'DIRECTED-1A wrong base expected type')
        );
        const checker = fixture.catalog.createChecker(environment);
        assert.throws(
            () => checker.check(
                checker.rootContext,
                fixture.telescopeFamily,
                wrongBaseType
            ),
            error => error instanceof CoreCheckerError
        );

        environment = environment.extend({
            name: 'directed_A',
            type: categoryUniverse(45),
            mode: explicitFunctorial,
            provenance: because(45, 'DIRECTED-1A A')
        });
        const constant = coreConstantDisplayedFamily(
            fixture.sigmaBase,
            kernelFree('directed_A', because(46, 'DIRECTED-1A A use')),
            because(46, 'DIRECTED-1A non-collapse constant')
        );
        const comparison = coreLfDefinitionalCompare(
            environment,
            fixture.telescopeFamily,
            constant,
            8
        );
        assert.equal(comparison.status, 'not-equal');
        assert.equal(comparison.steps, 0);
    });

    it('keeps the base catalog, MVP, browser, and rule boundary unchanged', () => {
        for (const owner of CORE_DIRECTED_1A_REVIEW.authorization.ownerIds) {
            assert.equal(owner in CORE_OWNER_SCHEMAS, false);
            assert.equal(owner in LAMBDAPI_V32_OWNER_BINDINGS, false);
            assert.equal(
                CORE_MVP_MANIFEST.owners.some(
                    entry => entry.owner === owner
                ),
                false
            );
        }
        assert.deepEqual(
            CORE_DIRECTED_1A_REVIEW.authorization.runtimeRuleIds,
            []
        );
        assert.deepEqual(
            CORE_DIRECTED_1A_REVIEW.authorization.proofTimeRuleIds,
            []
        );
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /directed_1a|CoreDirected1a|dttlf_/
        );
    });

    it('rejects malformed arity and a foreign LF environment', () => {
        const fixture = directedFixture();
        assert.throws(
            () => fixture.catalog.application(
                'sigma-category',
                [fixture.K],
                because(50, 'DIRECTED-1A malformed arity')
            ),
            error =>
                error instanceof CoreDirected1aCatalogError &&
                error.code === 'INVALID_CANDIDATE_ARITY'
        );
        assert.throws(
            () => fixture.catalog.createChecker(
                CoreLfDeclarationEnvironment.empty()
            ),
            error =>
                error instanceof CoreDirected1aCatalogError &&
                error.code === 'FOREIGN_CANDIDATE_ENVIRONMENT'
        );
    });

    it('serializes external primitives without shadow declarations', () => {
        const fixture = directedFixture();
        const serialized = serializeCoreLfKernelProbe({
            environment: fixture.environment,
            externalFreeReferences:
                fixture.catalog.externalFreeReferences,
            assertions: [{
                label: 'DIRECTED-1A nested telescope signature',
                term: fixture.telescopeFamily,
                type: fixture.expectedFamilyType,
                span: at(60, 1, 80)
            }]
        });
        assert.doesNotMatch(serialized.source, /symbol dttlf_/);
        assert.doesNotMatch(serialized.source, /dttlf_/);
        assert.match(serialized.source, /@Functord_cat/);
        assert.match(serialized.source, /@Sigma_cat /);
        assert.match(
            serialized.source,
            /@Sigma_catd_functord_catd/
        );
        assert.equal(
            serialized.sourceMap.filter(
                entry => entry.kind === 'declaration'
            ).length,
            3
        );
    });

    it(
        'has the generated nested telescope accepted by Lambdapi',
        { skip: process.env.EMDASH_RUN_LAMBDAPI_PROBES !== '1' },
        () => {
            const fixture = directedFixture();
            const serialized = serializeCoreLfKernelProbe({
                environment: fixture.environment,
                externalFreeReferences:
                    fixture.catalog.externalFreeReferences,
                assertions: [{
                    label: 'DIRECTED-1A nested telescope signature',
                    term: fixture.telescopeFamily,
                    type: fixture.expectedFamilyType,
                    span: at(70, 1, 80)
                }]
            });
            const result = checkLambdapiProbe(serialized, {
                packageRoot: resolve(__dirname, '../emdash2'),
                timeoutMs: 30_000
            });
            assert.equal(
                result.accepted,
                true,
                `Expected DIRECTED-1A acceptance:\n` +
                `${result.diagnostics}\n${serialized.source}`
            );
            assert.equal(result.timedOut, false);
        }
    );
});
