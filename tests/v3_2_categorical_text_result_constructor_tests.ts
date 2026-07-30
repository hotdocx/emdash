/**
 * Focused SYNTAX-PARITY-1C3 result-constructor implementation tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CoreCategoricalCategory,
    CoreCategoricalDisplayedFamily,
    CoreCategoricalProgram,
    CoreCategoricalTerm,
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    elaborateCoreCategoricalText
} from '../src/v3_2';

const sourceFile =
    'tests/fixtures/categorical-text-result-constructors.emdash';

const baseFixture = () => {
    const program = new CoreCategoricalProgram({ sourceFile });
    const K = program.category('result_text_K');
    const A = program.category('result_text_A');
    const C = program.category('result_text_C');
    const B = program.displayedFamily('result_text_B', K);
    const k = program.object('result_text_k', K);
    const a = program.object('result_text_a', A);
    const environment: readonly CoreCategoricalTextBinding[] =
        Object.freeze([
            { name: 'K', kind: 'category', value: K },
            { name: 'A', kind: 'category', value: A },
            { name: 'C', kind: 'category', value: C },
            { name: 'B', kind: 'displayed-family', value: B },
            { name: 'k', kind: 'term', value: k },
            { name: 'a', kind: 'term', value: a }
        ]);
    return {
        program,
        K,
        A,
        C,
        B,
        k,
        a,
        environment
    };
};

const data = baseFixture();

const routedCategory = (
    label: string
): CoreCategoricalCategory => Object.freeze({
    routeKind: 'category',
    label
}) as unknown as CoreCategoricalCategory;

const routedFamily = (
    label: string
): CoreCategoricalDisplayedFamily => Object.freeze({
    routeKind: 'displayed-family',
    label
}) as unknown as CoreCategoricalDisplayedFamily;

const routedTerm = (
    label: string
): CoreCategoricalTerm => Object.freeze({
    routeKind: 'term',
    label
}) as unknown as CoreCategoricalTerm;

const routeValues = Object.freeze({
    K: routedCategory('K'),
    A: routedCategory('A'),
    C: routedCategory('C'),
    B: routedFamily('B'),
    D: routedFamily('D'),
    F: routedTerm('F'),
    G: routedTerm('G'),
    k: routedTerm('k'),
    M: routedTerm('M'),
    FF: routedTerm('FF'),
    GG: routedTerm('GG')
});

const routeResults = Object.freeze({
    constantDisplayedFamily: routedFamily('constantd-result'),
    displayedFunctorFamily: routedFamily('functord-result'),
    dependentSectionMotive: routedFamily('section-motive-result'),
    dependentSectionTarget: routedFamily('section-target-result'),
    dependentSectionCategoryAt: routedCategory('section-category-result'),
    displayedProduct: routedFamily('productd-result'),
    fibre: routedCategory('fibre-result'),
    totalCategory: routedCategory('sigma-result'),
    displayedTransforCategory: routedCategory('transfd-result'),
    functorCategory: routedCategory('functor-result'),
    productCategory: routedCategory('product-result'),
    pullbackFamily: routedFamily('pullback-result'),
    identityFunctor: routedTerm('identity-result')
});

interface RouteCall {
    readonly method: keyof typeof routeResults;
    readonly arguments: readonly unknown[];
}

const routeCalls: RouteCall[] = [];

const recordRoute = <Method extends keyof typeof routeResults>(
    method: Method,
    arguments_: readonly unknown[]
): (typeof routeResults)[Method] => {
    routeCalls.push(Object.freeze({
        method,
        arguments: Object.freeze([...arguments_])
    }));
    return routeResults[method];
};

const routingProgram = {
    inspect: (value: CoreCategoricalTerm): unknown => value,
    serializeCategory: (value: CoreCategoricalCategory): string =>
        value.label,
    compareDisplayedFamilies: (
        left: CoreCategoricalDisplayedFamily,
        right: CoreCategoricalDisplayedFamily
    ) => Object.freeze({
        status: left === right ? 'equal' as const : 'distinct' as const
    }),
    constantDisplayedFamily: (...arguments_: readonly unknown[]) =>
        recordRoute('constantDisplayedFamily', arguments_),
    displayedFunctorFamily: (...arguments_: readonly unknown[]) =>
        recordRoute('displayedFunctorFamily', arguments_),
    dependentSectionMotive: (...arguments_: readonly unknown[]) =>
        recordRoute('dependentSectionMotive', arguments_),
    dependentSectionTarget: (...arguments_: readonly unknown[]) =>
        recordRoute('dependentSectionTarget', arguments_),
    dependentSectionCategoryAt: (...arguments_: readonly unknown[]) =>
        recordRoute('dependentSectionCategoryAt', arguments_),
    displayedProduct: (...arguments_: readonly unknown[]) =>
        recordRoute('displayedProduct', arguments_),
    fibre: (...arguments_: readonly unknown[]) =>
        recordRoute('fibre', arguments_),
    totalCategory: (...arguments_: readonly unknown[]) =>
        recordRoute('totalCategory', arguments_),
    displayedTransforCategory: (...arguments_: readonly unknown[]) =>
        recordRoute('displayedTransforCategory', arguments_),
    functorCategory: (...arguments_: readonly unknown[]) =>
        recordRoute('functorCategory', arguments_),
    productCategory: (...arguments_: readonly unknown[]) =>
        recordRoute('productCategory', arguments_),
    pullbackFamily: (...arguments_: readonly unknown[]) =>
        recordRoute('pullbackFamily', arguments_),
    identityFunctor: (...arguments_: readonly unknown[]) =>
        recordRoute('identityFunctor', arguments_)
} as unknown as CoreCategoricalProgram;

const routingEnvironment: readonly CoreCategoricalTextBinding[] =
    Object.freeze([
        { name: 'K', kind: 'category', value: routeValues.K },
        { name: 'A', kind: 'category', value: routeValues.A },
        { name: 'C', kind: 'category', value: routeValues.C },
        { name: 'B', kind: 'displayed-family', value: routeValues.B },
        { name: 'D', kind: 'displayed-family', value: routeValues.D },
        { name: 'F', kind: 'term', value: routeValues.F },
        { name: 'G', kind: 'term', value: routeValues.G },
        { name: 'k', kind: 'term', value: routeValues.k },
        { name: 'M', kind: 'term', value: routeValues.M },
        { name: 'FF', kind: 'term', value: routeValues.FF },
        { name: 'GG', kind: 'term', value: routeValues.GG }
    ]);

const route = (
    source: string,
    expected: 'category' | 'displayed-family'
): CoreCategoricalCategory | CoreCategoricalDisplayedFamily =>
    expected === 'category'
        ? elaborateCoreCategoricalText(routingProgram, {
            source,
            sourceFile,
            environment: routingEnvironment,
            expected: { kind: 'category' }
        })
        : elaborateCoreCategoricalText(routingProgram, {
            source,
            sourceFile,
            environment: routingEnvironment,
            expected: { kind: 'displayed-family' }
        });

const assertTextError = (
    action: () => unknown,
    code: CoreCategoricalTextError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreCategoricalTextError &&
            error.code === code
    );
};

describe('SYNTAX-PARITY-1C3 result constructors', () => {
    it('routes all twelve exact heads to existing typed methods', () => {
        const cases = [
            {
                source: 'constantd K A',
                expected: 'displayed-family',
                method: 'constantDisplayedFamily'
            },
            {
                source: 'functord A B',
                expected: 'displayed-family',
                method: 'displayedFunctorFamily'
            },
            {
                source: 'sectionMotive G',
                expected: 'displayed-family',
                method: 'dependentSectionMotive'
            },
            {
                source: 'sectionTarget G',
                expected: 'displayed-family',
                method: 'dependentSectionTarget'
            },
            {
                source: 'sectionCategory G k M',
                expected: 'category',
                method: 'dependentSectionCategoryAt'
            },
            {
                source: 'productd B D',
                expected: 'displayed-family',
                method: 'displayedProduct'
            },
            {
                source: 'fibre B k',
                expected: 'category',
                method: 'fibre'
            },
            {
                source: 'sigma B',
                expected: 'category',
                method: 'totalCategory'
            },
            {
                source: 'transfd FF GG',
                expected: 'category',
                method: 'displayedTransforCategory'
            },
            {
                source: 'functor A C',
                expected: 'category',
                method: 'functorCategory'
            },
            {
                source: 'product A C',
                expected: 'category',
                method: 'productCategory'
            },
            {
                source: 'pullback B F',
                expected: 'displayed-family',
                method: 'pullbackFamily'
            }
        ] as const;

        cases.forEach(testCase => {
            routeCalls.length = 0;
            const result = route(testCase.source, testCase.expected);
            assert.equal(routeCalls.at(-1)?.method, testCase.method);
            assert.equal(
                result,
                routeResults[testCase.method]
            );
        });
    });

    it('recurses through category/family operands and existing term heads',
        () => {
            routeCalls.length = 0;
            const family = route(
                'productd (pullback B F) (pullback D F)',
                'displayed-family'
            );
            assert.equal(family, routeResults.displayedProduct);
            assert.deepEqual(
                routeCalls.map(call => call.method),
                [
                    'pullbackFamily',
                    'pullbackFamily',
                    'displayedProduct'
                ]
            );

            routeCalls.length = 0;
            const term = elaborateCoreCategoricalText(
                routingProgram,
                {
                    source: 'id (fibre (productd B D) k)',
                    sourceFile,
                    environment: routingEnvironment,
                    expected: { kind: 'term' }
                }
            );
            assert.equal(term, routeResults.identityFunctor);
            assert.deepEqual(
                routeCalls.map(call => call.method),
                ['displayedProduct', 'fibre', 'identityFunctor']
            );
        });

    it('agrees with the real program for root and nested results', () => {
        const category = elaborateCoreCategoricalText(
            data.program,
            {
                source: 'functor A (fibre B k)',
                sourceFile,
                environment: data.environment,
                expected: { kind: 'category' }
            }
        );
        const directCategory = data.program.functorCategory(
            data.A,
            data.program.fibre(data.B, data.k)
        );
        assert.equal(
            data.program.compareCategories(
                category,
                directCategory
            ).status,
            'equal'
        );

        const term = elaborateCoreCategoricalText(
            data.program,
            {
                source: 'id (fibre B k)',
                sourceFile,
                environment: data.environment,
                expected: { kind: 'term' }
            }
        );
        assert.equal(
            data.program.compare(
                term,
                data.program.identityFunctor(
                    data.program.fibre(data.B, data.k)
                )
            ).status,
            'equal'
        );

        assert.equal(
            elaborateCoreCategoricalText(data.program, {
                source: 'B',
                sourceFile,
                environment: data.environment,
                expected: { kind: 'displayed-family' }
            }),
            data.B
        );
    });

    it('fails closed on result kind, arity, foreign values, and profiles',
        () => {
            assertTextError(
                () => elaborateCoreCategoricalText(data.program, {
                    source: 'B',
                    sourceFile,
                    environment: data.environment,
                    expected: { kind: 'category' }
                }),
                'EXPECTED_CATEGORY'
            );
            assertTextError(
                () => elaborateCoreCategoricalText(data.program, {
                    source: 'A',
                    sourceFile,
                    environment: data.environment,
                    expected: { kind: 'displayed-family' }
                }),
                'EXPECTED_DISPLAYED_FAMILY'
            );
            assertTextError(
                () => elaborateCoreCategoricalText(data.program, {
                    source: 'fibre B',
                    sourceFile,
                    environment: data.environment,
                    expected: { kind: 'category' }
                }),
                'EXPECTED_CATEGORY'
            );
            assertTextError(
                () => elaborateCoreCategoricalText(data.program, {
                    source: 'fibre B a',
                    sourceFile,
                    environment: data.environment,
                    expected: { kind: 'category' }
                }),
                'CATEGORICAL_REJECTION'
            );
            assertTextError(
                () => elaborateCoreCategoricalText(data.program, {
                    source: 'sigma B',
                    sourceFile,
                    environment: data.environment,
                    expected: { kind: 'category' }
                }),
                'CATEGORICAL_REJECTION'
            );

            const foreignProgram = new CoreCategoricalProgram();
            const foreign = foreignProgram.category(
                'foreign_result_category'
            );
            const foreignFamily = foreignProgram.displayedFamily(
                'foreign_result_family',
                foreign
            );
            assertTextError(
                () => elaborateCoreCategoricalText(data.program, {
                    source: 'Foreign',
                    sourceFile,
                    environment: [{
                        name: 'Foreign',
                        kind: 'category',
                        value: foreign
                    }],
                    expected: { kind: 'category' }
                }),
                'CATEGORICAL_REJECTION'
            );
            assertTextError(
                () => elaborateCoreCategoricalText(data.program, {
                    source: 'ForeignFamily',
                    sourceFile,
                    environment: [{
                        name: 'ForeignFamily',
                        kind: 'displayed-family',
                        value: foreignFamily
                    }],
                    expected: { kind: 'displayed-family' }
                }),
                'CATEGORICAL_REJECTION'
            );
        });
});
