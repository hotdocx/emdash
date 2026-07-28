/**
 * Executable end-user demonstration of FIBRED-PRODUCT-1A.
 *
 * Surface strings below are explanatory labels. The actual input is the
 * direct typed TypeScript construction API, so no Lambdapi parser or
 * production Lambdapi runtime is involved.
 */

import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
} from './categorical_fibred_product_transfer';
import {
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation
} from './categorical_program';
import {
    CoreLfComparisonResult
} from './lf_conversion';

export const CORE_CATEGORICAL_FIBRED_PRODUCT_DEMO_REVISION =
    'FIBRED-PRODUCT-1A-DEMO-1' as const;

export interface CoreCategoricalFibredProductDemoExample {
    readonly id:
        | 'transparent-product-transport'
        | 'componentwise-product-map';
    readonly surface: string;
    readonly compilation: CoreCategoricalProgramCompilation;
}

export interface CoreCategoricalFibredProductDemoComparison {
    readonly id: 'pointwise-fibre' | 'shared-base-transport';
    readonly left: string;
    readonly right: string;
    readonly status: 'equal';
    readonly steps: number;
    readonly ruleIds: readonly string[];
}

export interface CoreCategoricalFibredProductDemo {
    readonly revision:
        typeof CORE_CATEGORICAL_FIBRED_PRODUCT_DEMO_REVISION;
    readonly candidate: 'emdash-v3.2-fibred-product-1a';
    readonly construction: 'direct-typescript-categorical-program';
    readonly assumptions: readonly string[];
    readonly familyPresentation:
        'uncurry(Product_cat_func) o Product_pair(B,C)';
    readonly examples:
        readonly CoreCategoricalFibredProductDemoExample[];
    readonly comparisons:
        readonly CoreCategoricalFibredProductDemoComparison[];
    readonly outputSummary: {
        readonly fibre: '(B x C)[x] computes to B[x] x C[x]';
        readonly transport:
            '(B x C)[p] computes to Product_map_func(B[p],C[p])';
        readonly sameBaseDiscriminator: true;
    };
    readonly productionLambdapiDependency: false;
    readonly boundary:
        typeof CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY;
}

const example = (
    id: CoreCategoricalFibredProductDemoExample['id'],
    surface: string,
    compilation: CoreCategoricalProgramCompilation
): CoreCategoricalFibredProductDemoExample => Object.freeze({
    id,
    surface,
    compilation
});

const comparison = (
    id: CoreCategoricalFibredProductDemoComparison['id'],
    left: string,
    right: string,
    result: CoreLfComparisonResult
): CoreCategoricalFibredProductDemoComparison => {
    if (result.status !== 'equal') {
        throw new Error(
            `Fibred-product demo comparison '${id}' did not close`
        );
    }
    return Object.freeze({
        id,
        left,
        right,
        status: 'equal' as const,
        steps: result.steps,
        ruleIds: Object.freeze(
            result.trace.map(entry =>
                entry.reduction.kind === 'runtime'
                    ? entry.reduction.ruleId
                    : entry.reduction.kind
            )
        )
    });
};

export function runCoreCategoricalFibredProductDemo():
CoreCategoricalFibredProductDemo {
    const emdash = new CoreCategoricalProgram({
        sourceFile: 'examples/v3_2_categorical_fibred_product_demo.ts',
        profile: 'fibred-product-1a'
    });
    const K = emdash.category('demo_K', { line: 45 });
    const B = emdash.displayedFamily('demo_B', K, { line: 46 });
    const C = emdash.displayedFamily('demo_C', K, { line: 47 });
    const product = emdash.displayedProduct(B, C, { line: 48 });
    const x = emdash.object('demo_x', K, { line: 49 });
    const y = emdash.object('demo_y', K, { line: 50 });
    const p = emdash.hom('demo_p', K, x, y, { line: 51 });

    const productFibre = emdash.fibre(product, x, { line: 53 });
    const expectedFibre = emdash.productCategory(
        emdash.fibre(B, x, { line: 54 }),
        emdash.fibre(C, x, { line: 55 }),
        { line: 56 }
    );
    const productTransport = emdash.familyTransport(
        product,
        p,
        { line: 58 }
    );
    const componentwiseTransport = emdash.productMap(
        emdash.familyTransport(B, p, { line: 59 }),
        emdash.familyTransport(C, p, { line: 60 }),
        { line: 61 }
    );

    const fibreComparison = comparison(
        'pointwise-fibre',
        '(demo_B x demo_C)[demo_x]',
        'demo_B[demo_x] x demo_C[demo_x]',
        emdash.compareCategories(
            productFibre,
            expectedFibre,
            2_000
        )
    );
    const transportComparison = comparison(
        'shared-base-transport',
        '(demo_B x demo_C)[demo_p]',
        'Product_map_func(demo_B[demo_p],demo_C[demo_p])',
        emdash.compare(
            productTransport,
            componentwiseTransport,
            2_000
        )
    );

    return Object.freeze({
        revision: CORE_CATEGORICAL_FIBRED_PRODUCT_DEMO_REVISION,
        candidate: 'emdash-v3.2-fibred-product-1a',
        construction: 'direct-typescript-categorical-program',
        assumptions: Object.freeze([
            'demo_K : Cat',
            'demo_B, demo_C : Catd demo_K',
            'demo_x, demo_y : Obj demo_K',
            'demo_p : Hom demo_K demo_x demo_y'
        ]),
        familyPresentation:
            'uncurry(Product_cat_func) o Product_pair(B,C)',
        examples: Object.freeze([
            example(
                'transparent-product-transport',
                '(demo_B x demo_C)[demo_p]',
                emdash.compile(productTransport)
            ),
            example(
                'componentwise-product-map',
                'Product_map_func(' +
                    'demo_B[demo_p],demo_C[demo_p])',
                emdash.compile(componentwiseTransport)
            )
        ]),
        comparisons: Object.freeze([
            fibreComparison,
            transportComparison
        ]),
        outputSummary: Object.freeze({
            fibre:
                '(B x C)[x] computes to B[x] x C[x]' as const,
            transport: (
                '(B x C)[p] computes to Product_map_func(B[p],C[p])'
            ) as const,
            sameBaseDiscriminator: true as const
        }),
        productionLambdapiDependency: false,
        boundary: CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY
    });
}

export function formatCoreCategoricalFibredProductDemo(): string {
    const demo = runCoreCategoricalFibredProductDemo();
    return [
        `${demo.candidate} (${demo.revision})`,
        `construction: ${demo.construction}`,
        `family: ${demo.familyPresentation}`,
        'inputs:',
        ...demo.assumptions.map(assumption => `  ${assumption}`),
        'programs:',
        ...demo.examples.map(item => [
            `  ${item.id}: ${item.surface}`,
            `    Core: ${item.compilation.explicitCore}`,
            `    type: ${item.compilation.explicitInferredType}`
        ].join('\n')),
        'computed outputs:',
        `  ${demo.outputSummary.fibre}`,
        `  ${demo.outputSummary.transport}`,
        ...demo.comparisons.map(item =>
            `  ${item.id}: ${item.status} in ${item.steps} steps ` +
            `[${item.ruleIds.join(', ')}]`
        ),
        'same literal base arrow required: true',
        'production Lambdapi dependency: false'
    ].join('\n');
}
