/**
 * Executable end-user demonstration of FIBRED-STRUCTURE-1A.
 *
 * The surface strings are explanatory notation. The actual input is the
 * direct typed TypeScript construction API; no string parser or production
 * Lambdapi runtime participates.
 */

import {
    CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY
} from './categorical_fibred_structure_transfer';
import {
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation
} from './categorical_program';
import {
    CoreLfComparisonResult
} from './lf_conversion';

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_DEMO_REVISION =
    'FIBRED-STRUCTURE-1A-DEMO-1' as const;

export interface CoreCategoricalFibredStructureDemoExample {
    readonly id:
        | 'left-projection-point'
        | 'displayed-pairing-point'
        | 'derived-swap-point'
        | 'derived-diagonal-point'
        | 'left-projection-full-action';
    readonly surface: string;
    readonly compilation: CoreCategoricalProgramCompilation;
}

export interface CoreCategoricalFibredStructureDemoComparison {
    readonly id:
        | 'left-projection-computes'
        | 'pairing-computes'
        | 'swap-computes'
        | 'diagonal-computes'
        | 'full-capped-coherence'
        | 'canonical-grouped-reindex';
    readonly status: 'equal';
    readonly steps: number;
    readonly ruleIds: readonly string[];
}

export interface CoreCategoricalFibredStructureDemo {
    readonly revision:
        typeof CORE_CATEGORICAL_FIBRED_STRUCTURE_DEMO_REVISION;
    readonly candidate: 'emdash-v3.2-fibred-structure-1a';
    readonly construction: 'direct-typescript-categorical-program';
    readonly assumptions: readonly string[];
    readonly inputPrograms: readonly string[];
    readonly examples:
        readonly CoreCategoricalFibredStructureDemoExample[];
    readonly comparisons:
        readonly CoreCategoricalFibredStructureDemoComparison[];
    readonly outputSummary: {
        readonly projection:
            'projL_d(B,C)[x] computes to projL(B[x],C[x])';
        readonly pairing:
            'pair_d(FF,GG)[x] computes to pair(FF[x],GG[x])';
        readonly swap:
            'swap_d(B,C)[x] computes to pair(projR,projL)';
        readonly diagonal:
            'diag_d(B)[x] computes to pair(id,id)';
        readonly canonicalReindex:
            'reindex(P(B,C),F) emits P(reindex(B,F),reindex(C,F))';
        readonly rawKernelReindexStillNonConvertible: true;
    };
    readonly productionLambdapiDependency: false;
    readonly boundary:
        typeof CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY;
}

const runtimeRuleIds = (
    result: CoreLfComparisonResult
): readonly string[] => Object.freeze(
    result.trace.flatMap(entry =>
        entry.reduction.kind === 'runtime'
            ? [entry.reduction.ruleId]
            : []
    )
);

const comparison = (
    id: CoreCategoricalFibredStructureDemoComparison['id'],
    result: CoreLfComparisonResult
): CoreCategoricalFibredStructureDemoComparison => {
    if (result.status !== 'equal') {
        throw new Error(
            `Fibred-structure demo comparison '${id}' did not close`
        );
    }
    return Object.freeze({
        id,
        status: 'equal' as const,
        steps: result.steps,
        ruleIds: runtimeRuleIds(result)
    });
};

export function runCoreCategoricalFibredStructureDemo():
CoreCategoricalFibredStructureDemo {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'examples/v3_2_categorical_fibred_structure_demo.ts',
        profile: 'fibred-structure-1a'
    });
    const K = emdash.category('demo_K', { line: 52 });
    const E = emdash.displayedFamily('demo_E', K, { line: 53 });
    const B = emdash.displayedFamily('demo_B', K, { line: 54 });
    const C = emdash.displayedFamily('demo_C', K, { line: 55 });
    const FF = emdash.displayedFunctor(
        'demo_FF',
        E,
        B,
        { line: 56 }
    );
    const GG = emdash.displayedFunctor(
        'demo_GG',
        E,
        C,
        { line: 57 }
    );
    const x = emdash.object('demo_x', K, { line: 58 });
    const y = emdash.object('demo_y', K, { line: 59 });
    const p = emdash.hom('demo_p', K, x, y, { line: 60 });
    const Bx = emdash.fibre(B, x, { line: 61 });
    const Cx = emdash.fibre(C, x, { line: 62 });

    const leftProjection = emdash.displayedProductLeftProjection(
        B,
        C,
        { line: 65 }
    );
    const leftPoint = emdash.apply(leftProjection, x, {
        expectedShape: 'fibre-functor',
        source: { line: 66 }
    });
    const expectedLeft = emdash.productLeftProjection(
        Bx,
        Cx,
        { line: 67 }
    );

    const displayedPair = emdash.displayedProductPair(
        FF,
        GG,
        { line: 69 }
    );
    const pairPoint = emdash.apply(displayedPair, x, {
        expectedShape: 'fibre-functor',
        source: { line: 70 }
    });
    const expectedPair = emdash.functorPair(
        emdash.apply(FF, x, {
            expectedShape: 'fibre-functor',
            source: { line: 71 }
        }),
        emdash.apply(GG, x, {
            expectedShape: 'fibre-functor',
            source: { line: 72 }
        }),
        { line: 73 }
    );

    const swapPoint = emdash.apply(
        emdash.displayedProductSwap(B, C, { line: 75 }),
        x,
        {
            expectedShape: 'fibre-functor',
            source: { line: 76 }
        }
    );
    const expectedSwap = emdash.functorPair(
        emdash.productRightProjection(Bx, Cx, { line: 77 }),
        emdash.productLeftProjection(Bx, Cx, { line: 78 }),
        { line: 79 }
    );

    const diagonalPoint = emdash.apply(
        emdash.displayedProductDiagonal(B, { line: 81 }),
        x,
        {
            expectedShape: 'fibre-functor',
            source: { line: 82 }
        }
    );
    const identity = emdash.identityFunctor(Bx, { line: 83 });
    const expectedDiagonal = emdash.functorPair(
        identity,
        identity,
        { line: 84 }
    );

    const fullAction = emdash.displayedFunctorFullAction(
        leftProjection,
        x,
        y,
        { line: 86 }
    );
    const fullAtP = emdash.apply(
        fullAction,
        p,
        { source: { line: 87 } }
    );
    const cappedAction = emdash.apply(leftProjection, p, {
        expectedShape: 'transport-functor',
        source: { line: 88 }
    });

    const A = emdash.category('demo_A', { line: 90 });
    const F = emdash.functor('demo_F', A, K, { line: 91 });
    const grouped = emdash.displayedProduct(B, C, { line: 92 });
    const emittedReindex = emdash.pullbackFamily(
        grouped,
        F,
        { line: 93 }
    );
    const canonicalReindex = emdash.displayedProduct(
        emdash.pullbackFamily(B, F, { line: 94 }),
        emdash.pullbackFamily(C, F, { line: 95 }),
        { line: 96 }
    );

    const raw = new CoreCategoricalProgram({
        sourceFile:
            'examples/v3_2_categorical_fibred_structure_demo_raw.ts',
        profile: 'fibred-product-1a'
    });
    const rawK = raw.category('raw_K');
    const rawA = raw.category('raw_A');
    const rawB = raw.displayedFamily('raw_B', rawK);
    const rawC = raw.displayedFamily('raw_C', rawK);
    const rawF = raw.functor('raw_F', rawA, rawK);
    const rawReindex = raw.pullbackFamily(
        raw.displayedProduct(rawB, rawC),
        rawF
    );
    const rawCanonical = raw.displayedProduct(
        raw.pullbackFamily(rawB, rawF),
        raw.pullbackFamily(rawC, rawF)
    );
    if (
        raw.compareDisplayedFamilies(
            rawReindex,
            rawCanonical,
            4_000
        ).status !== 'not-equal'
    ) {
        throw new Error(
            'Raw kernel reindex presentation unexpectedly converted'
        );
    }

    return Object.freeze({
        revision: CORE_CATEGORICAL_FIBRED_STRUCTURE_DEMO_REVISION,
        candidate: 'emdash-v3.2-fibred-structure-1a',
        construction: 'direct-typescript-categorical-program',
        assumptions: Object.freeze([
            'demo_K : Cat',
            'demo_E, demo_B, demo_C : Catd demo_K',
            'demo_FF : Functord(demo_E,demo_B)',
            'demo_GG : Functord(demo_E,demo_C)',
            'demo_x, demo_y : Obj demo_K',
            'demo_p : Hom demo_K demo_x demo_y',
            'demo_F : Functor demo_A demo_K'
        ]),
        inputPrograms: Object.freeze([
            'projL_d(demo_B,demo_C)[demo_x]',
            'pair_d(demo_FF,demo_GG)[demo_x]',
            'swap_d(demo_B,demo_C)[demo_x]',
            'diag_d(demo_B)[demo_x]',
            'tapp1_func(projL_d(demo_B,demo_C),demo_x,demo_y)',
            'reindex(P(demo_B,demo_C),demo_F)'
        ]),
        examples: Object.freeze([
            Object.freeze({
                id: 'left-projection-point' as const,
                surface:
                    'projL_d(demo_B,demo_C)[demo_x]',
                compilation: emdash.compile(leftPoint)
            }),
            Object.freeze({
                id: 'displayed-pairing-point' as const,
                surface:
                    'pair_d(demo_FF,demo_GG)[demo_x]',
                compilation: emdash.compile(pairPoint)
            }),
            Object.freeze({
                id: 'derived-swap-point' as const,
                surface:
                    'swap_d(demo_B,demo_C)[demo_x]',
                compilation: emdash.compile(swapPoint)
            }),
            Object.freeze({
                id: 'derived-diagonal-point' as const,
                surface: 'diag_d(demo_B)[demo_x]',
                compilation: emdash.compile(diagonalPoint)
            }),
            Object.freeze({
                id: 'left-projection-full-action' as const,
                surface:
                    'tapp1_func(projL_d(demo_B,demo_C),' +
                    'demo_x,demo_y)',
                compilation: emdash.compile(fullAction)
            })
        ]),
        comparisons: Object.freeze([
            comparison(
                'left-projection-computes',
                emdash.compare(leftPoint, expectedLeft, 4_000)
            ),
            comparison(
                'pairing-computes',
                emdash.compare(pairPoint, expectedPair, 4_000)
            ),
            comparison(
                'swap-computes',
                emdash.compare(swapPoint, expectedSwap, 4_000)
            ),
            comparison(
                'diagonal-computes',
                emdash.compare(
                    diagonalPoint,
                    expectedDiagonal,
                    4_000
                )
            ),
            comparison(
                'full-capped-coherence',
                emdash.compare(cappedAction, fullAtP, 4_000)
            ),
            comparison(
                'canonical-grouped-reindex',
                emdash.compareDisplayedFamilies(
                    emittedReindex,
                    canonicalReindex,
                    4_000
                )
            )
        ]),
        outputSummary: Object.freeze({
            projection:
                'projL_d(B,C)[x] computes to projL(B[x],C[x])' as const,
            pairing:
                'pair_d(FF,GG)[x] computes to pair(FF[x],GG[x])' as const,
            swap:
                'swap_d(B,C)[x] computes to pair(projR,projL)' as const,
            diagonal:
                'diag_d(B)[x] computes to pair(id,id)' as const,
            canonicalReindex:
                'reindex(P(B,C),F) emits P(reindex(B,F),reindex(C,F))',
            rawKernelReindexStillNonConvertible: true as const
        }),
        productionLambdapiDependency: false,
        boundary:
            CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY
    });
}

export function formatCoreCategoricalFibredStructureDemo(): string {
    const demo = runCoreCategoricalFibredStructureDemo();
    return [
        `${demo.candidate} (${demo.revision})`,
        `construction: ${demo.construction}`,
        'inputs:',
        ...demo.assumptions.map(assumption => `  ${assumption}`),
        'programs:',
        ...demo.examples.map(item => [
            `  ${item.id}: ${item.surface}`,
            `    Core: ${item.compilation.explicitCore}`,
            `    type: ${item.compilation.explicitInferredType}`
        ].join('\n')),
        'computed outputs:',
        `  ${demo.outputSummary.projection}`,
        `  ${demo.outputSummary.pairing}`,
        `  ${demo.outputSummary.swap}`,
        `  ${demo.outputSummary.diagonal}`,
        `  ${demo.outputSummary.canonicalReindex}`,
        ...demo.comparisons.map(item =>
            `  ${item.id}: ${item.status} in ${item.steps} steps ` +
            `[${item.ruleIds.join(', ')}]`
        ),
        'raw kernel pullback/product conversion: false',
        'production Lambdapi dependency: false'
    ].join('\n');
}
