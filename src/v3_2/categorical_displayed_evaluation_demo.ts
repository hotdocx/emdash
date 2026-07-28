/**
 * Executable DISPLAYED-EVAL-1A end-user demonstration.
 *
 * The notation is explanatory. The executable input is the typed TypeScript
 * construction API, and the result is checked backend-neutral Core.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
} from './categorical_displayed_evaluation_transfer';
import {
    CoreCategoricalDiagnostic,
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation,
    coreCategoricalDiagnosticFromError
} from './categorical_program';
import {
    CoreLfComparisonResult
} from './lf_conversion';

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_DEMO_REVISION =
    'DISPLAYED-EVAL-1A-DEMO-1' as const;

const stableFibreSynopsis =
    'Functor_catd(Const_(Op K)(A),B)[k] = Functor_cat(A,B[k])' as const;

const rejectedInputSynopsis =
    'displayedContextLambda([{F:S}], B, ([F]) => apply(F,c:C))' as const;

export interface CoreCategoricalDisplayedEvaluationDemoExample {
    readonly id: 'varying' | 'recursive' | 'fixed';
    readonly surface: string;
    readonly typescriptInput: string;
    readonly irSummary: string;
    readonly coreSummary: string;
    readonly compilation: CoreCategoricalProgramCompilation;
}

export interface CoreCategoricalDisplayedEvaluationDemoResult {
    readonly revision:
        typeof CORE_CATEGORICAL_DISPLAYED_EVALUATION_DEMO_REVISION;
    readonly candidate: 'emdash-v3.2-displayed-evaluation-1a';
    readonly construction: 'direct-typescript-categorical-program';
    readonly pipeline: readonly [
        'typed TypeScript construction IR',
        'recursive typed-application tree',
        'displayed contextual compiler',
        'backend-neutral explicit Core',
        'generic checker/evaluator'
    ];
    readonly assumptions: readonly string[];
    readonly examples:
        readonly CoreCategoricalDisplayedEvaluationDemoExample[];
    readonly computation: {
        readonly stableFibre:
            'Functor_catd(Const_(Op K)(A),B)[k] = Functor_cat(A,B[k])';
        readonly stableFibreStatus: 'equal';
        readonly pointOutputKind: 'functor';
        readonly arrowStatus: 'equal';
        readonly reindexedOutputKind: 'displayed-functor';
        readonly higherActionOutputKind: 'functor';
        readonly runtimeRuleIds: readonly string[];
    };
    readonly rejectedInput:
        'displayedContextLambda([{F:S}], B, ([F]) => apply(F,c:C))';
    readonly negativeDiagnostic: CoreCategoricalDiagnostic;
    readonly newLambdapiMathematicalOwnerCount: 2;
    readonly newLambdapiRuntimeRuleCount: 2;
    readonly intrinsicCoreOwnerCount: 0;
    readonly stringParserDependency: false;
    readonly productionLambdapiDependency: false;
    readonly arbitraryMixedDomainEvaluationDeferred: true;
    readonly genuineDependentChainsDeferred: true;
}

const runtimeRuleIds = (
    ...results: readonly CoreLfComparisonResult[]
): readonly string[] => Object.freeze(
    [...new Set(results.flatMap(result =>
        result.trace.flatMap(entry =>
            entry.reduction.kind === 'runtime'
                ? [entry.reduction.ruleId]
                : []
        )
    ))]
);

export function runCoreCategoricalDisplayedEvaluationDemo():
CoreCategoricalDisplayedEvaluationDemoResult {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'examples/v3_2_categorical_displayed_evaluation_demo.ts',
        profile: 'fibred-displayed-evaluation-1'
    });
    const K = emdash.category('demo_K', { line: 1 });
    const A = emdash.category('demo_A', { line: 2 });
    const B = emdash.displayedFamily('demo_B', K, { line: 3 });
    const E = emdash.displayedFamily('demo_E', K, { line: 4 });
    const D = emdash.displayedFamily('demo_D', K, { line: 5 });
    const stable = emdash.displayedFunctorFamily(
        A,
        B,
        { line: 6 }
    );
    const constant = emdash.constantDisplayedFamily(
        K,
        A,
        { line: 7 }
    );
    const H = emdash.displayedFunctor(
        'demo_H',
        E,
        stable,
        { line: 8 }
    );
    const G = emdash.displayedFunctor(
        'demo_G',
        D,
        constant,
        { line: 9 }
    );

    const varying = emdash.displayedContextLambda(
        [
            { name: 'F', family: stable },
            { name: 'x', family: constant }
        ],
        B,
        ([F, x]) => emdash.apply(F, x),
        { source: { line: 12 } }
    );
    const recursive = emdash.displayedContextLambda(
        [
            { name: 'e', family: E },
            { name: 'd', family: D }
        ],
        B,
        ([e, d]) => emdash.apply(
            emdash.apply(H, e),
            emdash.apply(G, d)
        ),
        { source: { line: 20 } }
    );
    const a = emdash.object('demo_a', A, { line: 27 });
    const fixed = emdash.displayedContextLambda(
        [{ name: 'F', family: stable }],
        B,
        ([F]) => emdash.apply(F, a),
        { source: { line: 28 } }
    );

    const k = emdash.object('demo_k', K, { line: 32 });
    const l = emdash.object('demo_l', K, { line: 33 });
    const p = emdash.hom('demo_p', K, k, l, { line: 34 });
    const stableFibre = emdash.compareCategories(
        emdash.fibre(stable, k),
        emdash.functorCategory(A, emdash.fibre(B, k)),
        4_000
    );
    const point = emdash.compile(
        emdash.apply(varying, k, {
            expectedShape: 'fibre-functor'
        })
    );
    const capped = emdash.apply(varying, p, {
        expectedShape: 'transport-functor'
    });
    const higherAction = emdash.displayedFunctorFullAction(
        varying,
        k,
        l
    );
    const fullAtP = emdash.apply(higherAction, p);
    const arrow = emdash.compare(capped, fullAtP, 20_000);
    const L = emdash.category('demo_L', { line: 38 });
    const u = emdash.functor('demo_u', L, K, { line: 39 });
    const reindexed = emdash.compile(
        emdash.pullbackDisplayedFunctor(varying, u)
    );
    const higherActionCompilation = emdash.compile(higherAction);
    if (
        stableFibre.status !== 'equal' ||
        point.surfaceType.tag !== 'functor' ||
        arrow.status !== 'equal' ||
        reindexed.surfaceType.tag !== 'displayed-functor' ||
        higherActionCompilation.surfaceType.tag !== 'functor'
    ) {
        throw new Error(
            'DISPLAYED-EVAL-1A object/arrow/reindexing action drifted'
        );
    }

    let negativeDiagnostic: CoreCategoricalDiagnostic | undefined;
    try {
        const C = emdash.category('demo_C', { line: 45 });
        const c = emdash.object('demo_c', C, { line: 46 });
        emdash.displayedContextLambda(
            [{ name: 'F', family: stable }],
            B,
            ([F]) => emdash.apply(F, c),
            {
                source: {
                    line: 47,
                    detail: 'wrong fixed evaluation domain'
                }
            }
        );
    } catch (error: unknown) {
        negativeDiagnostic =
            coreCategoricalDiagnosticFromError(error);
        if (negativeDiagnostic === undefined) throw error;
    }
    if (negativeDiagnostic === undefined) {
        throw new Error(
            'DISPLAYED-EVAL-1A accepted a wrong fixed argument'
        );
    }

    return Object.freeze({
        revision:
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_DEMO_REVISION,
        candidate: 'emdash-v3.2-displayed-evaluation-1a',
        construction: 'direct-typescript-categorical-program',
        pipeline: Object.freeze([
            'typed TypeScript construction IR',
            'recursive typed-application tree',
            'displayed contextual compiler',
            'backend-neutral explicit Core',
            'generic checker/evaluator'
        ] as const),
        assumptions: Object.freeze([
            'demo_K demo_A : Cat',
            'demo_B demo_E demo_D : Catd demo_K',
            'S = Functor_catd(Const_catd(Op demo_K,demo_A),demo_B)',
            'X = Const_catd(demo_K,demo_A)',
            'demo_H : Functord(demo_E,S)',
            'demo_G : Functord(demo_D,X)'
        ]),
        examples: Object.freeze([
            Object.freeze({
                id: 'varying' as const,
                surface:
                    'λ (F : S, x : X) :^fd. F x',
                typescriptInput:
                    'displayedContextLambda([{F:S},{x:X}], B, ' +
                    '([F,x]) => apply(F,x))',
                irSummary:
                    'displayed-evaluation.varying-argument(slot F,slot x)',
                coreSummary:
                    'Eval_funcd ∘ Product_pair_funcd(projF,projx)',
                compilation: emdash.compile(varying)
            }),
            Object.freeze({
                id: 'recursive' as const,
                surface:
                    'λ (e : E, d : D) :^fd. demo_H[e](demo_G[d])',
                typescriptInput:
                    'displayedContextLambda([{e:E},{d:D}], B, ' +
                    '([e,d]) => apply(apply(H,e),apply(G,d)))',
                irSummary:
                    'displayed evaluation over two recursively compiled ' +
                    'indexed applications',
                coreSummary:
                    'Eval_funcd ∘ Product_pair_funcd(H∘projE,G∘projD)',
                compilation: emdash.compile(recursive)
            }),
            Object.freeze({
                id: 'fixed' as const,
                surface:
                    'λ F :^fd S. F demo_a',
                typescriptInput:
                    'displayedContextLambda([{F:S}], B, ' +
                    '([F]) => apply(F,a))',
                irSummary:
                    'displayed-evaluation.fixed-argument(slot F,demo_a)',
                coreSummary:
                    'Eval_funcd ∘ pair(id,' +
                    'const_section_func(demo_a)∘Terminal_funcd)',
                compilation: emdash.compile(fixed)
            })
        ]),
        computation: Object.freeze({
            stableFibre: stableFibreSynopsis,
            stableFibreStatus: 'equal' as const,
            pointOutputKind: 'functor' as const,
            arrowStatus: 'equal' as const,
            reindexedOutputKind: 'displayed-functor' as const,
            higherActionOutputKind: 'functor' as const,
            runtimeRuleIds: runtimeRuleIds(stableFibre, arrow)
        }),
        rejectedInput: rejectedInputSynopsis,
        negativeDiagnostic,
        newLambdapiMathematicalOwnerCount:
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .newMathematicalOwnerCount as 2,
        newLambdapiRuntimeRuleCount:
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .newMathematicalRuntimeRuleCount as 2,
        intrinsicCoreOwnerCount:
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY
                .newIntrinsicCoreOwnerCount as 0,
        stringParserDependency: false as const,
        productionLambdapiDependency: false as const,
        arbitraryMixedDomainEvaluationDeferred: true as const,
        genuineDependentChainsDeferred: true as const
    });
}

export function formatCoreCategoricalDisplayedEvaluationDemo(
    result: CoreCategoricalDisplayedEvaluationDemoResult =
        runCoreCategoricalDisplayedEvaluationDemo()
): string {
    const assumptions = result.assumptions.map(
        assumption => `  - ${assumption}`
    ).join('\n');
    const pipeline = result.pipeline.map(
        (stage, index) => `  ${index + 1}. ${stage}`
    ).join('\n');
    const examples = result.examples.map(example => [
        `  ${example.id}: ${example.surface}`,
        `    TypeScript: ${example.typescriptInput}`,
        `    IR: ${example.irSummary}`,
        `    Core: ${example.coreSummary}`
    ].join('\n')).join('\n');
    return [
        result.candidate,
        `Input path: ${result.construction}`,
        '',
        'Assumptions:',
        assumptions,
        '',
        'Pipeline:',
        pipeline,
        '',
        'Displayed evaluation inputs:',
        examples,
        '',
        'Checked computation:',
        `  Fibre: ${result.computation.stableFibre}`,
        `  Point output: ${result.computation.pointOutputKind}`,
        `  Arrow action: ${result.computation.arrowStatus}`,
        `  Reindexed output: ${result.computation.reindexedOutputKind}`,
        `  Iterable higher action: ` +
            result.computation.higherActionOutputKind,
        `  Runtime rules: ${result.computation.runtimeRuleIds.join(', ')}`,
        '',
        `Rejected input: ${result.rejectedInput}`,
        `Diagnostic: ${result.negativeDiagnostic.code} — ` +
            result.negativeDiagnostic.message,
        '',
        'New Lambdapi mathematical owners/rules: ' +
            `${result.newLambdapiMathematicalOwnerCount}/` +
            result.newLambdapiRuntimeRuleCount,
        `Intrinsic Core owners: ${result.intrinsicCoreOwnerCount}`,
        'Arbitrary mixed-domain evaluation: deferred',
        'Genuine dependent chains: deferred to DISPLAYED-CHAIN-0A',
        'String parser dependency: no',
        'Production Lambdapi dependency: no'
    ].join('\n');
}
