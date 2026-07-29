/**
 * Executable DISPLAYED-CHAIN-1A end-user demonstration.
 *
 * The input is the direct typed TypeScript construction API. No string
 * parser, RawExpr layer, second checker, or production Lambdapi process is
 * involved.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY
} from './categorical_displayed_chain_transfer';
import {
    CoreCategoricalDiagnostic,
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation,
    coreCategoricalDiagnosticFromError
} from './categorical_program';
import {
    CoreLfComparisonResult
} from './lf_conversion';

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_DEMO_REVISION =
    'DISPLAYED-CHAIN-1A-DEMO-1' as const;

export interface CoreCategoricalDisplayedChainDemoExample {
    readonly id: 'outer' | 'inner' | 'recursive';
    readonly surface: string;
    readonly typescriptInput: string;
    readonly irSummary: string;
    readonly coreSummary: string;
    readonly compilation: CoreCategoricalProgramCompilation;
}

export interface CoreCategoricalDisplayedChainDemoResult {
    readonly revision:
        typeof CORE_CATEGORICAL_DISPLAYED_CHAIN_DEMO_REVISION;
    readonly candidate: 'emdash-v3.2-displayed-chain-1a';
    readonly construction: 'direct-typescript-categorical-program';
    readonly telescope:
        'k : K; a : A[k]; b : B[(k,a)]';
    readonly pipeline: readonly [
        'typed TypeScript construction IR',
        'recursive contextual occurrence compiler',
        'sequential-Sigma/direct-displayed lowering',
        'backend-neutral explicit Core',
        'generic checker/evaluator'
    ];
    readonly assumptions: readonly string[];
    readonly examples:
        readonly CoreCategoricalDisplayedChainDemoExample[];
    readonly computation: {
        readonly outerObjectStatus: 'equal';
        readonly innerObjectStatus: 'equal';
        readonly recursiveObjectStatus: 'equal';
        readonly arrowIndependenceStatus: 'equal';
        readonly internalizedArrowNonCollapseStatus: 'not-equal';
        readonly reindexedOutputKind: 'displayed-functor';
        readonly runtimeRuleIds: readonly string[];
    };
    readonly rejectedInput:
        'B : Catd K instead of B : Catd(Sigma(A))';
    readonly negativeDiagnostic: CoreCategoricalDiagnostic;
    readonly newLambdapiMathematicalOwnerCount: 1;
    readonly newLambdapiRuntimeRuleCount: 6;
    readonly intrinsicCoreOwnerCount: 0;
    readonly stringParserDependency: false;
    readonly productionLambdapiDependency: false;
    readonly arbitraryTelescopeDepthDeferred: true;
    readonly generalNdCoherenceDeferred: true;
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

export function runCoreCategoricalDisplayedChainDemo():
CoreCategoricalDisplayedChainDemoResult {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'examples/v3_2_categorical_displayed_chain_demo.ts',
        profile: 'fibred-displayed-chain-1'
    });
    const K = emdash.category('demo_K', { line: 1 });
    const A = emdash.displayedFamily('demo_A', K, { line: 2 });
    const D = emdash.displayedFamily('demo_D', K, { line: 3 });
    const sigmaA = emdash.totalCategory(A, { line: 4 });
    const B = emdash.displayedFamily('demo_B', sigmaA, { line: 5 });
    const projection = emdash.sigmaProjection(A, { line: 6 });
    const liftedA = emdash.pullbackFamily(
        A,
        projection,
        { line: 7 }
    );
    const liftedD = emdash.pullbackFamily(
        D,
        projection,
        { line: 8 }
    );
    const FF = emdash.displayedFunctor(
        'demo_FF',
        A,
        D,
        { line: 9 }
    );
    const liftedFF = emdash.pullbackDisplayedFunctor(
        FF,
        projection,
        { line: 10 }
    );

    const outer = emdash.displayedDependentContextLambda(
        [
            { name: 'a', family: A },
            { name: 'b', family: B }
        ],
        liftedA,
        ([a]) => a,
        { source: { line: 12 } }
    );
    const inner = emdash.displayedDependentContextLambda(
        [
            { name: 'a', family: A },
            { name: 'b', family: B }
        ],
        B,
        ([, b]) => b,
        { source: { line: 18 } }
    );
    const recursive = emdash.displayedDependentContextLambda(
        [
            { name: 'a', family: A },
            { name: 'b', family: B }
        ],
        liftedD,
        ([a]) => emdash.apply(liftedFF, a),
        { source: { line: 24 } }
    );

    const k0 = emdash.object('demo_k0', K, { line: 30 });
    const k1 = emdash.object('demo_k1', K, { line: 31 });
    const p = emdash.hom('demo_p', K, k0, k1, { line: 32 });
    const a0 = emdash.object(
        'demo_a0',
        emdash.fibre(A, k0),
        { line: 33 }
    );
    const a1 = emdash.object(
        'demo_a1',
        emdash.fibre(A, k1),
        { line: 34 }
    );
    const alpha = emdash.hom(
        'demo_alpha',
        emdash.fibre(A, k1),
        emdash.apply(
            emdash.familyTransport(A, p),
            a0
        ),
        a1,
        { line: 35 }
    );
    const q = emdash.sigmaArrow(
        A,
        a0,
        a1,
        p,
        alpha,
        { line: 36 }
    );
    const z0 = emdash.dependentPair(A, k0, a0, { line: 37 });
    const b0 = emdash.object(
        'demo_b0',
        emdash.fibre(B, z0),
        { line: 38 }
    );
    const c0 = emdash.object(
        'demo_c0',
        emdash.fibre(B, z0),
        { line: 39 }
    );
    const applyAt = (
        displayedFunctor: typeof outer
    ) => emdash.apply(
        emdash.apply(
            displayedFunctor,
            z0,
            { expectedShape: 'fibre-functor' }
        ),
        b0
    );
    const outerObject = emdash.compare(
        applyAt(outer),
        a0,
        60_000
    );
    const innerObject = emdash.compare(
        applyAt(inner),
        b0,
        60_000
    );
    const recursiveObject = emdash.compare(
        applyAt(recursive),
        emdash.apply(
            emdash.apply(
                FF,
                k0,
                { expectedShape: 'fibre-functor' }
            ),
            a0
        ),
        60_000
    );
    const bCell = emdash.displayedFunctorInternalCell(
        outer,
        q,
        b0
    );
    const cCell = emdash.displayedFunctorInternalCell(
        outer,
        q,
        c0
    );
    const arrowIndependence = emdash.compare(
        bCell,
        cCell,
        60_000
    );
    const internalizedArrowNonCollapse = emdash.compare(
        bCell,
        alpha,
        60_000
    );
    const L = emdash.category('demo_L', { line: 45 });
    const u = emdash.functor('demo_u', L, sigmaA, { line: 46 });
    const reindexed = emdash.compile(
        emdash.pullbackDisplayedFunctor(outer, u)
    );
    if (
        outerObject.status !== 'equal' ||
        innerObject.status !== 'equal' ||
        recursiveObject.status !== 'equal' ||
        arrowIndependence.status !== 'equal' ||
        internalizedArrowNonCollapse.status !== 'not-equal' ||
        reindexed.surfaceType.tag !== 'displayed-functor'
    ) {
        throw new Error(
            'DISPLAYED-CHAIN-1A object/arrow/reindexing evidence drifted'
        );
    }

    let negativeDiagnostic: CoreCategoricalDiagnostic | undefined;
    try {
        const wrongB = emdash.displayedFamily(
            'demo_wrong_B',
            K,
            { line: 50 }
        );
        emdash.displayedDependentContextLambda(
            [
                { name: 'a', family: A },
                { name: 'b', family: wrongB }
            ],
            liftedA,
            ([a]) => a,
            { source: { line: 51 } }
        );
    } catch (error: unknown) {
        negativeDiagnostic =
            coreCategoricalDiagnosticFromError(error);
        if (negativeDiagnostic === undefined) throw error;
    }
    if (negativeDiagnostic === undefined) {
        throw new Error(
            'DISPLAYED-CHAIN-1A accepted a wrong next-family base'
        );
    }

    return Object.freeze({
        revision: CORE_CATEGORICAL_DISPLAYED_CHAIN_DEMO_REVISION,
        candidate: 'emdash-v3.2-displayed-chain-1a',
        construction: 'direct-typescript-categorical-program',
        telescope: 'k : K; a : A[k]; b : B[(k,a)]',
        pipeline: Object.freeze([
            'typed TypeScript construction IR',
            'recursive contextual occurrence compiler',
            'sequential-Sigma/direct-displayed lowering',
            'backend-neutral explicit Core',
            'generic checker/evaluator'
        ] as const),
        assumptions: Object.freeze([
            'demo_K : Cat',
            'demo_A demo_D : Catd demo_K',
            'demo_B : Catd(Sigma_cat demo_A)',
            'demo_FF : Functord demo_A demo_D'
        ]),
        examples: Object.freeze([
            Object.freeze({
                id: 'outer' as const,
                surface:
                    'λ a :^fd A. λ b :^fd B(a). a',
                typescriptInput:
                    'displayedDependentContextLambda(' +
                    '[{a:A},{b:B}], A↑, ([a,b]) => a)',
                irSummary:
                    'slot a under one genuine dependency edge',
                coreSummary:
                    'section_pullback(' +
                    'sigma_functord_sec(id_funcd A))',
                compilation: emdash.compile(outer)
            }),
            Object.freeze({
                id: 'inner' as const,
                surface:
                    'λ a :^fd A. λ b :^fd B(a). b',
                typescriptInput:
                    'displayedDependentContextLambda(' +
                    '[{a:A},{b:B}], B, ([a,b]) => b)',
                irSummary:
                    'slot b at the immediate dependent edge',
                coreSummary: 'id_funcd B',
                compilation: emdash.compile(inner)
            }),
            Object.freeze({
                id: 'recursive' as const,
                surface:
                    'λ a :^fd A. λ b :^fd B(a). FF[a]',
                typescriptInput:
                    'displayedDependentContextLambda(' +
                    '[{a:A},{b:B}], D↑, ([a,b]) => apply(FF↑,a))',
                irSummary:
                    'closed displayed-functor application over slot a',
                coreSummary:
                    'pullback(FF) ∘ ' +
                    'section_pullback(sigma_functord_sec(id A))',
                compilation: emdash.compile(recursive)
            })
        ]),
        computation: Object.freeze({
            outerObjectStatus: 'equal' as const,
            innerObjectStatus: 'equal' as const,
            recursiveObjectStatus: 'equal' as const,
            arrowIndependenceStatus: 'equal' as const,
            internalizedArrowNonCollapseStatus:
                'not-equal' as const,
            reindexedOutputKind: 'displayed-functor' as const,
            runtimeRuleIds: runtimeRuleIds(
                outerObject,
                innerObject,
                recursiveObject,
                arrowIndependence,
                internalizedArrowNonCollapse
            )
        }),
        rejectedInput:
            'B : Catd K instead of B : Catd(Sigma(A))',
        negativeDiagnostic,
        newLambdapiMathematicalOwnerCount:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY
                .newMathematicalOwnerCount as 1,
        newLambdapiRuntimeRuleCount:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY
                .newMathematicalRuntimeRuleCount as 6,
        intrinsicCoreOwnerCount:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY
                .newIntrinsicCoreOwnerCount as 0,
        stringParserDependency: false as const,
        productionLambdapiDependency: false as const,
        arbitraryTelescopeDepthDeferred: true as const,
        generalNdCoherenceDeferred: true as const
    });
}

export function formatCoreCategoricalDisplayedChainDemo(
    result: CoreCategoricalDisplayedChainDemoResult =
        runCoreCategoricalDisplayedChainDemo()
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
        `Telescope: ${result.telescope}`,
        '',
        'Assumptions:',
        assumptions,
        '',
        'Pipeline:',
        pipeline,
        '',
        'Dependent displayed inputs:',
        examples,
        '',
        'Checked computation:',
        `  Outer object a: ${result.computation.outerObjectStatus}`,
        `  Inner object b: ${result.computation.innerObjectStatus}`,
        `  Recursive FF[a]: ` +
            result.computation.recursiveObjectStatus,
        `  Arrow independent of ignored b: ` +
            result.computation.arrowIndependenceStatus,
        `  Internalized arrow does not collapse: ` +
            result.computation.internalizedArrowNonCollapseStatus,
        `  Reindexed output: ` +
            result.computation.reindexedOutputKind,
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
        'Arbitrary telescope depth: deferred',
        'General :^nd coherence: deferred',
        'String parser dependency: no',
        'Production Lambdapi dependency: no'
    ].join('\n');
}
