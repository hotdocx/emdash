/**
 * Executable end-user demonstration of DISPLAYED-BRACKET-1A.
 *
 * Surface strings document the intended notation. The actual input is the
 * direct typed TypeScript API; no string parser or production Lambdapi
 * process participates.
 */

import {
    CoreCategoricalDiagnostic,
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation,
    coreCategoricalDiagnosticFromError
} from './categorical_program';
import {
    CoreLfComparisonResult
} from './lf_conversion';

export const CORE_CATEGORICAL_DISPLAYED_BRACKET_DEMO_REVISION =
    'DISPLAYED-BRACKET-1A-DEMO-1' as const;

export interface CoreCategoricalDisplayedBracketDemoExample {
    readonly id:
        | 'projection'
        | 'exchange'
        | 'contraction'
        | 'mapped-pair'
        | 'three-sibling';
    readonly surface: string;
    readonly typescriptInput: string;
    /**
     * Stable human-facing synopsis. `compilation.explicitCore` retains the
     * complete backend-neutral Core term for tools and conformance checks.
     */
    readonly coreSummary: string;
    readonly coreTypeSummary: string;
    readonly compilation: CoreCategoricalProgramCompilation;
}

export interface CoreCategoricalDisplayedBracketDemoResult {
    readonly revision:
        typeof CORE_CATEGORICAL_DISPLAYED_BRACKET_DEMO_REVISION;
    readonly candidate: 'emdash-v3.2-displayed-bracket-1a';
    readonly construction: 'direct-typescript-categorical-program';
    readonly assumptions: readonly string[];
    readonly examples:
        readonly CoreCategoricalDisplayedBracketDemoExample[];
    readonly projectionComputation: {
        readonly objectInput:
            '(λ (b,c). b)[demo_x]';
        readonly objectOutput:
            'Product_projL_func(demo_B[demo_x],demo_C[demo_x])';
        readonly objectStatus: 'equal';
        readonly arrowInput:
            '(λ (b,c). b)[demo_p]';
        readonly arrowOutput:
            'full projection action evaluated at demo_p';
        readonly arrowStatus: 'equal';
        readonly runtimeRuleIds: readonly string[];
    };
    readonly negativeInput:
        'displayedContextLambda([{b:B},{e:E_L}], B, ...)';
    readonly negativeDiagnostic: CoreCategoricalDiagnostic;
    readonly dependencyPlanner:
        'independence-derived-no-user-flags';
    readonly genuineDependentChainsDeferred: true;
    readonly newLambdapiOwnerOrRule: false;
    readonly stringParserDependency: false;
    readonly productionLambdapiDependency: false;
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

export function runCoreCategoricalDisplayedBracketDemo():
CoreCategoricalDisplayedBracketDemoResult {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'examples/v3_2_categorical_displayed_bracket_demo.ts',
        profile: 'fibred-displayed-bracket-1'
    });
    const K = emdash.category('demo_K', { line: 70 });
    const B = emdash.displayedFamily('demo_B', K, { line: 71 });
    const C = emdash.displayedFamily('demo_C', K, { line: 72 });
    const D = emdash.displayedFamily('demo_D', K, { line: 73 });
    const Q = emdash.displayedFamily('demo_Q', K, { line: 74 });
    const FF = emdash.displayedFunctor(
        'demo_FF',
        B,
        D,
        { line: 75 }
    );
    const GG = emdash.displayedFunctor(
        'demo_GG',
        C,
        Q,
        { line: 76 }
    );

    const projection = emdash.displayedContextLambda(
        [
            { name: 'b', family: B },
            { name: 'c', family: C }
        ],
        B,
        ([b]) => b,
        { source: { line: 80 } }
    );
    const exchange = emdash.displayedContextLambda(
        [
            { name: 'b', family: B },
            { name: 'c', family: C }
        ],
        emdash.displayedProduct(C, B),
        ([b, c]) => emdash.fibrePair(c, b),
        { source: { line: 89 } }
    );
    const contraction = emdash.displayedContextLambda(
        [{ name: 'b', family: B }],
        emdash.displayedProduct(B, B),
        ([b]) => emdash.fibrePair(b, b),
        { source: { line: 98 } }
    );
    const mappedPair = emdash.displayedContextLambda(
        [
            { name: 'b', family: B },
            { name: 'c', family: C }
        ],
        emdash.displayedProduct(D, Q),
        ([b, c]) => emdash.fibrePair(
            emdash.apply(FF, b),
            emdash.apply(GG, c)
        ),
        { source: { line: 106 } }
    );
    const threeSibling = emdash.displayedContextLambda(
        [
            { name: 'b', family: B },
            { name: 'c', family: C },
            { name: 'd', family: D }
        ],
        emdash.displayedProduct(
            emdash.displayedProduct(D, B),
            C
        ),
        ([b, c, d]) => emdash.fibrePair(
            emdash.fibrePair(d, b),
            c
        ),
        { source: { line: 117 } }
    );

    const x = emdash.object('demo_x', K, { line: 126 });
    const y = emdash.object('demo_y', K, { line: 127 });
    const p = emdash.hom('demo_p', K, x, y, { line: 128 });
    const objectResult = emdash.compare(
        emdash.apply(projection, x, {
            expectedShape: 'fibre-functor'
        }),
        emdash.productLeftProjection(
            emdash.fibre(B, x),
            emdash.fibre(C, x)
        ),
        4_000
    );
    const arrowResult = emdash.compare(
        emdash.apply(projection, p, {
            expectedShape: 'transport-functor'
        }),
        emdash.apply(
            emdash.displayedFunctorFullAction(
                projection,
                x,
                y
            ),
            p
        ),
        4_000
    );
    if (
        objectResult.status !== 'equal' ||
        arrowResult.status !== 'equal'
    ) {
        throw new Error(
            'DISPLAYED-BRACKET-1A projection computation did not close'
        );
    }

    const foreignBase = emdash.category('demo_L', { line: 150 });
    const foreignFamily = emdash.displayedFamily(
        'demo_E_L',
        foreignBase,
        { line: 151 }
    );
    let negativeDiagnostic: CoreCategoricalDiagnostic | undefined;
    try {
        emdash.displayedContextLambda(
            [
                { name: 'b', family: B },
                { name: 'e', family: foreignFamily }
            ],
            B,
            ([b]) => b,
            {
                source: {
                    line: 154,
                    detail: 'cross-base displayed sibling block'
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
            'DISPLAYED-BRACKET-1A accepted a cross-base sibling block'
        );
    }

    return Object.freeze({
        revision: CORE_CATEGORICAL_DISPLAYED_BRACKET_DEMO_REVISION,
        candidate: 'emdash-v3.2-displayed-bracket-1a',
        construction: 'direct-typescript-categorical-program',
        assumptions: Object.freeze([
            'demo_K : Cat',
            'demo_B demo_C demo_D demo_Q : Catd demo_K',
            'demo_FF : Functord(demo_B,demo_D)',
            'demo_GG : Functord(demo_C,demo_Q)',
            'demo_x demo_y : Obj demo_K',
            'demo_p : Hom(demo_K,demo_x,demo_y)'
        ]),
        examples: Object.freeze([
            Object.freeze({
                id: 'projection' as const,
                surface: 'λ (b : B, c : C) :^fd. b',
                typescriptInput:
                    'displayedContextLambda([{b:B},{c:C}], B, ([b]) => b)',
                coreSummary:
                    'displayed-product-left-projection(B,C)',
                coreTypeSummary:
                    'Functord(Product_catd(B,C),B)',
                compilation: emdash.compile(projection)
            }),
            Object.freeze({
                id: 'exchange' as const,
                surface: 'λ (b : B, c : C) :^fd. (c,b)',
                typescriptInput:
                    'displayedContextLambda(..., ([b,c]) => ' +
                    'fibrePair(c,b))',
                coreSummary:
                    'displayed-product-pair(right-projection,' +
                    'left-projection)',
                coreTypeSummary:
                    'Functord(Product_catd(B,C),Product_catd(C,B))',
                compilation: emdash.compile(exchange)
            }),
            Object.freeze({
                id: 'contraction' as const,
                surface: 'λ b :^fd B. (b,b)',
                typescriptInput:
                    'displayedContextLambda([{b:B}], B×B, ([b]) => ' +
                    'fibrePair(b,b))',
                coreSummary:
                    'displayed-product-pair(identity_B,identity_B)',
                coreTypeSummary:
                    'Functord(B,Product_catd(B,B))',
                compilation: emdash.compile(contraction)
            }),
            Object.freeze({
                id: 'mapped-pair' as const,
                surface:
                    'λ (b : B, c : C) :^fd. (demo_FF[b],demo_GG[c])',
                typescriptInput:
                    'displayedContextLambda(..., ([b,c]) => ' +
                    'fibrePair(apply(FF,b),apply(GG,c)))',
                coreSummary:
                    'displayed-product-pair(FF∘left-projection,' +
                    'GG∘right-projection)',
                coreTypeSummary:
                    'Functord(Product_catd(B,C),Product_catd(D,Q))',
                compilation: emdash.compile(mappedPair)
            }),
            Object.freeze({
                id: 'three-sibling' as const,
                surface:
                    'λ (b : B, c : C, d : D) :^fd. ((d,b),c)',
                typescriptInput:
                    'displayedContextLambda(..., ([b,c,d]) => ' +
                    'fibrePair(fibrePair(d,b),c))',
                coreSummary:
                    'nested displayed projections and product pairing',
                coreTypeSummary:
                    'Functord(Product_catd(Product_catd(B,C),D),' +
                    'Product_catd(Product_catd(D,B),C))',
                compilation: emdash.compile(threeSibling)
            })
        ]),
        projectionComputation: Object.freeze({
            objectInput: '(λ (b,c). b)[demo_x]' as const,
            objectOutput:
                'Product_projL_func(demo_B[demo_x],demo_C[demo_x])' as const,
            objectStatus: 'equal' as const,
            arrowInput: '(λ (b,c). b)[demo_p]' as const,
            arrowOutput:
                'full projection action evaluated at demo_p' as const,
            arrowStatus: 'equal' as const,
            runtimeRuleIds: runtimeRuleIds(
                objectResult,
                arrowResult
            )
        }),
        negativeInput:
            'displayedContextLambda([{b:B},{e:E_L}], B, ...)',
        negativeDiagnostic,
        dependencyPlanner:
            'independence-derived-no-user-flags',
        genuineDependentChainsDeferred: true,
        newLambdapiOwnerOrRule: false,
        stringParserDependency: false,
        productionLambdapiDependency: false
    });
}

export function formatCoreCategoricalDisplayedBracketDemo(
    result: CoreCategoricalDisplayedBracketDemoResult =
        runCoreCategoricalDisplayedBracketDemo()
): string {
    const assumptions = result.assumptions.map(
        assumption => `  - ${assumption}`
    ).join('\n');
    const examples = result.examples.map(example => [
        `  ${example.id}: ${example.surface}`,
        `    TypeScript: ${example.typescriptInput}`,
        `    Core: ${example.coreSummary}`,
        `    Type: ${example.coreTypeSummary}`
    ].join('\n')).join('\n');
    return [
        result.candidate,
        `Input path: ${result.construction}`,
        '',
        'Assumptions:',
        assumptions,
        '',
        'Displayed contextual inputs:',
        examples,
        '',
        `Computed object input: ` +
            result.projectionComputation.objectInput,
        `Computed object output: ` +
            result.projectionComputation.objectOutput,
        `Computed arrow input: ` +
            result.projectionComputation.arrowInput,
        `Computed arrow output: ` +
            result.projectionComputation.arrowOutput,
        'Computation: equal via ' +
            result.projectionComputation.runtimeRuleIds.join(', '),
        '',
        `Rejected input: ${result.negativeInput}`,
        `Diagnostic: ${result.negativeDiagnostic.code} — ` +
            result.negativeDiagnostic.message,
        '',
        'Dependency planning: ' + result.dependencyPlanner,
        'Genuine dependent chains: deferred to DISPLAYED-CHAIN-0A',
        'New Lambdapi owner/rule: no',
        'String parser dependency: no',
        'Production Lambdapi dependency: no'
    ].join('\n');
}
