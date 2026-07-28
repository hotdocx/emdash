/**
 * Executable end-user demonstration of FIBRED-GROUPED-SEQUENTIAL-1.
 *
 * Surface strings explain the two presentations. The executable input is the
 * direct typed TypeScript API; no string parser or production Lambdapi
 * runtime participates.
 */

import {
    CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT
} from './categorical_grouped_sequential_contract';
import {
    CoreCategoricalContextPlanningError,
    coreCategoricalClosedContextClassifier,
    coreCategoricalContextSlotReference,
    coreCategoricalDisplayedContextClassifier,
    planCoreCategoricalContextDependencies
} from './categorical_context_dependencies';
import {
    CoreCategoricalGroupedSequentialComparison,
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation
} from './categorical_program';
import {
    provenance,
    sourceSpan,
    kernelFree
} from './kernel';
import {
    CoreLfComparisonResult
} from './lf_conversion';

export const CORE_CATEGORICAL_GROUPED_SEQUENTIAL_DEMO_REVISION =
    'FIBRED-GROUPED-SEQUENTIAL-1-DEMO-1' as const;

export interface CoreCategoricalGroupedSequentialDemoExample {
    readonly id:
        | 'sequential-object'
        | 'grouped-object'
        | 'grouped-tuple'
        | 'sequential-base-projection'
        | 'grouped-base-projection';
    readonly surface: string;
    readonly compilation: CoreCategoricalProgramCompilation;
}

export interface CoreCategoricalGroupedSequentialDemo {
    readonly revision:
        typeof CORE_CATEGORICAL_GROUPED_SEQUENTIAL_DEMO_REVISION;
    readonly candidate:
        'emdash-v3.2-fibred-grouped-sequential-1';
    readonly construction: 'direct-typescript-categorical-program';
    readonly assumptions: readonly string[];
    readonly presentations: {
        readonly sequential: string;
        readonly grouped: string;
        readonly dependencyEdges: readonly (readonly [number, number])[];
        readonly sequentialKinds: readonly string[];
        readonly groupedRelation: 'shared-minimal-base-siblings';
    };
    readonly examples:
        readonly CoreCategoricalGroupedSequentialDemoExample[];
    readonly comparisons:
        readonly CoreCategoricalGroupedSequentialComparison[];
    readonly dependencyEdgeDiagnostic: {
        readonly code: 'DEPENDENT_SIBLING_GROUP';
        readonly location: string;
        readonly message: string;
    };
    readonly totalCategoryCompared: false;
    readonly totalCategoryEqualityClaimed: false;
    readonly totalCategoryEquivalenceClaimed: false;
    readonly arrowLevelTotalComparisonClaimed: false;
    readonly newLambdapiMathematicalOwnerOrRule: false;
    readonly productionLambdapiDependency: false;
    readonly contract:
        typeof CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT;
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
    id: string,
    result: CoreLfComparisonResult
): CoreCategoricalGroupedSequentialComparison => {
    if (result.status !== 'equal') {
        throw new Error(
            `Grouped/sequential demo comparison '${id}' did not close`
        );
    }
    return Object.freeze({
        id,
        status: 'equal' as const,
        steps: result.steps,
        ruleIds: runtimeRuleIds(result)
    });
};

const dependencyEdgeDiagnostic = ():
CoreCategoricalGroupedSequentialDemo['dependencyEdgeDiagnostic'] => {
    const file =
        'examples/v3_2_categorical_grouped_sequential_demo.ts';
    const at = (line: number, detail: string) => provenance(
        'surface',
        detail,
        sourceSpan(file, line, 1, line, 2)
    );
    const K = kernelFree('edge_K', at(90, 'edge base'));
    const B = kernelFree('edge_B', at(91, 'edge first family'));
    const C = kernelFree('edge_C', at(92, 'edge dependent family'));
    try {
        planCoreCategoricalContextDependencies({
            slots: [
                {
                    name: 'k',
                    classifier:
                        coreCategoricalClosedContextClassifier(
                            { tag: 'object', category: K },
                            at(93, 'edge k classifier')
                        ),
                    provenance: at(93, 'edge k slot')
                },
                {
                    name: 'b',
                    classifier:
                        coreCategoricalDisplayedContextClassifier(
                            K,
                            B,
                            [
                                coreCategoricalContextSlotReference(
                                    0,
                                    at(94, 'k in B[k]')
                                )
                            ],
                            {
                                tag: 'object',
                                category: kernelFree(
                                    'edge_B_fibre',
                                    at(94, 'B fibre')
                                )
                            },
                            at(94, 'B[k] classifier')
                        ),
                    provenance: at(94, 'edge b slot')
                },
                {
                    name: 'c',
                    classifier:
                        coreCategoricalDisplayedContextClassifier(
                            K,
                            C,
                            [
                                coreCategoricalContextSlotReference(
                                    0,
                                    at(95, 'b in C[k,b]')
                                )
                            ],
                            {
                                tag: 'object',
                                category: kernelFree(
                                    'edge_C_fibre',
                                    at(95, 'C fibre')
                                )
                            },
                            at(95, 'C[k,b] classifier')
                        ),
                    provenance: at(95, 'edge c slot')
                }
            ],
            siblingGroups: [{
                positions: [1, 2],
                provenance: at(96, 'invalid b c group')
            }]
        });
    } catch (error: unknown) {
        if (
            error instanceof CoreCategoricalContextPlanningError &&
            error.code === 'DEPENDENT_SIBLING_GROUP' &&
            error.provenance.span !== undefined
        ) {
            return Object.freeze({
                code: error.code,
                location:
                    `${error.provenance.span.file}:` +
                    `${error.provenance.span.start.line}:` +
                    `${error.provenance.span.start.column}`,
                message: error.message
            });
        }
        throw error;
    }
    throw new Error(
        'Grouped/sequential demo accepted a genuine dependency edge'
    );
};

const example = (
    id: CoreCategoricalGroupedSequentialDemoExample['id'],
    surface: string,
    compilation: CoreCategoricalProgramCompilation
): CoreCategoricalGroupedSequentialDemoExample => Object.freeze({
    id,
    surface,
    compilation
});

export function runCoreCategoricalGroupedSequentialDemo():
CoreCategoricalGroupedSequentialDemo {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'examples/v3_2_categorical_grouped_sequential_demo.ts',
        profile: 'fibred-grouped-sequential-1'
    });
    const K = emdash.category('demo_K', { line: 20 });
    const B = emdash.displayedFamily('demo_B', K, { line: 21 });
    const C = emdash.displayedFamily('demo_C', K, { line: 22 });
    const context = emdash.groupedSequentialContext(
        'k',
        K,
        [
            { name: 'b', family: B },
            { name: 'c', family: C }
        ],
        { line: 24 }
    );
    const k = emdash.object('demo_k', K, { line: 26 });
    const Bk = emdash.fibre(B, k, { line: 27 });
    const Ck = emdash.fibre(C, k, { line: 28 });
    const b = emdash.object('demo_b', Bk, { line: 29 });
    const c = emdash.object('demo_c', Ck, { line: 30 });
    const objects = emdash.groupedSequentialObject(
        context,
        k,
        [b, c],
        { line: 32 }
    );

    const sequentialBase = emdash.apply(
        context.sequential.extensions[1].projectionToBase,
        objects.sequentialObject,
        { source: { line: 34 } }
    );
    const groupedBase = emdash.apply(
        emdash.sigmaProjection(context.grouped.family, { line: 35 }),
        objects.groupedObject,
        { source: { line: 36 } }
    );
    const sequentialPrefix = emdash.apply(
        context.sequential.extensions[1].projectionToPrevious,
        objects.sequentialObject,
        { source: { line: 37 } }
    );
    const leftAtK = emdash.apply(
        emdash.displayedProductLeftProjection(B, C, { line: 38 }),
        k,
        {
            expectedShape: 'fibre-functor',
            source: { line: 39 }
        }
    );
    const rightAtK = emdash.apply(
        emdash.displayedProductRightProjection(B, C, { line: 40 }),
        k,
        {
            expectedShape: 'fibre-functor',
            source: { line: 41 }
        }
    );

    return Object.freeze({
        revision:
            CORE_CATEGORICAL_GROUPED_SEQUENTIAL_DEMO_REVISION,
        candidate:
            'emdash-v3.2-fibred-grouped-sequential-1',
        construction: 'direct-typescript-categorical-program',
        assumptions: Object.freeze([
            'demo_K : Cat',
            'demo_B, demo_C : Catd demo_K',
            'demo_k : Obj demo_K',
            'demo_b : Obj demo_B[demo_k]',
            'demo_c : Obj demo_C[demo_k]'
        ]),
        presentations: Object.freeze({
            sequential: context.sequential.syntax,
            grouped: context.grouped.syntax,
            dependencyEdges: Object.freeze(
                context.plan.dependencyEdges.map(edge =>
                    Object.freeze([
                        edge.dependencyPosition,
                        edge.dependentPosition
                    ] as const)
                )
            ),
            sequentialKinds: Object.freeze(
                context.sequential.extensions.map(
                    extension => extension.presentation
                )
            ),
            groupedRelation:
                context.plan.groupedProducts[0].relation as
                    'shared-minimal-base-siblings'
        }),
        examples: Object.freeze([
            example(
                'sequential-object',
                '((demo_k,demo_b),demo_c)',
                emdash.compile(objects.sequentialObject)
            ),
            example(
                'grouped-object',
                '(demo_k,(demo_b,demo_c))',
                emdash.compile(objects.groupedObject)
            ),
            example(
                'grouped-tuple',
                '(demo_b,demo_c)',
                emdash.compile(objects.groupedTuple)
            ),
            example(
                'sequential-base-projection',
                'π_B ∘ π_C[((demo_k,demo_b),demo_c)]',
                emdash.compile(sequentialBase)
            ),
            example(
                'grouped-base-projection',
                'π_P[(demo_k,(demo_b,demo_c))]',
                emdash.compile(groupedBase)
            )
        ]),
        comparisons: Object.freeze([
            ...objects.sequentialFibreComparisons,
            objects.groupedFibreComparison,
            comparison(
                'sequential-prefix-projection',
                emdash.compare(
                    sequentialPrefix,
                    objects.sequentialPrefixObjects[0],
                    4_000
                )
            ),
            comparison(
                'sequential-base-projection',
                emdash.compare(sequentialBase, k, 4_000)
            ),
            comparison(
                'grouped-base-projection',
                emdash.compare(groupedBase, k, 4_000)
            ),
            comparison(
                'grouped-left-component-functor',
                emdash.compare(
                    leftAtK,
                    emdash.productLeftProjection(Bk, Ck),
                    4_000
                )
            ),
            comparison(
                'grouped-right-component-functor',
                emdash.compare(
                    rightAtK,
                    emdash.productRightProjection(Bk, Ck),
                    4_000
                )
            )
        ]),
        dependencyEdgeDiagnostic: dependencyEdgeDiagnostic(),
        totalCategoryCompared: false as const,
        totalCategoryEqualityClaimed: false as const,
        totalCategoryEquivalenceClaimed: false as const,
        arrowLevelTotalComparisonClaimed: false as const,
        newLambdapiMathematicalOwnerOrRule: false as const,
        productionLambdapiDependency: false as const,
        contract: CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT
    });
}

export function formatCoreCategoricalGroupedSequentialDemo(): string {
    const demo = runCoreCategoricalGroupedSequentialDemo();
    return [
        `${demo.candidate} (${demo.revision})`,
        `construction: ${demo.construction}`,
        'inputs:',
        ...demo.assumptions.map(assumption => `  ${assumption}`),
        'presentations:',
        `  sequential: ${demo.presentations.sequential}`,
        `  grouped: ${demo.presentations.grouped}`,
        `  dependency edges: ` +
            JSON.stringify(demo.presentations.dependencyEdges),
        `  sequential lowerings: ` +
            demo.presentations.sequentialKinds.join(', '),
        `  grouped relation: ${demo.presentations.groupedRelation}`,
        'programs:',
        ...demo.examples.map(item => [
            `  ${item.id}: ${item.surface}`,
            `    Core: ${item.compilation.explicitCore}`,
            `    type: ${item.compilation.explicitInferredType}`
        ].join('\n')),
        'computed conformance:',
        ...demo.comparisons.map(item =>
            `  ${item.id}: ${item.status} in ${item.steps} steps ` +
            `[${item.ruleIds.join(', ')}]`
        ),
        'negative dependency-edge diagnostic:',
        `  ${demo.dependencyEdgeDiagnostic.code} at ` +
            `${demo.dependencyEdgeDiagnostic.location}`,
        `  ${demo.dependencyEdgeDiagnostic.message}`,
        'total-category equality/equivalence compared: no',
        'arrow-level total comparison claimed: no',
        'new Lambdapi mathematical owner/rule: no',
        'production Lambdapi dependency: false'
    ].join('\n');
}
