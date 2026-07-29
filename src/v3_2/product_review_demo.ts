/**
 * Curated external-review report for the implemented emdash v3.2
 * TypeScript product path.
 *
 * This module composes existing structured demos. It adds no checker,
 * elaborator, Core owner, runtime rule, parser, browser surface, or
 * Lambdapi runtime dependency.
 */

import {
    CoreCategoricalBracketDemoResult,
    runCoreCategoricalBracketDemo
} from './categorical_bracket_demo';
import {
    CoreCategoricalDisplayedChainDemoResult,
    runCoreCategoricalDisplayedChainDemo
} from './categorical_displayed_chain_demo';
import {
    CoreDirectedDependentDemoResult,
    runCoreDirectedDependentDemo
} from './directed_dependent_demo';

export const CORE_PRODUCT_REVIEW_DEMO_REVISION =
    'PRODUCT-DEMO-1B-REPORT-1' as const;

export const CORE_PRODUCT_REVIEW_DEMO_PANEL_IDS = Object.freeze([
    'outer-dependent-lf',
    'ordinary-functorial-binding',
    'displayed-dependent-binding'
] as const);

const ADVANCED_WITNESS_COMMAND =
    './scripts/pnpmw run demo:categorical-displayed-nd-higher' as const;
const ADVANCED_WITNESS_REASON =
    'valuable-next-hom-higher-action-with-variable-startup-cost' as const;

export interface CoreProductReviewDemoComponents {
    readonly outerDependentLf: CoreDirectedDependentDemoResult;
    readonly ordinaryFunctorialBinding:
        CoreCategoricalBracketDemoResult;
    readonly displayedDependentBinding:
        CoreCategoricalDisplayedChainDemoResult;
}

export interface CoreProductReviewDemoResult {
    readonly revision: typeof CORE_PRODUCT_REVIEW_DEMO_REVISION;
    readonly candidate: 'emdash-v3.2-external-review-1';
    readonly construction:
        'direct-typescript-existing-structured-demos';
    readonly panelIds:
        typeof CORE_PRODUCT_REVIEW_DEMO_PANEL_IDS;
    readonly pipeline: readonly [
        'direct typed TypeScript construction',
        'recursive typed contextual elaboration',
        'backend-neutral explicit emdash Core',
        'generic LF checking, evaluation, and rewriting',
        'optional bounded Lambdapi conformance oracle'
    ];
    readonly components: CoreProductReviewDemoComponents;
    readonly productEffects: {
        readonly newMathematicalOwnerCount: 0;
        readonly newRuntimeRuleCount: 0;
        readonly newCheckerOrEvaluatorBranchCount: 0;
        readonly newParserDependencyCount: 0;
        readonly browserPromotion: false;
        readonly productionLambdapiDependency: false;
    };
    readonly supportedEnvelope: readonly [
        'outer-dependent-lambda-pi-and-sigma-telescope-evaluation',
        'ordinary-recursive-functorial-bracket-abstraction',
        'one-genuine-displayed-dependency-edge-with-object-and-arrow-evidence'
    ];
    readonly deferred: readonly [
        'arbitrary-displayed-telescope-depth',
        'general-nd-binder-and-coherence',
        'user-facing-string-syntax',
        'browser-profile-promotion',
        'systematic-groupoidal-closure',
        'whole-library-transfer-graduation'
    ];
    readonly advancedWitness: {
        readonly command:
            './scripts/pnpmw run demo:categorical-displayed-nd-higher';
        readonly includedByDefault: false;
        readonly reason:
            'valuable-next-hom-higher-action-with-variable-startup-cost';
    };
}

export type CoreProductReviewDemoErrorCode =
    'PRODUCT_REVIEW_COMPONENT_BOUNDARY_DRIFT';

export class CoreProductReviewDemoError extends Error {
    constructor(
        public readonly code: CoreProductReviewDemoErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreProductReviewDemoError';
    }
}

const failBoundary = (message: string): never => {
    throw new CoreProductReviewDemoError(
        'PRODUCT_REVIEW_COMPONENT_BOUNDARY_DRIFT',
        message
    );
};

const freezeComponents = (
    components: CoreProductReviewDemoComponents
): CoreProductReviewDemoComponents => Object.freeze({
    outerDependentLf: components.outerDependentLf,
    ordinaryFunctorialBinding:
        components.ordinaryFunctorialBinding,
    displayedDependentBinding:
        components.displayedDependentBinding
});

export function assembleCoreProductReviewDemo(
    components: CoreProductReviewDemoComponents
): CoreProductReviewDemoResult {
    const outer = components.outerDependentLf;
    const ordinary = components.ordinaryFunctorialBinding;
    const displayed = components.displayedDependentBinding;
    if (
        outer.profile !== 'emdash-v3.2-dttlf-directed-1' ||
        outer.construction !==
            'direct-typescript-scoped-builder' ||
        outer.productionLambdapiDependency ||
        ordinary.candidate !== 'emdash-v3.2-usability-1d' ||
        ordinary.construction !==
            'direct-typescript-categorical-program' ||
        ordinary.stringParserDependency ||
        ordinary.productionLambdapiDependency ||
        displayed.candidate !==
            'emdash-v3.2-displayed-chain-1a' ||
        displayed.construction !==
            'direct-typescript-categorical-program' ||
        displayed.telescope !==
            'k : K; a : A[k]; b : B[(k,a)]' ||
        displayed.stringParserDependency ||
        displayed.productionLambdapiDependency ||
        !displayed.arbitraryTelescopeDepthDeferred ||
        !displayed.generalNdCoherenceDeferred
    ) {
        return failBoundary(
            'One of the reviewed component demo boundaries drifted'
        );
    }

    return Object.freeze({
        revision: CORE_PRODUCT_REVIEW_DEMO_REVISION,
        candidate: 'emdash-v3.2-external-review-1' as const,
        construction:
            'direct-typescript-existing-structured-demos' as const,
        panelIds: CORE_PRODUCT_REVIEW_DEMO_PANEL_IDS,
        pipeline: Object.freeze([
            'direct typed TypeScript construction',
            'recursive typed contextual elaboration',
            'backend-neutral explicit emdash Core',
            'generic LF checking, evaluation, and rewriting',
            'optional bounded Lambdapi conformance oracle'
        ] as const),
        components: freezeComponents(components),
        productEffects: Object.freeze({
            newMathematicalOwnerCount: 0 as const,
            newRuntimeRuleCount: 0 as const,
            newCheckerOrEvaluatorBranchCount: 0 as const,
            newParserDependencyCount: 0 as const,
            browserPromotion: false as const,
            productionLambdapiDependency: false as const
        }),
        supportedEnvelope: Object.freeze([
            'outer-dependent-lambda-pi-and-sigma-telescope-evaluation',
            'ordinary-recursive-functorial-bracket-abstraction',
            'one-genuine-displayed-dependency-edge-with-object-and-arrow-evidence'
        ] as const),
        deferred: Object.freeze([
            'arbitrary-displayed-telescope-depth',
            'general-nd-binder-and-coherence',
            'user-facing-string-syntax',
            'browser-profile-promotion',
            'systematic-groupoidal-closure',
            'whole-library-transfer-graduation'
        ] as const),
        advancedWitness: Object.freeze({
            command: ADVANCED_WITNESS_COMMAND,
            includedByDefault: false as const,
            reason: ADVANCED_WITNESS_REASON
        })
    });
}

export function runCoreProductReviewDemo():
CoreProductReviewDemoResult {
    return assembleCoreProductReviewDemo({
        outerDependentLf: runCoreDirectedDependentDemo(),
        ordinaryFunctorialBinding:
            runCoreCategoricalBracketDemo(),
        displayedDependentBinding:
            runCoreCategoricalDisplayedChainDemo()
    });
}

const indent = (
    value: string,
    spaces = 2
): string => {
    const prefix = ' '.repeat(spaces);
    return value.split('\n').map(line => `${prefix}${line}`).join('\n');
};

const formatTrace = (
    result: CoreDirectedDependentDemoResult
): string => result.trace.map(
    entry => `${entry.step}. ${entry.reduction}`
).join(' -> ');

export function formatCoreProductReviewDemo(
    result: CoreProductReviewDemoResult =
        runCoreProductReviewDemo()
): string {
    const outer = result.components.outerDependentLf;
    const ordinary =
        result.components.ordinaryFunctorialBinding;
    const displayed =
        result.components.displayedDependentBinding;
    const pointwise = ordinary.examples.find(
        example => example.name === 'pointwise-application'
    );
    const diagonal = ordinary.examples.find(
        example => example.name === 'diagonal'
    );
    const exchange = ordinary.examples.find(
        example => example.name === 'exchange'
    );
    if (
        pointwise === undefined ||
        diagonal === undefined ||
        exchange === undefined
    ) {
        return failBoundary(
            'The ordinary bracket review corpus is incomplete'
        );
    }

    const pipeline = result.pipeline.map(
        (stage, index) => `  ${index + 1}. ${stage}`
    ).join('\n');
    const displayedInputs = displayed.examples.map(
        example => [
            `  - ${example.surface}`,
            `    TypeScript: ${example.typescriptInput}`,
            `    lowering: ${example.coreSummary}`
        ].join('\n')
    ).join('\n');
    const structuralBasis = [
        ...new Set(ordinary.examples.flatMap(
            example => example.structuralPrerequisites
        ))
    ].join(', ');

    return [
        'emdash v3.2 — external reviewer demonstration',
        `Candidate: ${result.candidate}`,
        `Input: ${result.construction}`,
        '',
        'Pipeline:',
        pipeline,
        '  (the Lambdapi oracle is optional and is not invoked here)',
        '',
        '=== 1. Outer dependent logical framework ===',
        'Input TypeScript:',
        indent(outer.surfaceInput),
        'Explicit locally nameless Core:',
        indent(outer.explicitCore),
        'Inferred type:',
        indent(outer.inferredType),
        'Reduced dependent type:',
        indent(outer.reducedType),
        `Computation: ${formatTrace(outer)}`,
        `Result: ${outer.reducedComputation}`,
        'Rejected wrong-family input:',
        indent(outer.negativeInput),
        `Diagnostic: ${outer.negativeDiagnostic.code} — ` +
            outer.negativeDiagnostic.summary,
        '',
        '=== 2. Ordinary functorial binding ===',
        `Input: ${pointwise.surfaceInput}`,
        `Inferred type: ${pointwise.inferredType}`,
        `Structural lowering: ${pointwise.structuralPrerequisites.join(', ')}`,
        `Also checked: ${diagonal.surfaceInput}`,
        `Also checked: ${exchange.surfaceInput}`,
        `Combined structural basis: ${structuralBasis}`,
        'Rejected wrong-category input:',
        indent(ordinary.negativeInput),
        `Diagnostic: ${ordinary.negativeDiagnostic.code} — ` +
            ordinary.negativeDiagnostic.message,
        '',
        '=== 3. Displayed dependent binding ===',
        `Telescope: ${displayed.telescope}`,
        displayedInputs,
        'Checked object/arrow behavior:',
        `  outer variable: ${displayed.computation.outerObjectStatus}`,
        `  dependent variable: ${displayed.computation.innerObjectStatus}`,
        `  recursive FF[a]: ${displayed.computation.recursiveObjectStatus}`,
        '  ignored dependent variable preserves arrow action: ' +
            displayed.computation.arrowIndependenceStatus,
        '  internalized arrow does not collapse: ' +
            displayed.computation.internalizedArrowNonCollapseStatus,
        `  reindexed result: ${displayed.computation.reindexedOutputKind}`,
        `  runtime rules exercised: ` +
            displayed.computation.runtimeRuleIds.length,
        '  existing displayed-chain profile owners/rules: ' +
            `${displayed.newLambdapiMathematicalOwnerCount}/` +
            displayed.newLambdapiRuntimeRuleCount,
        `Rejected wrong-base input: ${displayed.rejectedInput}`,
        `Diagnostic: ${displayed.negativeDiagnostic.code} — ` +
            displayed.negativeDiagnostic.message,
        '',
        'Product boundary:',
        '  new owners/rules/checker branches in this report: 0/0/0',
        '  string parser dependency: no',
        '  browser promotion: no',
        '  production Lambdapi dependency: no',
        '  supported: outer dependent LF, ordinary functorial brackets, ' +
            'one genuine displayed dependency edge',
        '  deferred: arbitrary displayed depth, general :^nd, user string ' +
            'syntax, browser promotion, groupoidal closure, whole-library ' +
            'transfer graduation',
        '',
        'Optional advanced higher-action witness:',
        `  ${result.advancedWitness.command}`
    ].join('\n');
}
