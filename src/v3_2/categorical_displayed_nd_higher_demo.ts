/**
 * Executable DISPLAYED-ND-HIGHER-TARGET-1A end-user demonstration.
 *
 * Input is the direct typed TypeScript construction API. The two new
 * constructors expose the rich category/action classifiers; ordinary
 * `hom`, `homBoundary`, and `apply` perform every action step.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_BOUNDARY,
    compileCoreCategoricalDisplayedNdHigherTargetTransfer
} from './categorical_displayed_nd_higher_target_transfer';
import {
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation
} from './categorical_program';
import {
    serializeCoreExpression
} from './core_serialization';

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_DEMO_REVISION =
    'DISPLAYED-ND-HIGHER-TARGET-1A-DEMO-1' as const;

export interface CoreCategoricalDisplayedNdHigherDemoResult {
    readonly revision:
        typeof CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_DEMO_REVISION;
    readonly candidate: 'emdash-v3.2-displayed-nd-higher-target-1a';
    readonly construction: 'direct-typescript-categorical-program';
    readonly surface: readonly [
        'H = displayedTransforInternalHomAction(FF,GG)',
        'H[epsilon]',
        'H[epsilon -> epsilonPrime]',
        'H[m]'
    ];
    readonly objectAction: CoreCategoricalProgramCompilation;
    readonly wholeHomAction: CoreCategoricalProgramCompilation;
    readonly higherCell: CoreCategoricalProgramCompilation;
    readonly normalizedObjectAction: string;
    readonly normalizedWholeHomAction: string;
    readonly runtimeProjectionRuleIds: readonly [
        'categorical.displayed-nd-higher.object-projection',
        'categorical.displayed-nd-higher.next-hom-projection'
    ];
    readonly higherCellType: 'hom';
    readonly newLambdapiMathematicalOwnerOrRule: false;
    readonly newIntrinsicOrCheckerBranch: false;
    readonly contextualIrOrBinderModeDelta: false;
    readonly stringParserDependency: false;
    readonly productionLambdapiDependency: false;
    readonly boundary:
        typeof CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_BOUNDARY;
}

export function runCoreCategoricalDisplayedNdHigherDemo():
CoreCategoricalDisplayedNdHigherDemoResult {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'examples/v3_2_categorical_displayed_nd_higher_demo.ts',
        profile: 'fibred-displayed-nd-higher-1'
    });
    const K = emdash.category('demo_K', { line: 1 });
    const E = emdash.displayedFamily('demo_E', K, { line: 2 });
    const D = emdash.displayedFamily('demo_D', K, { line: 3 });
    const FF = emdash.displayedFunctor('demo_FF', E, D, { line: 4 });
    const GG = emdash.displayedFunctor('demo_GG', E, D, { line: 5 });
    const epsilon = emdash.displayedTransfor(
        'demo_epsilon',
        FF,
        GG,
        { line: 6 }
    );
    const epsilonPrime = emdash.displayedTransfor(
        'demo_epsilon_prime',
        FF,
        GG,
        { line: 7 }
    );
    const transformationCategory = emdash.displayedTransforCategory(
        FF,
        GG,
        { line: 8 }
    );
    const m = emdash.hom(
        'demo_m',
        transformationCategory,
        epsilon,
        epsilonPrime,
        { line: 9 }
    );
    const action = emdash.displayedTransforInternalHomAction(
        FF,
        GG,
        { line: 10 }
    );
    const objectAction = emdash.apply(
        action,
        epsilon,
        {
            expectedShape: 'object-value',
            source: { line: 11 }
        }
    );
    const wholeHomAction = emdash.apply(
        action,
        emdash.homBoundary(
            transformationCategory,
            epsilon,
            epsilonPrime,
            { line: 12 }
        ),
        {
            expectedShape: 'whole-hom-action',
            source: { line: 12 }
        }
    );
    const higherCell = emdash.apply(
        wholeHomAction,
        m,
        {
            expectedShape: 'object-value',
            source: { line: 13 }
        }
    );
    const objectCompilation = emdash.compile(objectAction);
    const wholeHomCompilation = emdash.compile(wholeHomAction);
    const higherCellCompilation = emdash.compile(higherCell);
    if (higherCellCompilation.surfaceType.tag !== 'hom') {
        throw new Error(
            'DISPLAYED-ND-HIGHER consumer did not produce a higher cell'
        );
    }

    const transfer =
        compileCoreCategoricalDisplayedNdHigherTargetTransfer();
    const objectProjection = transfer.composedRuntime.rewriteHead(
        objectCompilation.explicitTerm
    );
    const nextHomProjection = transfer.composedRuntime.rewriteHead(
        wholeHomCompilation.explicitTerm
    );
    if (
        objectProjection.status !== 'rewritten' ||
        objectProjection.ruleId !==
            'categorical.displayed-nd-higher.object-projection' ||
        nextHomProjection.status !== 'rewritten' ||
        nextHomProjection.ruleId !==
            'categorical.displayed-nd-higher.next-hom-projection'
    ) {
        throw new Error(
            'DISPLAYED-ND-HIGHER generic action projections drifted'
        );
    }

    return Object.freeze({
        revision: CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_DEMO_REVISION,
        candidate:
            'emdash-v3.2-displayed-nd-higher-target-1a' as const,
        construction:
            'direct-typescript-categorical-program' as const,
        surface: Object.freeze([
            'H = displayedTransforInternalHomAction(FF,GG)',
            'H[epsilon]',
            'H[epsilon -> epsilonPrime]',
            'H[m]'
        ] as const),
        objectAction: objectCompilation,
        wholeHomAction: wholeHomCompilation,
        higherCell: higherCellCompilation,
        normalizedObjectAction:
            serializeCoreExpression(objectProjection.after),
        normalizedWholeHomAction:
            serializeCoreExpression(nextHomProjection.after),
        runtimeProjectionRuleIds: Object.freeze([
            'categorical.displayed-nd-higher.object-projection',
            'categorical.displayed-nd-higher.next-hom-projection'
        ] as const),
        higherCellType: 'hom' as const,
        newLambdapiMathematicalOwnerOrRule: false as const,
        newIntrinsicOrCheckerBranch: false as const,
        contextualIrOrBinderModeDelta: false as const,
        stringParserDependency: false as const,
        productionLambdapiDependency: false as const,
        boundary:
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_BOUNDARY
    });
}

export function formatCoreCategoricalDisplayedNdHigherDemo(
    result: CoreCategoricalDisplayedNdHigherDemoResult =
        runCoreCategoricalDisplayedNdHigherDemo()
): string {
    return [
        result.candidate,
        `Input path: ${result.construction}`,
        'Typed input:',
        ...result.surface.map(line => `  ${line}`),
        'Checked output:',
        `  object action: ${result.normalizedObjectAction}`,
        `  whole Hom action: ${result.normalizedWholeHomAction}`,
        `  H[m] classifier: ${result.higherCellType}`,
        'Runtime projections:',
        ...result.runtimeProjectionRuleIds.map(id => `  - ${id}`),
        'New Lambdapi mathematical owner/rule: no',
        'New intrinsic/checker branch: no',
        'String parser dependency: no',
        'Production Lambdapi dependency: no'
    ].join('\n');
}
