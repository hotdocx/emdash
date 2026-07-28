/**
 * Executable end-user demonstration of FIBRED-WEAKEN-REINDEX-1.
 *
 * The displayed notation is explanatory. The executable input is the direct
 * typed TypeScript API; no string parser or production Lambdapi process is
 * involved.
 */

import {
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_BOUNDARY
} from './categorical_fibred_weaken_reindex_transfer';
import {
    CoreCategoricalDiagnostic,
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation,
    coreCategoricalDiagnosticFromError
} from './categorical_program';
import {
    CoreLfComparisonResult
} from './lf_conversion';

export const CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_DEMO_REVISION =
    'FIBRED-WEAKEN-REINDEX-1-DEMO-1' as const;

const runtimeRuleIds = (
    result: CoreLfComparisonResult
): readonly string[] => Object.freeze(
    result.trace.flatMap(entry =>
        entry.reduction.kind === 'runtime'
            ? [entry.reduction.ruleId]
            : []
    )
);

const WEAKENING_POINT_INPUT =
    '(λ a :^fd demo_E. demo_s[indexOf(a)])' +
    '[demo_k][demo_a]';

export interface CoreCategoricalFibredWeakenReindexDemoResult {
    readonly revision:
        typeof CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_DEMO_REVISION;
    readonly candidate: 'emdash-v3.2-fibred-weaken-reindex-1';
    readonly construction: 'direct-typescript-categorical-program';
    readonly assumptions: readonly string[];
    readonly weakening: {
        readonly input:
            'λ a :^fd demo_E. demo_s[indexOf(a)]';
        readonly lowering: CoreCategoricalProgramCompilation;
        readonly pointInput: typeof WEAKENING_POINT_INPUT;
        readonly pointOutput: 'demo_s[demo_k]';
        readonly pointStatus: 'equal';
        readonly termTypeChecking: 'runtime-object-classifier-join';
        readonly classifierBridge: {
            readonly runtime: 'not-equal';
            readonly proofTime: 'solved';
            readonly proofRuleId:
                'stress.sigma-pi.uncurrying';
        };
    };
    readonly reindexing: {
        readonly input: 'demo_sigma^*demo_FF';
        readonly lowering: CoreCategoricalProgramCompilation;
        readonly pointInput:
            '(demo_sigma^*demo_FF)[demo_x]';
        readonly pointOutput:
            'demo_FF[demo_sigma[demo_x]]';
        readonly pointStatus: 'equal';
        readonly runtimeRuleIds: readonly string[];
        readonly abstractionBeforeAfterCoreEqual: true;
    };
    readonly negativeDiagnostic: CoreCategoricalDiagnostic;
    readonly newLambdapiMathematicalOwnerOrRule: false;
    readonly stringParserDependency: false;
    readonly productionLambdapiDependency: false;
    readonly boundary:
        typeof CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_BOUNDARY;
}

export function runCoreCategoricalFibredWeakenReindexDemo():
CoreCategoricalFibredWeakenReindexDemoResult {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'examples/v3_2_categorical_fibred_weaken_reindex_demo.ts',
        profile: 'fibred-weaken-reindex-1'
    });
    const K = emdash.category('demo_K', { line: 1 });
    const L = emdash.category('demo_L', { line: 2 });
    const E = emdash.displayedFamily('demo_E', K, { line: 3 });
    const D = emdash.displayedFamily('demo_D', K, { line: 4 });
    const sigma = emdash.functor('demo_sigma', L, K, { line: 5 });
    const FF = emdash.displayedFunctor(
        'demo_FF',
        E,
        D,
        { line: 6 }
    );
    const s = emdash.section('demo_s', D, { line: 7 });

    const weakened = emdash.displayedFunctorLambda(
        'a',
        E,
        D,
        a => emdash.apply(s, emdash.indexOf(a)),
        { source: { line: 10 } }
    );
    const weakeningCompilation = emdash.compile(weakened);
    const classifierCompatibility =
        emdash.displayedFunctorClassifierCompatibility(E, D);
    if (
        classifierCompatibility.runtime.status !== 'not-equal' ||
        classifierCompatibility.proofTime.status !== 'solved' ||
        classifierCompatibility.proofTime
            .ruleApplications[0]?.ruleId !==
                'stress.sigma-pi.uncurrying'
    ) {
        throw new Error('Displayed weakening classifier bridge drifted');
    }
    const k = emdash.object('demo_k', K, { line: 11 });
    const a = emdash.object(
        'demo_a',
        emdash.fibre(E, k),
        { line: 12 }
    );
    const weakenedPoint = emdash.apply(
        emdash.apply(weakened, k, {
            expectedShape: 'fibre-functor'
        }),
        a
    );
    const directPoint = emdash.apply(s, k, {
        expectedShape: 'dependent-object'
    });
    if (
        emdash.compile(weakenedPoint).explicitCore !==
            emdash.compile(directPoint).explicitCore
    ) {
        throw new Error('Displayed weakening point did not lower to s[k]');
    }

    const pulled = emdash.pullbackDisplayedFunctor(FF, sigma);
    const reindexCompilation = emdash.compile(pulled);
    const x = emdash.object('demo_x', L, { line: 20 });
    const pulledAt = emdash.apply(pulled, x, {
        expectedShape: 'fibre-functor'
    });
    const directAt = emdash.apply(
        FF,
        emdash.apply(sigma, x),
        { expectedShape: 'fibre-functor' }
    );
    const reindexComparison = emdash.compare(
        pulledAt,
        directAt,
        4_000
    );
    if (reindexComparison.status !== 'equal') {
        throw new Error('Displayed reindexing point did not compute');
    }

    const before = emdash.pullbackDisplayedFunctor(
        emdash.displayedFunctorLambda(
            'a',
            E,
            D,
            a0 => emdash.apply(FF, a0)
        ),
        sigma
    );
    const pulledE = emdash.pullbackFamily(E, sigma);
    const pulledD = emdash.pullbackFamily(D, sigma);
    const after = emdash.displayedFunctorLambda(
        'a',
        pulledE,
        pulledD,
        a0 => emdash.apply(pulled, a0)
    );
    if (
        emdash.compile(before).explicitCore !==
            emdash.compile(after).explicitCore
    ) {
        throw new Error(
            'Displayed reindexing did not commute with direct eta'
        );
    }

    let negativeDiagnostic: CoreCategoricalDiagnostic | undefined;
    try {
        emdash.pullbackDisplayedFunctor(
            FF,
            emdash.functor('demo_wrong', L, L)
        );
    } catch (error: unknown) {
        negativeDiagnostic =
            coreCategoricalDiagnosticFromError(error);
        if (negativeDiagnostic === undefined) throw error;
    }
    if (negativeDiagnostic === undefined) {
        throw new Error('Wrong-base displayed reindexing was accepted');
    }

    return Object.freeze({
        revision:
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_DEMO_REVISION,
        candidate: 'emdash-v3.2-fibred-weaken-reindex-1',
        construction: 'direct-typescript-categorical-program',
        assumptions: Object.freeze([
            'demo_K demo_L : Cat',
            'demo_E demo_D : Catd demo_K',
            'demo_sigma : demo_L ⊢ demo_K',
            'demo_FF : Functord demo_E demo_D',
            'demo_s : Π k :^n demo_K, demo_D[k]'
        ]),
        weakening: Object.freeze({
            input:
                'λ a :^fd demo_E. demo_s[indexOf(a)]',
            lowering: weakeningCompilation,
            pointInput: WEAKENING_POINT_INPUT,
            pointOutput: 'demo_s[demo_k]',
            pointStatus: 'equal' as const,
            termTypeChecking:
                'runtime-object-classifier-join' as const,
            classifierBridge: Object.freeze({
                runtime: 'not-equal' as const,
                proofTime: 'solved' as const,
                proofRuleId:
                    'stress.sigma-pi.uncurrying' as const
            })
        }),
        reindexing: Object.freeze({
            input: 'demo_sigma^*demo_FF',
            lowering: reindexCompilation,
            pointInput: '(demo_sigma^*demo_FF)[demo_x]',
            pointOutput: 'demo_FF[demo_sigma[demo_x]]',
            pointStatus: 'equal' as const,
            runtimeRuleIds: runtimeRuleIds(reindexComparison),
            abstractionBeforeAfterCoreEqual: true as const
        }),
        negativeDiagnostic,
        newLambdapiMathematicalOwnerOrRule: false,
        stringParserDependency: false,
        productionLambdapiDependency: false,
        boundary:
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_BOUNDARY
    });
}

export function formatCoreCategoricalFibredWeakenReindexDemo(
    result: CoreCategoricalFibredWeakenReindexDemoResult =
        runCoreCategoricalFibredWeakenReindexDemo()
): string {
    return [
        result.candidate,
        `Input path: ${result.construction}`,
        '',
        'Weakening:',
        `  Input: ${result.weakening.input}`,
        `  Core: ${result.weakening.lowering.explicitCore}`,
        `  Point: ${result.weakening.pointInput}`,
        `      ↦ ${result.weakening.pointOutput}`,
        `  Term type checking: ${result.weakening.termTypeChecking}`,
        '  Category classifier runtime: ' +
            result.weakening.classifierBridge.runtime,
        '  Category classifier proof time: ' +
            result.weakening.classifierBridge.proofTime +
            ' via ' +
            result.weakening.classifierBridge.proofRuleId,
        '',
        'Displayed reindexing:',
        `  Input: ${result.reindexing.input}`,
        `  Core: ${result.reindexing.lowering.explicitCore}`,
        `  Point: ${result.reindexing.pointInput}`,
        `      ↦ ${result.reindexing.pointOutput}`,
        '  Runtime: ' + result.reindexing.runtimeRuleIds.join(', '),
        '  Reindex before/after direct eta: identical explicit Core',
        '',
        'Rejected wrong-base input:',
        `  ${result.negativeDiagnostic.code}: ` +
            result.negativeDiagnostic.message,
        '',
        'New Lambdapi mathematical owner/rule: no',
        'String parser dependency: no',
        'Production Lambdapi dependency: no'
    ].join('\n');
}
