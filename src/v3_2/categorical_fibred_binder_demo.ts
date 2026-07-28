/**
 * Executable end-user demonstration of FIBRED-BINDER-1.
 *
 * Surface strings document the intended notation. The actual input is the
 * direct typed TypeScript API; no string parser or production Lambdapi
 * process participates.
 */

import {
    CORE_CATEGORICAL_FIBRED_BINDER_TRANSFER_BOUNDARY
} from './categorical_fibred_binder_transfer';
import {
    CoreCategoricalDiagnostic,
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation,
    coreCategoricalDiagnosticFromError
} from './categorical_program';
import {
    CoreLfComparisonResult
} from './lf_conversion';

export const CORE_CATEGORICAL_FIBRED_BINDER_DEMO_REVISION =
    'FIBRED-BINDER-1-DEMO-1' as const;

export interface CoreCategoricalFibredBinderDemoExample {
    readonly id: 'identity' | 'eta' | 'composition';
    readonly surface: string;
    readonly compilation: CoreCategoricalProgramCompilation;
}

export interface CoreCategoricalFibredBinderDemoResult {
    readonly revision:
        typeof CORE_CATEGORICAL_FIBRED_BINDER_DEMO_REVISION;
    readonly candidate: 'emdash-v3.2-fibred-binder-1';
    readonly construction: 'direct-typescript-categorical-program';
    readonly assumptions: readonly string[];
    readonly examples:
        readonly CoreCategoricalFibredBinderDemoExample[];
    readonly hiddenTelescope:
        'k :^n demo_K; a :^f demo_E[k]';
    readonly compositionPoint: {
        readonly input:
            '(λ a :^fd demo_E. demo_GG[demo_FF[a]])[demo_x][demo_u]';
        readonly output:
            'demo_GG[demo_x](demo_FF[demo_x](demo_u))';
        readonly status: 'equal';
        readonly runtimeRuleIds: readonly string[];
    };
    readonly classifierCompatibility: {
        readonly direct: string;
        readonly nested: string;
        readonly proofTime: 'solved';
        readonly runtime: 'not-equal';
        readonly proofRuleId: 'stress.sigma-pi.uncurrying';
    };
    readonly negativeInput:
        'λ a :^fd demo_E. a : Functord(demo_E,demo_D)';
    readonly negativeDiagnostic: CoreCategoricalDiagnostic;
    readonly newLambdapiMathematicalOwnerOrRule: false;
    readonly stringParserDependency: false;
    readonly productionLambdapiDependency: false;
    readonly boundary:
        typeof CORE_CATEGORICAL_FIBRED_BINDER_TRANSFER_BOUNDARY;
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

export function runCoreCategoricalFibredBinderDemo():
CoreCategoricalFibredBinderDemoResult {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'examples/v3_2_categorical_fibred_binder_demo.ts',
        profile: 'fibred-binder-1'
    });
    const K = emdash.category('demo_K', { line: 64 });
    const E = emdash.displayedFamily('demo_E', K, { line: 65 });
    const D = emdash.displayedFamily('demo_D', K, { line: 66 });
    const Q = emdash.displayedFamily('demo_Q', K, { line: 67 });
    const FF = emdash.displayedFunctor(
        'demo_FF',
        E,
        D,
        { line: 68 }
    );
    const GG = emdash.displayedFunctor(
        'demo_GG',
        D,
        Q,
        { line: 69 }
    );

    const identity = emdash.displayedFunctorLambda(
        'a',
        E,
        E,
        a => a,
        { source: { line: 72 } }
    );
    const eta = emdash.displayedFunctorLambda(
        'a',
        E,
        D,
        a => emdash.apply(FF, a, {
            expectedShape: 'object-value',
            source: { line: 77 }
        }),
        { source: { line: 76 } }
    );
    const composition = emdash.displayedFunctorLambda(
        'a',
        E,
        Q,
        a => emdash.apply(
            GG,
            emdash.apply(FF, a, {
                expectedShape: 'object-value'
            }),
            { expectedShape: 'object-value' }
        ),
        { source: { line: 84 } }
    );

    const x = emdash.object('demo_x', K, { line: 92 });
    const u = emdash.object(
        'demo_u',
        emdash.fibre(E, x),
        { line: 93 }
    );
    const computed = emdash.apply(
        emdash.apply(composition, x, {
            expectedShape: 'fibre-functor'
        }),
        u
    );
    const expected = emdash.apply(
        emdash.apply(GG, x, {
            expectedShape: 'fibre-functor'
        }),
        emdash.apply(
            emdash.apply(FF, x, {
                expectedShape: 'fibre-functor'
            }),
            u
        )
    );
    const pointComparison = emdash.compare(
        computed,
        expected,
        8_000
    );
    if (pointComparison.status !== 'equal') {
        throw new Error(
            'FIBRED-BINDER-1 composition point did not compute'
        );
    }

    const compatibility =
        emdash.displayedFunctorClassifierCompatibility(
            E,
            D,
            2_000,
            { line: 112 }
        );
    if (
        compatibility.proofTime.status !== 'solved' ||
        compatibility.runtime.status !== 'not-equal' ||
        compatibility.proofTime.ruleApplications[0]?.ruleId !==
            'stress.sigma-pi.uncurrying'
    ) {
        throw new Error(
            'FIBRED-BINDER-1 classifier boundary drifted'
        );
    }

    let negativeDiagnostic: CoreCategoricalDiagnostic | undefined;
    try {
        emdash.displayedFunctorLambda(
            'a',
            E,
            D,
            a => a,
            {
                source: {
                    line: 128,
                    detail: 'wrong direct displayed target'
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
            'FIBRED-BINDER-1 accepted a wrong identity target'
        );
    }

    return Object.freeze({
        revision: CORE_CATEGORICAL_FIBRED_BINDER_DEMO_REVISION,
        candidate: 'emdash-v3.2-fibred-binder-1',
        construction: 'direct-typescript-categorical-program',
        assumptions: Object.freeze([
            'demo_K : Cat',
            'demo_E demo_D demo_Q : Catd demo_K',
            'demo_FF : Functord demo_E demo_D',
            'demo_GG : Functord demo_D demo_Q',
            'demo_x : Obj demo_K',
            'demo_u : Obj demo_E[demo_x]'
        ]),
        examples: Object.freeze([
            Object.freeze({
                id: 'identity' as const,
                surface: 'λ a :^fd demo_E. a',
                compilation: emdash.compile(identity)
            }),
            Object.freeze({
                id: 'eta' as const,
                surface: 'λ a :^fd demo_E. demo_FF[a]',
                compilation: emdash.compile(eta)
            }),
            Object.freeze({
                id: 'composition' as const,
                surface:
                    'λ a :^fd demo_E. demo_GG[demo_FF[a]]',
                compilation: emdash.compile(composition)
            })
        ]),
        hiddenTelescope:
            'k :^n demo_K; a :^f demo_E[k]',
        compositionPoint: Object.freeze({
            input:
                '(λ a :^fd demo_E. demo_GG[demo_FF[a]])[demo_x][demo_u]',
            output:
                'demo_GG[demo_x](demo_FF[demo_x](demo_u))',
            status: 'equal' as const,
            runtimeRuleIds: runtimeRuleIds(pointComparison)
        }),
        classifierCompatibility: Object.freeze({
            direct: compatibility.explicitDirectClassifier,
            nested: compatibility.explicitNestedClassifier,
            proofTime: 'solved' as const,
            runtime: 'not-equal' as const,
            proofRuleId: 'stress.sigma-pi.uncurrying' as const
        }),
        negativeInput:
            'λ a :^fd demo_E. a : Functord(demo_E,demo_D)',
        negativeDiagnostic,
        newLambdapiMathematicalOwnerOrRule: false,
        stringParserDependency: false,
        productionLambdapiDependency: false,
        boundary:
            CORE_CATEGORICAL_FIBRED_BINDER_TRANSFER_BOUNDARY
    });
}

export function formatCoreCategoricalFibredBinderDemo(
    result: CoreCategoricalFibredBinderDemoResult =
        runCoreCategoricalFibredBinderDemo()
): string {
    const assumptions = result.assumptions.map(
        assumption => `  - ${assumption}`
    ).join('\n');
    const examples = result.examples.map(example => [
        `  ${example.id}: ${example.surface}`,
        `    Core: ${example.compilation.explicitCore}`,
        `    Type: ${example.compilation.explicitExpectedType}`
    ].join('\n')).join('\n');
    return [
        result.candidate,
        `Input path: ${result.construction}`,
        '',
        'Assumptions:',
        assumptions,
        '',
        'Direct displayed-functor inputs:',
        examples,
        '',
        `Hidden telescope: ${result.hiddenTelescope}`,
        `Computed input: ${result.compositionPoint.input}`,
        `Computed output: ${result.compositionPoint.output}`,
        'Point computation: equal via ' +
            result.compositionPoint.runtimeRuleIds.join(', '),
        '',
        'Classifier presentations:',
        `  direct: ${result.classifierCompatibility.direct}`,
        `  nested: ${result.classifierCompatibility.nested}`,
        '  proof-time comparison: solved via ' +
            result.classifierCompatibility.proofRuleId,
        '  runtime conversion: not-equal (presentations preserved)',
        '',
        'Rejected input:',
        `  ${result.negativeInput}`,
        `  ${result.negativeDiagnostic.code}: ` +
            result.negativeDiagnostic.message,
        '',
        'New Lambdapi mathematical owner/rule: no',
        'String parser dependency: no',
        'Production Lambdapi dependency: no'
    ].join('\n');
}
