/**
 * Runnable end-user witness for one genuine non-eta dependent categorical
 * abstraction.
 *
 * The typed callback `λ k :^n K. FF[k](s[k])` is evaluated once, reified as
 * first-order locally nameless contextual data, lowered to generic
 * `comp_fapp0` in `Catd_cat K`, and checked by the TypeScript LF kernel.
 */

import {
    CoreCategoricalDiagnostic,
    CoreCategoricalProgram,
    coreCategoricalDiagnosticFromError
} from './categorical_program';

const demoPath =
    'src/v3_2/categorical_dependent_composition_demo.ts';

export interface CoreCategoricalDependentCompositionDemoResult {
    readonly candidate: 'emdash-v3.2-usability-dependent-1a';
    readonly construction: 'direct-typescript-categorical-program';
    readonly assumptions: readonly string[];
    readonly surfaceInput:
        'λ k :^n demo_K. demo_FF[k](demo_s[k])';
    readonly contextualBody:
        'indexed-fibre-functor.object(index=0)';
    readonly lowering:
        'generic comp_fapp0 at Catd_cat demo_K';
    readonly explicitCore: string;
    readonly inferredType: string;
    readonly expectedType: string;
    readonly pointwiseMeaning:
        'Fibre_func(demo_FF,k)[piapp0(demo_s,k)]';
    readonly dependentPrerequisites: readonly string[];
    readonly negativeInput:
        'demo_FF[k](demo_q[k]), where demo_q : Obj(Pi_cat demo_Q)';
    readonly negativeDiagnostic: CoreCategoricalDiagnostic;
    readonly newLambdapiMathematicalOwnerOrRule: false;
    readonly generalDependentBracketAvailable: false;
    readonly stringParserDependency: false;
    readonly productionLambdapiDependency: false;
}

export function runCoreCategoricalDependentCompositionDemo():
CoreCategoricalDependentCompositionDemoResult {
    const emdash = new CoreCategoricalProgram({
        sourceFile: demoPath,
        profile: 'usability-dependent-1a'
    });
    const K = emdash.category('demo_K', { line: 54 });
    const E = emdash.displayedFamily('demo_E', K, { line: 55 });
    const D = emdash.displayedFamily('demo_D', K, { line: 56 });
    const Q = emdash.displayedFamily('demo_Q', K, { line: 57 });
    const FF = emdash.displayedFunctor(
        'demo_FF',
        E,
        D,
        { line: 58 }
    );
    const s = emdash.section('demo_s', E, { line: 59 });
    const q = emdash.section('demo_q', Q, { line: 60 });

    const composed = emdash.dependentLambda(
        'k',
        D,
        k => emdash.apply(
            emdash.apply(FF, k, {
                expectedShape: 'fibre-functor',
                source: { line: 64, column: 29 }
            }),
            emdash.apply(s, k, {
                expectedShape: 'dependent-object',
                source: { line: 64, column: 40 }
            }),
            {
                expectedShape: 'object-value',
                source: { line: 64, column: 36 }
            }
        ),
        {
            variation: 'natural',
            dependency: 'displayed',
            source: { line: 64, column: 17 }
        }
    );
    const inspection = emdash.inspect(composed);
    const evidence = inspection.abstractions.at(-1);
    if (
        evidence?.rule !==
            'categorical.dependent-section-composition' ||
        evidence.body.tag !== 'typed-application'
    ) {
        throw new Error(
            'Dependent composition demo lost its contextual evidence'
        );
    }
    const compilation = emdash.compile(composed);

    let negativeDiagnostic: CoreCategoricalDiagnostic | undefined;
    try {
        emdash.dependentLambda(
            'k',
            D,
            k => emdash.apply(
                emdash.apply(FF, k, {
                    expectedShape: 'fibre-functor'
                }),
                emdash.apply(q, k, {
                    expectedShape: 'dependent-object'
                }),
                {
                    source: {
                        line: 91,
                        column: 9,
                        detail: 'wrong displayed source family'
                    }
                }
            )
        );
    } catch (error: unknown) {
        negativeDiagnostic =
            coreCategoricalDiagnosticFromError(error);
        if (negativeDiagnostic === undefined) throw error;
    }
    if (negativeDiagnostic === undefined) {
        throw new Error(
            'Dependent composition demo accepted a wrong source family'
        );
    }

    return Object.freeze({
        candidate: 'emdash-v3.2-usability-dependent-1a',
        construction: 'direct-typescript-categorical-program',
        assumptions: Object.freeze([
            'demo_K : Cat',
            'demo_E demo_D demo_Q : Catd demo_K',
            'demo_FF : Functord demo_E demo_D',
            'demo_s : Obj(Pi_cat demo_E)',
            'demo_q : Obj(Pi_cat demo_Q)'
        ]),
        surfaceInput:
            'λ k :^n demo_K. demo_FF[k](demo_s[k])',
        contextualBody:
            'indexed-fibre-functor.object(index=0)',
        lowering:
            'generic comp_fapp0 at Catd_cat demo_K',
        explicitCore: compilation.explicitCore,
        inferredType: compilation.explicitInferredType,
        expectedType: compilation.explicitExpectedType,
        pointwiseMeaning:
            'Fibre_func(demo_FF,k)[piapp0(demo_s,k)]',
        dependentPrerequisites: Object.freeze([
            ...compilation.dependentPrerequisites
        ]),
        negativeInput:
            'demo_FF[k](demo_q[k]), where demo_q : Obj(Pi_cat demo_Q)',
        negativeDiagnostic,
        newLambdapiMathematicalOwnerOrRule: false,
        generalDependentBracketAvailable: false,
        stringParserDependency: false,
        productionLambdapiDependency: false
    });
}

export function formatCoreCategoricalDependentCompositionDemo(
    result: CoreCategoricalDependentCompositionDemoResult =
        runCoreCategoricalDependentCompositionDemo()
): string {
    const assumptions = result.assumptions.map(
        assumption => `  - ${assumption}`
    ).join('\n');
    return [
        'emdash v3.2 dependent section-composition demo',
        `Candidate: ${result.candidate}`,
        `Input path: ${result.construction}`,
        '',
        'Assumptions:',
        assumptions,
        '',
        `Input: ${result.surfaceInput}`,
        `Contextual body: ${result.contextualBody}`,
        `Lowering: ${result.lowering}`,
        `Explicit Core: ${result.explicitCore}`,
        `Inferred type: ${result.inferredType}`,
        `Expected type: ${result.expectedType}`,
        `Pointwise meaning: ${result.pointwiseMeaning}`,
        'Dependent basis: ' +
            result.dependentPrerequisites.join(', '),
        '',
        'Rejected family mismatch:',
        `  ${result.negativeInput}`,
        `  ${result.negativeDiagnostic.code}: ` +
            result.negativeDiagnostic.message,
        '',
        'New Lambdapi mathematical owner/rule: no',
        'General dependent bracket abstraction: not yet',
        'String parser dependency: no',
        'Production Lambdapi dependency: no'
    ].join('\n');
}
