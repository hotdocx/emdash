/**
 * Runnable end-user witness for ordinary categorical bracket abstraction.
 *
 * The input is direct typed TypeScript. The ergonomic facade lowers each
 * callback once to first-order contextual IR, compiles structural wiring to
 * backend-neutral explicit Core, and checks it with the generic LF checker.
 */

import {
    CoreCategoricalDiagnostic,
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation,
    coreCategoricalDiagnosticFromError
} from './categorical_program';

const demoPath = 'src/v3_2/categorical_bracket_demo.ts';

export interface CoreCategoricalBracketDemoExample {
    readonly name: 'pointwise-application' | 'diagonal' | 'exchange';
    readonly surfaceInput: string;
    readonly explicitCore: string;
    readonly inferredType: string;
    readonly structuralPrerequisites: readonly string[];
}

export interface CoreCategoricalBracketDemoResult {
    readonly candidate: 'emdash-v3.2-usability-1d';
    readonly construction: 'direct-typescript-categorical-program';
    readonly assumptions: readonly string[];
    readonly examples: readonly CoreCategoricalBracketDemoExample[];
    readonly negativeInput: string;
    readonly negativeDiagnostic: CoreCategoricalDiagnostic;
    readonly stringParserDependency: false;
    readonly productionLambdapiDependency: false;
}

const example = (
    name: CoreCategoricalBracketDemoExample['name'],
    surfaceInput: string,
    compilation: CoreCategoricalProgramCompilation
): CoreCategoricalBracketDemoExample => Object.freeze({
    name,
    surfaceInput,
    explicitCore: compilation.explicitCore,
    inferredType: compilation.explicitInferredType,
    structuralPrerequisites: Object.freeze([
        ...compilation.structuralPrerequisites
    ])
});

/**
 * Construct and check the representative ordinary categorical corpus.
 */
export function runCoreCategoricalBracketDemo():
CoreCategoricalBracketDemoResult {
    const emdash = new CoreCategoricalProgram({
        sourceFile: demoPath
    });
    const A = emdash.category('demo_A', { line: 59 });
    const B = emdash.category('demo_B', { line: 60 });
    const C = emdash.category('demo_C', { line: 61 });
    const functorsBC = emdash.functorCategory(B, C, { line: 62 });
    const functorsAC = emdash.functorCategory(A, C, { line: 63 });
    const H = emdash.functor(
        'demo_H',
        A,
        functorsBC,
        { line: 64 }
    );
    const K = emdash.functor('demo_K', A, B, { line: 70 });
    const D = emdash.functor(
        'demo_D',
        A,
        functorsAC,
        { line: 71 }
    );
    const E = emdash.functor(
        'demo_E',
        B,
        functorsAC,
        { line: 77 }
    );

    const pointwiseTerm = emdash.lambda(
        'x',
        A,
        C,
        x => emdash.apply(
            emdash.apply(H, x, {
                source: { line: 89, column: 13 }
            }),
            emdash.apply(K, x, {
                source: { line: 92, column: 13 }
            }),
            { source: { line: 88, column: 14 } }
        ),
        { source: { line: 84, column: 27 } }
    );
    const diagonalTerm = emdash.lambda(
        'x',
        A,
        C,
        x => emdash.apply(
            emdash.apply(D, x, {
                source: { line: 104, column: 13 }
            }),
            x,
            { source: { line: 103, column: 14 } }
        ),
        { source: { line: 99, column: 26 } }
    );
    const exchangeTerm = emdash.lambda(
        'x',
        A,
        functorsBC,
        x => emdash.lambda(
            'y',
            B,
            C,
            y => emdash.apply(
                emdash.apply(E, y, {
                    source: { line: 121, column: 17 }
                }),
                x,
                { source: { line: 120, column: 18 } }
            ),
            { source: { line: 116, column: 22 } }
        ),
        { source: { line: 112, column: 26 } }
    );

    const examples = Object.freeze([
        example(
            'pointwise-application',
            'λ x :^f demo_A. (demo_H x) (demo_K x)',
            emdash.compile(pointwiseTerm)
        ),
        example(
            'diagonal',
            'λ x :^f demo_A. (demo_D x) x',
            emdash.compile(diagonalTerm)
        ),
        example(
            'exchange',
            'λ x :^f demo_A. λ y :^f demo_B. (demo_E y) x',
            emdash.compile(exchangeTerm)
        )
    ]);

    const wrongObject = emdash.object(
        'demo_wrong_c',
        C,
        { line: 150 }
    );
    let negativeDiagnostic: CoreCategoricalDiagnostic | undefined;
    try {
        emdash.apply(K, wrongObject, {
            source: {
                line: 157,
                column: 9,
                detail:
                    'demo_K applied to a demo_C object instead of demo_A'
            }
        });
    } catch (error: unknown) {
        negativeDiagnostic =
            coreCategoricalDiagnosticFromError(error);
        if (negativeDiagnostic === undefined) throw error;
    }
    if (negativeDiagnostic === undefined) {
        throw new Error(
            'Categorical bracket demo unexpectedly accepted a ' +
            'wrong-category argument'
        );
    }

    return Object.freeze({
        candidate: 'emdash-v3.2-usability-1d',
        construction: 'direct-typescript-categorical-program',
        assumptions: Object.freeze([
            'demo_A, demo_B, demo_C : Cat',
            'demo_H : Functor demo_A (Functor_cat demo_B demo_C)',
            'demo_K : Functor demo_A demo_B',
            'demo_D : Functor demo_A (Functor_cat demo_A demo_C)',
            'demo_E : Functor demo_B (Functor_cat demo_A demo_C)'
        ]),
        examples,
        negativeInput:
            'demo_K demo_wrong_c, where demo_wrong_c : Obj demo_C',
        negativeDiagnostic,
        stringParserDependency: false,
        productionLambdapiDependency: false
    });
}

export function formatCoreCategoricalBracketDemo(
    result: CoreCategoricalBracketDemoResult =
        runCoreCategoricalBracketDemo()
): string {
    const assumptions = result.assumptions.map(
        assumption => `  - ${assumption}`
    ).join('\n');
    const examples = result.examples.map((entry, index) => [
        `${index + 1}. ${entry.name}`,
        `   input: ${entry.surfaceInput}`,
        `   explicit Core: ${entry.explicitCore}`,
        `   inferred type: ${entry.inferredType}`,
        '   structural basis: ' +
            entry.structuralPrerequisites.join(', ')
    ].join('\n')).join('\n\n');
    return [
        'emdash v3.2 categorical bracket demo',
        `Candidate: ${result.candidate}`,
        `Input path: ${result.construction}`,
        '',
        'Assumptions:',
        assumptions,
        '',
        'Checked examples:',
        examples,
        '',
        'Rejected wrong-category input:',
        `  ${result.negativeInput}`,
        `  ${result.negativeDiagnostic.code}: ` +
            result.negativeDiagnostic.message,
        '',
        'String parser dependency: no',
        'Production Lambdapi dependency: no'
    ].join('\n');
}
