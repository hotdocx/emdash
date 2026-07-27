/**
 * Runnable end-user witness for one natural/indexed dependent section eta.
 *
 * The direct TypeScript callback is evaluated once, recorded as immutable
 * locally nameless contextual IR, eta-lowered to explicit Core, and checked by
 * the generic LF checker. This is deliberately not a general dependent
 * bracket-abstraction claim.
 */

import {
    CoreCategoricalDiagnostic,
    CoreCategoricalProgram,
    coreCategoricalDiagnosticFromError,
    serializeCoreCategoricalExpression
} from './categorical_program';

const demoPath = 'src/v3_2/categorical_dependent_eta_demo.ts';

export interface CoreCategoricalDependentEtaDemoResult {
    readonly candidate: 'emdash-v3.2-usability-2a1';
    readonly construction: 'direct-typescript-categorical-program';
    readonly assumptions: readonly string[];
    readonly surfaceInput: 'λ k :^n demo_K. demo_s[k]';
    readonly contextualClassifier: {
        readonly tag: 'indexed-object';
        readonly baseCategory: string;
        readonly family: string;
        readonly index: 0;
    };
    readonly explicitCore: string;
    readonly inferredType: string;
    readonly expectedType: string;
    readonly dependentPrerequisites: readonly string[];
    readonly negativeInput:
        'demo_s[demo_p], where demo_p : Hom demo_K demo_x demo_y';
    readonly negativeDiagnostic: CoreCategoricalDiagnostic;
    readonly generalDependentBracketAvailable: false;
    readonly stringParserDependency: false;
    readonly productionLambdapiDependency: false;
}

/**
 * Construct, lower, and check the representative dependent eta.
 */
export function runCoreCategoricalDependentEtaDemo():
CoreCategoricalDependentEtaDemoResult {
    const emdash = new CoreCategoricalProgram({
        sourceFile: demoPath
    });
    const K = emdash.category('demo_K', { line: 48 });
    const E = emdash.displayedFamily('demo_E', K, { line: 49 });
    const x = emdash.object('demo_x', K, { line: 50 });
    const y = emdash.object('demo_y', K, { line: 51 });
    const p = emdash.hom('demo_p', K, x, y, { line: 52 });
    const s = emdash.section('demo_s', E, { line: 53 });

    const eta = emdash.dependentLambda(
        'k',
        E,
        k => emdash.apply(s, k, {
            expectedShape: 'dependent-object',
            source: { line: 59, column: 29 }
        }),
        {
            variation: 'natural',
            dependency: 'displayed',
            source: { line: 59, column: 17 }
        }
    );
    const inspection = emdash.inspect(eta);
    const compilation = emdash.compile(eta);
    const evidence = inspection.abstractions.at(-1);
    if (
        evidence?.rule !== 'categorical.dependent-eta' ||
        evidence.body.type.tag !== 'indexed-object'
    ) {
        throw new Error(
            'Dependent eta demo lost its indexed abstraction evidence'
        );
    }

    let negativeDiagnostic: CoreCategoricalDiagnostic | undefined;
    try {
        emdash.apply(s, p, {
            expectedShape: 'dependent-arrow',
            source: {
                line: 82,
                column: 9,
                detail: 'first untransferred section-arrow action'
            }
        });
    } catch (error: unknown) {
        negativeDiagnostic =
            coreCategoricalDiagnosticFromError(error);
        if (negativeDiagnostic === undefined) throw error;
    }
    if (negativeDiagnostic === undefined) {
        throw new Error(
            'Dependent eta demo unexpectedly accepted section-arrow action'
        );
    }

    return Object.freeze({
        candidate: 'emdash-v3.2-usability-2a1',
        construction: 'direct-typescript-categorical-program',
        assumptions: Object.freeze([
            'demo_K : Cat',
            'demo_E : Catd demo_K',
            'demo_s : Obj (Pi_cat demo_E)',
            'demo_p : Hom demo_K demo_x demo_y'
        ]),
        surfaceInput: 'λ k :^n demo_K. demo_s[k]',
        contextualClassifier: Object.freeze({
            tag: 'indexed-object',
            baseCategory: serializeCoreCategoricalExpression(
                evidence.body.type.baseCategory
            ),
            family: serializeCoreCategoricalExpression(
                evidence.body.type.family
            ),
            index: 0
        }),
        explicitCore: compilation.explicitCore,
        inferredType: compilation.explicitInferredType,
        expectedType: compilation.explicitExpectedType,
        dependentPrerequisites: Object.freeze([
            ...compilation.dependentPrerequisites
        ]),
        negativeInput:
            'demo_s[demo_p], where demo_p : Hom demo_K demo_x demo_y',
        negativeDiagnostic,
        generalDependentBracketAvailable: false,
        stringParserDependency: false,
        productionLambdapiDependency: false
    });
}

export function formatCoreCategoricalDependentEtaDemo(
    result: CoreCategoricalDependentEtaDemoResult =
        runCoreCategoricalDependentEtaDemo()
): string {
    const assumptions = result.assumptions.map(
        assumption => `  - ${assumption}`
    ).join('\n');
    return [
        'emdash v3.2 dependent categorical eta demo',
        `Candidate: ${result.candidate}`,
        `Input path: ${result.construction}`,
        '',
        'Assumptions:',
        assumptions,
        '',
        `Input: ${result.surfaceInput}`,
        'Contextual classifier: ' +
            `${result.contextualClassifier.tag}` +
            `(base=${result.contextualClassifier.baseCategory}, ` +
            `family=${result.contextualClassifier.family}, ` +
            `index=${result.contextualClassifier.index})`,
        `Explicit Core: ${result.explicitCore}`,
        `Inferred type: ${result.inferredType}`,
        `Expected type: ${result.expectedType}`,
        'Dependent basis: ' +
            result.dependentPrerequisites.join(', '),
        '',
        'Rejected next structural action:',
        `  ${result.negativeInput}`,
        `  ${result.negativeDiagnostic.code}: ` +
            result.negativeDiagnostic.message,
        '',
        'General dependent bracket abstraction: not yet',
        'String parser dependency: no',
        'Production Lambdapi dependency: no'
    ].join('\n');
}
