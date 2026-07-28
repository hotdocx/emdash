/**
 * Executable end-user demonstration of FIBRED-TRANSFD-1.
 *
 * Surface strings document the intended notation. Actual input is the direct
 * typed TypeScript API; neither a string parser nor a production Lambdapi
 * process participates.
 */

import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
} from './categorical_fibred_transfd_transfer';
import {
    CoreCategoricalDiagnostic,
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation,
    coreCategoricalDiagnosticFromError
} from './categorical_program';

export const CORE_CATEGORICAL_FIBRED_TRANSFD_DEMO_REVISION =
    'FIBRED-TRANSFD-1-DEMO-1' as const;

export interface CoreCategoricalFibredTransfdDemoExample {
    readonly id:
        | 'coherent-eta'
        | 'fibre-component'
        | 'point-component'
        | 'higher-cell'
        | 'composite-component';
    readonly surface: string;
    readonly compilation: CoreCategoricalProgramCompilation;
}

export interface CoreCategoricalFibredTransfdDemoResult {
    readonly revision:
        typeof CORE_CATEGORICAL_FIBRED_TRANSFD_DEMO_REVISION;
    readonly candidate: 'emdash-v3.2-fibred-transfd-1';
    readonly construction: 'direct-typescript-categorical-program';
    readonly assumptions: readonly string[];
    readonly examples:
        readonly CoreCategoricalFibredTransfdDemoExample[];
    readonly coherentAbstraction: {
        readonly input: 'λ k :^nd demo_K. demo_eta[k]';
        readonly output: 'demo_eta';
        readonly callbackCount: 1;
        readonly status: 'equal';
    };
    readonly classifierCompatibility: {
        readonly direct: string;
        readonly ordinaryNextHom: string;
        readonly sigmaPiNextHom: string;
        readonly directOrdinaryRuntime: 'not-equal';
        readonly directOrdinaryProofTime: 'solved';
        readonly directOrdinaryObjectRuntime: 'equal';
        readonly directSigmaPiRuntime: 'equal';
        readonly proofRuleId:
            'categorical.transfd.direct-second-hom';
    };
    readonly verticalComponentRuntimeRuleIds:
        readonly string[];
    readonly negativeInput:
        'λ k :^nd demo_K. demo_eta';
    readonly negativeDiagnostic: CoreCategoricalDiagnostic;
    readonly newLambdapiMathematicalOwnerOrRule: false;
    readonly stringParserDependency: false;
    readonly productionLambdapiDependency: false;
    readonly boundary:
        typeof CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY;
}

export function runCoreCategoricalFibredTransfdDemo():
CoreCategoricalFibredTransfdDemoResult {
    const emdash = new CoreCategoricalProgram({
        sourceFile:
            'examples/v3_2_categorical_fibred_transfd_demo.ts',
        profile: 'fibred-transfd-1'
    });
    const K = emdash.category('demo_K', { line: 1 });
    const E = emdash.displayedFamily('demo_E', K, { line: 2 });
    const D = emdash.displayedFamily('demo_D', K, { line: 3 });
    const FF = emdash.displayedFunctor(
        'demo_FF',
        E,
        D,
        { line: 4 }
    );
    const GG = emdash.displayedFunctor(
        'demo_GG',
        E,
        D,
        { line: 5 }
    );
    const HH = emdash.displayedFunctor(
        'demo_HH',
        E,
        D,
        { line: 6 }
    );
    const eta = emdash.displayedTransfor(
        'demo_eta',
        FF,
        GG,
        { line: 7 }
    );
    const theta = emdash.displayedTransfor(
        'demo_theta',
        GG,
        HH,
        { line: 8 }
    );
    const x = emdash.object('demo_x', K, { line: 9 });
    const y = emdash.object('demo_y', K, { line: 10 });
    const p = emdash.hom(
        'demo_p',
        K,
        x,
        y,
        { line: 11 }
    );
    const u = emdash.object(
        'demo_u',
        emdash.fibre(E, x),
        { line: 12 }
    );

    let callbackCount = 0;
    const coherentEta = emdash.displayedTransforLambda(
        'k',
        FF,
        GG,
        k => {
            callbackCount += 1;
            return emdash.apply(eta, k, {
                expectedShape: 'displayed-component',
                source: { line: 18 }
            });
        },
        { source: { line: 17 } }
    );
    const etaComparison = emdash.compare(coherentEta, eta);
    if (callbackCount !== 1 || etaComparison.status !== 'equal') {
        throw new Error(
            'FIBRED-TRANSFD-1 coherent eta did not lower exactly once'
        );
    }

    const component =
        emdash.displayedTransforComponent(eta, x, { line: 27 });
    const point = emdash.displayedTransforPoint(
        eta,
        x,
        u,
        { line: 28 }
    );
    const higher = emdash.displayedTransforNaturality(
        eta,
        p,
        u,
        { line: 29 }
    );
    const composite = emdash.composeDisplayedTransfor(
        theta,
        eta,
        { line: 30 }
    );
    const compositeComponent =
        emdash.displayedTransforComponent(
            composite,
            x,
            { line: 31 }
        );

    const compatibility =
        emdash.displayedTransforClassifierCompatibility(
            FF,
            GG,
            2_000,
            { line: 35 }
        );
    if (
        compatibility.directOrdinaryRuntime.status !==
            'not-equal' ||
        compatibility.directOrdinaryProofTime.status !==
            'solved' ||
        compatibility.directOrdinaryObjectRuntime.status !==
            'equal' ||
        compatibility.directSigmaPiRuntime.status !== 'equal' ||
        compatibility.directOrdinaryProofTime
            .ruleApplications[0]?.ruleId !==
            'categorical.transfd.direct-second-hom'
    ) {
        throw new Error(
            'FIBRED-TRANSFD-1 classifier boundary drifted'
        );
    }

    let negativeDiagnostic: CoreCategoricalDiagnostic | undefined;
    try {
        emdash.displayedTransforLambda(
            'k',
            FF,
            GG,
            () => eta,
            {
                source: {
                    line: 50,
                    detail: 'incoherent unprojected displayed eta body'
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
            'FIBRED-TRANSFD-1 accepted an unprojected eta body'
        );
    }

    return Object.freeze({
        revision: CORE_CATEGORICAL_FIBRED_TRANSFD_DEMO_REVISION,
        candidate: 'emdash-v3.2-fibred-transfd-1',
        construction: 'direct-typescript-categorical-program',
        assumptions: Object.freeze([
            'demo_K : Cat',
            'demo_E demo_D : Catd demo_K',
            'demo_FF demo_GG demo_HH : Functord demo_E demo_D',
            'demo_eta : Transfd demo_FF demo_GG',
            'demo_theta : Transfd demo_GG demo_HH',
            'demo_x demo_y : Obj demo_K',
            'demo_p : Hom demo_K demo_x demo_y',
            'demo_u : Obj demo_E[demo_x]'
        ]),
        examples: Object.freeze([
            Object.freeze({
                id: 'coherent-eta' as const,
                surface: 'λ k :^nd demo_K. demo_eta[k]',
                compilation: emdash.compile(coherentEta)
            }),
            Object.freeze({
                id: 'fibre-component' as const,
                surface: 'demo_eta[demo_x]',
                compilation: emdash.compile(component)
            }),
            Object.freeze({
                id: 'point-component' as const,
                surface: 'demo_eta[demo_x][demo_u]',
                compilation: emdash.compile(point)
            }),
            Object.freeze({
                id: 'higher-cell' as const,
                surface: 'demo_eta[demo_p][demo_u]',
                compilation: emdash.compile(higher)
            }),
            Object.freeze({
                id: 'composite-component' as const,
                surface:
                    '(demo_theta ∘ demo_eta)[demo_x]',
                compilation: emdash.compile(compositeComponent)
            })
        ]),
        coherentAbstraction: Object.freeze({
            input:
                'λ k :^nd demo_K. demo_eta[k]' as const,
            output: 'demo_eta' as const,
            callbackCount,
            status: 'equal' as const
        }),
        classifierCompatibility: Object.freeze({
            direct: compatibility.explicitDirectClassifier,
            ordinaryNextHom:
                compatibility.explicitOrdinaryNextHomClassifier,
            sigmaPiNextHom:
                compatibility.explicitSigmaPiNextHomClassifier,
            directOrdinaryRuntime: 'not-equal' as const,
            directOrdinaryProofTime: 'solved' as const,
            directOrdinaryObjectRuntime: 'equal' as const,
            directSigmaPiRuntime: 'equal' as const,
            proofRuleId:
                'categorical.transfd.direct-second-hom' as const
        }),
        verticalComponentRuntimeRuleIds: Object.freeze(
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
                .runtimeRuleIds.filter(id =>
                    id.startsWith(
                        'categorical.transfd.component-composition.'
                    )
                )
        ),
        negativeInput:
            'λ k :^nd demo_K. demo_eta' as const,
        negativeDiagnostic,
        newLambdapiMathematicalOwnerOrRule: false,
        stringParserDependency: false,
        productionLambdapiDependency: false,
        boundary:
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
    });
}

export function formatCoreCategoricalFibredTransfdDemo(
    result: CoreCategoricalFibredTransfdDemoResult =
        runCoreCategoricalFibredTransfdDemo()
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
        'Assumptions:',
        assumptions,
        'Examples:',
        examples,
        'Coherent eta:',
        `  ${result.coherentAbstraction.input}`,
        `  ↦ ${result.coherentAbstraction.output}`,
        `  callback count: ${result.coherentAbstraction.callbackCount}`,
        'Classifier presentations:',
        `  direct: ${result.classifierCompatibility.direct}`,
        '  ordinary next hom: ' +
            result.classifierCompatibility.ordinaryNextHom,
        '  Sigma/Pi next hom: ' +
            result.classifierCompatibility.sigmaPiNextHom,
        '  direct/ordinary runtime: ' +
            result.classifierCompatibility.directOrdinaryRuntime,
        '  direct/ordinary proof-time: ' +
            result.classifierCompatibility.directOrdinaryProofTime,
        '  object-classifier runtime: ' +
            result.classifierCompatibility
                .directOrdinaryObjectRuntime,
        '  Sigma/Pi runtime: ' +
            result.classifierCompatibility.directSigmaPiRuntime,
        'Negative example:',
        `  ${result.negativeInput}`,
        `  ${result.negativeDiagnostic.phase}/` +
            `${result.negativeDiagnostic.code}: ` +
            result.negativeDiagnostic.message,
        'New Lambdapi mathematical owner/rule: no',
        'String parser dependency: no',
        'Production Lambdapi dependency: no'
    ].join('\n');
}
