/**
 * Executable end-user demonstration of FIBRED-COMPREHENSION-1A.
 *
 * Surface strings below are explanatory labels. The actual input is the
 * direct typed TypeScript construction API, so no Lambdapi parser or
 * production Lambdapi runtime is involved.
 */

import {
    CORE_CATEGORICAL_COMPREHENSION_TRANSFER_BOUNDARY,
    compileCoreCategoricalComprehensionTransfer
} from './categorical_comprehension_transfer';
import {
    CoreCategoricalProgram,
    CoreCategoricalProgramCompilation,
    serializeCoreCategoricalExpression
} from './categorical_program';

export const CORE_CATEGORICAL_COMPREHENSION_DEMO_REVISION =
    'FIBRED-COMPREHENSION-1A-DEMO-1' as const;

export interface CoreCategoricalComprehensionDemoExample {
    readonly id:
        | 'dependent-pair'
        | 'canonical-sigma-arrow'
        | 'totalized-object-action'
        | 'totalized-arrow-action'
        | 'further-dependent-substitution';
    readonly surface: string;
    readonly compilation: CoreCategoricalProgramCompilation;
}

export interface CoreCategoricalComprehensionDemoReduction {
    readonly id: 'object-action' | 'arrow-action';
    readonly ruleId: string;
    readonly resultCore: string;
}

export interface CoreCategoricalComprehensionDemo {
    readonly revision:
        typeof CORE_CATEGORICAL_COMPREHENSION_DEMO_REVISION;
    readonly candidate: 'emdash-v3.2-fibred-comprehension-1a';
    readonly construction: 'direct-typescript-categorical-program';
    readonly assumptions: readonly string[];
    readonly examples:
        readonly CoreCategoricalComprehensionDemoExample[];
    readonly reductions:
        readonly CoreCategoricalComprehensionDemoReduction[];
    readonly outputSummary: {
        readonly objectAction: '(a,u) maps to (F[a],u)';
        readonly arrowAction: '(p,alpha) maps to (F[p],alpha)';
        readonly dependentChain:
            'Q over Sigma(D) reindexes over Sigma(F*D)';
    };
    readonly productionLambdapiDependency: false;
    readonly boundary:
        typeof CORE_CATEGORICAL_COMPREHENSION_TRANSFER_BOUNDARY;
}

const example = (
    id: CoreCategoricalComprehensionDemoExample['id'],
    surface: string,
    compilation: CoreCategoricalProgramCompilation
): CoreCategoricalComprehensionDemoExample => Object.freeze({
    id,
    surface,
    compilation
});

export function runCoreCategoricalComprehensionDemo():
CoreCategoricalComprehensionDemo {
    const emdash = new CoreCategoricalProgram({
        sourceFile: 'examples/v3_2_categorical_comprehension_demo.ts',
        profile: 'fibred-comprehension-1a'
    });
    const A = emdash.category('demo_A', { line: 45 });
    const K = emdash.category('demo_K', { line: 46 });
    const F = emdash.functor('demo_F', A, K, { line: 47 });
    const D = emdash.displayedFamily('demo_D', K, { line: 48 });
    const pulledD = emdash.pullbackFamily(D, F, { line: 49 });

    const a = emdash.object('demo_a', A, { line: 51 });
    const b = emdash.object('demo_b', A, { line: 52 });
    const p = emdash.hom('demo_p', A, a, b, { line: 53 });
    const Da = emdash.fibre(pulledD, a, { line: 54 });
    const Db = emdash.fibre(pulledD, b, { line: 55 });
    const u = emdash.object('demo_u', Da, { line: 56 });
    const v = emdash.object('demo_v', Db, { line: 57 });
    const transport = emdash.familyTransport(
        pulledD,
        p,
        { line: 58 }
    );
    const transportedU = emdash.apply(
        transport,
        u,
        { source: { line: 59 } }
    );
    const alpha = emdash.hom(
        'demo_alpha',
        Db,
        transportedU,
        v,
        { line: 60 }
    );

    const pair = emdash.dependentPair(
        pulledD,
        a,
        u,
        { line: 62 }
    );
    const sigmaArrow = emdash.sigmaArrow(
        pulledD,
        u,
        v,
        p,
        alpha,
        { line: 63 }
    );
    const totalization = emdash.pullbackTotal(
        F,
        D,
        { line: 64 }
    );
    const objectImage = emdash.apply(
        totalization,
        pair,
        { source: { line: 65 } }
    );
    const arrowImage = emdash.apply(
        totalization,
        sigmaArrow,
        { source: { line: 66 } }
    );

    const sigmaD = emdash.totalCategory(D, { line: 68 });
    const Q = emdash.displayedFamily('demo_Q', sigmaD, { line: 69 });
    const substitutedQ = emdash.substituteFamily(
        Q,
        totalization,
        { line: 70 }
    );
    const chainFibre = emdash.fibre(
        substitutedQ,
        pair,
        { line: 71 }
    );
    const q = emdash.object('demo_q', chainFibre, { line: 72 });

    const objectCompilation = emdash.compile(objectImage);
    const arrowCompilation = emdash.compile(arrowImage);
    const runtime = compileCoreCategoricalComprehensionTransfer().runtime;
    const objectReduction = runtime.rewriteHead(
        objectCompilation.explicitTerm
    );
    const arrowReduction = runtime.rewriteHead(
        arrowCompilation.explicitTerm
    );
    if (
        objectReduction.status !== 'rewritten' ||
        arrowReduction.status !== 'rewritten'
    ) {
        throw new Error(
            'Fibred comprehension demo lost its selected computation rules'
        );
    }

    return Object.freeze({
        revision: CORE_CATEGORICAL_COMPREHENSION_DEMO_REVISION,
        candidate: 'emdash-v3.2-fibred-comprehension-1a',
        construction: 'direct-typescript-categorical-program',
        assumptions: Object.freeze([
            'demo_A, demo_K : Cat',
            'demo_F : Functor demo_A demo_K',
            'demo_D : Catd demo_K',
            'demo_a, demo_b : Obj demo_A',
            'demo_p : Hom demo_A demo_a demo_b',
            'demo_u : Obj demo_D[demo_F[demo_a]]',
            'demo_v : Obj demo_D[demo_F[demo_b]]',
            'demo_alpha : Hom demo_D[demo_F[demo_b]] ' +
                '(demo_D[demo_F[demo_p]][demo_u]) demo_v',
            'demo_Q : Catd (Sigma demo_D)'
        ]),
        examples: Object.freeze([
            example(
                'dependent-pair',
                '(demo_a, demo_u) : Obj (Sigma (demo_F*demo_D))',
                emdash.compile(pair)
            ),
            example(
                'canonical-sigma-arrow',
                '(demo_p, demo_alpha) : ' +
                    'Hom (Sigma (demo_F*demo_D)) ' +
                    '(demo_a,demo_u) (demo_b,demo_v)',
                emdash.compile(sigmaArrow)
            ),
            example(
                'totalized-object-action',
                'sigmaPullbackTotal(demo_F,demo_D)[(demo_a,demo_u)]',
                objectCompilation
            ),
            example(
                'totalized-arrow-action',
                'sigmaPullbackTotal(demo_F,demo_D)[(demo_p,demo_alpha)]',
                arrowCompilation
            ),
            example(
                'further-dependent-substitution',
                'demo_q : demo_Q[' +
                    'sigmaPullbackTotal(demo_F,demo_D)[(demo_a,demo_u)]]',
                emdash.compile(q)
            )
        ]),
        reductions: Object.freeze([
            Object.freeze({
                id: 'object-action' as const,
                ruleId: objectReduction.ruleId,
                resultCore: serializeCoreCategoricalExpression(
                    objectReduction.after
                )
            }),
            Object.freeze({
                id: 'arrow-action' as const,
                ruleId: arrowReduction.ruleId,
                resultCore: serializeCoreCategoricalExpression(
                    arrowReduction.after
                )
            })
        ]),
        outputSummary: Object.freeze({
            objectAction: '(a,u) maps to (F[a],u)' as const,
            arrowAction: '(p,alpha) maps to (F[p],alpha)' as const,
            dependentChain:
                'Q over Sigma(D) reindexes over Sigma(F*D)' as const
        }),
        productionLambdapiDependency: false,
        boundary: CORE_CATEGORICAL_COMPREHENSION_TRANSFER_BOUNDARY
    });
}

export function formatCoreCategoricalComprehensionDemo(): string {
    const demo = runCoreCategoricalComprehensionDemo();
    return [
        `${demo.candidate} (${demo.revision})`,
        `construction: ${demo.construction}`,
        'inputs:',
        ...demo.assumptions.map(assumption => `  ${assumption}`),
        'programs:',
        ...demo.examples.map(item => [
            `  ${item.id}: ${item.surface}`,
            `    Core: ${item.compilation.explicitCore}`,
            `    type: ${item.compilation.explicitInferredType}`
        ].join('\n')),
        'computed outputs:',
        `  ${demo.outputSummary.objectAction}`,
        `  ${demo.outputSummary.arrowAction}`,
        `  ${demo.outputSummary.dependentChain}`,
        ...demo.reductions.map(reduction =>
            `  ${reduction.ruleId}: ${reduction.resultCore}`
        ),
        'production Lambdapi dependency: false'
    ].join('\n');
}
