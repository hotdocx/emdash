/**
 * Runnable end-user witness for the reviewed directed dependent continuation.
 *
 * The input is built directly with the ergonomic scoped TypeScript builder.
 * No string parser or Lambdapi process participates in checking/evaluation.
 */

import {
    CoreCheckerError
} from './checker';
import {
    coreConstantDisplayedFamily,
    coreDisplayedFamilyType
} from './dependent';
import {
    createCoreDirectedContinuationKernel
} from './directed_graduation';
import {
    CoreLfScopedBuilder
} from './lf_builder';
import {
    coreLfCombinedWeakHead,
    coreLfDefinitionalCompare
} from './lf_conversion';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    KernelExpression,
    binderMode,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    provenance,
    sourceSpan
} from './kernel';
import {
    serializeKernelExpression
} from './lambdapi';

const demoPath = 'examples/v3_2_directed_dependent_demo.ts';

const at = (
    line: number
) => sourceSpan(demoPath, line, 1, line, 2);

const because = (
    line: number,
    detail: string
) => provenance('surface', detail, at(line));

const explicitFunctorial = binderMode('explicit', 'functorial');

const owner = (
    name: Parameters<typeof kernelApplication>[0],
    arguments_: readonly KernelExpression[] = [],
    line = 1
): KernelExpression => kernelApplication(
    name,
    arguments_.map(value => ({ value })),
    because(line, `dependent demo owner ${name}`)
);

const categoryUniverse = (
    line: number
): KernelExpression => owner('category-universe', [], line);

const categoryOfCategories = (
    line: number
): KernelExpression => owner('category-of-categories', [], line);

const objectClassifier = (
    category: KernelExpression,
    line: number
): KernelExpression => owner('object-classifier', [category], line);

const decode = (
    classifier: KernelExpression,
    line: number
): KernelExpression => owner('decode', [classifier], line);

const objectType = (
    category: KernelExpression,
    line: number
): KernelExpression => decode(objectClassifier(category, line), line);

const sectionCategory = (
    base: KernelExpression,
    family: KernelExpression,
    line: number
): KernelExpression => owner(
    'section-category',
    [base, family],
    line
);

const fibre = (
    base: KernelExpression,
    family: KernelExpression,
    point: KernelExpression,
    line: number
): KernelExpression => owner(
    'functor-object',
    [base, categoryOfCategories(line), family, point],
    line
);

const familyObjectType = (
    base: KernelExpression,
    family: KernelExpression,
    point: KernelExpression,
    line: number
): KernelExpression => objectType(
    fibre(base, family, point, line),
    line
);

const encodedPairFamily = (
    base: KernelExpression,
    family: KernelExpression,
    line: number
): KernelExpression => {
    const nodeProvenance = because(line, 'dependent demo pair family');
    const pairIndex = kernelBound(
        0,
        because(line, 'dependent demo pair index')
    );
    return kernelLambda(
        kernelBinder(
            'pairIndex',
            objectType(base, line),
            explicitFunctorial,
            nodeProvenance
        ),
        objectClassifier(
            fibre(base, family, pairIndex, line),
            line
        ),
        nodeProvenance
    );
};

const telescopePointFunctor = (
    base: KernelExpression,
    family: KernelExpression,
    telescope: KernelExpression,
    point: KernelExpression,
    line: number
): KernelExpression => owner(
    'transfor-component-capped',
    [
        base,
        categoryOfCategories(line),
        family,
        coreConstantDisplayedFamily(
            base,
            categoryOfCategories(line),
            because(line, 'dependent demo constant Cat family')
        ),
        point,
        telescope
    ],
    line
);

const serialize = (
    expression: KernelExpression
): string => serializeKernelExpression(expression);

export interface CoreDirectedDependentDemoDiagnostic {
    readonly code: CoreCheckerError['code'];
    readonly summary: string;
    readonly message: string;
}

export interface CoreDirectedDependentDemoTraceEntry {
    readonly step: number;
    readonly reduction: string;
}

export interface CoreDirectedDependentDemoResult {
    readonly profile: 'emdash-v3.2-dttlf-directed-1';
    readonly construction: 'direct-typescript-scoped-builder';
    readonly surfaceInput: string;
    readonly assumptions: readonly string[];
    readonly explicitCore: string;
    readonly inferredType: string;
    readonly reducedType: string;
    readonly computationRedex: string;
    readonly reducedComputation: string;
    readonly trace: readonly CoreDirectedDependentDemoTraceEntry[];
    readonly negativeInput: string;
    readonly negativeDiagnostic: CoreDirectedDependentDemoDiagnostic;
    readonly productionLambdapiDependency: false;
}

const surfaceInput = [
    'builder.apply(',
    '  builder.lam("section", sectionType, section =>',
    '    piapp0(sigmaBase, telescopeFamily, section, pair)),',
    '  s',
    ')'
].join('\n');

const freezeTrace = (
    trace: readonly CoreDirectedDependentDemoTraceEntry[]
): readonly CoreDirectedDependentDemoTraceEntry[] => Object.freeze(
    trace.map(entry => Object.freeze({ ...entry }))
);

/**
 * Construct, infer, check, and reduce the reviewed dependent witness.
 */
export function runCoreDirectedDependentDemo():
CoreDirectedDependentDemoResult {
    const catalog = createCoreDirectedContinuationKernel(
        because(1, 'dependent demo continuation catalog')
    );
    let environment = catalog.environment;
    const assume = (
        name: string,
        type: KernelExpression,
        line: number
    ): KernelExpression => {
        environment = environment.extend({
            name,
            type,
            mode: explicitFunctorial,
            provenance: because(line, `dependent demo assumption ${name}`)
        });
        return kernelFree(
            name,
            because(line, `dependent demo reference ${name}`)
        );
    };

    const K = assume('demo_K', categoryUniverse(2), 2);
    const R = assume(
        'demo_R',
        coreDisplayedFamilyType(
            K,
            because(3, 'dependent demo R classifier')
        ),
        3
    );
    const constantCategoryFamily = coreConstantDisplayedFamily(
        K,
        categoryOfCategories(4),
        because(4, 'dependent demo constant category family')
    );
    const telescopeCategory =
        catalog.directed1b.directed1a.displayedFunctorCategory(
            K,
            R,
            constantCategoryFamily,
            because(5, 'dependent demo telescope category')
        );
    const FF = assume(
        'demo_FF',
        objectType(telescopeCategory, 6),
        6
    );
    const k = assume('demo_k', objectType(K, 7), 7);
    const r = assume(
        'demo_r',
        familyObjectType(K, R, k, 8),
        8
    );

    const sigmaBase =
        catalog.directed1b.directed1a.sigmaCategory(
            K,
            R,
            because(9, 'dependent demo Sigma base')
        );
    const telescopeFamily =
        catalog.directed1b.directed1a.sigmaTelescopeFamily(
            K,
            R,
            FF,
            because(10, 'dependent demo telescope family')
        );
    const pair = catalog.directed1b.dependentPair(
        objectClassifier(K, 11),
        encodedPairFamily(K, R, 11),
        k,
        r,
        because(11, 'dependent demo dependent pair')
    );
    const sectionType = objectType(
        sectionCategory(sigmaBase, telescopeFamily, 12),
        12
    );
    const section = assume('demo_s', sectionType, 13);

    const builder = new CoreLfScopedBuilder(
        because(14, 'dependent demo scoped TypeScript input')
    );
    const evaluator = builder.lam(
        'section',
        builder.embed(sectionType),
        sectionToken => catalog.builderApplication(
            builder,
            'section-object-evaluation',
            [
                builder.embed(sigmaBase),
                builder.embed(telescopeFamily),
                sectionToken,
                builder.embed(pair)
            ],
            because(15, 'dependent demo section evaluation')
        ),
        explicitFunctorial,
        because(15, 'dependent demo outer LF evaluator')
    );
    const application = builder.apply(
        evaluator,
        builder.embed(section),
        'explicit',
        because(16, 'dependent demo outer LF application')
    );
    const explicitCore = builder.lower(application);

    const rawFibre = fibre(
        sigmaBase,
        telescopeFamily,
        pair,
        17
    );
    const reducedFibre = owner(
        'functor-object',
        [
            fibre(K, R, k, 18),
            categoryOfCategories(18),
            telescopePointFunctor(K, R, FF, k, 18),
            r
        ],
        18
    );
    const reducedType = objectType(reducedFibre, 19);

    const checker = catalog.createChecker(environment);
    const inferred = checker.infer(
        checker.rootContext,
        explicitCore
    );
    if (inferred.type.tag === 'kind') {
        throw new Error(
            'The dependent demo unexpectedly inferred checker-only KIND'
        );
    }
    checker.check(
        checker.rootContext,
        explicitCore,
        reducedType
    );
    const typeComparison = coreLfDefinitionalCompare(
        environment,
        inferred.type,
        reducedType,
        16,
        undefined,
        catalog.runtimeProgram
    );
    if (typeComparison.status !== 'equal') {
        throw new Error(
            `The dependent demo type did not reduce within its reviewed ` +
                `budget: ${typeComparison.status}`
        );
    }

    const computationBuilder = new CoreLfScopedBuilder(
        because(20, 'dependent demo computation witness')
    );
    const computationLambda = computationBuilder.lam(
        'section',
        computationBuilder.embed(sectionType),
        _sectionToken => computationBuilder.embed(rawFibre),
        explicitFunctorial,
        because(21, 'dependent demo fibre abstraction')
    );
    const computationRedex = computationBuilder.lower(
        computationBuilder.apply(
            computationLambda,
            computationBuilder.embed(section),
            'explicit',
            because(22, 'dependent demo fibre redex')
        )
    );
    const computation = coreLfCombinedWeakHead(
        environment,
        computationRedex,
        16,
        undefined,
        catalog.runtimeProgram
    );
    if (
        computation.status !== 'weak-head-normal' ||
        !kernelExpressionEquals(computation.expression, reducedFibre)
    ) {
        throw new Error(
            `The dependent demo computation did not reach its reviewed ` +
                `fibre: ${computation.status}`
        );
    }
    const trace = computation.trace.map(entry => ({
        step: entry.step + 1,
        reduction: entry.kind === 'runtime'
            ? entry.ruleId
            : entry.kind
    }));

    const S = assume(
        'demo_wrong_S',
        coreDisplayedFamilyType(
            K,
            because(23, 'dependent demo wrong S classifier')
        ),
        23
    );
    const q = assume(
        'demo_wrong_q',
        familyObjectType(K, S, k, 24),
        24
    );
    const wrongPair = catalog.directed1b.dependentPair(
        objectClassifier(K, 25),
        encodedPairFamily(K, S, 25),
        k,
        q,
        because(25, 'dependent demo wrong-family pair')
    );
    const wrongEvaluation = catalog.sectionObjectEvaluation(
        sigmaBase,
        telescopeFamily,
        section,
        wrongPair,
        because(26, 'dependent demo wrong-family evaluation')
    );
    let negativeDiagnostic:
        CoreDirectedDependentDemoDiagnostic | undefined;
    try {
        const negativeChecker = catalog.createChecker(environment);
        negativeChecker.infer(
            negativeChecker.rootContext,
            wrongEvaluation
        );
    } catch (error: unknown) {
        if (!(error instanceof CoreCheckerError)) throw error;
        negativeDiagnostic = Object.freeze({
            code: error.code,
            summary:
                'The dependent pair belongs to displayed family S, ' +
                'but this section expects the Sigma telescope over R.',
            message: error.message
        });
    }
    if (negativeDiagnostic === undefined) {
        throw new Error(
            'The dependent demo wrong-family pair was unexpectedly accepted'
        );
    }

    return Object.freeze({
        profile: 'emdash-v3.2-dttlf-directed-1',
        construction: 'direct-typescript-scoped-builder',
        surfaceInput,
        assumptions: Object.freeze([
            'K : Cat',
            'R : Catd K',
            'FF : telescope over R',
            'k : Obj K',
            'r : Obj (R k)',
            's : section of the Sigma telescope'
        ]),
        explicitCore: serialize(explicitCore),
        inferredType: serialize(inferred.type),
        reducedType: serialize(reducedType),
        computationRedex: serialize(computationRedex),
        reducedComputation: serialize(computation.expression),
        trace: freezeTrace(trace),
        negativeInput:
            'piapp0 sigmaBase telescopeFamily s (pair k q), ' +
            'where q belongs to a different displayed family S',
        negativeDiagnostic,
        productionLambdapiDependency: false
    });
}

export function formatCoreDirectedDependentDemo(
    result: CoreDirectedDependentDemoResult =
        runCoreDirectedDependentDemo()
): string {
    const assumptions = result.assumptions.map(
        assumption => `  - ${assumption}`
    ).join('\n');
    const trace = result.trace.map(
        entry => `  ${entry.step}. ${entry.reduction}`
    ).join('\n');
    return [
        'emdash v3.2 directed dependent demo',
        `Profile: ${result.profile}`,
        `Input path: ${result.construction}`,
        '',
        'Assumptions:',
        assumptions,
        '',
        'Input:',
        result.surfaceInput,
        '',
        'Explicit Core:',
        result.explicitCore,
        '',
        'Inferred type:',
        result.inferredType,
        '',
        'Reduced type:',
        result.reducedType,
        '',
        'Combined fibre computation:',
        `  redex: ${result.computationRedex}`,
        `  result: ${result.reducedComputation}`,
        '  trace:',
        trace,
        '',
        'Rejected wrong-family input:',
        `  ${result.negativeInput}`,
        `  ${result.negativeDiagnostic.code}: ` +
            result.negativeDiagnostic.summary,
        `  detail: ${result.negativeDiagnostic.message}`,
        '',
        'Production Lambdapi dependency: no'
    ].join('\n');
}
