/**
 * Explicit Node-oriented fresh checker for PathOut presentation requests.
 *
 * This adapter owns no semantics. It constructs the finite reviewer fixtures
 * and delegates to the already-qualified PathOut transfer, ordinary LF
 * checker, and definitional comparator. Import it only for an explicit fresh
 * check; the browser-safe presentation module never imports this file.
 */

import {
    coreCategoricalFibredStructureCoreName
} from './categorical_fibred_structure_transfer';
import {
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    coreCategoricalStructuralSymbolCoreName
} from './categorical_structural_transfer';
import { createCoreLfChecker } from './lf_checker';
import { coreLfDefinitionalCompare } from './lf_conversion';
import { CoreLfDeclarationEnvironment } from './lf_declarations';
import {
    KernelExpression,
    Plicity,
    binderMode,
    kernelApplication,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from './kernel';
import { serializeKernelExpression } from './lambdapi';
import {
    CorePathoutPresentationRequest,
    serializeCorePathoutPresentationRequest
} from './pathout_presentation';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_CORE_NAMES
} from './pathind_fixed_source_transfer';
import {
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES
} from './pathout_foundation_transfer';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY,
    CORE_PATHOUT_TRANSITIVITY_1E_CORE_NAMES,
    CORE_PATHOUT_TRANSITIVITY_1E_LINKAGE,
    CorePathoutTransitivity1eCompilation,
    compileCorePathoutTransitivity1eTransfer
} from './pathout_transitivity_transfer';

export const CORE_PATHOUT_PRESENTATION_1F_CHECK_REVISION =
    'PATHOUT-LIBRARY-PRESENTATION-1F-NODE-CHECK-1' as const;

export type CorePathoutFreshCheckErrorCode =
    | 'VARIABLE_ROLE_CONFLICT'
    | 'SEMANTIC_REJECTION'
    | 'NORMAL_FORM_MISMATCH';

export class CorePathoutFreshCheckError extends Error {
    constructor(
        public readonly code: CorePathoutFreshCheckErrorCode,
        public readonly request: CorePathoutPresentationRequest,
        message: string,
        public readonly underlying?: unknown
    ) {
        super(message);
        this.name = 'CorePathoutFreshCheckError';
    }
}

export interface CorePathoutFreshCheckResult {
    readonly revision: typeof CORE_PATHOUT_PRESENTATION_1F_CHECK_REVISION;
    readonly status: 'freshly-checked';
    readonly evidenceClass: 'fresh-TypeScript-semantic-check';
    readonly request: CorePathoutPresentationRequest;
    readonly canonicalSource: string;
    readonly explicitCore: string;
    readonly expectedType: string;
    readonly checkedType: string;
    readonly normalForm?: {
        readonly status: 'definitionally-equal';
        readonly expression: string;
        readonly comparisonSteps: number;
    };
    readonly compilation: {
        readonly adapterCache: 'created-this-call' | 'reused-in-process';
        readonly elapsedMs: number;
        readonly transparentDefinitionCount: 5;
        readonly localRuntimeRuleCount: 1;
        readonly localProofRuleCount: 0;
        readonly runtimeRuleIds: readonly string[];
    };
    readonly semanticCheckpoint: '3b113ad';
    readonly completionLedger: '10432ba';
    readonly productionBackend: 'typescript-emdash';
    readonly lambdapiRole: 'bounded-conformance-oracle-not-run-by-this-check';
}

const nodeProvenance = provenance(
    'derived',
    'PATHOUT-LIBRARY-PRESENTATION-1F fresh semantic check'
);

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        Object.freeze(value);
    }
    return value;
};

interface CallArgument {
    readonly plicity: Plicity;
    readonly value: KernelExpression;
}

const call = (
    name: string,
    arguments_: readonly CallArgument[]
): KernelExpression => kernelCall(
    kernelFree(name, nodeProvenance),
    arguments_,
    nodeProvenance
);

const linkedCoreName = (backendName: string): string => {
    const link = CORE_PATHOUT_TRANSITIVITY_1E_LINKAGE.entries.find(
        entry =>
            entry.kind === 'free-declaration' &&
            entry.backendName === backendName
    );
    if (link === undefined || link.kind !== 'free-declaration') {
        throw new Error(`No PathOut presentation link for ${backendName}`);
    }
    return link.coreName;
};

const categoryType = (): KernelExpression => kernelApplication(
    'category-universe',
    [],
    nodeProvenance
);

const categoryOfCategories = (): KernelExpression => kernelApplication(
    'category-of-categories',
    [],
    nodeProvenance
);

const decode = (classifier: KernelExpression): KernelExpression =>
    kernelApplication(
        'decode',
        [{ value: classifier }],
        nodeProvenance
    );

const objectType = (base: KernelExpression): KernelExpression =>
    decode(kernelApplication(
        'object-classifier',
        [{ value: base }],
        nodeProvenance
    ));

const homType = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => decode(kernelApplication(
    'hom-classifier',
    [{ value: base }, { value: source }, { value: target }],
    nodeProvenance
));

const displayedFamilyType = (
    base: KernelExpression
): KernelExpression => decode(call(
    linkedCoreName('Catd'),
    [{ plicity: 'explicit', value: base }]
));

const functorObject = (
    source: KernelExpression,
    target: KernelExpression,
    functor: KernelExpression,
    object: KernelExpression
): KernelExpression => kernelApplication(
    'functor-object',
    [
        { value: source },
        { value: target },
        { value: functor },
        { value: object }
    ],
    nodeProvenance
);

const fibre = (
    base: KernelExpression,
    family: KernelExpression,
    point: KernelExpression
): KernelExpression => functorObject(
    base,
    categoryOfCategories(),
    family,
    point
);

const sectionCategory = (
    base: KernelExpression,
    family: KernelExpression
): KernelExpression => kernelApplication(
    'section-category',
    [{ value: base }, { value: family }],
    nodeProvenance
);

const homCategory = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => kernelApplication(
    'hom-category',
    [{ value: base }, { value: source }, { value: target }],
    nodeProvenance
);

const component = (
    base: KernelExpression,
    sourceFamily: KernelExpression,
    targetFamily: KernelExpression,
    point: KernelExpression,
    displayedFunctor: KernelExpression
): KernelExpression => kernelApplication(
    'transfor-component-capped',
    [
        { value: base },
        { value: categoryOfCategories() },
        { value: sourceFamily },
        { value: targetFamily },
        { value: point },
        { value: displayedFunctor }
    ],
    nodeProvenance
);

const pathoutCategory = (
    base: KernelExpression,
    source: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutCategory,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]
);

const pathoutObject = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression,
    arrow: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutObject,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target },
        { plicity: 'explicit', value: arrow }
    ]
);

const pathoutReflexiveObject = (
    base: KernelExpression,
    source: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutReflexiveObject,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]
);

const pathoutReflexiveArrow = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression,
    arrow: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutReflexiveArrow,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target },
        { plicity: 'explicit', value: arrow }
    ]
);

const pathInductionSection = (
    base: KernelExpression,
    source: KernelExpression,
    motive: KernelExpression,
    datum: KernelExpression
): KernelExpression => call(
    CORE_PATHIND_FIXED_SOURCE_1C_CORE_NAMES.pathInductionSection,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: motive },
        { plicity: 'explicit', value: datum }
    ]
);

const representable = (
    base: KernelExpression,
    source: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.representableFamily,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]
);

const pathCompositionFunctor = (
    base: KernelExpression,
    source: KernelExpression,
    middle: KernelExpression,
    first: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_TRANSITIVITY_1E_CORE_NAMES.path_comp_func,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: middle },
        { plicity: 'explicit', value: first }
    ]
);

const identityFunctor = (base: KernelExpression): KernelExpression => call(
    coreCategoricalStructuralSymbolCoreName(
        CORE_CATEGORICAL_STRUCTURAL_SYMBOLS.identityFunctor
    ),
    [{ plicity: 'implicit', value: base }]
);

const stablePrecomposition = (
    base: KernelExpression,
    source: KernelExpression,
    middle: KernelExpression,
    target: KernelExpression,
    first: KernelExpression,
    second: KernelExpression
): KernelExpression => call(
    coreCategoricalFibredStructureCoreName('precomposition-action'),
    [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: identityFunctor(base) },
        { plicity: 'explicit', value: target },
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: middle },
        { plicity: 'explicit', value: first },
        { plicity: 'explicit', value: second }
    ]
);

interface SemanticFixture {
    readonly environment: CoreLfDeclarationEnvironment;
    readonly term: KernelExpression;
    readonly expectedType: KernelExpression;
    readonly expectedNormalForm?: KernelExpression;
}

class FixtureBuilder {
    private environment_: CoreLfDeclarationEnvironment;
    private readonly variables = new Map<string, {
        readonly type: KernelExpression;
        readonly term: KernelExpression;
    }>();

    constructor(
        private readonly request: CorePathoutPresentationRequest,
        environment: CoreLfDeclarationEnvironment
    ) {
        this.environment_ = environment;
    }

    get environment(): CoreLfDeclarationEnvironment {
        return this.environment_;
    }

    add(name: string, type: KernelExpression): KernelExpression {
        const existing = this.variables.get(name);
        if (existing !== undefined) {
            if (!kernelExpressionEquals(existing.type, type)) {
                throw new CorePathoutFreshCheckError(
                    'VARIABLE_ROLE_CONFLICT',
                    this.request,
                    `Variable '${name}' is used with incompatible roles`
                );
            }
            return existing.term;
        }
        const term = kernelFree(name, nodeProvenance);
        try {
            this.environment_ = this.environment_.extend({
                name,
                type,
                mode: binderMode('explicit', 'functorial'),
                provenance: nodeProvenance,
                transparency: 'opaque'
            });
        } catch (error: unknown) {
            throw new CorePathoutFreshCheckError(
                'SEMANTIC_REJECTION',
                this.request,
                `Cannot add presentation variable '${name}'`,
                error
            );
        }
        this.variables.set(name, { type, term });
        return term;
    }
}

const argumentNames = (
    request: CorePathoutPresentationRequest
): readonly string[] => request.arguments.map(argument => argument.name);

const createFixture = (
    request: CorePathoutPresentationRequest,
    compilation: CorePathoutTransitivity1eCompilation
): SemanticFixture => {
    serializeCorePathoutPresentationRequest(request);
    const names = argumentNames(request);
    const fixture = new FixtureBuilder(
        request,
        compilation.compiled.environment
    );
    const Z = fixture.add(names[0] as string, categoryType());
    const x = fixture.add(names[1] as string, objectType(Z));

    if (request.formId === 'pathout-category') {
        return {
            environment: fixture.environment,
            term: pathoutCategory(Z, x),
            expectedType: categoryType()
        };
    }

    if (request.formId === 'fixed-source-induction') {
        const pathout = pathoutCategory(Z, x);
        const E = fixture.add(
            names[2] as string,
            displayedFamilyType(pathout)
        );
        const u = fixture.add(
            names[3] as string,
            objectType(fibre(
                pathout,
                E,
                pathoutReflexiveObject(Z, x)
            ))
        );
        return {
            environment: fixture.environment,
            term: pathInductionSection(Z, x, E, u),
            expectedType: objectType(sectionCategory(pathout, E))
        };
    }

    const y = fixture.add(names[2] as string, objectType(Z));
    if (request.formId === 'canonical-rho') {
        const p = fixture.add(names[3] as string, homType(Z, x, y));
        const pathout = pathoutCategory(Z, x);
        return {
            environment: fixture.environment,
            term: pathoutReflexiveArrow(Z, x, y, p),
            expectedType: homType(
                pathout,
                pathoutReflexiveObject(Z, x),
                pathoutObject(Z, x, y, p)
            )
        };
    }

    const z = fixture.add(names[3] as string, objectType(Z));
    const first = fixture.add(names[4] as string, homType(Z, x, y));
    const second = fixture.add(names[5] as string, homType(Z, y, z));
    const repX = representable(Z, x);
    const repY = representable(Z, y);
    const composition = pathCompositionFunctor(Z, x, y, first);
    const term = functorObject(
        homCategory(Z, y, z),
        homCategory(Z, x, z),
        component(Z, repY, repX, z, composition),
        second
    );
    return {
        environment: fixture.environment,
        term,
        expectedType: homType(Z, x, z),
        expectedNormalForm: stablePrecomposition(
            Z,
            x,
            y,
            z,
            first,
            second
        )
    };
};

let cachedCompilation: CorePathoutTransitivity1eCompilation | undefined;

const semanticCompilation = (): {
    readonly compilation: CorePathoutTransitivity1eCompilation;
    readonly cache: 'created-this-call' | 'reused-in-process';
    readonly elapsedMs: number;
} => {
    const start = Date.now();
    if (cachedCompilation !== undefined) {
        return {
            compilation: cachedCompilation,
            cache: 'reused-in-process',
            elapsedMs: Date.now() - start
        };
    }
    cachedCompilation = compileCorePathoutTransitivity1eTransfer();
    return {
        compilation: cachedCompilation,
        cache: 'created-this-call',
        elapsedMs: Date.now() - start
    };
};

/**
 * Freshly check one parsed request through the existing TypeScript semantics.
 * The first call in a process may spend several minutes constructing the
 * qualified transfer; subsequent calls reuse only that immutable compilation.
 */
export function checkCorePathoutPresentationRequest(
    request: CorePathoutPresentationRequest
): CorePathoutFreshCheckResult {
    const canonicalSource =
        serializeCorePathoutPresentationRequest(request);
    const semantic = semanticCompilation();
    let fixture: SemanticFixture;
    try {
        fixture = createFixture(request, semantic.compilation);
        const checker = createCoreLfChecker(
            fixture.environment,
            8192,
            semantic.compilation.composedRuntime
        );
        const checked = checker.check(
            checker.rootContext,
            fixture.term,
            fixture.expectedType
        );
        let normalForm: CorePathoutFreshCheckResult['normalForm'];
        if (fixture.expectedNormalForm !== undefined) {
            const comparison = coreLfDefinitionalCompare(
                fixture.environment,
                fixture.term,
                fixture.expectedNormalForm,
                8192,
                undefined,
                semantic.compilation.composedRuntime
            );
            if (comparison.status !== 'equal') {
                throw new CorePathoutFreshCheckError(
                    'NORMAL_FORM_MISMATCH',
                    request,
                    'Composition presentation did not reach its reviewed ' +
                    `normal form: ${comparison.status}`
                );
            }
            normalForm = {
                status: 'definitionally-equal',
                expression: serializeKernelExpression(
                    fixture.expectedNormalForm
                ),
                comparisonSteps: comparison.steps
            };
        }
        return deepFreeze({
            revision: CORE_PATHOUT_PRESENTATION_1F_CHECK_REVISION,
            status: 'freshly-checked' as const,
            evidenceClass: 'fresh-TypeScript-semantic-check' as const,
            request,
            canonicalSource,
            explicitCore: serializeKernelExpression(checked.term),
            expectedType: serializeKernelExpression(fixture.expectedType),
            checkedType: serializeKernelExpression(checked.type),
            ...(normalForm === undefined ? {} : { normalForm }),
            compilation: {
                adapterCache: semantic.cache,
                elapsedMs: semantic.elapsedMs,
                transparentDefinitionCount: 5 as const,
                localRuntimeRuleCount: 1 as const,
                localProofRuleCount: 0 as const,
                runtimeRuleIds: [
                    ...CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY.runtimeRuleIds
                ]
            },
            semanticCheckpoint: '3b113ad' as const,
            completionLedger: '10432ba' as const,
            productionBackend: 'typescript-emdash' as const,
            lambdapiRole:
                'bounded-conformance-oracle-not-run-by-this-check' as const
        });
    } catch (error: unknown) {
        if (error instanceof CorePathoutFreshCheckError) throw error;
        throw new CorePathoutFreshCheckError(
            'SEMANTIC_REJECTION',
            request,
            `PathOut presentation was rejected: ${
                error instanceof Error ? error.message : String(error)
            }`,
            error
        );
    }
}

/** Format one actual TypeScript semantic-check result. */
export function formatCorePathoutFreshCheck(
    result: CorePathoutFreshCheckResult
): string {
    return [
        'FRESH TYPESCRIPT SEMANTIC CHECK: ACCEPTED',
        `Expression: ${result.canonicalSource}`,
        `Presentation: ${result.request.formId}`,
        `Evidence class: ${result.evidenceClass}`,
        '',
        'Explicit backend-neutral Core:',
        result.explicitCore,
        '',
        'Checked type:',
        result.checkedType,
        ...(result.normalForm === undefined
            ? []
            : [
                '',
                'Reviewed normal form:',
                result.normalForm.expression,
                `Comparison steps: ${result.normalForm.comparisonSteps}`
            ]),
        '',
        `Semantic checkpoint: ${result.semanticCheckpoint}`,
        `Completion ledger: ${result.completionLedger}`,
        `Compilation cache: ${result.compilation.adapterCache}`,
        `Compilation elapsed: ${result.compilation.elapsedMs} ms`,
        'Production backend: TypeScript/emdash',
        'Lambdapi was not run; it remains the bounded conformance oracle.'
    ].join('\n');
}
