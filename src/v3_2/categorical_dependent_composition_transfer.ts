/**
 * USABILITY-DEPENDENT-1A transfer closure for section composition.
 *
 * The active kernel already owns generic categorical composition, the
 * terminal category, the Catd-hom facade reduction, and the Pi-object facade
 * reduction. This module transfers exactly that existing closure through the
 * generic declaration/runtime engines. It adds no intrinsic Core owner and
 * invents no TypeScript-only equation.
 */

import {
    CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE,
    CoreCategoricalDependentCompilation,
    compileCoreCategoricalDependentTransfer
} from './categorical_dependent_transfer';
import {
    CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE
} from './categorical_structural_transfer';
import {
    CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE,
    coreDirectedContinuationTransferSymbol
} from './directed_continuation_transfer';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferBuilderExpression,
    CoreLfTransferDeclaration,
    CoreLfTransferExpression,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferRuntimeRule,
    CoreLfTransferScopedBuilder,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    CoreLfCompiledDeclarationModule,
    CoreLfTransferDeclarationLink,
    CoreLfTransferDeclarationLinkage,
    compileCoreLfDeclarations,
    createCoreLfTransferDeclarationLinkage
} from './lf_transfer_compiler';
import {
    CoreLfMixedDeclarationContext
} from './lf_transfer_mixed';
import {
    CoreLfCompiledRuntimeProgram,
    CoreLfComposedRuntimeProgram,
    compileCoreLfRuntimeProgram
} from './lf_transfer_runtime';
import {
    binderMode
} from './kernel';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_REVISION =
    'USABILITY-DEPENDENT-1A-SECTION-COMPOSITION-TRANSFER-1' as const;

export const CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SOURCE_SHA256 =
    'sha256:ccda94c638af8d4fa7ce122967dcc30159c713846eedd53cee0df83123b48a11';

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner =
    coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const homClassifier =
    coreDirectedContinuationTransferSymbol('hom-classifier');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-category-category'
    );
const constantDisplayedFamily =
    coreDirectedContinuationTransferSymbol(
        'constant-displayed-family'
    );
const sectionCategory =
    coreDirectedContinuationTransferSymbol('section-category');
const displayedFunctorCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-functor-category'
    );

export const CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS =
Object.freeze({
    terminalCategory:
        coreLfQualifiedSymbol(MODULE_ID, 'Terminal_cat'),
    genericComposition:
        coreLfQualifiedSymbol(MODULE_ID, 'comp_fapp0')
});

const {
    terminalCategory,
    genericComposition
} = CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS;

export type CoreCategoricalDependentCompositionPrerequisiteId =
    | 'terminal-category'
    | 'generic-category-composition'
    | 'displayed-hom-classifier-reduction'
    | 'section-object-classifier-reduction';

export interface CoreCategoricalDependentCompositionPrerequisite {
    readonly id:
        CoreCategoricalDependentCompositionPrerequisiteId;
    readonly authorityName: string;
    readonly activeAuthority:
        | 'active-declaration'
        | 'active-runtime-rule';
}

export const CORE_CATEGORICAL_DEPENDENT_COMPOSITION_PREREQUISITES:
readonly CoreCategoricalDependentCompositionPrerequisite[] =
Object.freeze([
    Object.freeze({
        id: 'terminal-category' as const,
        authorityName: 'Terminal_cat',
        activeAuthority: 'active-declaration' as const
    }),
    Object.freeze({
        id: 'generic-category-composition' as const,
        authorityName: 'comp_fapp0',
        activeAuthority: 'active-declaration' as const
    }),
    Object.freeze({
        id: 'displayed-hom-classifier-reduction' as const,
        authorityName: 'Hom_cat(Catd_cat)-to-Functord_cat',
        activeAuthority: 'active-runtime-rule' as const
    }),
    Object.freeze({
        id: 'section-object-classifier-reduction' as const,
        authorityName: 'Obj(Pi_cat)-to-Obj(Functord_cat)',
        activeAuthority: 'active-runtime-rule' as const
    })
]);

const implicitMode = binderMode('implicit', 'functorial');
const explicitMode = binderMode('explicit', 'functorial');

interface BuilderArgument {
    readonly plicity: 'explicit' | 'implicit';
    readonly value: CoreLfTransferBuilderExpression;
}

const call = (
    builder: CoreLfTransferScopedBuilder,
    callee: CoreLfTransferBuilderExpression,
    arguments_: readonly BuilderArgument[]
): CoreLfTransferBuilderExpression =>
    builder.call(callee, arguments_);

const globalCall = (
    builder: CoreLfTransferScopedBuilder,
    symbol: CoreLfQualifiedSymbol,
    arguments_: readonly BuilderArgument[]
): CoreLfTransferBuilderExpression =>
    call(builder, builder.global(symbol), arguments_);

const decode = (
    builder: CoreLfTransferScopedBuilder,
    classifier: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, decodeOwner, [{
        plicity: 'explicit',
        value: classifier
    }]);

const objectType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(
        builder,
        globalCall(builder, objectClassifier, [{
            plicity: 'explicit',
            value: base
        }])
    );

const homType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(
        builder,
        globalCall(builder, homClassifier, [
            { plicity: 'explicit', value: base },
            { plicity: 'explicit', value: source },
            { plicity: 'explicit', value: target }
        ])
    );

const displayedFamilyType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    objectType(
        builder,
        globalCall(builder, displayedCategoryCategory, [{
            plicity: 'explicit',
            value: base
        }])
    );

const genericCompositionType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'X',
            objectType(builder, A),
            X => builder.pi(
                'Y',
                objectType(builder, A),
                Y => builder.pi(
                    'Z',
                    objectType(builder, A),
                    Z => builder.pi(
                        'g',
                        homType(builder, A, Y, Z),
                        _g => builder.pi(
                            'f',
                            homType(builder, A, X, Y),
                            _f => homType(builder, A, X, Z),
                            explicitMode
                        ),
                        explicitMode
                    ),
                    implicitMode
                ),
                implicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const declarations: readonly CoreLfTransferDeclaration[] = [
    {
        order: 0,
        symbol: terminalCategory,
        type: (() => {
            const builder = new CoreLfTransferScopedBuilder();
            return builder.term(builder.global(category));
        })(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'constant',
            sourceOpacity: 'opaque'
        },
        provenance: source('constant symbol Terminal_cat : Cat;')
    },
    {
        order: 1,
        symbol: genericComposition,
        type: genericCompositionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'ordinary',
            sourceOpacity: 'opaque'
        },
        provenance: source(
            'symbol comp_fapp0 : Π [A : Cat], ' +
            'Π [X_A Y_A : τ (Obj A)], Π [Z_A : τ (Obj A)]'
        )
    }
];

export const CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'usability-dependent-1a-section-composition',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        homClassifier,
        displayedCategoryCategory,
        constantDisplayedFamily,
        sectionCategory,
        displayedFunctorCategory
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_MODULE,
    {
        revision:
            'USABILITY-DEPENDENT-1A-SECTION-COMPOSITION-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_MODULE
                .revision,
        entries: declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact active v3.2 declaration signature required by the ' +
                'approved section-composition witness'
        }))
    }
);

const dependencyLink = (
    symbol: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const link = [
        ...CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE.entries,
        ...CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries,
        ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries
    ].find(candidate =>
        candidate.symbol.moduleId === symbol.moduleId &&
        candidate.symbol.name === symbol.name
    );
    if (link === undefined) {
        throw new Error(
            `USABILITY-DEPENDENT-1A has no dependency link for ` +
            `${symbol.moduleId}.${symbol.name}`
        );
    }
    return Object.freeze({
        ...link,
        order,
        symbol: Object.freeze({ ...link.symbol })
    });
};

const externalSymbols =
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_MODULE
        .externalSymbols
        .map(external => external.symbol);

export const CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_MODULE,
        {
            revision:
                'USABILITY-DEPENDENT-1A-SECTION-COMPOSITION-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_MODULE
                    .revision,
            entries: [
                ...externalSymbols.map(dependencyLink),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `emdash_v3_2_usability_dependent_1a_` +
                        declaration.symbol.name,
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

/**
 * Core's stable `hom-classifier` denotes Lambdapi
 * `Hom = Obj(Hom_cat ...)`. The active `Hom_cat(Catd_cat)` rule therefore
 * induces this classifier rule. Installing it at `Hom`, rather than beneath
 * an outer `decode`, keeps the transferred conversion reusable and lets the
 * generic congruence engine derive decoded equality.
 */
const displayedHomClassifierRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const catd = globalCall(
        builder,
        displayedCategoryCategory,
        [{ plicity: 'explicit', value: K }]
    );
    const functord = globalCall(
        builder,
        displayedFunctorCategory,
        [
            { plicity: 'implicit', value: K },
            { plicity: 'explicit', value: E },
            { plicity: 'explicit', value: D }
        ]
    );
    return {
        order: 0,
        id: 'categorical.displayed-hom-classifier.reduce',
        groupId: 'categorical.displayed-hom-classifier',
        clauseOrder: 0,
        sourceOwner: homClassifier,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'E',
                type: builder.template(
                    displayedFamilyType(builder, K)
                )
            },
            {
                name: 'D',
                type: builder.template(
                    displayedFamilyType(builder, K)
                )
            }
        ],
        left: builder.pattern(
            globalCall(builder, homClassifier, [
                { plicity: 'explicit', value: catd },
                { plicity: 'explicit', value: E },
                { plicity: 'explicit', value: D }
            ])
        ),
        right: builder.template(
            globalCall(builder, objectClassifier, [{
                plicity: 'explicit',
                value: functord
            }])
        ),
        provenance: source(
            'rule Hom_cat (@Catd_cat $K) $E $D ' +
            '↪ @Functord_cat $K $E $D;'
        )
    };
};

const sectionObjectClassifierRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const pi = globalCall(
        builder,
        sectionCategory,
        [
            { plicity: 'implicit', value: K },
            { plicity: 'explicit', value: E }
        ]
    );
    const terminalFamily = globalCall(
        builder,
        constantDisplayedFamily,
        [
            { plicity: 'explicit', value: K },
            {
                plicity: 'explicit',
                value: builder.global(terminalCategory)
            }
        ]
    );
    const functord = globalCall(
        builder,
        displayedFunctorCategory,
        [
            { plicity: 'implicit', value: K },
            { plicity: 'explicit', value: terminalFamily },
            { plicity: 'explicit', value: E }
        ]
    );
    return {
        order: 1,
        id: 'categorical.section-object-classifier.reduce',
        groupId: 'categorical.section-object-classifier',
        clauseOrder: 0,
        sourceOwner: objectClassifier,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'E',
                type: builder.template(
                    displayedFamilyType(builder, K)
                )
            }
        ],
        left: builder.pattern(
            globalCall(builder, objectClassifier, [{
                plicity: 'explicit',
                value: pi
            }])
        ),
        right: builder.template(
            globalCall(builder, objectClassifier, [{
                plicity: 'explicit',
                value: functord
            }])
        ),
        provenance: source(
            'rule Obj (@Pi_cat $K $E) ↪ Obj ' +
            '(@Functord_cat $K (@Const_catd $K Terminal_cat) $E);'
        )
    };
};

const runtimeRules = Object.freeze([
    displayedHomClassifierRule(),
    sectionObjectClassifierRule()
]);

export const CORE_CATEGORICAL_DEPENDENT_COMPOSITION_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        'USABILITY-DEPENDENT-1A-SECTION-COMPOSITION-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'usability-dependent-1a-section-composition-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        homClassifier,
        displayedCategoryCategory,
        constantDisplayedFamily,
        sectionCategory,
        displayedFunctorCategory,
        terminalCategory
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const CORE_CATEGORICAL_DEPENDENT_COMPOSITION_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_RUNTIME_MODULE,
    {
        revision:
            'USABILITY-DEPENDENT-1A-SECTION-COMPOSITION-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DEPENDENT_COMPOSITION_RUNTIME_MODULE
                .revision,
        entries: runtimeRules.map((rule, order) => ({
            order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact active v3.2 facade reduction required to check the ' +
                'generic Catd composition as a stable section'
        }))
    }
);

export const CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_BOUNDARY =
Object.freeze({
    status: 'root-only-approved-section-composition-closure',
    declarationCount: declarations.length,
    runtimeRuleCount: runtimeRules.length,
    declarationNames: Object.freeze([
        terminalCategory.name,
        genericComposition.name
    ]),
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    allEntriesUseGenericTransferEngines: true,
    classifierRulesAreInstalledAtStableCoreHeads: true,
    newIntrinsicCoreOwners: 0,
    newMathematicalRules: 0,
    proofRulesInstalled: false,
    doesNotProvide: Object.freeze([
        'general-dependent-bracket-abstraction',
        'displayed-weakening-exchange-or-contraction',
        'dependent-curry',
        'arbitrary-reindexing',
        'browser-api',
        'semantic-profile-expansion',
        'lambdapi-string-parser',
        'bulk-library-transfer'
    ])
});

export interface CoreCategoricalDependentCompositionCompilation {
    readonly dependent: CoreCategoricalDependentCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
    readonly declarationContext: CoreLfMixedDeclarationContext;
}

export function compileCoreCategoricalDependentCompositionTransfer():
CoreCategoricalDependentCompositionCompilation {
    validateCoreLfScaleEngineReview();
    const dependent =
        compileCoreCategoricalDependentTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_MODULE,
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_POLICY,
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE,
        {
            initialEnvironment: dependent.compiled.environment,
            runtimeProgram: dependent.structural.composedRuntime
        }
    );
    const initialContext = new CoreLfMixedDeclarationContext(
        dependent.declarationContext,
        [initialCompiled]
    );
    const runtime = compileCoreLfRuntimeProgram(
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_RUNTIME_MODULE,
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_RUNTIME_POLICY,
        initialContext
    );
    const composedRuntime = new CoreLfComposedRuntimeProgram([
        ...dependent.structural.composedRuntime.fragments,
        runtime
    ]);
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_MODULE,
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_POLICY,
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE,
        {
            initialEnvironment: dependent.compiled.environment,
            runtimeProgram: composedRuntime
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        dependent.declarationContext,
        [compiled]
    );
    return Object.freeze({
        dependent,
        compiled,
        runtime,
        composedRuntime,
        declarationContext
    });
}

export function coreCategoricalDependentCompositionCoreName(
    prerequisite:
        | 'terminal-category'
        | 'generic-category-composition'
): string {
    const symbol = prerequisite === 'terminal-category'
        ? terminalCategory
        : genericComposition;
    const link =
        CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE
            .entries
            .find(candidate =>
                candidate.symbol.moduleId === symbol.moduleId &&
                candidate.symbol.name === symbol.name
            );
    if (link === undefined || link.kind !== 'free-declaration') {
        throw new Error(
            `Categorical dependent composition prerequisite ` +
            `'${prerequisite}' has no free Core declaration`
        );
    }
    return link.coreName;
}
