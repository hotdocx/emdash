/**
 * USABILITY-2A0 typed transfer of closed-index displayed application.
 *
 * The active `Fibre_func` and `functord_transport_func` signatures are
 * compiled as opaque candidate declarations through the generic LF engine.
 * Their transparent Lambdapi bodies and all displayed coherence remain with
 * the active authority. In particular, this module does not invent or expose
 * the deliberately inactive whole `functord_laxity_transf`.
 */

import {
    CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE,
    CoreCategoricalStructuralCompilation,
    compileCoreCategoricalStructuralTransfer
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
    binderMode
} from './kernel';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_CATEGORICAL_DEPENDENT_TRANSFER_REVISION =
    'USABILITY-2A0-CLOSED-DISPLAYED-APPLICATION-1' as const;

export const CORE_CATEGORICAL_DEPENDENT_SOURCE_SHA256 =
    'sha256:10638f01b4bd2163b7c7cd254db76d5343b073ddbc7cc7a18c6ca2755c35a91a';

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner =
    coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const functorClassifier =
    coreDirectedContinuationTransferSymbol('functor-classifier');
const homClassifier =
    coreDirectedContinuationTransferSymbol('hom-classifier');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-category-category'
    );
const displayedFunctorCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-functor-category'
    );
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');

export const CORE_CATEGORICAL_DEPENDENT_SYMBOLS = Object.freeze({
    fibreFunctor: coreLfQualifiedSymbol(MODULE_ID, 'Fibre_func'),
    displayedTransportFunctor:
        coreLfQualifiedSymbol(MODULE_ID, 'functord_transport_func')
});

export type CoreCategoricalDependentPrerequisiteId =
    | 'displayed-functor-fibre'
    | 'displayed-functor-transport';

export interface CoreCategoricalDependentPrerequisite {
    readonly id: CoreCategoricalDependentPrerequisiteId;
    readonly symbol: CoreLfQualifiedSymbol;
    readonly activeAuthority: 'checked-transparent-definition';
}

export const CORE_CATEGORICAL_DEPENDENT_PREREQUISITES:
readonly CoreCategoricalDependentPrerequisite[] = Object.freeze([
    Object.freeze({
        id: 'displayed-functor-fibre' as const,
        symbol: CORE_CATEGORICAL_DEPENDENT_SYMBOLS.fibreFunctor,
        activeAuthority: 'checked-transparent-definition' as const
    }),
    Object.freeze({
        id: 'displayed-functor-transport' as const,
        symbol:
            CORE_CATEGORICAL_DEPENDENT_SYMBOLS
                .displayedTransportFunctor,
        activeAuthority: 'checked-transparent-definition' as const
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

const functorType = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(
        builder,
        globalCall(builder, functorClassifier, [
            { plicity: 'explicit', value: source },
            { plicity: 'explicit', value: target }
        ])
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

const displayedFunctorType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    objectType(
        builder,
        globalCall(builder, displayedFunctorCategory, [
            { plicity: 'implicit', value: base },
            { plicity: 'explicit', value: sourceFamily },
            { plicity: 'explicit', value: targetFamily }
        ])
    );

const fibreCategory = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorObject, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: builder.global(categoryOfCategories) },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: point }
    ]);

const fibreFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            E => builder.pi(
                'D',
                displayedFamilyType(builder, K),
                D => builder.pi(
                    'FF',
                    displayedFunctorType(builder, K, E, D),
                    FF => builder.pi(
                        'z',
                        objectType(builder, K),
                        z => functorType(
                            builder,
                            fibreCategory(builder, K, E, z),
                            fibreCategory(builder, K, D, z)
                        ),
                        explicitMode
                    ),
                    explicitMode
                ),
                implicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const displayedTransportFunctorType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            E => builder.pi(
                'D',
                displayedFamilyType(builder, K),
                D => builder.pi(
                    'FF',
                    displayedFunctorType(builder, K, E, D),
                    _FF => builder.pi(
                        'x',
                        objectType(builder, K),
                        x => builder.pi(
                            'y',
                            objectType(builder, K),
                            y => builder.pi(
                                'p',
                                homType(builder, K, x, y),
                                _p => functorType(
                                    builder,
                                    fibreCategory(
                                        builder,
                                        K,
                                        E,
                                        x
                                    ),
                                    fibreCategory(
                                        builder,
                                        K,
                                        D,
                                        y
                                    )
                                ),
                                explicitMode
                            ),
                            implicitMode
                        ),
                        implicitMode
                    ),
                    explicitMode
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
        symbol: CORE_CATEGORICAL_DEPENDENT_SYMBOLS.fibreFunctor,
        type: fibreFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'ordinary',
            sourceOpacity: 'transparent'
        },
        provenance: source(
            'symbol Fibre_func [K : Cat] [E D : τ (Catd K)]'
        )
    },
    {
        order: 1,
        symbol:
            CORE_CATEGORICAL_DEPENDENT_SYMBOLS
                .displayedTransportFunctor,
        type: displayedTransportFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'ordinary',
            sourceOpacity: 'transparent'
        },
        provenance: source(
            'symbol functord_transport_func [K : Cat] ' +
            '[E D : τ (Catd K)]'
        )
    }
];

export const CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_DEPENDENT_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'usability-2a0-closed-displayed-application',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_DEPENDENT_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        functorClassifier,
        homClassifier,
        categoryOfCategories,
        displayedCategoryCategory,
        displayedFunctorCategory,
        functorObject
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_CATEGORICAL_DEPENDENT_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE,
    {
        revision:
            'USABILITY-2A0-CLOSED-DISPLAYED-APPLICATION-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE.revision,
        entries: declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact active v3.2 displayed application signature; ' +
                'transparent body and coherence remain Lambdapi authority'
        }))
    }
);

const dependencyLink = (
    symbol: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const link = [
        ...CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries,
        ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries
    ].find(candidate =>
        candidate.symbol.moduleId === symbol.moduleId &&
        candidate.symbol.name === symbol.name
    );
    if (link === undefined) {
        throw new Error(
            `USABILITY-2A0 has no compiled dependency link for ` +
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
    CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE.externalSymbols.map(
        external => external.symbol
    );

export const CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE,
        {
            revision:
                'USABILITY-2A0-CLOSED-DISPLAYED-APPLICATION-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE.revision,
            entries: [
                ...externalSymbols.map(dependencyLink),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `emdash_v3_2_usability_2a0_` +
                        declaration.symbol.name,
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

export const CORE_CATEGORICAL_DEPENDENT_TRANSFER_BOUNDARY =
Object.freeze({
    status: 'root-only-closed-index-signature-transfer',
    prerequisiteCount:
        CORE_CATEGORICAL_DEPENDENT_PREREQUISITES.length,
    allCandidateDeclarationsUseGenericCompiler: true,
    candidateTransparentBodiesInstalled: false,
    runtimeRulesInstalled: false,
    proofRulesInstalled: false,
    wholeDisplayedLaxityStatus:
        'deliberately-inactive-in-authority',
    doesNotProvide: Object.freeze([
        'indexed-contextual-slot',
        'natural-or-displayed-bracket-abstraction',
        'whole-displayed-laxity-transfor',
        'new-intrinsic-core-owner',
        'owner-specific-checker-case',
        'owner-specific-evaluator-case',
        'typescript-only-categorical-computation',
        'lambdapi-string-parser',
        'browser-api',
        'semantic-profile-expansion',
        'frontend-graduation'
    ])
});

export interface CoreCategoricalDependentCompilation {
    readonly structural: CoreCategoricalStructuralCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
}

export function compileCoreCategoricalDependentTransfer():
CoreCategoricalDependentCompilation {
    validateCoreLfScaleEngineReview();
    const structural =
        compileCoreCategoricalStructuralTransfer();
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DEPENDENT_TRANSFER_MODULE,
        CORE_CATEGORICAL_DEPENDENT_TRANSFER_POLICY,
        CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE,
        {
            initialEnvironment: structural.compiled.environment,
            runtimeProgram: structural.composedRuntime
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        structural.declarationContext,
        [compiled]
    );
    return Object.freeze({
        structural,
        compiled,
        declarationContext
    });
}

export function coreCategoricalDependentCoreName(
    prerequisite: CoreCategoricalDependentPrerequisiteId
): string {
    const entry = CORE_CATEGORICAL_DEPENDENT_PREREQUISITES.find(
        candidate => candidate.id === prerequisite
    );
    if (entry === undefined) {
        throw new Error(
            `Unknown categorical dependent prerequisite ` +
            `'${prerequisite}'`
        );
    }
    const link =
        CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE.entries.find(
            candidate =>
                candidate.symbol.moduleId === entry.symbol.moduleId &&
                candidate.symbol.name === entry.symbol.name
        );
    if (link === undefined || link.kind !== 'free-declaration') {
        throw new Error(
            `Categorical dependent prerequisite '${prerequisite}' has ` +
            'no free Core declaration'
        );
    }
    return link.coreName;
}
