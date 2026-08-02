/**
 * COMPOSITIONAL-NATURAL-ACTION-CORRECTION-1B2 signatures-only transfer.
 *
 * The active kernel already owns classifier-exact pre/postwhiskering action
 * functors. This fragment imports only those two signatures; it adds no
 * runtime rule, proof rule, definition mirror, or mathematical owner.
 */

import {
    CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_LINKAGE,
    CoreCategoricalDirectMixedConstantMiddleCompilation,
    compileCoreCategoricalDirectMixedConstantMiddleTransfer
} from './categorical_direct_mixed_constant_middle_transfer';
import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE
} from './categorical_fibred_product_transfer';
import {
    CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256
} from './categorical_mixed_mode_transfer';
import {
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
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

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_REVISION =
    'COMPOSITIONAL-NATURAL-ACTION-1B2-GENERIC-TRANSFER-1' as const;

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner = coreDirectedContinuationTransferSymbol('decode');
const functorClassifier =
    coreDirectedContinuationTransferSymbol('functor-classifier');
const transforCategory =
    coreDirectedContinuationTransferSymbol('transfor-category');
const {
    functorComposition
} = CORE_CATEGORICAL_STRUCTURAL_SYMBOLS;

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

export const CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_SYMBOLS =
Object.freeze({
    prewhiskeringAction: symbol('comp_cat_con_fapp1_func'),
    postwhiskeringAction: symbol('comp_cat_cov_fapp1_func')
});

const {
    prewhiskeringAction,
    postwhiskeringAction
} = CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_SYMBOLS;

const implicitMode = binderMode('implicit', 'functorial');
const explicitMode = binderMode('explicit', 'functorial');

interface BuilderArgument {
    readonly plicity: 'explicit' | 'implicit';
    readonly value: CoreLfTransferBuilderExpression;
}

const globalCall = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfQualifiedSymbol,
    arguments_: readonly BuilderArgument[]
): CoreLfTransferBuilderExpression =>
    builder.call(builder.global(target), arguments_);

const decode = (
    builder: CoreLfTransferScopedBuilder,
    classifier: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression => globalCall(
    builder,
    decodeOwner,
    [{ plicity: 'explicit', value: classifier }]
);

const functorType = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression => decode(
    builder,
    globalCall(builder, functorClassifier, [
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ])
);

const transforCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression => globalCall(
    builder,
    transforCategory,
    [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: sourceFunctor },
        { plicity: 'explicit', value: targetFunctor }
    ]
);

const composeFunctors = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    middle: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    outer: CoreLfTransferBuilderExpression,
    inner: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression => globalCall(
    builder,
    functorComposition,
    [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: middle },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: outer },
        { plicity: 'explicit', value: inner }
    ]
);

const prewhiskeringActionType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'X',
        builder.global(category),
        X => builder.pi(
            'Y',
            builder.global(category),
            Y => builder.pi(
                'Z',
                builder.global(category),
                Z => builder.pi(
                    'L',
                    functorType(builder, X, Y),
                    L => builder.pi(
                        'F',
                        functorType(builder, Y, Z),
                        F => builder.pi(
                            'G',
                            functorType(builder, Y, Z),
                            G => functorType(
                                builder,
                                transforCategoryAt(
                                    builder,
                                    Y,
                                    Z,
                                    F,
                                    G
                                ),
                                transforCategoryAt(
                                    builder,
                                    X,
                                    Z,
                                    composeFunctors(
                                        builder,
                                        X,
                                        Y,
                                        Z,
                                        F,
                                        L
                                    ),
                                    composeFunctors(
                                        builder,
                                        X,
                                        Y,
                                        Z,
                                        G,
                                        L
                                    )
                                )
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

const postwhiskeringActionType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'X',
        builder.global(category),
        X => builder.pi(
            'Y',
            builder.global(category),
            Y => builder.pi(
                'Z',
                builder.global(category),
                Z => builder.pi(
                    'M',
                    functorType(builder, Y, Z),
                    M => builder.pi(
                        'F',
                        functorType(builder, X, Y),
                        F => builder.pi(
                            'G',
                            functorType(builder, X, Y),
                            G => functorType(
                                builder,
                                transforCategoryAt(
                                    builder,
                                    X,
                                    Y,
                                    F,
                                    G
                                ),
                                transforCategoryAt(
                                    builder,
                                    X,
                                    Z,
                                    composeFunctors(
                                        builder,
                                        X,
                                        Y,
                                        Z,
                                        M,
                                        F
                                    ),
                                    composeFunctors(
                                        builder,
                                        X,
                                        Y,
                                        Z,
                                        M,
                                        G
                                    )
                                )
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

const declarations: readonly CoreLfTransferDeclaration[] = Object.freeze([
    {
        order: 0,
        symbol: prewhiskeringAction,
        type: prewhiskeringActionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'ordinary',
            sourceOpacity: 'transparent'
        },
        provenance: source(
            'symbol comp_cat_con_fapp1_func [X Y Z : Cat]'
        )
    },
    {
        order: 1,
        symbol: postwhiskeringAction,
        type: postwhiskeringActionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'ordinary',
            sourceOpacity: 'transparent'
        },
        provenance: source(
            'symbol comp_cat_cov_fapp1_func [X Y Z : Cat]'
        )
    }
]);

const externalSymbols = Object.freeze([
    category,
    decodeOwner,
    functorClassifier,
    transforCategory,
    functorComposition
]);

export const CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'compositional-natural-action-1b2-signatures',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: externalSymbols.map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_MODULE,
    {
        revision: 'COMPOSITIONAL-NATURAL-ACTION-1B2-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_MODULE.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact pre-existing active-kernel classifier-exact action'
        }))
    }
);

const dependencyLinks = Object.freeze([
    ...CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries,
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries
]);

const dependencyLink = (
    target: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const link = dependencyLinks.find(candidate =>
        candidate.symbol.moduleId === target.moduleId &&
        candidate.symbol.name === target.name
    );
    if (link === undefined) {
        throw new Error(
            'COMPOSITIONAL-NATURAL-ACTION-1B2 has no dependency link for ' +
                `${target.moduleId}.${target.name}`
        );
    }
    return Object.freeze({
        ...link,
        order,
        symbol: Object.freeze({ ...link.symbol })
    });
};

export const CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage = createCoreLfTransferDeclarationLinkage(
    CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_MODULE,
    {
        revision: 'COMPOSITIONAL-NATURAL-ACTION-1B2-LINKAGE-1',
        moduleRevision:
            CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_MODULE.revision,
        entries: [
            ...externalSymbols.map(dependencyLink),
            ...declarations.map((declaration, index) => ({
                order: externalSymbols.length + index,
                symbol: declaration.symbol,
                kind: 'free-declaration' as const,
                coreName:
                    'emdash_v3_2_compositional_natural_1b2_' +
                    declaration.symbol.name,
                backendName: declaration.symbol.name
            }))
        ]
    }
);

const declarationCoreName = (target: CoreLfQualifiedSymbol): string => {
    const entry =
        CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_LINKAGE.entries.find(
            candidate =>
                candidate.symbol.moduleId === target.moduleId &&
                candidate.symbol.name === target.name
        );
    if (entry === undefined || entry.kind !== 'free-declaration') {
        throw new Error(
            'COMPOSITIONAL-NATURAL-ACTION-1B2 lost declaration link for ' +
                `${target.moduleId}.${target.name}`
        );
    }
    return entry.coreName;
};

export const CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_CORE_NAMES =
Object.freeze({
    prewhiskeringAction: declarationCoreName(prewhiskeringAction),
    postwhiskeringAction: declarationCoreName(postwhiskeringAction)
});

export type CoreCategoricalCompositionalNaturalSymbolId =
    keyof typeof CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_CORE_NAMES;

export function coreCategoricalCompositionalNaturalCoreName(
    id: CoreCategoricalCompositionalNaturalSymbolId
): string {
    return CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_CORE_NAMES[id];
}

export const CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_BOUNDARY =
Object.freeze({
    decision: 'D-DTTLF-USABILITY-075',
    declarationNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    declarationCount: declarations.length,
    runtimeRuleCount: 0,
    proofRuleCount: 0,
    activeKernelOwnerDelta: 0,
    importedExistingOwnerCount: declarations.length,
    coreNodeDelta: 0,
    checkerBranchDelta: 0,
    externalCoherenceEvidenceDelta: 0
});

export interface CoreCategoricalCompositionalNaturalCompilation {
    readonly prerequisite:
        CoreCategoricalDirectMixedConstantMiddleCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment:
        CoreCategoricalDirectMixedConstantMiddleCompilation[
            'runtimeFragment'
        ];
    readonly runtime:
        CoreCategoricalDirectMixedConstantMiddleCompilation['runtime'];
    readonly composedRuntime:
        CoreCategoricalDirectMixedConstantMiddleCompilation[
            'composedRuntime'
        ];
}

let cachedCompilation:
    CoreCategoricalCompositionalNaturalCompilation | undefined;

export function compileCoreCategoricalCompositionalNaturalTransfer():
CoreCategoricalCompositionalNaturalCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    const prerequisite =
        compileCoreCategoricalDirectMixedConstantMiddleTransfer();
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_MODULE,
        CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_POLICY,
        CORE_CATEGORICAL_COMPOSITIONAL_NATURAL_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: prerequisite.composedRuntime,
            comparisonStepLimit: 512
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        prerequisite.declarationContext,
        [compiled]
    );
    cachedCompilation = Object.freeze({
        prerequisite,
        compiled,
        declarationContext,
        runtimeFragment: prerequisite.runtimeFragment,
        runtime: prerequisite.runtime,
        composedRuntime: prerequisite.composedRuntime
    });
    return cachedCompilation;
}
