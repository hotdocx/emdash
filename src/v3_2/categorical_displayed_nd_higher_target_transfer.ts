/**
 * DISPLAYED-ND-HIGHER-TARGET-1A generic transfer.
 *
 * This fragment installs the three active next-hom action interfaces and
 * their two projection rules over the dependency-closed D-020 foundation.
 * All five commands already belong to active emdash v3.2 authority.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
} from './categorical_displayed_nd_higher_audit';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE,
    CoreCategoricalDisplayedNdHigherFoundationCompilation,
    compileCoreCategoricalDisplayedNdHigherFoundationTransfer
} from './categorical_displayed_nd_higher_foundation_transfer';
import {
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
    CoreLfCompiledRuntimeFragment,
    CoreLfCompiledRuntimeProgram,
    CoreLfComposedRuntimeProgram,
    compileCoreLfRuntimeFragment
} from './lf_transfer_runtime';
import {
    binderMode
} from './kernel';

const MODULE_ID = 'emdash.emdash3_2';
const SOURCE_SHA256 =
    'sha256:' +
    '4d5791fc95c158308b87c970b622da35c2dd0ec64bd32b7f535679a95eba195a';

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_REVISION =
    'DISPLAYED-ND-HIGHER-TARGET-1A-GENERIC-TRANSFER-1' as const;

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner =
    coreDirectedContinuationTransferSymbol('decode');
const functorClassifier =
    coreDirectedContinuationTransferSymbol('functor-classifier');
const homCategory =
    coreDirectedContinuationTransferSymbol('hom-category');
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const functorHomFull =
    coreDirectedContinuationTransferSymbol('functor-hom-full');

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const displayedFamilyClassifier = symbol('Catd');
const displayedFunctorClassifier = symbol('Functord');
const displayedTransformationClassifier = symbol('Transfd');
const displayedTransformationCategory = symbol('Transfd_cat');
const displayedIdentity = symbol('id_funcd');

const {
    displayedComposition,
    displayedOpposite,
    displayedOppositeAction,
    displayedHomTarget,
    displayedInternalHom
} = CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS;

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_SYMBOLS =
Object.freeze({
    actionFunctor: symbol('tdapp1_int_func_transfd'),
    objectAction: symbol('tdapp1_int_fapp0_transfd'),
    nextHomAction: symbol('tdapp1_int_fapp1_func_transfd')
});

const {
    actionFunctor,
    objectAction,
    nextHomAction
} = CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_SYMBOLS;

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
    target: CoreLfQualifiedSymbol,
    arguments_: readonly BuilderArgument[]
): CoreLfTransferBuilderExpression =>
    call(builder, builder.global(target), arguments_);

const decode = (
    builder: CoreLfTransferScopedBuilder,
    classifier: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, decodeOwner, [{
        plicity: 'explicit',
        value: classifier
    }]);

const functorType = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, functorClassifier, [
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]));

const displayedFamilyType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, displayedFamilyClassifier, [{
        plicity: 'explicit',
        value: base
    }]));

const displayedFunctorType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, displayedFunctorClassifier, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: sourceFamily },
        { plicity: 'explicit', value: targetFamily }
    ]));

const displayedTransformationType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(
        builder,
        displayedTransformationClassifier,
        [
            { plicity: 'implicit', value: base },
            { plicity: 'implicit', value: sourceFamily },
            { plicity: 'implicit', value: targetFamily },
            { plicity: 'explicit', value: sourceFunctor },
            { plicity: 'explicit', value: targetFunctor }
        ]
    ));

const displayedTransformationCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedTransformationCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: sourceFunctor },
        { plicity: 'explicit', value: targetFunctor }
    ]);

const displayedIdentityAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedIdentity, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: family }
    ]);

const displayedOppositeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedOpposite, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const displayedOppositeActionAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedOppositeAction, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: functor }
    ]);

const displayedHomTargetAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedHomTarget, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const displayedInternalHomAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedInternalHom, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: functor }
    ]);

const displayedComposeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    middleFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    outer: CoreLfTransferBuilderExpression,
    inner: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedComposition, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: middleFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: outer },
        { plicity: 'explicit', value: inner }
    ]);

const homCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, homCategory, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]);

const functorObjectAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorObject, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: object }
    ]);

const functorHomFullAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorHomFull, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: functor },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject }
    ]);

interface TargetEndpoints {
    readonly sourceCategory: CoreLfTransferBuilderExpression;
    readonly targetCategory: CoreLfTransferBuilderExpression;
    readonly targetSourceFamily: CoreLfTransferBuilderExpression;
    readonly targetTargetFamily: CoreLfTransferBuilderExpression;
    readonly targetSourceFunctor: CoreLfTransferBuilderExpression;
    readonly targetTargetFunctor: CoreLfTransferBuilderExpression;
}

const targetEndpoints = (
    builder: CoreLfTransferScopedBuilder,
    K: CoreLfTransferBuilderExpression,
    E: CoreLfTransferBuilderExpression,
    D: CoreLfTransferBuilderExpression,
    FF: CoreLfTransferBuilderExpression,
    GG: CoreLfTransferBuilderExpression
): TargetEndpoints => {
    const sourceCategory = displayedTransformationCategoryAt(
        builder,
        K,
        E,
        D,
        FF,
        GG
    );
    const oppositeE = displayedOppositeAt(builder, K, E);
    const oppositeD = displayedOppositeAt(builder, K, D);
    const homTargetE = displayedHomTargetAt(builder, K, E);
    const sourceFunctor = displayedInternalHomAt(
        builder,
        K,
        E,
        E,
        displayedIdentityAt(builder, K, E)
    );
    const targetFunctor = displayedComposeAt(
        builder,
        K,
        oppositeE,
        oppositeD,
        homTargetE,
        displayedInternalHomAt(builder, K, E, D, GG),
        displayedOppositeActionAt(builder, K, E, D, FF)
    );
    return {
        sourceCategory,
        targetCategory: displayedTransformationCategoryAt(
            builder,
            K,
            oppositeE,
            homTargetE,
            sourceFunctor,
            targetFunctor
        ),
        targetSourceFamily: oppositeE,
        targetTargetFamily: homTargetE,
        targetSourceFunctor: sourceFunctor,
        targetTargetFunctor: targetFunctor
    };
};

const actionFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    K: CoreLfTransferBuilderExpression,
    E: CoreLfTransferBuilderExpression,
    D: CoreLfTransferBuilderExpression,
    FF: CoreLfTransferBuilderExpression,
    GG: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, actionFunctor, [
        { plicity: 'implicit', value: K },
        { plicity: 'implicit', value: E },
        { plicity: 'implicit', value: D },
        { plicity: 'implicit', value: FF },
        { plicity: 'implicit', value: GG }
    ]);

const objectActionAt = (
    builder: CoreLfTransferScopedBuilder,
    K: CoreLfTransferBuilderExpression,
    E: CoreLfTransferBuilderExpression,
    D: CoreLfTransferBuilderExpression,
    FF: CoreLfTransferBuilderExpression,
    GG: CoreLfTransferBuilderExpression,
    epsilon: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, objectAction, [
        { plicity: 'implicit', value: K },
        { plicity: 'implicit', value: E },
        { plicity: 'implicit', value: D },
        { plicity: 'implicit', value: FF },
        { plicity: 'implicit', value: GG },
        { plicity: 'explicit', value: epsilon }
    ]);

const nextHomActionAt = (
    builder: CoreLfTransferScopedBuilder,
    K: CoreLfTransferBuilderExpression,
    E: CoreLfTransferBuilderExpression,
    D: CoreLfTransferBuilderExpression,
    FF: CoreLfTransferBuilderExpression,
    GG: CoreLfTransferBuilderExpression,
    epsilon: CoreLfTransferBuilderExpression,
    epsilonPrime: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, nextHomAction, [
        { plicity: 'implicit', value: K },
        { plicity: 'implicit', value: E },
        { plicity: 'implicit', value: D },
        { plicity: 'implicit', value: FF },
        { plicity: 'implicit', value: GG },
        { plicity: 'explicit', value: epsilon },
        { plicity: 'explicit', value: epsilonPrime }
    ]);

const source = (
    sourceFragment: string,
    canonicalCommandOrdinal: number
) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment,
    canonicalCommandOrdinal
});

const opaqueModifiers = {
    visibility: 'public' as const,
    rigidity: 'ordinary' as const,
    sourceOpacity: 'opaque' as const
};

const actionFunctorType = (): CoreLfTransferExpression => {
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
                        'GG',
                        displayedFunctorType(builder, K, E, D),
                        GG => {
                            const endpoints =
                                targetEndpoints(builder, K, E, D, FF, GG);
                            return functorType(
                                builder,
                                endpoints.sourceCategory,
                                endpoints.targetCategory
                            );
                        },
                        implicitMode
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

const objectActionType = (): CoreLfTransferExpression => {
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
                        'GG',
                        displayedFunctorType(builder, K, E, D),
                        GG => {
                            const endpoints =
                                targetEndpoints(builder, K, E, D, FF, GG);
                            return builder.pi(
                                'epsilon',
                                displayedTransformationType(
                                    builder,
                                    K,
                                    E,
                                    D,
                                    FF,
                                    GG
                                ),
                                _epsilon => displayedTransformationType(
                                    builder,
                                    K,
                                    endpoints.targetSourceFamily,
                                    endpoints.targetTargetFamily,
                                    endpoints.targetSourceFunctor,
                                    endpoints.targetTargetFunctor
                                ),
                                explicitMode
                            );
                        },
                        implicitMode
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

const nextHomActionType = (): CoreLfTransferExpression => {
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
                        'GG',
                        displayedFunctorType(builder, K, E, D),
                        GG => {
                            const endpoints =
                                targetEndpoints(builder, K, E, D, FF, GG);
                            const epsilonType =
                                displayedTransformationType(
                                    builder,
                                    K,
                                    E,
                                    D,
                                    FF,
                                    GG
                                );
                            return builder.pi(
                                'epsilon',
                                epsilonType,
                                epsilon => builder.pi(
                                    'epsilonPrime',
                                    epsilonType,
                                    epsilonPrime => functorType(
                                        builder,
                                        homCategoryAt(
                                            builder,
                                            endpoints.sourceCategory,
                                            epsilon,
                                            epsilonPrime
                                        ),
                                        homCategoryAt(
                                            builder,
                                            endpoints.targetCategory,
                                            objectActionAt(
                                                builder,
                                                K,
                                                E,
                                                D,
                                                FF,
                                                GG,
                                                epsilon
                                            ),
                                            objectActionAt(
                                                builder,
                                                K,
                                                E,
                                                D,
                                                FF,
                                                GG,
                                                epsilonPrime
                                            )
                                        )
                                    ),
                                    explicitMode
                                ),
                                explicitMode
                            );
                        },
                        implicitMode
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

const declarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: actionFunctor,
        type: actionFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: source(
            'symbol tdapp1_int_func_transfd : Π [K : Cat]',
            1073
        )
    }),
    Object.freeze({
        order: 1,
        symbol: objectAction,
        type: objectActionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: source(
            'symbol tdapp1_int_fapp0_transfd : Π [K : Cat]',
            1074
        )
    }),
    Object.freeze({
        order: 2,
        symbol: nextHomAction,
        type: nextHomActionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueModifiers,
        provenance: source(
            'symbol tdapp1_int_fapp1_func_transfd : Π [K : Cat]',
            1076
        )
    })
]);

const targetExternalSymbols = Object.freeze([
    category,
    decodeOwner,
    functorClassifier,
    homCategory,
    functorObject,
    functorHomFull,
    displayedFamilyClassifier,
    displayedFunctorClassifier,
    displayedTransformationClassifier,
    displayedTransformationCategory,
    displayedIdentity,
    displayedComposition,
    displayedOpposite,
    displayedOppositeAction,
    displayedHomTarget,
    displayedInternalHom
]);

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'displayed-nd-higher-target-1a-signatures',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: SOURCE_SHA256,
    dependencies: [],
    externalSymbols: targetExternalSymbols.map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_MODULE,
    {
        revision:
            'DISPLAYED-ND-HIGHER-TARGET-1A-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_MODULE
                .revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact active existing-authority interface approved by ' +
                'D-DTTLF-USABILITY-021'
        }))
    }
);

const prerequisiteLinks = [
    ...CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE
        .entries
];

const auditedCoreLinks =
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
        .dependencyBoundary.alreadyAvailableCoreOwnerLinks;
const auditedFreeLinks =
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
        .dependencyBoundary.alreadyAvailableFreeDeclarationLinks;

const symbolEquals = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId &&
    left.name === right.name;

const dependencyLink = (
    target: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const inherited = prerequisiteLinks.find(link =>
        symbolEquals(link.symbol, target)
    );
    if (inherited !== undefined) {
        return Object.freeze({
            ...inherited,
            order,
            symbol: Object.freeze({ ...target })
        });
    }
    const core = auditedCoreLinks.find(link =>
        link.symbol === target.name
    );
    if (core !== undefined) {
        return Object.freeze({
            order,
            symbol: target,
            kind: 'core-owner' as const,
            owner: core.owner
        });
    }
    const free = auditedFreeLinks.find(link =>
        link.symbol === target.name
    );
    if (free !== undefined) {
        return Object.freeze({
            order,
            symbol: target,
            kind: 'free-declaration' as const,
            coreName: free.coreName,
            backendName: free.symbol
        });
    }
    throw new Error(
        `No displayed higher target dependency link for ${target.name}`
    );
};

const targetCoreName = (
    target: CoreLfQualifiedSymbol
): string =>
    'emdash_v3_2_displayed_nd_higher_target_' + target.name;

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_MODULE,
        {
            revision:
                'DISPLAYED-ND-HIGHER-TARGET-1A-SIGNATURE-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_MODULE
                    .revision,
            entries: [
                ...targetExternalSymbols.map(dependencyLink),
                ...declarations.map((declaration, index) => ({
                    order: targetExternalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName: targetCoreName(declaration.symbol),
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

interface RuntimeVariables {
    readonly K: CoreLfTransferBuilderExpression;
    readonly E: CoreLfTransferBuilderExpression;
    readonly D: CoreLfTransferBuilderExpression;
    readonly FF: CoreLfTransferBuilderExpression;
    readonly GG: CoreLfTransferBuilderExpression;
    readonly epsilon: CoreLfTransferBuilderExpression;
    readonly epsilonPrime?: CoreLfTransferBuilderExpression;
    readonly variables: CoreLfTransferRuntimeRule['variables'];
}

const runtimeVariables = (
    builder: CoreLfTransferScopedBuilder,
    includeTarget: boolean
): RuntimeVariables => {
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const FF = builder.capture('FF');
    const GG = builder.capture('GG');
    const epsilon = builder.capture('epsilon');
    const epsilonPrime = includeTarget
        ? builder.capture('epsilonPrime')
        : undefined;
    const epsilonType = displayedTransformationType(
        builder,
        K,
        E,
        D,
        FF,
        GG
    );
    const variables: CoreLfTransferRuntimeRule['variables'] = [
        {
            name: 'K',
            type: builder.template(builder.global(category))
        },
        {
            name: 'E',
            type: builder.template(displayedFamilyType(builder, K))
        },
        {
            name: 'D',
            type: builder.template(displayedFamilyType(builder, K))
        },
        {
            name: 'FF',
            type: builder.template(displayedFunctorType(builder, K, E, D))
        },
        {
            name: 'GG',
            type: builder.template(displayedFunctorType(builder, K, E, D))
        },
        {
            name: 'epsilon',
            type: builder.template(epsilonType)
        },
        ...(epsilonPrime === undefined
            ? []
            : [{
                name: 'epsilonPrime',
                type: builder.template(epsilonType)
            }])
    ];
    return {
        K,
        E,
        D,
        FF,
        GG,
        epsilon,
        epsilonPrime,
        variables
    };
};

const objectProjectionRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const {
        K, E, D, FF, GG, epsilon, variables
    } = runtimeVariables(builder, false);
    const endpoints = targetEndpoints(builder, K, E, D, FF, GG);
    return {
        order: 0,
        id: 'categorical.displayed-nd-higher.object-projection',
        groupId: 'categorical.displayed-nd-higher',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables,
        left: builder.pattern(functorObjectAt(
            builder,
            endpoints.sourceCategory,
            endpoints.targetCategory,
            actionFunctorAt(builder, K, E, D, FF, GG),
            epsilon
        )),
        right: builder.template(objectActionAt(
            builder,
            K,
            E,
            D,
            FF,
            GG,
            epsilon
        )),
        provenance: source(
            'rule fapp0 (@tdapp1_int_func_transfd $K $E $D $FF $GG) $ϵ',
            1075
        )
    };
};

const nextHomProjectionRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const {
        K, E, D, FF, GG, epsilon, epsilonPrime, variables
    } = runtimeVariables(builder, true);
    if (epsilonPrime === undefined) {
        throw new Error('Missing higher-action target endpoint');
    }
    const endpoints = targetEndpoints(builder, K, E, D, FF, GG);
    return {
        order: 1,
        id: 'categorical.displayed-nd-higher.next-hom-projection',
        groupId: 'categorical.displayed-nd-higher',
        clauseOrder: 1,
        sourceOwner: functorHomFull,
        variables,
        left: builder.pattern(functorHomFullAt(
            builder,
            endpoints.sourceCategory,
            endpoints.targetCategory,
            actionFunctorAt(builder, K, E, D, FF, GG),
            epsilon,
            epsilonPrime
        )),
        right: builder.template(nextHomActionAt(
            builder,
            K,
            E,
            D,
            FF,
            GG,
            epsilon,
            epsilonPrime
        )),
        provenance: source(
            'rule @fapp1_func _ _ ' +
                '(@tdapp1_int_func_transfd $K $E $D $FF $GG) $ϵ $ϵ\'',
            1077
        )
    };
};

const runtimeRules:
readonly CoreLfTransferRuntimeRule[] = Object.freeze([
    objectProjectionRule(),
    nextHomProjectionRule()
]);

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'DISPLAYED-ND-HIGHER-TARGET-1A-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'displayed-nd-higher-target-1a-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        ...targetExternalSymbols,
        actionFunctor,
        objectAction,
        nextHomAction
    ].map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_RUNTIME_MODULE,
    {
        revision:
            'DISPLAYED-ND-HIGHER-TARGET-1A-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_RUNTIME_MODULE
                .revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact active existing-authority projection approved by ' +
                'D-DTTLF-USABILITY-021'
        }))
    }
);

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_CORE_NAMES =
Object.freeze({
    actionFunctor: targetCoreName(actionFunctor),
    objectAction: targetCoreName(objectAction),
    nextHomAction: targetCoreName(nextHomAction)
});

export type CoreCategoricalDisplayedNdHigherTargetSymbolId =
    | 'action-functor'
    | 'object-action'
    | 'next-hom-action';

const coreNameById:
Readonly<Record<
    CoreCategoricalDisplayedNdHigherTargetSymbolId,
    string
>> = Object.freeze({
    'action-functor':
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_CORE_NAMES.actionFunctor,
    'object-action':
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_CORE_NAMES.objectAction,
    'next-hom-action':
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_CORE_NAMES.nextHomAction
});

export function coreCategoricalDisplayedNdHigherTargetCoreName(
    id: CoreCategoricalDisplayedNdHigherTargetSymbolId
): string {
    return coreNameById[id];
}

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_BOUNDARY =
Object.freeze({
    revision: CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_REVISION,
    proposalCheckpoint:
        'fead6e10a625c0402eb6e5c2f6336c797e70f29e',
    decision: 'D-DTTLF-USABILITY-021-approved-as-proposed',
    declarationNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    declarationCount: declarations.length,
    runtimeRuleCount: runtimeRules.length,
    proofRuleCount: 0,
    activeLambdapiOwnerDelta: 0,
    activeLambdapiRuleDelta: 0,
    intrinsicCoreOwnerDelta: 0,
    ownerSpecificCheckerOrEvaluatorDelta: 0,
    contextualIrNodeDelta: 0,
    binderModeDelta: 0,
    surfaceMethodCount: 2,
    browserPromotionDelta: 0,
    allEntriesUseGenericTransferEngines: true
});

export interface CoreCategoricalDisplayedNdHigherTargetCompilation {
    readonly prerequisite:
        CoreCategoricalDisplayedNdHigherFoundationCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation:
    CoreCategoricalDisplayedNdHigherTargetCompilation | undefined;

export function compileCoreCategoricalDisplayedNdHigherTargetTransfer():
CoreCategoricalDisplayedNdHigherTargetCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    const prerequisite =
        compileCoreCategoricalDisplayedNdHigherFoundationTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_MODULE,
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_POLICY,
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: prerequisite.composedRuntime,
            comparisonStepLimit: 512
        }
    );
    const initialContext = new CoreLfMixedDeclarationContext(
        prerequisite.declarationContext,
        [initialCompiled]
    );
    const runtimeFragment = compileCoreLfRuntimeFragment(
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_RUNTIME_MODULE,
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_RUNTIME_POLICY,
        initialContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: prerequisite.runtimeFragment
            }],
            comparisonStepLimit: 512
        }
    );
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_MODULE,
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_POLICY,
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: runtimeFragment.runtime,
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
        runtimeFragment,
        runtime: runtimeFragment.localProgram,
        composedRuntime: runtimeFragment.runtime
    });
    return cachedCompilation;
}
