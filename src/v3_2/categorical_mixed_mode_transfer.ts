/**
 * MIXED-NEST-0A existing-authority transfer closure.
 *
 * The active Lambdapi kernel already owns the mixed-variance `Hom_catd` and
 * `Transf_catd` families. This fragment imports exactly those two signatures,
 * the prerequisite pointwise-opposite fibre projection, their two fibre
 * projections, and the functor-Hom classifier fold. It adds no mathematical
 * owner, rule, intrinsic Core form, or checker branch.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE
} from './categorical_displayed_chain_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_LINKAGE,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_SYMBOLS
} from './categorical_displayed_evaluation_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE
} from './categorical_displayed_nd_higher_foundation_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_LINKAGE,
    CoreCategoricalDisplayedNdHigherTargetCompilation,
    compileCoreCategoricalDisplayedNdHigherTargetTransfer
} from './categorical_displayed_nd_higher_target_transfer';
import {
    CORE_CATEGORICAL_MIXED_MODE_CORE_NAMES,
    CoreCategoricalMixedModeSymbolId,
    coreCategoricalMixedModeCoreName
} from './categorical_mixed_mode_contract';
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
    CoreLfCompiledRuntimeFragment,
    CoreLfCompiledRuntimeProgram,
    CoreLfComposedRuntimeProgram,
    compileCoreLfRuntimeFragment
} from './lf_transfer_runtime';
import {
    binderMode
} from './kernel';

export {
    CORE_CATEGORICAL_MIXED_MODE_CORE_NAMES,
    coreCategoricalMixedModeCoreName
};
export type {
    CoreCategoricalMixedModeSymbolId
};

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_CATEGORICAL_MIXED_MODE_TRANSFER_REVISION =
    'MIXED-NEST-0A-GENERIC-TRANSFER-1' as const;

export const CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256 =
    'sha256:ccda94c638af8d4fa7ce122967dcc30159c713846eedd53cee0df83123b48a11';

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner =
    coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-category-category'
    );
const sectionCategory =
    coreDirectedContinuationTransferSymbol('section-category');
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const homCategory =
    coreDirectedContinuationTransferSymbol('hom-category');
const transforCategory =
    coreDirectedContinuationTransferSymbol('transfor-category');

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const oppositeCategory = symbol('Op_cat');
const sectionObject = symbol('piapp0');

const {
    stableFunctorFamily
} = CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_SYMBOLS;

const {
    displayedOpposite
} = CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS;

export const CORE_CATEGORICAL_MIXED_MODE_SYMBOLS = Object.freeze({
    displayedHomFamily: symbol('Hom_catd'),
    displayedTransforFamily: symbol('Transf_catd')
});

const {
    displayedHomFamily,
    displayedTransforFamily
} = CORE_CATEGORICAL_MIXED_MODE_SYMBOLS;

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

const objectType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, objectClassifier, [{
        plicity: 'explicit',
        value: base
    }]));

const displayedCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedCategoryCategory, [{
        plicity: 'explicit',
        value: base
    }]);

const displayedFamilyType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    objectType(builder, displayedCategoryAt(builder, base));

const oppositeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, oppositeCategory, [{
        plicity: 'explicit',
        value: base
    }]);

const displayedOppositeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedOpposite, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const sectionCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sectionCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const sectionType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    objectType(builder, sectionCategoryAt(builder, base, family));

const stableFunctorFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, stableFunctorFamily, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]);

const displayedHomFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedHomFamily, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]);

const displayedTransforFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedTransforFamily, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: sourceFamily },
        { plicity: 'explicit', value: targetFamily },
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

const fibreAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    functorObjectAt(
        builder,
        base,
        builder.global(categoryOfCategories),
        family,
        point
    );

const sectionAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    section: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sectionObject, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: family },
        { plicity: 'explicit', value: section },
        { plicity: 'explicit', value: point }
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

const transforCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, transforCategory, [
        { plicity: 'implicit', value: sourceCategory },
        { plicity: 'implicit', value: targetCategory },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]);

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const opaqueInjectiveModifiers = Object.freeze({
    visibility: 'public' as const,
    rigidity: 'injective' as const,
    sourceOpacity: 'opaque' as const
});

const displayedHomFamilyType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            E => builder.pi(
                'X',
                sectionType(
                    builder,
                    K,
                    displayedOppositeAt(builder, K, E)
                ),
                X => builder.pi(
                    'Y',
                    sectionType(builder, K, E),
                    () => displayedFamilyType(builder, K),
                    explicitMode
                ),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const displayedTransforFamilyType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'A',
            displayedFamilyType(builder, oppositeAt(builder, K)),
            A => builder.pi(
                'B',
                displayedFamilyType(builder, K),
                B => {
                    const family = stableFunctorFamilyAt(
                        builder,
                        K,
                        A,
                        B
                    );
                    return builder.pi(
                        'FF',
                        sectionType(
                            builder,
                            K,
                            displayedOppositeAt(builder, K, family)
                        ),
                        FF => builder.pi(
                            'GG',
                            sectionType(builder, K, family),
                            () => displayedFamilyType(builder, K),
                            explicitMode
                        ),
                        explicitMode
                    );
                },
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const declarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: displayedHomFamily,
        type: displayedHomFamilyType(),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueInjectiveModifiers,
        provenance: source(
            'injective symbol Hom_catd [K : Cat] ' +
                '(E : τ (Catd K)) (X : τ (Obj (Pi_cat (Op_catd E)))) ' +
                '(Y : τ (Obj (Pi_cat E))) : τ (Catd K)'
        )
    }),
    Object.freeze({
        order: 1,
        symbol: displayedTransforFamily,
        type: displayedTransforFamilyType(),
        body: coreLfTransferAbsentBody(),
        modifiers: opaqueInjectiveModifiers,
        provenance: source(
            'injective symbol Transf_catd [K : Cat] ' +
                '(A : τ (Catd (Op_cat K))) (B : τ (Catd K))'
        )
    })
]);

const externalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    sectionCategory,
    functorObject,
    homCategory,
    transforCategory,
    oppositeCategory,
    sectionObject,
    stableFunctorFamily,
    displayedOpposite
]);

export const CORE_CATEGORICAL_MIXED_MODE_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_MIXED_MODE_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'mixed-nest-0a-signatures',
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

export const CORE_CATEGORICAL_MIXED_MODE_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_MIXED_MODE_TRANSFER_MODULE,
    {
        revision: 'MIXED-NEST-0A-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_MIXED_MODE_TRANSFER_MODULE.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact active v3.2 existing-authority mixed-family ' +
                'signature selected by the approved mixed-mode plan'
        }))
    }
);

const prerequisiteLinks = [
    ...CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE
        .entries,
    ...CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_LINKAGE.entries,
    ...CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE.entries,
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries
];

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
    const inherited = prerequisiteLinks.find(candidate =>
        symbolEquals(candidate.symbol, target)
    );
    if (inherited === undefined) {
        throw new Error(
            `MIXED-NEST-0A has no dependency link for ${target.name}`
        );
    }
    return Object.freeze({
        ...inherited,
        order,
        symbol: Object.freeze({ ...target })
    });
};

const mixedCoreName = (
    target: CoreLfQualifiedSymbol
): string => {
    const entry = Object.entries(
        CORE_CATEGORICAL_MIXED_MODE_SYMBOLS
    ).find(([, symbol_]) =>
        symbol_.moduleId === target.moduleId &&
        symbol_.name === target.name
    );
    if (entry === undefined) {
        throw new Error(
            `Mixed-mode declaration '${target.name}' has no Core name ` +
            'contract entry'
        );
    }
    return coreCategoricalMixedModeCoreName(
        entry[0] as CoreCategoricalMixedModeSymbolId
    );
};

export const CORE_CATEGORICAL_MIXED_MODE_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_MIXED_MODE_TRANSFER_MODULE,
        {
            revision: 'MIXED-NEST-0A-SIGNATURE-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_MIXED_MODE_TRANSFER_MODULE.revision,
            entries: [
                ...externalSymbols.map(dependencyLink),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName: mixedCoreName(declaration.symbol),
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

const displayedOppositeFibreRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const k = builder.capture('k');
    return {
        order: 0,
        id: 'categorical.mixed-mode.displayed-opposite-fibre',
        groupId: 'categorical.mixed-mode.displayed-opposite-fibre',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'E',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'k',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            K,
            builder.global(categoryOfCategories),
            displayedOppositeAt(builder, K, E),
            k
        )),
        right: builder.template(oppositeAt(
            builder,
            fibreAt(builder, K, E, k)
        )),
        provenance: source(
            'rule @fapp0 $K Cat_cat (@Op_catd $K $E) $k'
        )
    };
};

const homFibreRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const X = builder.capture('X');
    const Y = builder.capture('Y');
    const k = builder.capture('k');
    const oppositeE = displayedOppositeAt(builder, K, E);
    return {
        order: 1,
        id: 'categorical.mixed-mode.hom-family-fibre',
        groupId: 'categorical.mixed-mode.hom-family-fibre',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'E',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'X',
                type: builder.template(
                    sectionType(builder, K, oppositeE)
                )
            },
            {
                name: 'Y',
                type: builder.template(sectionType(builder, K, E))
            },
            {
                name: 'k',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            K,
            builder.global(categoryOfCategories),
            displayedHomFamilyAt(builder, K, E, X, Y),
            k
        )),
        right: builder.template(homCategoryAt(
            builder,
            fibreAt(builder, K, E, k),
            sectionAt(builder, K, oppositeE, X, k),
            sectionAt(builder, K, E, Y, k)
        )),
        provenance: source(
            'rule @fapp0 $K Cat_cat (@Hom_catd $K $E $X $Y) $k'
        )
    };
};

const transforFibreRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const FF = builder.capture('FF');
    const GG = builder.capture('GG');
    const k = builder.capture('k');
    const family = stableFunctorFamilyAt(builder, K, A, B);
    const oppositeFamily = displayedOppositeAt(builder, K, family);
    return {
        order: 2,
        id: 'categorical.mixed-mode.transfor-family-fibre',
        groupId: 'categorical.mixed-mode.transfor-family-fibre',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'A',
                type: builder.template(
                    displayedFamilyType(builder, oppositeAt(builder, K))
                )
            },
            {
                name: 'B',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'FF',
                type: builder.template(
                    sectionType(builder, K, oppositeFamily)
                )
            },
            {
                name: 'GG',
                type: builder.template(sectionType(builder, K, family))
            },
            {
                name: 'k',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            K,
            builder.global(categoryOfCategories),
            displayedTransforFamilyAt(builder, K, A, B, FF, GG),
            k
        )),
        right: builder.template(transforCategoryAt(
            builder,
            fibreAt(builder, oppositeAt(builder, K), A, k),
            fibreAt(builder, K, B, k),
            sectionAt(builder, K, oppositeFamily, FF, k),
            sectionAt(builder, K, family, GG, k)
        )),
        provenance: source(
            'rule @fapp0 $K Cat_cat ' +
                '(@Transf_catd $K $A $B $FF $GG) $k'
        )
    };
};

const functorHomFoldRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const FF = builder.capture('FF');
    const GG = builder.capture('GG');
    const family = stableFunctorFamilyAt(builder, K, A, B);
    const oppositeFamily = displayedOppositeAt(builder, K, family);
    return {
        order: 3,
        id: 'categorical.mixed-mode.functor-hom-fold',
        groupId: 'categorical.mixed-mode.functor-hom-fold',
        clauseOrder: 0,
        sourceOwner: displayedHomFamily,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'A',
                type: builder.template(
                    displayedFamilyType(builder, oppositeAt(builder, K))
                )
            },
            {
                name: 'B',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'FF',
                type: builder.template(
                    sectionType(builder, K, oppositeFamily)
                )
            },
            {
                name: 'GG',
                type: builder.template(sectionType(builder, K, family))
            }
        ],
        left: builder.pattern(
            displayedHomFamilyAt(builder, K, family, FF, GG)
        ),
        right: builder.template(displayedTransforFamilyAt(
            builder,
            K,
            A,
            B,
            FF,
            GG
        )),
        provenance: source(
            'rule @Hom_catd $K ' +
                '(@Functor_catd $K $A $B) $FF $GG'
        )
    };
};

const runtimeRules = Object.freeze([
    displayedOppositeFibreRule(),
    homFibreRule(),
    transforFibreRule(),
    functorHomFoldRule()
]);

export const CORE_CATEGORICAL_MIXED_MODE_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'MIXED-NEST-0A-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'mixed-nest-0a-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        ...externalSymbols,
        ...declarations.map(declaration => declaration.symbol)
    ].map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const CORE_CATEGORICAL_MIXED_MODE_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_MIXED_MODE_RUNTIME_MODULE,
    {
        revision: 'MIXED-NEST-0A-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_MIXED_MODE_RUNTIME_MODULE.revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact active v3.2 existing-authority mixed-family ' +
                'computation selected by the approved mixed-mode plan'
        }))
    }
);

export const CORE_CATEGORICAL_MIXED_MODE_TRANSFER_BOUNDARY =
Object.freeze({
    revision: CORE_CATEGORICAL_MIXED_MODE_TRANSFER_REVISION,
    decision:
        'approved-mixed-mode-architecture-and-next-slice-2026-07-31',
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
    externalCoherenceEvidenceDelta: 0,
    nestedAbstractionLowererDelta: 0,
    textOrBrowserDelta: 0,
    allEntriesUseGenericTransferEngines: true
});

export interface CoreCategoricalMixedModeCompilation {
    readonly prerequisite:
        CoreCategoricalDisplayedNdHigherTargetCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation:
    CoreCategoricalMixedModeCompilation | undefined;

export function compileCoreCategoricalMixedModeTransfer():
CoreCategoricalMixedModeCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    const prerequisite =
        compileCoreCategoricalDisplayedNdHigherTargetTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_MIXED_MODE_TRANSFER_MODULE,
        CORE_CATEGORICAL_MIXED_MODE_TRANSFER_POLICY,
        CORE_CATEGORICAL_MIXED_MODE_TRANSFER_LINKAGE,
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
        CORE_CATEGORICAL_MIXED_MODE_RUNTIME_MODULE,
        CORE_CATEGORICAL_MIXED_MODE_RUNTIME_POLICY,
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
        CORE_CATEGORICAL_MIXED_MODE_TRANSFER_MODULE,
        CORE_CATEGORICAL_MIXED_MODE_TRANSFER_POLICY,
        CORE_CATEGORICAL_MIXED_MODE_TRANSFER_LINKAGE,
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
