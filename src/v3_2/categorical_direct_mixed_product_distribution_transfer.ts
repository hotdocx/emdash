/**
 * DIRECT-MIXED-PRODUCT-DISTRIBUTION-1G generic transfer.
 *
 * One active displayed functor distributes a pair of mixed functors into a
 * pointwise product target. Its point/full/capped projections are compiled by
 * the generic LF declaration/runtime engines; no intrinsic Core owner or
 * owner-specific checker/evaluator path is added.
 */

import {
    CoreCategoricalDirectMixedSourceActionCompilation,
    compileCoreCategoricalDirectMixedSourceActionTransfer
} from './categorical_direct_mixed_source_action_transfer';
import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE
} from './categorical_fibred_product_transfer';
import {
    CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE
} from './categorical_fibred_structure_transfer';
import {
    CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_LINKAGE
} from './categorical_mixed_action_transfer';
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

export const
CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_REVISION =
    'DIRECT-MIXED-PRODUCT-DISTRIBUTION-1G-GENERIC-TRANSFER-1' as const;

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner = coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const homClassifier =
    coreDirectedContinuationTransferSymbol('hom-classifier');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol('displayed-category-category');
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const functorHomFull =
    coreDirectedContinuationTransferSymbol('functor-hom-full');
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const transforComponentCapped =
    coreDirectedContinuationTransferSymbol('transfor-component-capped');
const transforHomFull =
    coreDirectedContinuationTransferSymbol('transfor-hom-full');
const transforHomCapped =
    coreDirectedContinuationTransferSymbol('transfor-hom-capped');

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const displayedFamilyClassifier = symbol('Catd');
const displayedFunctorClassifier = symbol('Functord');
const oppositeCategory = symbol('Op_cat');
const stableFunctorFamily = symbol('Functor_catd');

const {
    functorCategory,
    identityFunctor,
    functorComposition,
    productCategory,
    productPair,
    uncurryPackage
} = CORE_CATEGORICAL_STRUCTURAL_SYMBOLS;
const {
    internalProductFunctor
} = CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS;

export const
CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_SYMBOLS =
Object.freeze({
    distributor:
        coreLfQualifiedSymbol(MODULE_ID, 'Functor_catd_product_funcd')
});

const {
    distributor
} = CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_SYMBOLS;

const implicitMode = binderMode('implicit', 'functorial');

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

const homType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, homClassifier, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]));

const oppositeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, oppositeCategory, [{
        plicity: 'explicit',
        value: base
    }]);

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

const functorCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorCategory, [
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]);

const productCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, productCategory, [
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
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

const functorHomCappedAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorHomCapped, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: functor },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: arrow }
    ]);

const transforComponentAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression,
    transfor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, transforComponentCapped, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: sourceFunctor },
        { plicity: 'implicit', value: targetFunctor },
        { plicity: 'explicit', value: object },
        { plicity: 'explicit', value: transfor }
    ]);

const transforHomFullAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    transfor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, transforHomFull, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: sourceFunctor },
        { plicity: 'implicit', value: targetFunctor },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: transfor }
    ]);

const transforHomCappedAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    transfor: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, transforHomCapped, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: sourceFunctor },
        { plicity: 'implicit', value: targetFunctor },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: transfor },
        { plicity: 'explicit', value: arrow }
    ]);

const pairAt = (
    builder: CoreLfTransferScopedBuilder,
    leftCategory: CoreLfTransferBuilderExpression,
    rightCategory: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, productPair, [
        { plicity: 'implicit', value: leftCategory },
        { plicity: 'implicit', value: rightCategory },
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
    ]);

const composeFunctorsAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    middle: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    outer: CoreLfTransferBuilderExpression,
    inner: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorComposition, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: middle },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: outer },
        { plicity: 'explicit', value: inner }
    ]);

const transparentDisplayedProduct = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression => {
    const cat = builder.global(categoryOfCategories);
    const catProduct = productCategoryAt(builder, cat, cat);
    const catEndofunctors = functorCategoryAt(builder, cat, cat);
    const uncurriedProduct = functorObjectAt(
        builder,
        functorCategoryAt(builder, cat, catEndofunctors),
        functorCategoryAt(builder, catProduct, cat),
        globalCall(builder, uncurryPackage, [
            { plicity: 'implicit', value: cat },
            { plicity: 'implicit', value: cat },
            { plicity: 'implicit', value: cat }
        ]),
        builder.global(internalProductFunctor)
    );
    const familyCategory = functorCategoryAt(builder, base, cat);
    return composeFunctorsAt(
        builder,
        base,
        catProduct,
        cat,
        uncurriedProduct,
        pairAt(builder, familyCategory, familyCategory, left, right)
    );
};

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

const stableFunctorFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, stableFunctorFamily, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: sourceFamily },
        { plicity: 'explicit', value: targetFamily }
    ]);

const distributorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    leftTarget: CoreLfTransferBuilderExpression,
    rightTarget: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, distributor, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: leftTarget },
        { plicity: 'implicit', value: rightTarget }
    ]);

const distributorFamilies = (
    builder: CoreLfTransferScopedBuilder,
    K: CoreLfTransferBuilderExpression,
    A: CoreLfTransferBuilderExpression,
    B: CoreLfTransferBuilderExpression,
    C: CoreLfTransferBuilderExpression
) => {
    const left = stableFunctorFamilyAt(builder, K, A, B);
    const right = stableFunctorFamilyAt(builder, K, A, C);
    return {
        source: transparentDisplayedProduct(builder, K, left, right),
        target: stableFunctorFamilyAt(
            builder,
            K,
            A,
            transparentDisplayedProduct(builder, K, B, C)
        )
    };
};

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const distributorType = (): CoreLfTransferExpression => {
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
                B => builder.pi(
                    'C',
                    displayedFamilyType(builder, K),
                    C => {
                        const families = distributorFamilies(
                            builder,
                            K,
                            A,
                            B,
                            C
                        );
                        return displayedFunctorType(
                            builder,
                            K,
                            families.source,
                            families.target
                        );
                    },
                    implicitMode
                ),
                implicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const declarations: readonly CoreLfTransferDeclaration[] = Object.freeze([
    {
        order: 0,
        symbol: distributor,
        type: distributorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'injective',
            sourceOpacity: 'opaque'
        },
        provenance: source(
            'injective symbol Functor_catd_product_funcd [K : Cat]'
        )
    }
]);

export const
CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'direct-mixed-product-distribution-1g-signature',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        homClassifier,
        categoryOfCategories,
        displayedCategoryCategory,
        functorObject,
        functorHomFull,
        functorHomCapped,
        transforComponentCapped,
        transforHomFull,
        transforHomCapped,
        displayedFamilyClassifier,
        displayedFunctorClassifier,
        oppositeCategory,
        stableFunctorFamily,
        functorCategory,
        identityFunctor,
        functorComposition,
        productCategory,
        productPair,
        uncurryPackage,
        internalProductFunctor
    ].map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const
CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_MODULE,
    {
        revision:
            'DIRECT-MIXED-PRODUCT-DISTRIBUTION-1G-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_MODULE
                .revision,
        entries: [{
            order: 0,
            target: {
                kind: 'declaration' as const,
                symbol: distributor
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact D-DTTLF-USABILITY-048 active injective owner'
        }]
    }
);

const dependencyLinks = Object.freeze([
    ...CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE.entries,
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
            'DIRECT-MIXED-PRODUCT-DISTRIBUTION-1G has no dependency link ' +
                `for ${target.moduleId}.${target.name}`
        );
    }
    return Object.freeze({
        ...link,
        order,
        symbol: Object.freeze({ ...link.symbol })
    });
};

const externalSymbols =
    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_MODULE
        .externalSymbols
        .map(external => external.symbol);

export const
CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_MODULE,
        {
            revision:
                'DIRECT-MIXED-PRODUCT-DISTRIBUTION-1G-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_MODULE
                    .revision,
            entries: [
                ...externalSymbols.map(dependencyLink),
                {
                    order: externalSymbols.length,
                    symbol: distributor,
                    kind: 'free-declaration' as const,
                    coreName:
                        'emdash_v3_2_direct_mixed_product_1g_' +
                        'Functor_catd_product_funcd',
                    backendName: distributor.name
                }
            ]
        }
    );

const pointRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const k = builder.capture('k');
    const families = distributorFamilies(builder, K, A, B, C);
    const cat = builder.global(categoryOfCategories);
    const sourceFibre = fibreAt(builder, oppositeAt(builder, K), A, k);
    return {
        order: 0,
        id: 'categorical.direct-mixed-product-distribution.point',
        groupId: 'categorical.direct-mixed-product-distribution',
        clauseOrder: 0,
        sourceOwner: transforComponentCapped,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'A',
                type: builder.template(displayedFamilyType(
                    builder,
                    oppositeAt(builder, K)
                ))
            },
            {
                name: 'B',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'C',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'k',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(transforComponentAt(
            builder,
            K,
            cat,
            builder.wildcard(families.source),
            builder.wildcard(families.target),
            k,
            distributorAt(builder, K, A, B, C)
        )),
        right: builder.template(globalCall(builder, identityFunctor, [{
            plicity: 'implicit',
            value: productCategoryAt(
                builder,
                functorCategoryAt(
                    builder,
                    sourceFibre,
                    fibreAt(builder, K, B, k)
                ),
                functorCategoryAt(
                    builder,
                    sourceFibre,
                    fibreAt(builder, K, C, k)
                )
            )
        }])),
        provenance: source(
            'rule @tapp0_fapp0 $K Cat_cat _ _ $k ' +
                '(@Functor_catd_product_funcd $K $A $B $C)'
        )
    };
};

const fullRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const families = distributorFamilies(builder, K, A, B, C);
    const cat = builder.global(categoryOfCategories);
    return {
        order: 1,
        id: 'categorical.direct-mixed-product-distribution.full-action',
        groupId: 'categorical.direct-mixed-product-distribution',
        clauseOrder: 1,
        sourceOwner: transforHomFull,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'A',
                type: builder.template(displayedFamilyType(
                    builder,
                    oppositeAt(builder, K)
                ))
            },
            {
                name: 'B',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'C',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(transforHomFullAt(
            builder,
            K,
            cat,
            builder.wildcard(families.source),
            builder.wildcard(families.target),
            x,
            y,
            distributorAt(builder, K, A, B, C)
        )),
        right: builder.template(functorHomFullAt(
            builder,
            K,
            cat,
            families.source,
            x,
            y
        )),
        provenance: source(
            'rule @tapp1_func $K Cat_cat _ _ $x $y ' +
                '(@Functor_catd_product_funcd $K $A $B $C)'
        )
    };
};

const cappedRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const families = distributorFamilies(builder, K, A, B, C);
    const cat = builder.global(categoryOfCategories);
    return {
        order: 2,
        id: 'categorical.direct-mixed-product-distribution.capped-action',
        groupId: 'categorical.direct-mixed-product-distribution',
        clauseOrder: 2,
        sourceOwner: transforHomCapped,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'A',
                type: builder.template(displayedFamilyType(
                    builder,
                    oppositeAt(builder, K)
                ))
            },
            {
                name: 'B',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'C',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, K, x, y))
            }
        ],
        left: builder.pattern(transforHomCappedAt(
            builder,
            K,
            cat,
            builder.wildcard(families.source),
            builder.wildcard(families.target),
            x,
            y,
            distributorAt(builder, K, A, B, C),
            p
        )),
        right: builder.template(functorHomCappedAt(
            builder,
            K,
            cat,
            families.source,
            x,
            y,
            p
        )),
        provenance: source(
            'rule @tapp1_fapp0 $K Cat_cat _ _ $x $y ' +
                '(@Functor_catd_product_funcd $K $A $B $C) $p'
        )
    };
};

const runtimeRules = Object.freeze([
    pointRule(),
    fullRule(),
    cappedRule()
]);

export const
CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        'DIRECT-MIXED-PRODUCT-DISTRIBUTION-1G-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'direct-mixed-product-distribution-1g-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [...externalSymbols, distributor].map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const
CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_RUNTIME_MODULE,
    {
        revision:
            'DIRECT-MIXED-PRODUCT-DISTRIBUTION-1G-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_RUNTIME_MODULE
                .revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact D-DTTLF-USABILITY-048 active projection'
        }))
    }
);

const distributorLink =
    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_LINKAGE
        .entries
        .find(entry =>
            entry.symbol.moduleId === distributor.moduleId &&
            entry.symbol.name === distributor.name
        );

if (
    distributorLink === undefined ||
    distributorLink.kind !== 'free-declaration'
) {
    throw new Error(
        'DIRECT-MIXED-PRODUCT-DISTRIBUTION-1G lost its distributor link'
    );
}

export const
CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_CORE_NAMES =
Object.freeze({
    distributor: distributorLink.coreName
});

export type CoreCategoricalDirectMixedProductDistributionSymbolId =
    keyof typeof CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_CORE_NAMES;

export function coreCategoricalDirectMixedProductDistributionCoreName(
    id: CoreCategoricalDirectMixedProductDistributionSymbolId
): string {
    return CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_CORE_NAMES[id];
}

export const CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_BOUNDARY =
Object.freeze({
    decision: 'D-DTTLF-USABILITY-048',
    declarationNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    declarationCount: declarations.length,
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    runtimeRuleCount: runtimeRules.length,
    activeLambdapiOwnerDelta: 1,
    activeLambdapiRuleDelta: 3,
    intrinsicCoreOwnerDelta: 0,
    ownerSpecificCheckerOrEvaluatorDelta: 0,
    externalOracleDelta: 0,
    externalCoherenceEvidenceDelta: 0,
    contextualIrNodeDelta: 0,
    recursiveFactorizationCaseDelta: 1,
    textOrBrowserDelta: 0,
    transfersContextualCurry: false,
    allEntriesUseGenericTransferEngines: true
});

export interface CoreCategoricalDirectMixedProductDistributionCompilation {
    readonly prerequisite:
        CoreCategoricalDirectMixedSourceActionCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation:
    CoreCategoricalDirectMixedProductDistributionCompilation | undefined;

export function compileCoreCategoricalDirectMixedProductDistributionTransfer():
CoreCategoricalDirectMixedProductDistributionCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    const prerequisite =
        compileCoreCategoricalDirectMixedSourceActionTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_MODULE,
        CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_POLICY,
        CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_LINKAGE,
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
        CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_RUNTIME_MODULE,
        CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_RUNTIME_POLICY,
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
        CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_MODULE,
        CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_POLICY,
        CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_LINKAGE,
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
