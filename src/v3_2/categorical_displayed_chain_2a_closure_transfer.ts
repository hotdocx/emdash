/**
 * DISPLAYED-CHAIN-2A isolated generic transfer closure.
 *
 * This continuation preserves the completed DISPLAYED-CHAIN-1A fragment and
 * adds exactly three existing signatures, six exact existing computations,
 * two narrow checked Product_pair projection normal forms, and the one
 * D-017-approved componentwise fdapp1_int_cell rule. Every declaration and
 * rule goes through the generic LF compilers.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE,
    CoreCategoricalDisplayedChainCompilation,
    compileCoreCategoricalDisplayedChainTransfer
} from './categorical_displayed_chain_transfer';
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
CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_REVISION =
    'DISPLAYED-CHAIN-2A-CLOSURE-GENERIC-TRANSFER-1' as const;

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_SOURCE_SHA256 =
    'sha256:c190da66e017d8156e9b8e894c7c9b7122df3d4ccad21b1712b7ed51b995a515';

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const groupoid =
    coreDirectedContinuationTransferSymbol('groupoid-universe');
const decodeOwner =
    coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const functorClassifier =
    coreDirectedContinuationTransferSymbol('functor-classifier');
const homCategory =
    coreDirectedContinuationTransferSymbol('hom-category');
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
const decodedDependentPair =
    coreDirectedContinuationTransferSymbol('decoded-dependent-pair');

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const sigmaFirst = symbol('sigma_Fst');
const sigmaSecond = symbol('sigma_Snd');
const productGroupoid = symbol('Product_grpd');
const functorCategory = symbol('Functor_cat');
const functorComposition = symbol('comp_cat_fapp0');
const productCategory = symbol('Product_cat');
const productPair = symbol('Product_pair');
const productMap = symbol('Product_map_func');
const productLeftProjection = symbol('Product_projL_func');
const productRightProjection = symbol('Product_projR_func');
const uncurryPackage = symbol('uncurry_func_func');
const internalProductFunctor = symbol('Product_cat_func');
const displayedProductPair = symbol('Product_pair_funcd');
const displayedTransportLeft =
    symbol('functord_transport_lhs_func');
const displayedTransportRight =
    symbol('functord_transport_rhs_func');
const displayedInternalCell = symbol('fdapp1_int_cell');

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

const objectClassifierAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, objectClassifier, [{
        plicity: 'explicit',
        value: base
    }]);

const objectType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, objectClassifierAt(builder, base));

const functorType = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, functorClassifier, [
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]));

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

const groupoidFamilyType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    builder.pi(
        'x',
        decode(builder, base),
        _x => builder.global(groupoid),
        explicitMode
    );

const applyFamily = (
    builder: CoreLfTransferScopedBuilder,
    family: CoreLfTransferBuilderExpression,
    value: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    call(builder, family, [{
        plicity: 'explicit',
        value
    }]);

const decodedPairAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, decodedDependentPair, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const sigmaFirstAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    pair: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaFirst, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: family },
        { plicity: 'explicit', value: pair }
    ]);

const sigmaSecondAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    pair: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaSecond, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: family },
        { plicity: 'explicit', value: pair }
    ]);

const constantGroupoidFamily = (
    builder: CoreLfTransferScopedBuilder,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    builder.lam(
        'ignored',
        decode(builder, left),
        _x => right,
        explicitMode
    );

const productGroupoidAt = (
    builder: CoreLfTransferScopedBuilder,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, productGroupoid, [
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
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

const productPairAt = (
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

const productObjectComponents = (
    builder: CoreLfTransferScopedBuilder,
    leftCategory: CoreLfTransferBuilderExpression,
    rightCategory: CoreLfTransferBuilderExpression,
    pair: CoreLfTransferBuilderExpression
) => {
    const leftClassifier = objectClassifierAt(builder, leftCategory);
    const rightClassifier = objectClassifierAt(builder, rightCategory);
    const family = constantGroupoidFamily(
        builder,
        leftClassifier,
        rightClassifier
    );
    return {
        first: sigmaFirstAt(
            builder,
            leftClassifier,
            family,
            pair
        ),
        second: sigmaSecondAt(
            builder,
            leftClassifier,
            family,
            pair
        )
    };
};

const functorCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorCategory, [
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

const displayedFunctorCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedFunctorCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]);

const displayedFunctorType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    objectType(
        builder,
        displayedFunctorCategoryAt(builder, base, source, target)
    );

const fibre = (
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

const displayedTransportSideAt = (
    builder: CoreLfTransferScopedBuilder,
    side: CoreLfQualifiedSymbol,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor_: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    targetPoint: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, side, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor_ },
        { plicity: 'implicit', value: sourcePoint },
        { plicity: 'implicit', value: targetPoint },
        { plicity: 'explicit', value: arrow }
    ]);

const displayedInternalCellAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor_: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    targetPoint: CoreLfTransferBuilderExpression,
    baseArrow: CoreLfTransferBuilderExpression,
    sourceValue: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedInternalCell, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor_ },
        { plicity: 'implicit', value: sourcePoint },
        { plicity: 'implicit', value: targetPoint },
        { plicity: 'explicit', value: baseArrow },
        { plicity: 'explicit', value: sourceValue }
    ]);

const ordinaryProjectionAt = (
    builder: CoreLfTransferScopedBuilder,
    side: 'left' | 'right',
    leftCategory: CoreLfTransferBuilderExpression,
    rightCategory: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(
        builder,
        side === 'left'
            ? productLeftProjection
            : productRightProjection,
        [
            { plicity: 'implicit', value: leftCategory },
            { plicity: 'implicit', value: rightCategory }
        ]
    );

const ordinaryProductMapAt = (
    builder: CoreLfTransferScopedBuilder,
    A: CoreLfTransferBuilderExpression,
    Aprime: CoreLfTransferBuilderExpression,
    B: CoreLfTransferBuilderExpression,
    Bprime: CoreLfTransferBuilderExpression,
    F: CoreLfTransferBuilderExpression,
    G: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, productMap, [
        { plicity: 'implicit', value: A },
        { plicity: 'implicit', value: Aprime },
        { plicity: 'implicit', value: B },
        { plicity: 'implicit', value: Bprime },
        { plicity: 'explicit', value: F },
        { plicity: 'explicit', value: G }
    ]);

const composeFunctors = (
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

const uncurryPackageAt = (
    builder: CoreLfTransferScopedBuilder,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, uncurryPackage, [
        { plicity: 'implicit', value: left },
        { plicity: 'implicit', value: right },
        { plicity: 'implicit', value: target }
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
        uncurryPackageAt(builder, cat, cat, cat),
        builder.global(internalProductFunctor)
    );
    const familyCategory = functorCategoryAt(builder, base, cat);
    return composeFunctors(
        builder,
        base,
        catProduct,
        cat,
        uncurriedProduct,
        productPairAt(
            builder,
            familyCategory,
            familyCategory,
            left,
            right
        )
    );
};

const displayedProductPairAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    leftFamily: CoreLfTransferBuilderExpression,
    rightFamily: CoreLfTransferBuilderExpression,
    leftFunctor: CoreLfTransferBuilderExpression,
    rightFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedProductPair, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: leftFamily },
        { plicity: 'implicit', value: rightFamily },
        { plicity: 'explicit', value: leftFunctor },
        { plicity: 'explicit', value: rightFunctor }
    ]);

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const modifiers = () => ({
    visibility: 'public' as const,
    rigidity: 'injective' as const,
    sourceOpacity: 'opaque' as const
});

const sigmaFirstType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'a',
        builder.global(groupoid),
        a => builder.pi(
            'P',
            groupoidFamilyType(builder, a),
            P => builder.pi(
                's',
                decodedPairAt(builder, a, P),
                _s => decode(builder, a),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const sigmaSecondType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'a',
        builder.global(groupoid),
        a => builder.pi(
            'P',
            groupoidFamilyType(builder, a),
            P => builder.pi(
                's',
                decodedPairAt(builder, a, P),
                s => decode(builder, applyFamily(
                    builder,
                    P,
                    sigmaFirstAt(builder, a, P, s)
                )),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const productGroupoidType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(groupoid),
        _A => builder.pi(
            'B',
            builder.global(groupoid),
            _B => builder.global(groupoid),
            explicitMode
        ),
        explicitMode
    ));
};

const declarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: sigmaFirst,
        type: sigmaFirstType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers(),
        provenance: source('injective symbol sigma_Fst [a P]')
    }),
    Object.freeze({
        order: 1,
        symbol: sigmaSecond,
        type: sigmaSecondType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers(),
        provenance: source('injective symbol sigma_Snd [a P]')
    }),
    Object.freeze({
        order: 2,
        symbol: productGroupoid,
        type: productGroupoidType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers(),
        provenance: source('injective symbol Product_grpd')
    })
]);

const signatureExternalSymbols = Object.freeze([
    groupoid,
    decodeOwner,
    decodedDependentPair
]);

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'displayed-chain-2a-closure-signatures',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: signatureExternalSymbols.map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_MODULE,
    {
        revision:
            'DISPLAYED-CHAIN-2A-CLOSURE-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_MODULE
                .revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact existing active signature approved by ' +
                'D-DTTLF-USABILITY-017'
        }))
    }
);

const prerequisiteLinks = [
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
    const link = prerequisiteLinks.find(candidate =>
        symbolEquals(candidate.symbol, target)
    );
    if (link === undefined) {
        throw new Error(
            `DISPLAYED-CHAIN-2A has no dependency link for ` +
                `${target.moduleId}.${target.name}`
        );
    }
    return Object.freeze({
        ...link,
        order,
        symbol: Object.freeze({ ...link.symbol })
    });
};

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_MODULE,
        {
            revision:
                'DISPLAYED-CHAIN-2A-CLOSURE-SIGNATURE-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_MODULE
                    .revision,
            entries: [
                ...signatureExternalSymbols.map(dependencyLink),
                ...declarations.map((declaration, index) => ({
                    order: signatureExternalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `emdash_v3_2_displayed_chain_2a_` +
                        declaration.symbol.name,
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

const productGroupoidDecodeRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    return {
        order: 0,
        id:
            'categorical.displayed-chain-2a.' +
            'product-groupoid-decode',
        groupId:
            'categorical.displayed-chain-2a.product-groupoid',
        clauseOrder: 0,
        sourceOwner: decodeOwner,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(groupoid))
            },
            {
                name: 'B',
                type: builder.template(builder.global(groupoid))
            }
        ],
        left: builder.pattern(decode(
            builder,
            productGroupoidAt(builder, A, B)
        )),
        right: builder.template(decodedPairAt(
            builder,
            A,
            constantGroupoidFamily(builder, A, B)
        )),
        provenance: source('rule τ (Product_grpd $A $B)')
    };
};

const productObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    return {
        order: 1,
        id: 'categorical.displayed-chain-2a.product-object',
        groupId: 'categorical.displayed-chain-2a.product-object',
        clauseOrder: 0,
        sourceOwner: objectClassifier,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'B',
                type: builder.template(builder.global(category))
            }
        ],
        left: builder.pattern(objectClassifierAt(
            builder,
            productCategoryAt(builder, A, B)
        )),
        right: builder.template(productGroupoidAt(
            builder,
            objectClassifierAt(builder, A),
            objectClassifierAt(builder, B)
        )),
        provenance: source('rule Obj (Product_cat $A $B)')
    };
};

const productProjectionObjectRule = (
    side: 'left' | 'right',
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const p = builder.capture('p');
    const product = productCategoryAt(builder, A, B);
    const components = productObjectComponents(builder, A, B, p);
    return {
        order,
        id:
            `categorical.displayed-chain-2a.product-${side}-` +
            'projection.object',
        groupId:
            'categorical.displayed-chain-2a.product-projection',
        clauseOrder: side === 'left' ? 0 : 1,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'B',
                type: builder.template(builder.global(category))
            },
            {
                name: 'p',
                type: builder.template(objectType(builder, product))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            product,
            side === 'left' ? A : B,
            ordinaryProjectionAt(builder, side, A, B),
            p
        )),
        right: builder.template(
            side === 'left' ? components.first : components.second
        ),
        provenance: source(
            `rule @fapp0 _ _ (@Product_proj` +
                `${side === 'left' ? 'L' : 'R'}_func $A $B) $p`
        )
    };
};

const productHomRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const p = builder.capture('p');
    const q = builder.capture('q');
    const product = productCategoryAt(builder, A, B);
    const pComponents = productObjectComponents(builder, A, B, p);
    const qComponents = productObjectComponents(builder, A, B, q);
    return {
        order: 4,
        id: 'categorical.displayed-chain-2a.product.general-hom',
        groupId: 'categorical.displayed-chain-2a.product-hom',
        clauseOrder: 0,
        sourceOwner: homCategory,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'B',
                type: builder.template(builder.global(category))
            },
            {
                name: 'p',
                type: builder.template(objectType(builder, product))
            },
            {
                name: 'q',
                type: builder.template(objectType(builder, product))
            }
        ],
        left: builder.pattern(homCategoryAt(builder, product, p, q)),
        right: builder.template(productCategoryAt(
            builder,
            homCategoryAt(
                builder,
                A,
                pComponents.first,
                qComponents.first
            ),
            homCategoryAt(
                builder,
                B,
                pComponents.second,
                qComponents.second
            )
        )),
        provenance: source(
            'rule Hom_cat (Product_cat $A $B) $p $q'
        )
    };
};

const productMapObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const Aprime = builder.capture('Aprime');
    const B = builder.capture('B');
    const Bprime = builder.capture('Bprime');
    const F = builder.capture('F');
    const G = builder.capture('G');
    const ab = builder.capture('ab');
    const sourceProduct = productCategoryAt(builder, A, B);
    const targetProduct =
        productCategoryAt(builder, Aprime, Bprime);
    const components = productObjectComponents(builder, A, B, ab);
    return {
        order: 5,
        id: 'categorical.displayed-chain-2a.product-map.object',
        groupId: 'categorical.displayed-chain-2a.product-map',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'Aprime',
                type: builder.template(builder.global(category))
            },
            {
                name: 'B',
                type: builder.template(builder.global(category))
            },
            {
                name: 'Bprime',
                type: builder.template(builder.global(category))
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, A, Aprime))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, B, Bprime))
            },
            {
                name: 'ab',
                type: builder.template(objectType(
                    builder,
                    sourceProduct
                ))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            sourceProduct,
            targetProduct,
            ordinaryProductMapAt(
                builder,
                A,
                Aprime,
                B,
                Bprime,
                F,
                G
            ),
            ab
        )),
        right: builder.template(productPairAt(
            builder,
            Aprime,
            Bprime,
            functorObjectAt(
                builder,
                A,
                Aprime,
                F,
                components.first
            ),
            functorObjectAt(
                builder,
                B,
                Bprime,
                G,
                components.second
            )
        )),
        provenance: source(
            'rule @fapp0 _ _ ' +
                "(@Product_map_func $A $A' $B $B' $F $G) $ab"
        )
    };
};

const productPairProjectionBetaRule = (
    side: 'left' | 'right',
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const leftClassifier = objectClassifierAt(builder, A);
    const family = constantGroupoidFamily(
        builder,
        leftClassifier,
        objectClassifierAt(builder, B)
    );
    const pair = productPairAt(builder, A, B, x, y);
    return {
        order,
        id:
            `categorical.displayed-chain-2a.product-pair-${side}.` +
            'delta-beta',
        groupId:
            'categorical.displayed-chain-2a.product-pair-projection',
        clauseOrder: side === 'left' ? 0 : 1,
        sourceOwner: side === 'left' ? sigmaFirst : sigmaSecond,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'B',
                type: builder.template(builder.global(category))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, B))
            }
        ],
        left: builder.pattern(
            side === 'left'
                ? sigmaFirstAt(builder, leftClassifier, family, pair)
                : sigmaSecondAt(builder, leftClassifier, family, pair)
        ),
        right: builder.template(side === 'left' ? x : y),
        provenance: source(
            `derived active transparent Product_pair plus ` +
                `sigma_${side === 'left' ? 'Fst' : 'Snd'} beta`
        )
    };
};

const displayedProductPairInternalCellRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const FF = builder.capture('FF');
    const GG = builder.capture('GG');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const u = builder.capture('u');
    const sourceFibre = fibre(builder, K, E, x);
    const product = transparentDisplayedProduct(builder, K, B, C);
    const component = (
        family: CoreLfTransferBuilderExpression,
        displayedFunctor_: CoreLfTransferBuilderExpression
    ) => {
        const targetFibre = fibre(builder, K, family, y);
        const left = functorObjectAt(
            builder,
            sourceFibre,
            targetFibre,
            displayedTransportSideAt(
                builder,
                displayedTransportLeft,
                K,
                E,
                family,
                displayedFunctor_,
                x,
                y,
                p
            ),
            u
        );
        const right = functorObjectAt(
            builder,
            sourceFibre,
            targetFibre,
            displayedTransportSideAt(
                builder,
                displayedTransportRight,
                K,
                E,
                family,
                displayedFunctor_,
                x,
                y,
                p
            ),
            u
        );
        return {
            category: homCategoryAt(
                builder,
                targetFibre,
                left,
                right
            ),
            cell: displayedInternalCellAt(
                builder,
                K,
                E,
                family,
                displayedFunctor_,
                x,
                y,
                p,
                u
            )
        };
    };
    const leftComponent = component(B, FF);
    const rightComponent = component(C, GG);
    return {
        order: 8,
        id:
            'categorical.displayed-chain-2a.' +
            'displayed-product-pair-internal-cell',
        groupId:
            'categorical.displayed-chain-2a.displayed-product-pair',
        clauseOrder: 0,
        sourceOwner: displayedInternalCell,
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
                name: 'B',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'C',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'FF',
                type: builder.template(
                    displayedFunctorType(builder, K, E, B)
                )
            },
            {
                name: 'GG',
                type: builder.template(
                    displayedFunctorType(builder, K, E, C)
                )
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
                type: builder.template(
                    decode(builder, globalCall(
                        builder,
                        coreDirectedContinuationTransferSymbol(
                            'hom-classifier'
                        ),
                        [
                            { plicity: 'explicit', value: K },
                            { plicity: 'explicit', value: x },
                            { plicity: 'explicit', value: y }
                        ]
                    ))
                )
            },
            {
                name: 'u',
                type: builder.template(objectType(builder, sourceFibre))
            }
        ],
        left: builder.pattern(displayedInternalCellAt(
            builder,
            K,
            E,
            builder.wildcard(product),
            displayedProductPairAt(
                builder,
                K,
                E,
                B,
                C,
                FF,
                GG
            ),
            x,
            y,
            p,
            u
        )),
        right: builder.template(productPairAt(
            builder,
            leftComponent.category,
            rightComponent.category,
            leftComponent.cell,
            rightComponent.cell
        )),
        provenance: source(
            'rule @fdapp1_int_cell $K $E _ ' +
                '(@Product_pair_funcd $K $E $B $C $FF $GG) ' +
                '$x $y $p $u'
        )
    };
};

const runtimeRules:
readonly CoreLfTransferRuntimeRule[] = Object.freeze([
    productGroupoidDecodeRule(),
    productObjectRule(),
    productProjectionObjectRule('left', 2),
    productProjectionObjectRule('right', 3),
    productHomRule(),
    productMapObjectRule(),
    productPairProjectionBetaRule('left', 6),
    productPairProjectionBetaRule('right', 7),
    displayedProductPairInternalCellRule()
]);

const runtimeExternalSymbols = Object.freeze([
    category,
    groupoid,
    decodeOwner,
    objectClassifier,
    functorClassifier,
    coreDirectedContinuationTransferSymbol('hom-classifier'),
    homCategory,
    categoryOfCategories,
    displayedCategoryCategory,
    displayedFunctorCategory,
    functorObject,
    decodedDependentPair,
    sigmaFirst,
    sigmaSecond,
    productGroupoid,
    functorCategory,
    functorComposition,
    productCategory,
    productPair,
    productMap,
    productLeftProjection,
    productRightProjection,
    uncurryPackage,
    internalProductFunctor,
    displayedProductPair,
    displayedTransportLeft,
    displayedTransportRight,
    displayedInternalCell
]);

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'DISPLAYED-CHAIN-2A-CLOSURE-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'displayed-chain-2a-closure-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: runtimeExternalSymbols.map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_RUNTIME_MODULE,
    {
        revision: 'DISPLAYED-CHAIN-2A-CLOSURE-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_RUNTIME_MODULE
                .revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact existing or D-017-approved owner-position ' +
                'computation, checked through the generic LF compiler'
        }))
    }
);

const exactExistingRuntimeRuleIds = Object.freeze([
    'categorical.displayed-chain-2a.product-groupoid-decode',
    'categorical.displayed-chain-2a.product-object',
    'categorical.displayed-chain-2a.product-left-projection.object',
    'categorical.displayed-chain-2a.product-right-projection.object',
    'categorical.displayed-chain-2a.product.general-hom',
    'categorical.displayed-chain-2a.product-map.object'
]);

const derivedRuntimeRuleIds = Object.freeze([
    'categorical.displayed-chain-2a.product-pair-left.delta-beta',
    'categorical.displayed-chain-2a.product-pair-right.delta-beta'
]);

const newRuntimeRuleIds = Object.freeze([
    'categorical.displayed-chain-2a.' +
        'displayed-product-pair-internal-cell'
]);

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_BOUNDARY =
Object.freeze({
    status: 'displayed-chain-2a-closure-generic-transfer',
    reviewRevision:
        'DISPLAYED-CHAIN-2A-CLOSURE-0A-REVIEWED-1',
    existingDeclarationNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    existingDeclarationCount: declarations.length,
    exactExistingRuntimeRuleIds,
    exactExistingRuntimeRuleCount:
        exactExistingRuntimeRuleIds.length,
    derivedRuntimeRuleIds,
    derivedRuntimeRuleCount: derivedRuntimeRuleIds.length,
    newRuntimeRuleIds,
    newRuntimeRuleCount: newRuntimeRuleIds.length,
    totalContinuationRuntimeRuleCount: runtimeRules.length,
    continuationComparisonStepLimit: 512,
    defaultCoreComparisonStepLimit: 256,
    activeMathematicalSymbolDelta: 0,
    activeRuntimeRuleDelta: 1,
    activeProofRuleDelta: 0,
    intrinsicCoreOwnerDelta: 0,
    ownerSpecificCheckerOrEvaluatorDelta: 0,
    externalSubjectReductionOracleCount: 0,
    completedChain1MutatedInPlace: false,
    allEntriesUseGenericTransferEngines: true
});

export interface CoreCategoricalDisplayedChain2aClosureCompilation {
    readonly prerequisite:
        CoreCategoricalDisplayedChainCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation:
    CoreCategoricalDisplayedChain2aClosureCompilation | undefined;

/**
 * Compile the frozen, subject-checked closure without executing the
 * Node-loaded D-017/scale review-ledger validator. Browser products consume
 * this path; the ordinary transfer entry point below additionally revalidates
 * those closure-specific ledgers.
 */
export function compileCoreCategoricalDisplayedChain2aClosureRuntime():
CoreCategoricalDisplayedChain2aClosureCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    const prerequisite =
        compileCoreCategoricalDisplayedChainTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_MODULE,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_POLICY,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_LINKAGE,
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
    const inheritedRuntimeFragment =
        new CoreLfCompiledRuntimeFragment(
            prerequisite.runtimeFragment.localProgram,
            [],
            prerequisite.composedRuntime
        );
    const runtimeFragment = compileCoreLfRuntimeFragment(
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_RUNTIME_MODULE,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_RUNTIME_POLICY,
        initialContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: inheritedRuntimeFragment
            }],
            comparisonStepLimit: 512
        }
    );
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_MODULE,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_POLICY,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_LINKAGE,
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

const validateHistoricalReviewLedgers = (): void => {
    const engineReview = require(
        './scale_engine_review'
    ) as typeof import('./scale_engine_review');
    const closureReview = require(
        './categorical_displayed_chain_2a_closure_review'
    ) as typeof import(
        './categorical_displayed_chain_2a_closure_review'
    );
    engineReview.validateCoreLfScaleEngineReview();
    closureReview.validateCoreCategoricalDisplayedChain2aClosureReview();
};

/**
 * Node/evidence entry point: revalidate the historical authorization records
 * before returning the same checked runtime compilation.
 */
export function compileCoreCategoricalDisplayedChain2aClosureTransfer():
CoreCategoricalDisplayedChain2aClosureCompilation {
    validateHistoricalReviewLedgers();
    return compileCoreCategoricalDisplayedChain2aClosureRuntime();
}
