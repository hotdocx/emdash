/**
 * FIBRED-STRUCTURE-1A transfer of fixed-base fibrewise-product structure.
 *
 * The product family itself remains the transparent composite
 *
 *   P(B,C) = uncurry(Product_cat_func) o Product_pair(B,C).
 *
 * D-DTTLF-USABILITY-006 adds exactly three injective mathematical owners
 * and eleven runtime rules: displayed left/right projections, displayed
 * pairing, their point/full/capped actions, and the two whole pairing
 * betas. Swap and diagonal remain transparent Core composites.
 */

import {
    CORE_CATEGORICAL_COMPREHENSION_TRANSFER_LINKAGE
} from './categorical_comprehension_transfer';
import {
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS,
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE
} from './categorical_dependent_composition_transfer';
import {
    CORE_CATEGORICAL_DEPENDENT_SYMBOLS,
    CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE
} from './categorical_dependent_transfer';
import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE,
    CoreCategoricalFibredProductCompilation,
    compileCoreCategoricalFibredProductTransfer
} from './categorical_fibred_product_transfer';
import {
    validateCoreCategoricalFibredStructureReview
} from './categorical_fibred_structure_review';
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
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_REVISION =
    'FIBRED-STRUCTURE-1A-FIXED-BASE-UNIVERSAL-PROPERTY-1' as const;

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_SOURCE_SHA256 =
    'sha256:7fe3f4c706bea0f9fc0ae9c11865a2c464abc4aa9df1ab434d08710dbaf360fe';

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
const homCategory =
    coreDirectedContinuationTransferSymbol('hom-category');
const transforCategory =
    coreDirectedContinuationTransferSymbol('transfor-category');
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
const functorHomFull =
    coreDirectedContinuationTransferSymbol('functor-hom-full');
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const transforComponentCapped =
    coreDirectedContinuationTransferSymbol(
        'transfor-component-capped'
    );
const transforHomFull =
    coreDirectedContinuationTransferSymbol('transfor-hom-full');
const transforHomCapped =
    coreDirectedContinuationTransferSymbol('transfor-hom-capped');

const {
    genericComposition
} = CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS;

const {
    functorCategory,
    identityFunctor,
    functorComposition,
    productCategory,
    productPair,
    productLeftProjection,
    productRightProjection,
    uncurryPackage
} = CORE_CATEGORICAL_STRUCTURAL_SYMBOLS;

const {
    internalProductFunctor
} = CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS;

const {
    fibreFunctor,
    displayedTransportFunctor
} = CORE_CATEGORICAL_DEPENDENT_SYMBOLS;

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_SYMBOLS =
Object.freeze({
    precompositionFunctor:
        coreLfQualifiedSymbol(MODULE_ID, 'comp_cat_con_func'),
    precompositionAction:
        coreLfQualifiedSymbol(
            MODULE_ID,
            'hom_precomp_along_fapp0'
        ),
    displayedIdentity:
        coreLfQualifiedSymbol(MODULE_ID, 'id_funcd'),
    displayedProductLeftProjection:
        coreLfQualifiedSymbol(MODULE_ID, 'Product_projL_funcd'),
    displayedProductRightProjection:
        coreLfQualifiedSymbol(MODULE_ID, 'Product_projR_funcd'),
    displayedProductPair:
        coreLfQualifiedSymbol(MODULE_ID, 'Product_pair_funcd')
});

const {
    precompositionFunctor,
    precompositionAction,
    displayedIdentity,
    displayedProductLeftProjection,
    displayedProductRightProjection,
    displayedProductPair
} = CORE_CATEGORICAL_FIBRED_STRUCTURE_SYMBOLS;

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
    decode(builder, globalCall(builder, objectClassifier, [{
        plicity: 'explicit',
        value: base
    }]));

const functorType = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, functorClassifier, [
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]));

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
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, transforCategory, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: sourceFunctor },
        { plicity: 'explicit', value: targetFunctor }
    ]);

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
    objectType(builder, globalCall(builder, displayedFunctorCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: sourceFamily },
        { plicity: 'explicit', value: targetFamily }
    ]));

const fapp0 = (
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

const fapp1FullAt = (
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

const fapp1At = (
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

const tapp0At = (
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

const tapp1FullAt = (
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

const tapp1At = (
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

const identityFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, identityFunctor, [{
        plicity: 'implicit',
        value: base
    }]);

const composeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    middle: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    outer: CoreLfTransferBuilderExpression,
    inner: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, genericComposition, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: middle },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: outer },
        { plicity: 'explicit', value: inner }
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

const projectionAt = (
    builder: CoreLfTransferScopedBuilder,
    side: 'left' | 'right',
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(
        builder,
        side === 'left'
            ? productLeftProjection
            : productRightProjection,
        [
            { plicity: 'implicit', value: left },
            { plicity: 'implicit', value: right }
        ]
    );

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
    const uncurriedProduct = fapp0(
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
        pairAt(builder, familyCategory, familyCategory, left, right)
    );
};

const fibre = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    fapp0(
        builder,
        base,
        builder.global(categoryOfCategories),
        family,
        point
    );

const precompositionFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    middle: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, precompositionFunctor, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: middle },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: functor }
    ]);

const precompositionActionAt = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    fixedTarget: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    precomposingArrow: CoreLfTransferBuilderExpression,
    incomingArrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, precompositionAction, [
        { plicity: 'implicit', value: sourceCategory },
        { plicity: 'implicit', value: targetCategory },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: fixedTarget },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: precomposingArrow },
        { plicity: 'explicit', value: incomingArrow }
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

const fibreFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, fibreFunctor, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor },
        { plicity: 'explicit', value: point }
    ]);

const displayedTransportAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    targetPoint: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedTransportFunctor, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor },
        { plicity: 'implicit', value: sourcePoint },
        { plicity: 'implicit', value: targetPoint },
        { plicity: 'explicit', value: arrow }
    ]);

const displayedProjectionAt = (
    builder: CoreLfTransferScopedBuilder,
    side: 'left' | 'right',
    base: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(
        builder,
        side === 'left'
            ? displayedProductLeftProjection
            : displayedProductRightProjection,
        [
            { plicity: 'implicit', value: base },
            { plicity: 'explicit', value: left },
            { plicity: 'explicit', value: right }
        ]
    );

const displayedPairAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression,
    leftFunctor: CoreLfTransferBuilderExpression,
    rightFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedProductPair, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: left },
        { plicity: 'implicit', value: right },
        { plicity: 'explicit', value: leftFunctor },
        { plicity: 'explicit', value: rightFunctor }
    ]);

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const publicModifiers = (
    rigidity: 'ordinary' | 'injective',
    sourceOpacity: 'transparent' | 'opaque'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity
});

const precompositionFunctorType = (): CoreLfTransferExpression => {
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
                    'F',
                    functorType(builder, X, Y),
                    _F => functorType(
                        builder,
                        functorCategoryAt(builder, Y, Z),
                        functorCategoryAt(builder, X, Z)
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

const precompositionActionType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'F',
                functorType(builder, A, B),
                F => builder.pi(
                    'Z',
                    objectType(builder, B),
                    Z => builder.pi(
                        'W',
                        objectType(builder, A),
                        W => builder.pi(
                            'X',
                            objectType(builder, A),
                            X => builder.pi(
                                'h',
                                homType(builder, A, W, X),
                                _h => builder.pi(
                                    'g',
                                    homType(
                                        builder,
                                        B,
                                        fapp0(
                                            builder,
                                            A,
                                            B,
                                            F,
                                            X
                                        ),
                                        Z
                                    ),
                                    _g => homType(
                                        builder,
                                        B,
                                        fapp0(
                                            builder,
                                            A,
                                            B,
                                            F,
                                            W
                                        ),
                                        Z
                                    ),
                                    explicitMode
                                ),
                                explicitMode
                            ),
                            implicitMode
                        ),
                        implicitMode
                    ),
                    explicitMode
                ),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const displayedIdentityType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            E => displayedFunctorType(builder, K, E, E),
            implicitMode
        ),
        implicitMode
    ));
};

const displayedProjectionType = (
    side: 'left' | 'right'
): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'B',
            displayedFamilyType(builder, K),
            B => builder.pi(
                'C',
                displayedFamilyType(builder, K),
                C => displayedFunctorType(
                    builder,
                    K,
                    transparentDisplayedProduct(builder, K, B, C),
                    side === 'left' ? B : C
                ),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const displayedPairType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            E => builder.pi(
                'B',
                displayedFamilyType(builder, K),
                B => builder.pi(
                    'C',
                    displayedFamilyType(builder, K),
                    C => builder.pi(
                        'FF',
                        displayedFunctorType(builder, K, E, B),
                        FF => builder.pi(
                            'GG',
                            displayedFunctorType(builder, K, E, C),
                            _GG => displayedFunctorType(
                                builder,
                                K,
                                E,
                                transparentDisplayedProduct(
                                    builder,
                                    K,
                                    B,
                                    C
                                )
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
        ),
        implicitMode
    ));
};

const declarations: readonly CoreLfTransferDeclaration[] = [
    {
        order: 0,
        symbol: precompositionFunctor,
        type: precompositionFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol comp_cat_con_func [X Y Z : Cat]'
        )
    },
    {
        order: 1,
        symbol: precompositionAction,
        type: precompositionActionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol hom_precomp_along_fapp0 [A B : Cat]'
        )
    },
    {
        order: 2,
        symbol: displayedIdentity,
        type: displayedIdentityType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol id_funcd [K : Cat] [E : τ (Catd K)]'
        )
    },
    {
        order: 3,
        symbol: displayedProductLeftProjection,
        type: displayedProjectionType('left'),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Product_projL_funcd [K : Cat]'
        )
    },
    {
        order: 4,
        symbol: displayedProductRightProjection,
        type: displayedProjectionType('right'),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Product_projR_funcd [K : Cat]'
        )
    },
    {
        order: 5,
        symbol: displayedProductPair,
        type: displayedPairType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Product_pair_funcd [K : Cat]'
        )
    }
];

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'fibred-structure-1a-signatures',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_FIBRED_STRUCTURE_SOURCE_SHA256,
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
        functorObject,
        functorCategory,
        functorComposition,
        productCategory,
        productPair,
        productLeftProjection,
        productRightProjection,
        uncurryPackage,
        internalProductFunctor
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

const newOwnerNames = new Set([
    'Product_projL_funcd',
    'Product_projR_funcd',
    'Product_pair_funcd'
]);

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_MODULE,
    {
        revision: 'FIBRED-STRUCTURE-1A-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_MODULE.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence: newOwnerNames.has(declaration.symbol.name)
                ? 'Exact injective mathematical owner approved by ' +
                    'D-DTTLF-USABILITY-006'
                : 'Existing active v3.2 prerequisite signature'
        }))
    }
);

const earlierLinks = [
    ...CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_COMPREHENSION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries,
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries
];

const dependencyLink = (
    symbol: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const link = earlierLinks.find(candidate =>
        candidate.symbol.moduleId === symbol.moduleId &&
        candidate.symbol.name === symbol.name
    );
    if (link === undefined) {
        throw new Error(
            `FIBRED-STRUCTURE-1A has no dependency link for ` +
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
    CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_MODULE
        .externalSymbols
        .map(external => external.symbol);

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_MODULE,
        {
            revision: 'FIBRED-STRUCTURE-1A-SIGNATURE-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_MODULE
                    .revision,
            entries: [
                ...externalSymbols.map(dependencyLink),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `emdash_v3_2_fibred_structure_1a_` +
                        declaration.symbol.name,
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

const projectionVariables = (
    builder: CoreLfTransferScopedBuilder,
    includeArrow: boolean
) => {
    const K = builder.capture('K');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const variables = [
        {
            name: 'K',
            type: builder.template(builder.global(category))
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
    ];
    if (includeArrow) {
        variables.push({
            name: 'p',
            type: builder.template(homType(builder, K, x, y))
        });
    }
    return { K, B, C, x, y, p, variables };
};

const projectionPointRule = (
    side: 'left' | 'right',
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const x = builder.capture('x');
    const product = transparentDisplayedProduct(builder, K, B, C);
    const target = side === 'left' ? B : C;
    return {
        order,
        id:
            `categorical.fibred-structure.${side}-projection.point`,
        groupId: 'categorical.fibred-structure',
        clauseOrder: order,
        sourceOwner: transforComponentCapped,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
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
            }
        ],
        left: builder.pattern(tapp0At(
            builder,
            K,
            builder.global(categoryOfCategories),
            builder.wildcard(product),
            builder.wildcard(target),
            x,
            displayedProjectionAt(builder, side, K, B, C)
        )),
        right: builder.template(projectionAt(
            builder,
            side,
            fibre(builder, K, B, x),
            fibre(builder, K, C, x)
        )),
        provenance: source(
            `rule @tapp0_fapp0 $K Cat_cat _ _ $x ` +
            `(@Product_proj${side === 'left' ? 'L' : 'R'}_funcd ` +
            '$K $B $C)'
        )
    };
};

const projectionFullRule = (
    side: 'left' | 'right',
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const {
        K, B, C, x, y, variables
    } = projectionVariables(builder, false);
    const cat = builder.global(categoryOfCategories);
    const product = transparentDisplayedProduct(builder, K, B, C);
    const target = side === 'left' ? B : C;
    const sourceFibre = fibre(builder, K, product, x);
    const targetSourceFibre = fibre(builder, K, target, x);
    const targetTargetFibre = fibre(builder, K, target, y);
    return {
        order,
        id:
            `categorical.fibred-structure.${side}-projection.full-action`,
        groupId: 'categorical.fibred-structure',
        clauseOrder: order,
        sourceOwner: transforHomFull,
        variables,
        left: builder.pattern(tapp1FullAt(
            builder,
            K,
            cat,
            builder.wildcard(product),
            builder.wildcard(target),
            x,
            y,
            displayedProjectionAt(builder, side, K, B, C)
        )),
        right: builder.template(composeFunctors(
            builder,
            homCategoryAt(builder, K, x, y),
            functorCategoryAt(
                builder,
                targetSourceFibre,
                targetTargetFibre
            ),
            functorCategoryAt(
                builder,
                sourceFibre,
                targetTargetFibre
            ),
            precompositionFunctorAt(
                builder,
                sourceFibre,
                targetSourceFibre,
                targetTargetFibre,
                projectionAt(
                    builder,
                    side,
                    fibre(builder, K, B, x),
                    fibre(builder, K, C, x)
                )
            ),
            fapp1FullAt(builder, K, cat, target, x, y)
        )),
        provenance: source(
            `rule @tapp1_func $K Cat_cat _ _ $x $y ` +
            `(@Product_proj${side === 'left' ? 'L' : 'R'}_funcd ` +
            '$K $B $C)'
        )
    };
};

const projectionCappedRule = (
    side: 'left' | 'right',
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const {
        K, B, C, x, y, p, variables
    } = projectionVariables(builder, true);
    const cat = builder.global(categoryOfCategories);
    const product = transparentDisplayedProduct(builder, K, B, C);
    const target = side === 'left' ? B : C;
    return {
        order,
        id:
            `categorical.fibred-structure.${side}-projection.capped-action`,
        groupId: 'categorical.fibred-structure',
        clauseOrder: order,
        sourceOwner: transforHomCapped,
        variables,
        left: builder.pattern(tapp1At(
            builder,
            K,
            cat,
            builder.wildcard(product),
            builder.wildcard(target),
            x,
            y,
            displayedProjectionAt(builder, side, K, B, C),
            p
        )),
        right: builder.template(precompositionActionAt(
            builder,
            cat,
            cat,
            identityFunctorAt(builder, cat),
            fibre(builder, K, target, y),
            fibre(builder, K, product, x),
            fibre(builder, K, target, x),
            projectionAt(
                builder,
                side,
                fibre(builder, K, B, x),
                fibre(builder, K, C, x)
            ),
            fapp1At(builder, K, cat, target, x, y, p)
        )),
        provenance: source(
            `rule @tapp1_fapp0 $K Cat_cat _ _ $x $y ` +
            `(@Product_proj${side === 'left' ? 'L' : 'R'}_funcd ` +
            '$K $B $C) $p'
        )
    };
};

const pairingVariables = (
    builder: CoreLfTransferScopedBuilder,
    includeEndpoints: boolean,
    includeArrow: boolean
) => {
    const K = builder.capture('K');
    const E = builder.capture('E');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const FF = builder.capture('FF');
    const GG = builder.capture('GG');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const variables = [
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
            type: builder.template(displayedFunctorType(
                builder,
                K,
                E,
                B
            ))
        },
        {
            name: 'GG',
            type: builder.template(displayedFunctorType(
                builder,
                K,
                E,
                C
            ))
        }
    ];
    if (includeEndpoints) {
        variables.push(
            {
                name: 'x',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, K))
            }
        );
    }
    if (includeArrow) {
        variables.push({
            name: 'p',
            type: builder.template(homType(builder, K, x, y))
        });
    }
    return { K, E, B, C, FF, GG, x, y, p, variables };
};

const pairingPointRule = (
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const {
        K, E, B, C, FF, GG, x, variables
    } = pairingVariables(builder, false, false);
    variables.push({
        name: 'x',
        type: builder.template(objectType(builder, K))
    });
    const cat = builder.global(categoryOfCategories);
    const product = transparentDisplayedProduct(builder, K, B, C);
    const Ex = fibre(builder, K, E, x);
    return {
        order,
        id: 'categorical.fibred-structure.pairing.point',
        groupId: 'categorical.fibred-structure',
        clauseOrder: order,
        sourceOwner: transforComponentCapped,
        variables,
        left: builder.pattern(tapp0At(
            builder,
            K,
            cat,
            E,
            product,
            x,
            displayedPairAt(builder, K, E, B, C, FF, GG)
        )),
        right: builder.template(pairAt(
            builder,
            functorCategoryAt(builder, Ex, fibre(builder, K, B, x)),
            functorCategoryAt(builder, Ex, fibre(builder, K, C, x)),
            tapp0At(builder, K, cat, E, B, x, FF),
            tapp0At(builder, K, cat, E, C, x, GG)
        )),
        provenance: source(
            'rule @tapp0_fapp0 $K Cat_cat _ _ $x ' +
            '(@Product_pair_funcd $K $E $B $C $FF $GG)'
        )
    };
};

const pairingFullRule = (
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const {
        K, E, B, C, FF, GG, x, y, variables
    } = pairingVariables(builder, true, false);
    const cat = builder.global(categoryOfCategories);
    const product = transparentDisplayedProduct(builder, K, B, C);
    const baseHom = homCategoryAt(builder, K, x, y);
    const Ex = fibre(builder, K, E, x);
    return {
        order,
        id: 'categorical.fibred-structure.pairing.full-action',
        groupId: 'categorical.fibred-structure',
        clauseOrder: order,
        sourceOwner: transforHomFull,
        variables,
        left: builder.pattern(tapp1FullAt(
            builder,
            K,
            cat,
            E,
            product,
            x,
            y,
            displayedPairAt(builder, K, E, B, C, FF, GG)
        )),
        right: builder.template(pairAt(
            builder,
            functorCategoryAt(
                builder,
                baseHom,
                functorCategoryAt(
                    builder,
                    Ex,
                    fibre(builder, K, B, y)
                )
            ),
            functorCategoryAt(
                builder,
                baseHom,
                functorCategoryAt(
                    builder,
                    Ex,
                    fibre(builder, K, C, y)
                )
            ),
            tapp1FullAt(builder, K, cat, E, B, x, y, FF),
            tapp1FullAt(builder, K, cat, E, C, x, y, GG)
        )),
        provenance: source(
            'rule @tapp1_func $K Cat_cat _ _ $x $y ' +
            '(@Product_pair_funcd $K $E $B $C $FF $GG)'
        )
    };
};

const pairingCappedRule = (
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const {
        K, E, B, C, FF, GG, x, y, p, variables
    } = pairingVariables(builder, true, true);
    const cat = builder.global(categoryOfCategories);
    const product = transparentDisplayedProduct(builder, K, B, C);
    const Ex = fibre(builder, K, E, x);
    return {
        order,
        id: 'categorical.fibred-structure.pairing.capped-action',
        groupId: 'categorical.fibred-structure',
        clauseOrder: order,
        sourceOwner: transforHomCapped,
        variables,
        left: builder.pattern(tapp1At(
            builder,
            K,
            cat,
            E,
            product,
            x,
            y,
            displayedPairAt(builder, K, E, B, C, FF, GG),
            p
        )),
        right: builder.template(pairAt(
            builder,
            functorCategoryAt(builder, Ex, fibre(builder, K, B, y)),
            functorCategoryAt(builder, Ex, fibre(builder, K, C, y)),
            tapp1At(builder, K, cat, E, B, x, y, FF, p),
            tapp1At(builder, K, cat, E, C, x, y, GG, p)
        )),
        provenance: source(
            'rule @tapp1_fapp0 $K Cat_cat _ _ $x $y ' +
            '(@Product_pair_funcd $K $E $B $C $FF $GG) $p'
        )
    };
};

const pairingBetaRule = (
    side: 'left' | 'right',
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const {
        K, E, B, C, FF, GG, variables
    } = pairingVariables(builder, false, false);
    const product = transparentDisplayedProduct(builder, K, B, C);
    const target = side === 'left' ? B : C;
    return {
        order,
        id:
            `categorical.fibred-structure.${side}-projection.pairing-beta`,
        groupId: 'categorical.fibred-structure',
        clauseOrder: order,
        sourceOwner: genericComposition,
        variables,
        left: builder.pattern(composeAt(
            builder,
            displayedCategoryAt(builder, K),
            E,
            product,
            target,
            displayedProjectionAt(builder, side, K, B, C),
            displayedPairAt(builder, K, E, B, C, FF, GG)
        )),
        right: builder.template(side === 'left' ? FF : GG),
        provenance: source(
            `rule @comp_fapp0 (@Catd_cat $K) _ _ _ ` +
            `(@Product_proj${side === 'left' ? 'L' : 'R'}_funcd ` +
            '$K $B $C) ' +
            '(@Product_pair_funcd $K _ $B $C $FF $GG)'
        )
    };
};

const displayedFibreFacadeRule = (
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const FF = builder.capture('FF');
    const x = builder.capture('x');
    const cat = builder.global(categoryOfCategories);
    return {
        order,
        id: 'categorical.displayed-functor-fibre.delta',
        groupId: 'categorical.displayed-functor-facade',
        clauseOrder: 0,
        sourceOwner: fibreFunctor,
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
                name: 'D',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'FF',
                type: builder.template(displayedFunctorType(
                    builder,
                    K,
                    E,
                    D
                ))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(fibreFunctorAt(
            builder,
            K,
            E,
            D,
            FF,
            x
        )),
        right: builder.template(tapp0At(
            builder,
            K,
            cat,
            E,
            D,
            x,
            FF
        )),
        provenance: source(
            'symbol Fibre_func [K : Cat] [E D : τ (Catd K)] ' +
            '(FF : τ (Functord E D)) (z : τ (Obj K)) ' +
            '≔ @tapp0_fapp0 K Cat_cat E D z FF'
        )
    };
};

const displayedTransportFacadeRule = (
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const FF = builder.capture('FF');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const cat = builder.global(categoryOfCategories);
    return {
        order,
        id: 'categorical.displayed-functor-transport.delta',
        groupId: 'categorical.displayed-functor-facade',
        clauseOrder: 1,
        sourceOwner: displayedTransportFunctor,
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
                name: 'D',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'FF',
                type: builder.template(displayedFunctorType(
                    builder,
                    K,
                    E,
                    D
                ))
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
        left: builder.pattern(displayedTransportAt(
            builder,
            K,
            E,
            D,
            FF,
            x,
            y,
            p
        )),
        right: builder.template(tapp1At(
            builder,
            K,
            cat,
            E,
            D,
            x,
            y,
            FF,
            p
        )),
        provenance: source(
            'symbol functord_transport_func [K : Cat] ' +
            '[E D : τ (Catd K)] (FF : τ (Functord E D)) ' +
            '≔ @tapp1_fapp0 K Cat_cat E D x y FF p'
        )
    };
};

const fullTransforActionEvaluationRule = (
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const F = builder.capture('F');
    const G = builder.capture('G');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const eta = builder.capture('eta');
    const p = builder.capture('p');
    const cat = builder.global(categoryOfCategories);
    return {
        order,
        id: 'categorical.transfor-full-action.evaluate.cat-normalize',
        groupId: 'categorical.transfor-full-action',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, A, cat))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, A, cat))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'eta',
                type: builder.template(objectType(
                    builder,
                    transforCategoryAt(builder, A, cat, F, G)
                ))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, A, x, y))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            homCategoryAt(builder, A, x, y),
            functorCategoryAt(
                builder,
                fapp0(builder, A, cat, F, x),
                fapp0(builder, A, cat, G, y)
            ),
            tapp1FullAt(builder, A, cat, F, G, x, y, eta),
            p
        )),
        right: builder.template(tapp1At(
            builder,
            A,
            cat,
            F,
            G,
            x,
            y,
            eta,
            p
        )),
        provenance: source(
            'rule fapp0 (@tapp1_func $A $B $F $G $X $Y $ϵ) $f ' +
            '↪ @tapp1_fapp0 $A $B $F $G $X $Y $ϵ $f'
        )
    };
};

const displayedIdentityPointRule = (
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const x = builder.capture('x');
    const cat = builder.global(categoryOfCategories);
    return {
        order,
        id: 'categorical.displayed-identity.point.delta',
        groupId: 'categorical.displayed-identity',
        clauseOrder: 0,
        sourceOwner: transforComponentCapped,
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
                name: 'x',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(tapp0At(
            builder,
            K,
            cat,
            E,
            E,
            x,
            displayedIdentityAt(builder, K, E)
        )),
        right: builder.template(identityFunctorAt(
            builder,
            fibre(builder, K, E, x)
        )),
        provenance: source(
            'active id_funcd delta-specialization of: ' +
            'rule @tapp0_fapp0 $K Cat_cat $E $E $Y ' +
            '(@id (@Catd_cat $K) $E)'
        )
    };
};

const runtimeRules = Object.freeze([
    projectionPointRule('left', 0),
    projectionFullRule('left', 1),
    projectionCappedRule('left', 2),
    projectionPointRule('right', 3),
    projectionFullRule('right', 4),
    projectionCappedRule('right', 5),
    pairingPointRule(6),
    pairingFullRule(7),
    pairingCappedRule(8),
    pairingBetaRule('left', 9),
    pairingBetaRule('right', 10),
    displayedFibreFacadeRule(11),
    displayedTransportFacadeRule(12),
    fullTransforActionEvaluationRule(13),
    displayedIdentityPointRule(14)
]);

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'FIBRED-STRUCTURE-1A-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'fibred-structure-1a-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_FIBRED_STRUCTURE_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        functorClassifier,
        homClassifier,
        homCategory,
        transforCategory,
        categoryOfCategories,
        displayedCategoryCategory,
        displayedFunctorCategory,
        functorObject,
        functorHomFull,
        functorHomCapped,
        transforComponentCapped,
        transforHomFull,
        transforHomCapped,
        genericComposition,
        functorCategory,
        identityFunctor,
        functorComposition,
        productCategory,
        productPair,
        productLeftProjection,
        productRightProjection,
        uncurryPackage,
        internalProductFunctor,
        fibreFunctor,
        displayedTransportFunctor,
        precompositionFunctor,
        precompositionAction,
        displayedIdentity,
        displayedProductLeftProjection,
        displayedProductRightProjection,
        displayedProductPair
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

const newRuleIds = Object.freeze(
    runtimeRules
        .slice(0, 11)
        .map(rule => rule.id)
);

const prerequisiteRuleIds = Object.freeze([
    'categorical.displayed-functor-fibre.delta',
    'categorical.displayed-functor-transport.delta',
    'categorical.transfor-full-action.evaluate.cat-normalize',
    'categorical.displayed-identity.point.delta'
] as const);

const prerequisiteRuleEvidence = (ruleId: string): string => {
    switch (ruleId) {
    case 'categorical.displayed-functor-fibre.delta':
        return 'Typed delta of the existing transparent Fibre_func facade';
    case 'categorical.displayed-functor-transport.delta':
        return 'Typed delta of the existing transparent ' +
            'functord_transport_func facade';
    case 'categorical.transfor-full-action.evaluate.cat-normalize':
        return 'Typed Cat-valued normal-form specialization of existing ' +
            'full-to-capped action';
    case 'categorical.displayed-identity.point.delta':
        return 'Typed normal-form specialization of existing id_funcd point ' +
            'computation';
    default:
        throw new Error(
            `Unknown FIBRED-STRUCTURE-1A prerequisite rule '${ruleId}'`
        );
    }
};

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_FIBRED_STRUCTURE_RUNTIME_MODULE,
    {
        revision: 'FIBRED-STRUCTURE-1A-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_FIBRED_STRUCTURE_RUNTIME_MODULE.revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence: newRuleIds.includes(rule.id)
                ? 'Exact runtime rule approved and active under ' +
                    'D-DTTLF-USABILITY-006'
                : prerequisiteRuleEvidence(rule.id)
        }))
    }
);

export const CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY =
Object.freeze({
    status: 'root-only-approved-fibred-structure-closure',
    decisionId: 'D-DTTLF-USABILITY-006',
    familyPresentation:
        'transparent-uncurry-product-pair-composite',
    newMathematicalOwnerCount: 3,
    newKernelDeclarationCount: 3,
    existingPrerequisiteDeclarationCount: 3,
    declarationCount: declarations.length,
    newOwnerNames: Object.freeze([
        'Product_projL_funcd',
        'Product_projR_funcd',
        'Product_pair_funcd'
    ]),
    prerequisiteDeclarationNames: Object.freeze([
        'comp_cat_con_func',
        'hom_precomp_along_fapp0',
        'id_funcd'
    ]),
    newRuntimeRuleCount: newRuleIds.length,
    prerequisiteRuntimeRuleCount: prerequisiteRuleIds.length,
    runtimeRuleCount: runtimeRules.length,
    newRuntimeRuleIds: newRuleIds,
    prerequisiteRuntimeRuleIds: prerequisiteRuleIds,
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    allEntriesUseGenericTransferEngines: true,
    allLocalRuntimeRulesSubjectChecked: true,
    wildcardOrNewPatternShapeRequired: false,
    proofRulesInstalled: false,
    swapOwnerAdded: false,
    diagonalOwnerAdded: false,
    productFamilyOwnerAdded: false,
    kernelReindexingRuleAdded: false,
    rawPullbackProductConversionClaimed: false,
    doesNotProvide: Object.freeze([
        'Product_catd-primitive-or-alias',
        'universe-level-product-projection-transfors',
        'primitive-swap-or-diagonal-owner',
        'kernel-pullback-product-reindexing-equality',
        'global-Functord-product-conversion',
        'dependent-chain-exchange',
        'direct-fd-or-nd-binders',
        'browser-profile',
        'lambdapi-string-parser',
        'bulk-library-transfer'
    ])
});

export interface CoreCategoricalFibredStructureCompilation {
    readonly prerequisite: CoreCategoricalFibredProductCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
    readonly declarationContext: CoreLfMixedDeclarationContext;
}

export function compileCoreCategoricalFibredStructureTransfer():
CoreCategoricalFibredStructureCompilation {
    validateCoreLfScaleEngineReview();
    validateCoreCategoricalFibredStructureReview();
    const prerequisite =
        compileCoreCategoricalFibredProductTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_MODULE,
        CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_POLICY,
        CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: prerequisite.composedRuntime
        }
    );
    const initialContext = new CoreLfMixedDeclarationContext(
        prerequisite.declarationContext,
        [initialCompiled]
    );
    const prerequisiteFragment = new CoreLfCompiledRuntimeFragment(
        prerequisite.runtime,
        [],
        prerequisite.composedRuntime
    );
    const runtimeFragment = compileCoreLfRuntimeFragment(
        CORE_CATEGORICAL_FIBRED_STRUCTURE_RUNTIME_MODULE,
        CORE_CATEGORICAL_FIBRED_STRUCTURE_RUNTIME_POLICY,
        initialContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: prerequisiteFragment
            }]
        }
    );
    const runtime = runtimeFragment.localProgram;
    const composedRuntime = runtimeFragment.runtime;
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_MODULE,
        CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_POLICY,
        CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: composedRuntime
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        prerequisite.declarationContext,
        [compiled]
    );
    return Object.freeze({
        prerequisite,
        compiled,
        runtimeFragment,
        runtime,
        composedRuntime,
        declarationContext
    });
}

export type CoreCategoricalFibredStructureSymbolId =
    | 'precomposition-functor'
    | 'precomposition-action'
    | 'displayed-identity'
    | 'displayed-product-left-projection'
    | 'displayed-product-right-projection'
    | 'displayed-product-pair';

const symbolById:
Readonly<Record<
    CoreCategoricalFibredStructureSymbolId,
    CoreLfQualifiedSymbol
>> = Object.freeze({
    'precomposition-functor': precompositionFunctor,
    'precomposition-action': precompositionAction,
    'displayed-identity': displayedIdentity,
    'displayed-product-left-projection':
        displayedProductLeftProjection,
    'displayed-product-right-projection':
        displayedProductRightProjection,
    'displayed-product-pair': displayedProductPair
});

export function coreCategoricalFibredStructureCoreName(
    id: CoreCategoricalFibredStructureSymbolId
): string {
    const symbol = symbolById[id];
    const link =
        CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE.entries.find(
            candidate =>
                candidate.symbol.moduleId === symbol.moduleId &&
                candidate.symbol.name === symbol.name
        );
    if (link === undefined || link.kind !== 'free-declaration') {
        throw new Error(
            `Categorical fibred-structure declaration '${id}' has no ` +
            'free Core declaration'
        );
    }
    return link.coreName;
}
