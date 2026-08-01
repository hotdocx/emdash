/**
 * DIRECT-MIXED-CONSTANT-MIDDLE-COMPOSITION-1M generic transfer.
 *
 * This fragment adds the variance-qualified displayed lift of ordinary
 * functor composition. It also acquires only the ordinary composition-pair
 * signature/alias and object beta needed for useful point computation. The
 * direct nested binder remains fundamental; no curry package or total-context
 * section participates in this transfer.
 */

import {
    CoreCategoricalDirectMixedWeakeningCompilation,
    CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_LINKAGE,
    compileCoreCategoricalDirectMixedWeakeningTransfer
} from './categorical_direct_mixed_weakening_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_LINKAGE
} from './categorical_displayed_chain_2a_closure_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE
} from './categorical_displayed_nd_higher_foundation_transfer';
import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE
} from './categorical_fibred_product_transfer';
import {
    CORE_CATEGORICAL_FIBRED_STRUCTURE_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE
} from './categorical_fibred_structure_transfer';
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
    coreLfTransferExplicitBody,
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
CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_REVISION =
    'DIRECT-MIXED-CONSTANT-MIDDLE-1M-GENERIC-TRANSFER-1' as const;

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const groupoid =
    coreDirectedContinuationTransferSymbol('groupoid-universe');
const decodeOwner = coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const functorClassifier =
    coreDirectedContinuationTransferSymbol('functor-classifier');
const homClassifier =
    coreDirectedContinuationTransferSymbol('hom-classifier');
const homCategory =
    coreDirectedContinuationTransferSymbol('hom-category');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol('displayed-category-category');
const constantDisplayedFamily =
    coreDirectedContinuationTransferSymbol('constant-displayed-family');
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
const decodedDependentPair =
    coreDirectedContinuationTransferSymbol('decoded-dependent-pair');

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const displayedFunctorClassifier = symbol('Functord');
const oppositeCategory = symbol('Op_cat');
const stableFunctorFamily = symbol('Functor_catd');
const sigmaFirst = symbol('sigma_Fst');
const sigmaSecond = symbol('sigma_Snd');
const productGroupoid = symbol('Product_grpd');

const {
    functorCategory,
    functorComposition,
    productCategory,
    productPair,
    uncurryPackage
} = CORE_CATEGORICAL_STRUCTURAL_SYMBOLS;
const {
    internalProductFunctor
} = CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS;
const {
    precompositionFunctor
} = CORE_CATEGORICAL_FIBRED_STRUCTURE_SYMBOLS;

export const CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_SYMBOLS =
Object.freeze({
    ordinaryCompositionPair: symbol('comp_prod_func'),
    functorCompositionPair: symbol('Functor_comp_pair_func'),
    displayedComposition: symbol('Functor_comp_pair_funcd')
});

const {
    ordinaryCompositionPair,
    functorCompositionPair,
    displayedComposition
} = CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_SYMBOLS;

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

const constantFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    fibre: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, constantDisplayedFamily, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: fibre }
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

const compositionFamilies = (
    builder: CoreLfTransferScopedBuilder,
    K: CoreLfTransferBuilderExpression,
    X: CoreLfTransferBuilderExpression,
    A: CoreLfTransferBuilderExpression,
    B: CoreLfTransferBuilderExpression
) => {
    const left = stableFunctorFamilyAt(
        builder,
        K,
        A,
        constantFamilyAt(builder, K, X)
    );
    const right = stableFunctorFamilyAt(
        builder,
        K,
        constantFamilyAt(builder, oppositeAt(builder, K), X),
        B
    );
    return {
        source: transparentDisplayedProduct(builder, K, left, right),
        target: stableFunctorFamilyAt(builder, K, A, B)
    };
};

const ordinaryCompositionPairAt = (
    builder: CoreLfTransferScopedBuilder,
    ambient: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    middle: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, ordinaryCompositionPair, [
        { plicity: 'implicit', value: ambient },
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: middle },
        { plicity: 'implicit', value: target }
    ]);

const functorCompositionPairAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    middle: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorCompositionPair, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: middle },
        { plicity: 'implicit', value: target }
    ]);

const displayedCompositionAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    middle: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedComposition, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: middle },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily }
    ]);

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

const productObjectComponents = (
    builder: CoreLfTransferScopedBuilder,
    leftCategory: CoreLfTransferBuilderExpression,
    rightCategory: CoreLfTransferBuilderExpression,
    pair: CoreLfTransferBuilderExpression
) => {
    const left = objectClassifierAt(builder, leftCategory);
    const family = constantGroupoidFamily(
        builder,
        left,
        objectClassifierAt(builder, rightCategory)
    );
    return {
        first: globalCall(builder, sigmaFirst, [
            { plicity: 'implicit', value: left },
            { plicity: 'implicit', value: family },
            { plicity: 'explicit', value: pair }
        ]),
        second: globalCall(builder, sigmaSecond, [
            { plicity: 'implicit', value: left },
            { plicity: 'implicit', value: family },
            { plicity: 'explicit', value: pair }
        ])
    };
};

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const ordinaryCompositionPairType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'W',
            objectType(builder, A),
            W => builder.pi(
                'X',
                objectType(builder, A),
                X => builder.pi(
                    'Z',
                    objectType(builder, A),
                    Z => functorType(
                        builder,
                        productCategoryAt(
                            builder,
                            homCategoryAt(builder, A, W, X),
                            homCategoryAt(builder, A, X, Z)
                        ),
                        homCategoryAt(builder, A, W, Z)
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

const functorCompositionPairType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'C',
                builder.global(category),
                C => functorType(
                    builder,
                    productCategoryAt(
                        builder,
                        functorCategoryAt(builder, A, B),
                        functorCategoryAt(builder, B, C)
                    ),
                    functorCategoryAt(builder, A, C)
                ),
                implicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const functorCompositionPairBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'A',
        builder.global(category),
        A => builder.lam(
            'B',
            builder.global(category),
            B => builder.lam(
                'C',
                builder.global(category),
                C => ordinaryCompositionPairAt(
                    builder,
                    builder.global(categoryOfCategories),
                    A,
                    B,
                    C
                ),
                implicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const displayedCompositionType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'X',
            builder.global(category),
            X => builder.pi(
                'A',
                displayedFamilyType(builder, oppositeAt(builder, K)),
                A => builder.pi(
                    'B',
                    displayedFamilyType(builder, K),
                    B => {
                        const families = compositionFamilies(
                            builder,
                            K,
                            X,
                            A,
                            B
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
        symbol: ordinaryCompositionPair,
        type: ordinaryCompositionPairType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'ordinary',
            sourceOpacity: 'opaque'
        },
        provenance: source('symbol comp_prod_func [A : Cat]')
    },
    {
        order: 1,
        symbol: functorCompositionPair,
        type: functorCompositionPairType(),
        body: coreLfTransferExplicitBody(functorCompositionPairBody()),
        modifiers: {
            visibility: 'public',
            rigidity: 'ordinary',
            sourceOpacity: 'transparent'
        },
        provenance: source(
            'symbol Functor_comp_pair_func [A B C : Cat]'
        )
    },
    {
        order: 2,
        symbol: displayedComposition,
        type: displayedCompositionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'injective',
            sourceOpacity: 'opaque'
        },
        provenance: source(
            'injective symbol Functor_comp_pair_funcd [K X : Cat]'
        )
    }
]);

const externalSymbols = Object.freeze([
    category,
    groupoid,
    decodeOwner,
    objectClassifier,
    functorClassifier,
    homClassifier,
    homCategory,
    categoryOfCategories,
    displayedCategoryCategory,
    constantDisplayedFamily,
    functorObject,
    functorHomFull,
    functorHomCapped,
    transforComponentCapped,
    transforHomFull,
    transforHomCapped,
    decodedDependentPair,
    displayedFunctorClassifier,
    oppositeCategory,
    stableFunctorFamily,
    sigmaFirst,
    sigmaSecond,
    productGroupoid,
    functorCategory,
    functorComposition,
    productCategory,
    productPair,
    uncurryPackage,
    internalProductFunctor,
    precompositionFunctor
]);

export const CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'direct-mixed-constant-middle-1m-signatures',
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

export const CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_MODULE,
    {
        revision: 'DIRECT-MIXED-CONSTANT-MIDDLE-1M-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_MODULE
                .revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: declaration.symbol.name === 'Functor_comp_pair_func'
                ? 'checked-transparent-definition' as const
                : 'opaque-signature' as const,
            evidence: declaration.symbol.name ===
                'Functor_comp_pair_funcd'
                ? 'Exact D-DTTLF-USABILITY-052 active injective owner'
                : 'Exact pre-existing ordinary composition prerequisite'
        }))
    }
);

const dependencyLinks = Object.freeze([
    ...CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE
        .entries,
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
            'DIRECT-MIXED-CONSTANT-MIDDLE-1M has no dependency link for ' +
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
CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage = createCoreLfTransferDeclarationLinkage(
    CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_MODULE,
    {
        revision: 'DIRECT-MIXED-CONSTANT-MIDDLE-1M-LINKAGE-1',
        moduleRevision:
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_MODULE
                .revision,
        entries: [
            ...externalSymbols.map(dependencyLink),
            ...declarations.map((declaration, index) => ({
                order: externalSymbols.length + index,
                symbol: declaration.symbol,
                kind: 'free-declaration' as const,
                coreName:
                    'emdash_v3_2_direct_mixed_constant_middle_1m_' +
                    declaration.symbol.name,
                backendName: declaration.symbol.name
            }))
        ]
    }
);

const ordinaryPointRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const W = builder.capture('W');
    const X = builder.capture('X');
    const Z = builder.capture('Z');
    const pg = builder.capture('pg');
    const cat = builder.global(categoryOfCategories);
    const leftHom = homCategoryAt(builder, cat, W, X);
    const rightHom = homCategoryAt(builder, cat, X, Z);
    const sourceCategory = productCategoryAt(builder, leftHom, rightHom);
    const targetCategory = homCategoryAt(builder, cat, W, Z);
    const components = productObjectComponents(
        builder,
        leftHom,
        rightHom,
        pg
    );
    return {
        order: 0,
        id: 'categorical.direct-mixed-constant-middle.ordinary-point',
        groupId: 'categorical.direct-mixed-constant-middle',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            { name: 'W', type: builder.template(builder.global(category)) },
            { name: 'X', type: builder.template(builder.global(category)) },
            { name: 'Z', type: builder.template(builder.global(category)) },
            {
                name: 'pg',
                type: builder.template(objectType(builder, sourceCategory))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            builder.wildcard(sourceCategory),
            builder.wildcard(targetCategory),
            ordinaryCompositionPairAt(builder, cat, W, X, Z),
            pg
        )),
        // `comp_cat_fapp0` is the existing checked transparent facade for
        // the source term `@comp_fapp0 Cat_cat`. Orienting to that
        // definitionally equal presentation keeps its already-transferred
        // object/arrow rules iterable without adding a semantic rule here.
        right: builder.template(composeFunctorsAt(
            builder,
            W,
            X,
            Z,
            components.second,
            components.first
        )),
        provenance: source(
            'Cat_cat specialization of: rule fapp0 ' +
                '(@comp_prod_func $A $W $X $Z) $pg'
        )
    };
};

const displayedPointRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const X = builder.capture('X');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const k = builder.capture('k');
    const families = compositionFamilies(builder, K, X, A, B);
    return {
        order: 1,
        id: 'categorical.direct-mixed-constant-middle.point',
        groupId: 'categorical.direct-mixed-constant-middle',
        clauseOrder: 1,
        sourceOwner: transforComponentCapped,
        variables: [
            { name: 'K', type: builder.template(builder.global(category)) },
            { name: 'X', type: builder.template(builder.global(category)) },
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
            { name: 'k', type: builder.template(objectType(builder, K)) }
        ],
        left: builder.pattern(transforComponentAt(
            builder,
            K,
            builder.global(categoryOfCategories),
            builder.wildcard(families.source),
            builder.wildcard(families.target),
            k,
            displayedCompositionAt(builder, K, X, A, B)
        )),
        right: builder.template(functorCompositionPairAt(
            builder,
            fibreAt(builder, oppositeAt(builder, K), A, k),
            X,
            fibreAt(builder, K, B, k)
        )),
        provenance: source(
            'rule @tapp0_fapp0 $K Cat_cat _ _ $k ' +
                '(@Functor_comp_pair_funcd $K $X $A $B)'
        )
    };
};

const displayedFullRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const X = builder.capture('X');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const families = compositionFamilies(builder, K, X, A, B);
    const sourceFibre = fibreAt(builder, K, families.source, x);
    const targetFibreX = fibreAt(builder, K, families.target, x);
    const targetFibreY = fibreAt(builder, K, families.target, y);
    const point = functorCompositionPairAt(
        builder,
        fibreAt(builder, oppositeAt(builder, K), A, x),
        X,
        fibreAt(builder, K, B, x)
    );
    return {
        order: 2,
        id: 'categorical.direct-mixed-constant-middle.full-action',
        groupId: 'categorical.direct-mixed-constant-middle',
        clauseOrder: 2,
        sourceOwner: transforHomFull,
        variables: [
            { name: 'K', type: builder.template(builder.global(category)) },
            { name: 'X', type: builder.template(builder.global(category)) },
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
            { name: 'x', type: builder.template(objectType(builder, K)) },
            { name: 'y', type: builder.template(objectType(builder, K)) }
        ],
        left: builder.pattern(transforHomFullAt(
            builder,
            K,
            builder.global(categoryOfCategories),
            builder.wildcard(families.source),
            builder.wildcard(families.target),
            x,
            y,
            displayedCompositionAt(builder, K, X, A, B)
        )),
        right: builder.template(composeFunctorsAt(
            builder,
            homCategoryAt(builder, K, x, y),
            functorCategoryAt(builder, targetFibreX, targetFibreY),
            functorCategoryAt(builder, sourceFibre, targetFibreY),
            precompositionFunctorAt(
                builder,
                sourceFibre,
                targetFibreX,
                targetFibreY,
                point
            ),
            functorHomFullAt(
                builder,
                K,
                builder.global(categoryOfCategories),
                families.target,
                x,
                y
            )
        )),
        provenance: source(
            'rule @tapp1_func $K Cat_cat _ _ $x $y ' +
                '(@Functor_comp_pair_funcd $K $X $A $B)'
        )
    };
};

const displayedCappedRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const X = builder.capture('X');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const families = compositionFamilies(builder, K, X, A, B);
    const sourceFibre = fibreAt(builder, K, families.source, x);
    const targetFibreX = fibreAt(builder, K, families.target, x);
    const targetFibreY = fibreAt(builder, K, families.target, y);
    return {
        order: 3,
        id: 'categorical.direct-mixed-constant-middle.capped-action',
        groupId: 'categorical.direct-mixed-constant-middle',
        clauseOrder: 3,
        sourceOwner: transforHomCapped,
        variables: [
            { name: 'K', type: builder.template(builder.global(category)) },
            { name: 'X', type: builder.template(builder.global(category)) },
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
            { name: 'x', type: builder.template(objectType(builder, K)) },
            { name: 'y', type: builder.template(objectType(builder, K)) },
            { name: 'p', type: builder.template(homType(builder, K, x, y)) }
        ],
        left: builder.pattern(transforHomCappedAt(
            builder,
            K,
            builder.global(categoryOfCategories),
            builder.wildcard(families.source),
            builder.wildcard(families.target),
            x,
            y,
            displayedCompositionAt(builder, K, X, A, B),
            p
        )),
        right: builder.template(composeFunctorsAt(
            builder,
            sourceFibre,
            targetFibreX,
            targetFibreY,
            functorHomCappedAt(
                builder,
                K,
                builder.global(categoryOfCategories),
                families.target,
                x,
                y,
                p
            ),
            functorCompositionPairAt(
                builder,
                fibreAt(builder, oppositeAt(builder, K), A, x),
                X,
                fibreAt(builder, K, B, x)
            )
        )),
        provenance: source(
            'rule @tapp1_fapp0 $K Cat_cat _ _ $x $y ' +
                '(@Functor_comp_pair_funcd $K $X $A $B) $p'
        )
    };
};

const runtimeRules = Object.freeze([
    ordinaryPointRule(),
    displayedPointRule(),
    displayedFullRule(),
    displayedCappedRule()
]);

export const
CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'DIRECT-MIXED-CONSTANT-MIDDLE-1M-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'direct-mixed-constant-middle-1m-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [...externalSymbols, ...declarations.map(
        declaration => declaration.symbol
    )].map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const
CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_RUNTIME_MODULE,
    {
        revision: 'DIRECT-MIXED-CONSTANT-MIDDLE-1M-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_RUNTIME_MODULE
                .revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence: rule.order === 0
                ? 'Exact pre-existing comp_prod_func object beta'
                : 'Exact D-DTTLF-USABILITY-052 active projection'
        }))
    }
);

const declarationCoreName = (target: CoreLfQualifiedSymbol): string => {
    const entry =
        CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_LINKAGE
            .entries
            .find(candidate =>
                candidate.symbol.moduleId === target.moduleId &&
                candidate.symbol.name === target.name
            );
    if (entry === undefined || entry.kind !== 'free-declaration') {
        throw new Error(
            'DIRECT-MIXED-CONSTANT-MIDDLE-1M lost its declaration link for ' +
                `${target.moduleId}.${target.name}`
        );
    }
    return entry.coreName;
};

export const CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_CORE_NAMES =
Object.freeze({
    ordinaryCompositionPair: declarationCoreName(ordinaryCompositionPair),
    functorCompositionPair: declarationCoreName(functorCompositionPair),
    displayedComposition: declarationCoreName(displayedComposition)
});

export type CoreCategoricalDirectMixedConstantMiddleSymbolId =
    keyof typeof CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_CORE_NAMES;

export function coreCategoricalDirectMixedConstantMiddleCoreName(
    id: CoreCategoricalDirectMixedConstantMiddleSymbolId
): string {
    return CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_CORE_NAMES[id];
}

export const CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_BOUNDARY =
Object.freeze({
    decision: 'D-DTTLF-USABILITY-052',
    declarationNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    declarationCount: declarations.length,
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    runtimeRuleCount: runtimeRules.length,
    activeLambdapiOwnerDelta: 1,
    activeLambdapiRuleDelta: 3,
    preExistingOrdinaryDeclarationDelta: 2,
    preExistingOrdinaryRuleDelta: 1,
    ordinaryPointTransferScope: 'Cat_cat-specialization' as const,
    ordinaryPointRightPresentation:
        'checked-transparent-comp_cat_fapp0' as const,
    excludedOrdinaryActionProjectionCount: 3,
    intrinsicCoreOwnerDelta: 0,
    ownerSpecificCheckerOrEvaluatorDelta: 0,
    externalCoherenceEvidenceDelta: 0,
    contextualCurryDependency: false,
    totalContextSectionDependency: false,
    directNestedIntroductionRemainsFundamental: true,
    allEntriesUseGenericTransferEngines: true
});

export interface CoreCategoricalDirectMixedConstantMiddleCompilation {
    readonly prerequisite: CoreCategoricalDirectMixedWeakeningCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation:
    CoreCategoricalDirectMixedConstantMiddleCompilation | undefined;

export function compileCoreCategoricalDirectMixedConstantMiddleTransfer():
CoreCategoricalDirectMixedConstantMiddleCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    const prerequisite =
        compileCoreCategoricalDirectMixedWeakeningTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_MODULE,
        CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_POLICY,
        CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_LINKAGE,
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
        CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_RUNTIME_MODULE,
        CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_RUNTIME_POLICY,
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
        CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_MODULE,
        CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_POLICY,
        CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_LINKAGE,
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
