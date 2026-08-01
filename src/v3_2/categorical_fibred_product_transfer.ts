/**
 * FIBRED-PRODUCT-1A transfer of the first fibrewise-cartesian product
 * computation.
 *
 * The active kernel already represents the product of two Cat-valued
 * families by the transparent composite
 *
 *   uncurry(Product_cat_func) o Product_pair(B,C).
 *
 * No `Product_catd` declaration is introduced. This fragment imports the
 * existing stable owners needed to expose that composite, transfers the
 * already-active prerequisite computations through the generic declaration
 * and runtime compilers, and adds exactly the two rules approved by
 * D-DTTLF-USABILITY-004.
 *
 * Some prerequisite rules below are explicit delta-specializations of
 * transparent source definitions (`comp_cat_fapp0`, `Product_pair`, and
 * `uncurry_func_func`). They are recorded separately from the two genuinely
 * new active Lambdapi rules.
 */

import {
    CORE_CATEGORICAL_COMPREHENSION_TRANSFER_LINKAGE,
    CoreCategoricalComprehensionCompilation,
    compileCoreCategoricalComprehensionTransfer
} from './categorical_comprehension_transfer';
import {
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE
} from './categorical_dependent_composition_transfer';
import {
    CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE
} from './categorical_dependent_transfer';
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

export const CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_REVISION =
    'FIBRED-PRODUCT-1A-TRANSPARENT-PRODUCT-1' as const;

/* Updated mechanically after the active kernel tranche is frozen. */
export const CORE_CATEGORICAL_FIBRED_PRODUCT_SOURCE_SHA256 =
    'sha256:c09f503aff20cb3f9f5b59fcb1dbb4339bdfa853b48931ebd0dcce9b827ef29f';

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
const transforClassifier =
    coreDirectedContinuationTransferSymbol('transfor-classifier');
const transforCategory =
    coreDirectedContinuationTransferSymbol('transfor-category');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const transforHomCapped =
    coreDirectedContinuationTransferSymbol('transfor-hom-capped');

const {
    functorCategory,
    identityFunctor,
    functorComposition,
    productCategory,
    productPair,
    productMap,
    evaluationFunctor,
    uncurryPackage
} = CORE_CATEGORICAL_STRUCTURAL_SYMBOLS;

export const CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS =
Object.freeze({
    postcompositionAction:
        coreLfQualifiedSymbol(MODULE_ID, 'hom_postcomp_fapp0'),
    internalProductFunctor:
        coreLfQualifiedSymbol(MODULE_ID, 'Product_cat_func'),
    partialProductFunctor:
        coreLfQualifiedSymbol(MODULE_ID, 'Product_cat_fapp0_func'),
    productLeftAction:
        coreLfQualifiedSymbol(
            MODULE_ID,
            'Product_cat_fapp1_fapp0_functord'
        ),
    fixedRightProductMap:
        coreLfQualifiedSymbol(
            MODULE_ID,
            'Product_cat_fapp1_tapp0_func'
        )
});

const {
    postcompositionAction,
    internalProductFunctor,
    partialProductFunctor,
    productLeftAction,
    fixedRightProductMap
} = CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS;

export type CoreCategoricalFibredProductPrerequisiteId =
    | 'transparent-uncurry-package'
    | 'ordinary-functor-composition-action'
    | 'paired-functor-action'
    | 'internal-product-object-ladder'
    | 'internal-product-left-action'
    | 'fixed-right-product-map-action'
    | 'evaluation-action'
    | 'postcomposition-object-action'
    | 'explicit-core-inferred-slot-normalization';

export interface CoreCategoricalFibredProductPrerequisite {
    readonly id: CoreCategoricalFibredProductPrerequisiteId;
    readonly activeAuthority:
        | 'checked-transparent-definition'
        | 'active-runtime-rule';
    readonly sourceOwners: readonly string[];
}

export const CORE_CATEGORICAL_FIBRED_PRODUCT_PREREQUISITES:
readonly CoreCategoricalFibredProductPrerequisite[] = Object.freeze([
    Object.freeze({
        id: 'transparent-uncurry-package' as const,
        activeAuthority: 'checked-transparent-definition' as const,
        sourceOwners: Object.freeze([
            'uncurry_func_func',
            'comp_cat_cov_func',
            'Product_mapL_func_func'
        ])
    }),
    Object.freeze({
        id: 'ordinary-functor-composition-action' as const,
        activeAuthority: 'active-runtime-rule' as const,
        sourceOwners: Object.freeze(['comp_cat_fapp0'])
    }),
    Object.freeze({
        id: 'paired-functor-action' as const,
        activeAuthority: 'active-runtime-rule' as const,
        sourceOwners: Object.freeze(['Struct_sigma', 'Product_pair'])
    }),
    Object.freeze({
        id: 'internal-product-object-ladder' as const,
        activeAuthority: 'active-runtime-rule' as const,
        sourceOwners: Object.freeze([
            'Product_cat_func',
            'Product_cat_fapp0_func'
        ])
    }),
    Object.freeze({
        id: 'internal-product-left-action' as const,
        activeAuthority: 'active-runtime-rule' as const,
        sourceOwners: Object.freeze([
            'Product_cat_fapp1_fapp0_functord'
        ])
    }),
    Object.freeze({
        id: 'fixed-right-product-map-action' as const,
        activeAuthority: 'active-runtime-rule' as const,
        sourceOwners: Object.freeze([
            'Product_cat_fapp1_tapp0_func'
        ])
    }),
    Object.freeze({
        id: 'evaluation-action' as const,
        activeAuthority: 'active-runtime-rule' as const,
        sourceOwners: Object.freeze(['Eval_func'])
    }),
    Object.freeze({
        id: 'postcomposition-object-action' as const,
        activeAuthority: 'active-runtime-rule' as const,
        sourceOwners: Object.freeze(['hom_postcomp_fapp0'])
    }),
    Object.freeze({
        id: 'explicit-core-inferred-slot-normalization' as const,
        activeAuthority: 'active-runtime-rule' as const,
        sourceOwners: Object.freeze([
            'id_func',
            'Eval_func',
            'hom_postcomp_fapp0'
        ])
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

const homClassifierAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, homClassifier, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
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

const transforClassifierAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, transforClassifier, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: sourceFunctor },
        { plicity: 'explicit', value: targetFunctor }
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

const fapp1 = (
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

const tapp1 = (
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

const pair = (
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

const productMapAt = (
    builder: CoreLfTransferScopedBuilder,
    leftSource: CoreLfTransferBuilderExpression,
    leftTarget: CoreLfTransferBuilderExpression,
    rightSource: CoreLfTransferBuilderExpression,
    rightTarget: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, productMap, [
        { plicity: 'implicit', value: leftSource },
        { plicity: 'implicit', value: leftTarget },
        { plicity: 'implicit', value: rightSource },
        { plicity: 'implicit', value: rightTarget },
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
    ]);

const evaluationAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, evaluationFunctor, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target }
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

const partialProductAt = (
    builder: CoreLfTransferScopedBuilder,
    left: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, partialProductFunctor, [{
        plicity: 'explicit',
        value: left
    }]);

const productLeftActionAt = (
    builder: CoreLfTransferScopedBuilder,
    leftSource: CoreLfTransferBuilderExpression,
    leftTarget: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, productLeftAction, [
        { plicity: 'implicit', value: leftSource },
        { plicity: 'implicit', value: leftTarget },
        { plicity: 'explicit', value: functor }
    ]);

const fixedRightProductMapAt = (
    builder: CoreLfTransferScopedBuilder,
    leftSource: CoreLfTransferBuilderExpression,
    leftTarget: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, fixedRightProductMap, [
        { plicity: 'implicit', value: leftSource },
        { plicity: 'implicit', value: leftTarget },
        { plicity: 'implicit', value: right },
        { plicity: 'explicit', value: functor }
    ]);

const postcompose = (
    builder: CoreLfTransferScopedBuilder,
    targetCategory: CoreLfTransferBuilderExpression,
    sourceCategory: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    fixedSource: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression,
    incoming: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, postcompositionAction, [
        { plicity: 'implicit', value: targetCategory },
        { plicity: 'implicit', value: sourceCategory },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: fixedSource },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: arrow },
        { plicity: 'explicit', value: incoming }
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

const internalProductFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    const cat = builder.global(categoryOfCategories);
    return builder.term(functorType(
        builder,
        cat,
        functorCategoryAt(builder, cat, cat)
    ));
};

const partialProductFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    const cat = builder.global(categoryOfCategories);
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        _A => functorType(builder, cat, cat),
        explicitMode
    ));
};

const productLeftActionType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    const cat = builder.global(categoryOfCategories);
    const endofunctors = functorCategoryAt(builder, cat, cat);
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'Aprime',
            builder.global(category),
            Aprime => builder.pi(
                'G',
                functorType(builder, A, Aprime),
                _G => homType(
                    builder,
                    endofunctors,
                    partialProductAt(builder, A),
                    partialProductAt(builder, Aprime)
                ),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const fixedRightProductMapType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'Aprime',
            builder.global(category),
            Aprime => builder.pi(
                'B',
                builder.global(category),
                B => builder.pi(
                    'G',
                    functorType(builder, A, Aprime),
                    _G => functorType(
                        builder,
                        productCategoryAt(builder, A, B),
                        productCategoryAt(builder, Aprime, B)
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

const postcompositionActionType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'F',
                functorType(builder, B, A),
                F => builder.pi(
                    'W',
                    objectType(builder, A),
                    W => builder.pi(
                        'X',
                        objectType(builder, B),
                        X => builder.pi(
                            'Y',
                            objectType(builder, B),
                            Y => builder.pi(
                                'f',
                                homType(builder, B, X, Y),
                                _f => builder.pi(
                                    'g',
                                    homType(
                                        builder,
                                        A,
                                        W,
                                        fapp0(
                                            builder,
                                            B,
                                            A,
                                            F,
                                            X
                                        )
                                    ),
                                    _g => homType(
                                        builder,
                                        A,
                                        W,
                                        fapp0(
                                            builder,
                                            B,
                                            A,
                                            F,
                                            Y
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
                    explicitMode
                ),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const declarations: readonly CoreLfTransferDeclaration[] = [
    {
        order: 0,
        symbol: internalProductFunctor,
        type: internalProductFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'constant symbol Product_cat_func : τ (Functor Cat_cat ' +
            '(Functor_cat Cat_cat Cat_cat))'
        )
    },
    {
        order: 1,
        symbol: partialProductFunctor,
        type: partialProductFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Product_cat_fapp0_func (A : Cat)'
        )
    },
    {
        order: 2,
        symbol: productLeftAction,
        type: productLeftActionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol Product_cat_fapp1_fapp0_functord [A A_prime : Cat]'
        )
    },
    {
        order: 3,
        symbol: fixedRightProductMap,
        type: fixedRightProductMapType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol Product_cat_fapp1_tapp0_func [A A_prime B : Cat]'
        )
    },
    {
        order: 4,
        symbol: postcompositionAction,
        type: postcompositionActionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol hom_postcomp_fapp0 [A B : Cat]'
        )
    }
];

export const CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'fibred-product-1a-signatures',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_FIBRED_PRODUCT_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        functorClassifier,
        homClassifier,
        categoryOfCategories,
        functorObject,
        functorCategory,
        productCategory
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_MODULE,
    {
        revision: 'FIBRED-PRODUCT-1A-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_MODULE.revision,
        entries: declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                declaration.symbol === productLeftAction
                    ? 'Existing active owner at its proof-time-normalized ' +
                        'ordinary transfor classifier'
                    : 'Existing active v3.2 prerequisite signature'
        }))
    }
);

const earlierLinks = [
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
            `FIBRED-PRODUCT-1A has no dependency link for ` +
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
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_MODULE
        .externalSymbols
        .map(external => external.symbol);

export const CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_MODULE,
        {
            revision: 'FIBRED-PRODUCT-1A-SIGNATURE-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_MODULE
                    .revision,
            entries: [
                ...externalSymbols.map(dependencyLink),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `emdash_v3_2_fibred_product_1a_` +
                        declaration.symbol.name,
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

const compositionObjectRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const F = builder.capture('F');
    const G = builder.capture('G');
    const x = builder.capture('x');
    return {
        order: 0,
        id: 'categorical.composition.object.delta',
        groupId: 'categorical.composition',
        clauseOrder: 0,
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
                name: 'C',
                type: builder.template(builder.global(category))
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, B, C))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, A, B))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, A))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            A,
            C,
            composeFunctors(builder, A, B, C, F, G),
            x
        )),
        right: builder.template(fapp0(
            builder,
            B,
            C,
            F,
            fapp0(builder, A, B, G, x)
        )),
        provenance: source(
            'active delta-specialization of: rule @fapp0 $A $C ' +
            '(@comp_fapp0 Cat_cat $A $B $C $F $G) $x'
        )
    };
};

const compositionArrowRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const F = builder.capture('F');
    const G = builder.capture('G');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const Gx = fapp0(builder, A, B, G, x);
    const Gy = fapp0(builder, A, B, G, y);
    return {
        order: 1,
        id: 'categorical.composition.arrow.delta',
        groupId: 'categorical.composition',
        clauseOrder: 1,
        sourceOwner: functorHomCapped,
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
                name: 'C',
                type: builder.template(builder.global(category))
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, B, C))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, A, B))
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
                name: 'p',
                type: builder.template(homType(builder, A, x, y))
            }
        ],
        left: builder.pattern(fapp1(
            builder,
            A,
            C,
            composeFunctors(builder, A, B, C, F, G),
            x,
            y,
            p
        )),
        right: builder.template(fapp1(
            builder,
            B,
            C,
            F,
            Gx,
            Gy,
            fapp1(builder, A, B, G, x, y, p)
        )),
        provenance: source(
            'active delta-specialization of: rule @fapp1_fapp0 ' +
            '$A $C (@comp_fapp0 Cat_cat $A $B $C $F $G) $x $y $p'
        )
    };
};

const pairedFunctorObjectRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const X = builder.capture('X');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const G = builder.capture('G');
    const i = builder.capture('i');
    const functorsXA = functorCategoryAt(builder, X, A);
    const functorsXB = functorCategoryAt(builder, X, B);
    return {
        order: 4,
        id: 'categorical.product-pair.object.delta',
        groupId: 'categorical.product-pair',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'X',
                type: builder.template(builder.global(category))
            },
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'B',
                type: builder.template(builder.global(category))
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, X, A))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, X, B))
            },
            {
                name: 'i',
                type: builder.template(objectType(builder, X))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            X,
            productCategoryAt(builder, A, B),
            pair(builder, functorsXA, functorsXB, F, G),
            i
        )),
        right: builder.template(pair(
            builder,
            A,
            B,
            fapp0(builder, X, A, F, i),
            fapp0(builder, X, B, G, i)
        )),
        provenance: source(
            'active Product_pair delta-specialization of: ' +
            'rule @fapp0 $X (Product_cat $A $B) ' +
            '(Struct_sigma $F $G) $i'
        )
    };
};

const homClassifierDeltaRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const x = builder.capture('x');
    const y = builder.capture('y');
    return {
        order: 2,
        id: 'categorical.hom-classifier.delta',
        groupId: 'categorical.hom-classifier',
        clauseOrder: 0,
        sourceOwner: homClassifier,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, A))
            }
        ],
        left: builder.pattern(homClassifierAt(builder, A, x, y)),
        right: builder.template(objectClassifierAt(
            builder,
            homCategoryAt(builder, A, x, y)
        )),
        provenance: source(
            'active transparent definition: ' +
            'injective symbol Hom (A : Cat) (x y : Obj A) ' +
            ': Grpd ≔ Obj (Hom_cat A x y)'
        )
    };
};

const productHomCategoryRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const x = builder.capture('x');
    const xprime = builder.capture('xprime');
    const y = builder.capture('y');
    const yprime = builder.capture('yprime');
    return {
        order: 3,
        id: 'categorical.product.hom-category',
        groupId: 'categorical.product-hom',
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
                name: 'x',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'xprime',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, B))
            },
            {
                name: 'yprime',
                type: builder.template(objectType(builder, B))
            }
        ],
        left: builder.pattern(homCategoryAt(
            builder,
            productCategoryAt(builder, A, B),
            pair(builder, A, B, x, y),
            pair(builder, A, B, xprime, yprime)
        )),
        right: builder.template(productCategoryAt(
            builder,
            homCategoryAt(builder, A, x, xprime),
            homCategoryAt(builder, B, y, yprime)
        )),
        provenance: source(
            'active Product_pair delta-specialization of: ' +
            'rule Hom_cat (Product_cat $A $B) ' +
            '(Struct_sigma $x $y) (Struct_sigma $xprime $yprime)'
        )
    };
};

const pairedFunctorArrowRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const X = builder.capture('X');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const G = builder.capture('G');
    const i = builder.capture('i');
    const j = builder.capture('j');
    const p = builder.capture('p');
    const Fi = fapp0(builder, X, A, F, i);
    const Fj = fapp0(builder, X, A, F, j);
    const Gi = fapp0(builder, X, B, G, i);
    const Gj = fapp0(builder, X, B, G, j);
    return {
        order: 5,
        id: 'categorical.product-pair.arrow.delta',
        groupId: 'categorical.product-pair',
        clauseOrder: 1,
        sourceOwner: functorHomCapped,
        variables: [
            {
                name: 'X',
                type: builder.template(builder.global(category))
            },
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'B',
                type: builder.template(builder.global(category))
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, X, A))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, X, B))
            },
            {
                name: 'i',
                type: builder.template(objectType(builder, X))
            },
            {
                name: 'j',
                type: builder.template(objectType(builder, X))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, X, i, j))
            }
        ],
        left: builder.pattern(fapp1(
            builder,
            X,
            productCategoryAt(builder, A, B),
            pair(
                builder,
                functorCategoryAt(builder, X, A),
                functorCategoryAt(builder, X, B),
                F,
                G
            ),
            i,
            j,
            p
        )),
        right: builder.template(pair(
            builder,
            homCategoryAt(builder, A, Fi, Fj),
            homCategoryAt(builder, B, Gi, Gj),
            fapp1(builder, X, A, F, i, j, p),
            fapp1(builder, X, B, G, i, j, p)
        )),
        provenance: source(
            'active Product_pair delta-specialization of: ' +
            'rule @fapp1_fapp0 $X (Product_cat $A $B) ' +
            '(Struct_sigma $F $G) $i $j $p'
        )
    };
};

const internalProductFirstObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const cat = builder.global(categoryOfCategories);
    return {
        order: 6,
        id: 'categorical.internal-product.first-object',
        groupId: 'categorical.internal-product',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [{
            name: 'A',
            type: builder.template(builder.global(category))
        }],
        left: builder.pattern(fapp0(
            builder,
            cat,
            functorCategoryAt(builder, cat, cat),
            builder.global(internalProductFunctor),
            A
        )),
        right: builder.template(partialProductAt(builder, A)),
        provenance: source(
            'rule @fapp0 _ _ Product_cat_func $A'
        )
    };
};

const internalProductSecondObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const cat = builder.global(categoryOfCategories);
    return {
        order: 7,
        id: 'categorical.internal-product.second-object',
        groupId: 'categorical.internal-product',
        clauseOrder: 1,
        sourceOwner: functorObject,
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
        left: builder.pattern(fapp0(
            builder,
            cat,
            cat,
            partialProductAt(builder, A),
            B
        )),
        right: builder.template(productCategoryAt(builder, A, B)),
        provenance: source(
            'rule @fapp0 Cat_cat Cat_cat ' +
            '(@Product_cat_fapp0_func $A) $B'
        )
    };
};

const internalProductArrowRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const Aprime = builder.capture('Aprime');
    const G = builder.capture('G');
    const cat = builder.global(categoryOfCategories);
    return {
        order: 8,
        id: 'categorical.internal-product.left-arrow',
        groupId: 'categorical.internal-product',
        clauseOrder: 2,
        sourceOwner: functorHomCapped,
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
                name: 'G',
                type: builder.template(functorType(
                    builder,
                    A,
                    Aprime
                ))
            }
        ],
        left: builder.pattern(fapp1(
            builder,
            cat,
            functorCategoryAt(builder, cat, cat),
            builder.global(internalProductFunctor),
            A,
            Aprime,
            G
        )),
        right: builder.template(productLeftActionAt(
            builder,
            A,
            Aprime,
            G
        )),
        provenance: source(
            'rule @fapp1_fapp0 _ _ Product_cat_func $A $Aprime $G'
        )
    };
};

const fixedRightProductObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const Aprime = builder.capture('Aprime');
    const B = builder.capture('B');
    const G = builder.capture('G');
    const x = builder.capture('x');
    const y = builder.capture('y');
    return {
        order: 9,
        id: 'categorical.fixed-right-product.object',
        groupId: 'categorical.fixed-right-product',
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
                name: 'G',
                type: builder.template(functorType(
                    builder,
                    A,
                    Aprime
                ))
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
        left: builder.pattern(fapp0(
            builder,
            productCategoryAt(builder, A, B),
            productCategoryAt(builder, Aprime, B),
            fixedRightProductMapAt(
                builder,
                A,
                Aprime,
                B,
                G
            ),
            pair(builder, A, B, x, y)
        )),
        right: builder.template(pair(
            builder,
            Aprime,
            B,
            fapp0(builder, A, Aprime, G, x),
            y
        )),
        provenance: source(
            'rule @fapp0 _ _ ' +
            '(@Product_cat_fapp1_tapp0_func $A $Aprime $B $G) ' +
            '(Struct_sigma $x $y)'
        )
    };
};

const fixedRightProductArrowRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const Aprime = builder.capture('Aprime');
    const B = builder.capture('B');
    const G = builder.capture('G');
    const x = builder.capture('x');
    const xprime = builder.capture('xprime');
    const y = builder.capture('y');
    const yprime = builder.capture('yprime');
    const p = builder.capture('p');
    const q = builder.capture('q');
    const Gx = fapp0(builder, A, Aprime, G, x);
    const Gxprime = fapp0(builder, A, Aprime, G, xprime);
    return {
        order: 10,
        id: 'categorical.fixed-right-product.arrow',
        groupId: 'categorical.fixed-right-product',
        clauseOrder: 1,
        sourceOwner: functorHomCapped,
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
                name: 'G',
                type: builder.template(functorType(
                    builder,
                    A,
                    Aprime
                ))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'xprime',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, B))
            },
            {
                name: 'yprime',
                type: builder.template(objectType(builder, B))
            },
            {
                name: 'p',
                type: builder.template(homType(
                    builder,
                    A,
                    x,
                    xprime
                ))
            },
            {
                name: 'q',
                type: builder.template(homType(
                    builder,
                    B,
                    y,
                    yprime
                ))
            }
        ],
        left: builder.pattern(fapp1(
            builder,
            productCategoryAt(builder, A, B),
            productCategoryAt(builder, Aprime, B),
            fixedRightProductMapAt(
                builder,
                A,
                Aprime,
                B,
                G
            ),
            pair(builder, A, B, x, y),
            pair(builder, A, B, xprime, yprime),
            pair(
                builder,
                homCategoryAt(builder, A, x, xprime),
                homCategoryAt(builder, B, y, yprime),
                p,
                q
            )
        )),
        right: builder.template(pair(
            builder,
            homCategoryAt(builder, Aprime, Gx, Gxprime),
            homCategoryAt(builder, B, y, yprime),
            fapp1(builder, A, Aprime, G, x, xprime, p),
            q
        )),
        provenance: source(
            'rule @fapp1_fapp0 _ _ ' +
            '(@Product_cat_fapp1_tapp0_func $A $Aprime $B $G) ' +
            '(Struct_sigma $x $y) (Struct_sigma $xprime $yprime) ' +
            '(Struct_sigma $p $q)'
        )
    };
};

const categoryUniverseHomRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const cat = builder.global(categoryOfCategories);
    return {
        order: 11,
        id: 'categorical.category-universe.hom',
        groupId: 'categorical.category-universe',
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
            }
        ],
        left: builder.pattern(homCategoryAt(builder, cat, A, B)),
        right: builder.template(functorCategoryAt(builder, A, B)),
        provenance: source(
            'rule Hom_cat Cat_cat $A $B ↪ Functor_cat $A $B'
        )
    };
};

const functorHomCategoryRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const G = builder.capture('G');
    return {
        order: 12,
        id: 'categorical.functor.hom-category',
        groupId: 'categorical.transfor-classifier',
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
                name: 'F',
                type: builder.template(functorType(builder, A, B))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, A, B))
            }
        ],
        left: builder.pattern(homCategoryAt(
            builder,
            functorCategoryAt(builder, A, B),
            F,
            G
        )),
        right: builder.template(transforCategoryAt(
            builder,
            A,
            B,
            F,
            G
        )),
        provenance: source(
            'rule Hom_cat (Functor_cat $A $B) $F $G ' +
            '↪ Transf_cat $F $G'
        )
    };
};

const transforClassifierDeltaRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const G = builder.capture('G');
    return {
        order: 13,
        id: 'categorical.transfor-classifier.delta',
        groupId: 'categorical.transfor-classifier',
        clauseOrder: 1,
        sourceOwner: transforClassifier,
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
                name: 'F',
                type: builder.template(functorType(builder, A, B))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, A, B))
            }
        ],
        left: builder.pattern(transforClassifierAt(
            builder,
            A,
            B,
            F,
            G
        )),
        right: builder.template(objectClassifierAt(
            builder,
            transforCategoryAt(builder, A, B, F, G)
        )),
        provenance: source(
            'active transparent definition: ' +
            'injective symbol Transf [A B : Cat] (F G : Functor A B) ' +
            ': Grpd ≔ Obj (Transf_cat F G)'
        )
    };
};

const evaluationObjectRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const x = builder.capture('x');
    const functors = functorCategoryAt(builder, A, B);
    return {
        order: 14,
        id: 'categorical.evaluation.object',
        groupId: 'categorical.evaluation',
        clauseOrder: 0,
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
                name: 'F',
                type: builder.template(functorType(builder, A, B))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, A))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            productCategoryAt(builder, functors, A),
            B,
            evaluationAt(builder, A, B),
            pair(builder, functors, A, F, x)
        )),
        right: builder.template(fapp0(builder, A, B, F, x)),
        provenance: source(
            'rule fapp0 (@Eval_func $A $B) ' +
            '(Struct_sigma $F $x)'
        )
    };
};

const evaluationArrowRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const G = builder.capture('G');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const eta = builder.capture('eta');
    const p = builder.capture('p');
    const functors = functorCategoryAt(builder, A, B);
    return {
        order: 15,
        id: 'categorical.evaluation.arrow',
        groupId: 'categorical.evaluation',
        clauseOrder: 1,
        sourceOwner: functorHomCapped,
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
                name: 'F',
                type: builder.template(functorType(builder, A, B))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, A, B))
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
                type: builder.template(homType(
                    builder,
                    functors,
                    F,
                    G
                ))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, A, x, y))
            }
        ],
        left: builder.pattern(fapp1(
            builder,
            productCategoryAt(builder, functors, A),
            B,
            evaluationAt(builder, A, B),
            pair(builder, functors, A, F, x),
            pair(builder, functors, A, G, y),
            pair(
                builder,
                homCategoryAt(builder, functors, F, G),
                homCategoryAt(builder, A, x, y),
                eta,
                p
            )
        )),
        right: builder.template(tapp1(
            builder,
            A,
            B,
            F,
            G,
            x,
            y,
            eta,
            p
        )),
        provenance: source(
            'rule @fapp1_fapp0 _ _ (@Eval_func $A $B) ' +
            '(Struct_sigma $F $x) (Struct_sigma $G $y) ' +
            '(Struct_sigma $eta $p)'
        )
    };
};

/*
 * The fixed-right product action has already normalized the two Hom-category
 * annotations on its paired arrow to Transf_cat and Functor_cat. Retain the
 * exact generic evaluation rule above and this typed Cat-valued normal-form
 * specialization so the structural matcher need not admit wildcards or
 * conversion-aware patterns.
 */
const evaluationCatArrowNormalizationRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const F = builder.capture('F');
    const G = builder.capture('G');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const eta = builder.capture('eta');
    const p = builder.capture('p');
    const cat = builder.global(categoryOfCategories);
    const functors = functorCategoryAt(builder, cat, cat);
    return {
        order: 16,
        id: 'categorical.evaluation.arrow.cat-normalize',
        groupId: 'categorical.evaluation',
        clauseOrder: 2,
        sourceOwner: functorHomCapped,
        variables: [
            {
                name: 'F',
                type: builder.template(functorType(builder, cat, cat))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, cat, cat))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, cat))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, cat))
            },
            {
                name: 'eta',
                type: builder.template(homType(
                    builder,
                    functors,
                    F,
                    G
                ))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, cat, x, y))
            }
        ],
        left: builder.pattern(fapp1(
            builder,
            productCategoryAt(builder, functors, cat),
            cat,
            evaluationAt(builder, cat, cat),
            pair(builder, functors, cat, F, x),
            pair(builder, functors, cat, G, y),
            pair(
                builder,
                transforCategoryAt(builder, cat, cat, F, G),
                functorCategoryAt(builder, x, y),
                eta,
                p
            )
        )),
        right: builder.template(tapp1(
            builder,
            cat,
            cat,
            F,
            G,
            x,
            y,
            eta,
            p
        )),
        provenance: source(
            'typed Cat-valued classifier-normal-form specialization of: ' +
            'rule @fapp1_fapp0 _ _ (@Eval_func $A $B) ' +
            '(Struct_sigma $F $x) (Struct_sigma $G $y) ' +
            '(Struct_sigma $eta $p)'
        )
    };
};

const postcompositionObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const B = builder.capture('B');
    const E = builder.capture('E');
    const W = builder.capture('W');
    const X = builder.capture('X');
    const Y = builder.capture('Y');
    const p = builder.capture('p');
    const G = builder.capture('G');
    const w = builder.capture('w');
    const cat = builder.global(categoryOfCategories);
    const EX = fapp0(builder, B, cat, E, X);
    const EY = fapp0(builder, B, cat, E, Y);
    const Ep = fapp1(builder, B, cat, E, X, Y, p);
    return {
        order: 19,
        id: 'categorical.postcomposition.object',
        groupId: 'categorical.postcomposition',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'B',
                type: builder.template(builder.global(category))
            },
            {
                name: 'E',
                type: builder.template(functorType(builder, B, cat))
            },
            {
                name: 'W',
                type: builder.template(builder.global(category))
            },
            {
                name: 'X',
                type: builder.template(objectType(builder, B))
            },
            {
                name: 'Y',
                type: builder.template(objectType(builder, B))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, B, X, Y))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, W, EX))
            },
            {
                name: 'w',
                type: builder.template(objectType(builder, W))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            W,
            EY,
            postcompose(
                builder,
                cat,
                B,
                E,
                W,
                X,
                Y,
                p,
                G
            ),
            w
        )),
        right: builder.template(fapp0(
            builder,
            EX,
            EY,
            Ep,
            fapp0(builder, W, EX, G, w)
        )),
        provenance: source(
            'rule @fapp0 _ _ (@hom_postcomp_fapp0 ' +
            'Cat_cat $B $E $W $X $Y $p $G) $w'
        )
    };
};

const postcompositionIdentityObjectNormalizationRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const W = builder.capture('W');
    const X = builder.capture('X');
    const Y = builder.capture('Y');
    const p = builder.capture('p');
    const G = builder.capture('G');
    const w = builder.capture('w');
    const cat = builder.global(categoryOfCategories);
    const identity = identityFunctorAt(builder, cat);
    const EX = fapp0(builder, cat, cat, identity, X);
    const EY = fapp0(builder, cat, cat, identity, Y);
    const Ep = fapp1(builder, cat, cat, identity, X, Y, p);
    return {
        order: 20,
        id: 'categorical.postcomposition.object.identity-target-normalize',
        groupId: 'categorical.postcomposition',
        clauseOrder: 1,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'W',
                type: builder.template(builder.global(category))
            },
            {
                name: 'X',
                type: builder.template(objectType(builder, cat))
            },
            {
                name: 'Y',
                type: builder.template(objectType(builder, cat))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, cat, X, Y))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, W, EX))
            },
            {
                name: 'w',
                type: builder.template(objectType(builder, W))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            W,
            Y,
            postcompose(
                builder,
                cat,
                cat,
                identity,
                W,
                X,
                Y,
                p,
                G
            ),
            w
        )),
        right: builder.template(fapp0(
            builder,
            EX,
            EY,
            Ep,
            fapp0(builder, W, EX, G, w)
        )),
        provenance: source(
            'typed identity-family normal-form specialization of: ' +
            'rule @fapp0 _ _ (@hom_postcomp_fapp0 ' +
            'Cat_cat $B $E $W $X $Y $p $G) $w'
        )
    };
};

const uncurryObjectNormalizationRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const G = builder.capture('G');
    const cat = builder.global(categoryOfCategories);
    const functorsBC = functorCategoryAt(builder, B, C);
    const curried = functorCategoryAt(
        builder,
        A,
        functorsBC
    );
    const uncurried = functorCategoryAt(
        builder,
        productCategoryAt(builder, A, B),
        C
    );
    const evaluationSource = productCategoryAt(
        builder,
        functorsBC,
        B
    );
    return {
        order: 23,
        id: 'categorical.uncurry.object.delta-normalize',
        groupId: 'categorical.uncurry',
        clauseOrder: 0,
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
                name: 'C',
                type: builder.template(builder.global(category))
            },
            {
                name: 'G',
                type: builder.template(functorType(
                    builder,
                    A,
                    functorsBC
                ))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            curried,
            uncurried,
            uncurryPackageAt(builder, A, B, C),
            G
        )),
        right: builder.template(postcompose(
            builder,
            cat,
            cat,
            identityFunctorAt(builder, cat),
            productCategoryAt(builder, A, B),
            evaluationSource,
            C,
            evaluationAt(builder, B, C),
            fixedRightProductMapAt(
                builder,
                A,
                functorsBC,
                B,
                G
            )
        )),
        provenance: source(
            'active delta/runtime normal form of: ' +
            'fapp0 (@uncurry_func_func $A $B $C) $G'
        )
    };
};

const postcompositionArrowRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const B = builder.capture('B');
    const E = builder.capture('E');
    const W = builder.capture('W');
    const X = builder.capture('X');
    const Y = builder.capture('Y');
    const p = builder.capture('p');
    const G = builder.capture('G');
    const w = builder.capture('w');
    const wprime = builder.capture('wprime');
    const q = builder.capture('q');
    const cat = builder.global(categoryOfCategories);
    const EX = fapp0(builder, B, cat, E, X);
    const EY = fapp0(builder, B, cat, E, Y);
    const Ep = fapp1(builder, B, cat, E, X, Y, p);
    const Gw = fapp0(builder, W, EX, G, w);
    const Gwprime = fapp0(builder, W, EX, G, wprime);
    return {
        order: 21,
        id: 'categorical.postcomposition.arrow',
        groupId: 'categorical.postcomposition',
        clauseOrder: 2,
        sourceOwner: functorHomCapped,
        variables: [
            {
                name: 'B',
                type: builder.template(builder.global(category))
            },
            {
                name: 'E',
                type: builder.template(functorType(builder, B, cat))
            },
            {
                name: 'W',
                type: builder.template(builder.global(category))
            },
            {
                name: 'X',
                type: builder.template(objectType(builder, B))
            },
            {
                name: 'Y',
                type: builder.template(objectType(builder, B))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, B, X, Y))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, W, EX))
            },
            {
                name: 'w',
                type: builder.template(objectType(builder, W))
            },
            {
                name: 'wprime',
                type: builder.template(objectType(builder, W))
            },
            {
                name: 'q',
                type: builder.template(homType(
                    builder,
                    W,
                    w,
                    wprime
                ))
            }
        ],
        left: builder.pattern(fapp1(
            builder,
            W,
            EY,
            postcompose(
                builder,
                cat,
                B,
                E,
                W,
                X,
                Y,
                p,
                G
            ),
            w,
            wprime,
            q
        )),
        right: builder.template(fapp1(
            builder,
            EX,
            EY,
            Ep,
            Gw,
            Gwprime,
            fapp1(builder, W, EX, G, w, wprime, q)
        )),
        provenance: source(
            'rule @fapp1_fapp0 _ _ (@hom_postcomp_fapp0 ' +
            'Cat_cat $B $E $W $X $Y $p $G) $w $wprime $q'
        )
    };
};

/*
 * The active rule writes both outer category slots as inferred `_` slots.
 * Generic explicit Core reconstructs the target as E[Y]. When E is the
 * identity family, an already-normalized checked redex instead carries the
 * definitionally equal category Y. Keep the exact generic rule above and add
 * this typed identity-family normal-form specialization; this does not add a
 * Lambdapi rule or relax the generic runtime compiler's wildcard boundary.
 */
const postcompositionIdentityArrowNormalizationRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const W = builder.capture('W');
    const X = builder.capture('X');
    const Y = builder.capture('Y');
    const p = builder.capture('p');
    const G = builder.capture('G');
    const w = builder.capture('w');
    const wprime = builder.capture('wprime');
    const q = builder.capture('q');
    const cat = builder.global(categoryOfCategories);
    const identity = identityFunctorAt(builder, cat);
    const EX = fapp0(builder, cat, cat, identity, X);
    const EY = fapp0(builder, cat, cat, identity, Y);
    const Ep = fapp1(builder, cat, cat, identity, X, Y, p);
    const Gw = fapp0(builder, W, EX, G, w);
    const Gwprime = fapp0(builder, W, EX, G, wprime);
    return {
        order: 22,
        id: 'categorical.postcomposition.arrow.identity-target-normalize',
        groupId: 'categorical.postcomposition',
        clauseOrder: 3,
        sourceOwner: functorHomCapped,
        variables: [
            {
                name: 'W',
                type: builder.template(builder.global(category))
            },
            {
                name: 'X',
                type: builder.template(objectType(builder, cat))
            },
            {
                name: 'Y',
                type: builder.template(objectType(builder, cat))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, cat, X, Y))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, W, EX))
            },
            {
                name: 'w',
                type: builder.template(objectType(builder, W))
            },
            {
                name: 'wprime',
                type: builder.template(objectType(builder, W))
            },
            {
                name: 'q',
                type: builder.template(homType(
                    builder,
                    W,
                    w,
                    wprime
                ))
            }
        ],
        left: builder.pattern(fapp1(
            builder,
            W,
            Y,
            postcompose(
                builder,
                cat,
                cat,
                identity,
                W,
                X,
                Y,
                p,
                G
            ),
            w,
            wprime,
            q
        )),
        right: builder.template(fapp1(
            builder,
            EX,
            EY,
            Ep,
            Gw,
            Gwprime,
            fapp1(builder, W, EX, G, w, wprime, q)
        )),
        provenance: source(
            'typed identity-family normal-form specialization of: ' +
            'rule @fapp1_fapp0 _ _ (@hom_postcomp_fapp0 ' +
            'Cat_cat $B $E $W $X $Y $p $G) $w $wprime $q'
        )
    };
};

const identityFunctorObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const x = builder.capture('x');
    return {
        order: 17,
        id: 'categorical.identity-functor.object.delta',
        groupId: 'categorical.identity-functor',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, A))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            A,
            A,
            identityFunctorAt(builder, A),
            x
        )),
        right: builder.template(x),
        provenance: source(
            'active id_func delta-specialization of: ' +
            'rule @fapp0 $A $A (@id Cat_cat $A) $x'
        )
    };
};

const identityFunctorArrowRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    return {
        order: 18,
        id: 'categorical.identity-functor.arrow.delta',
        groupId: 'categorical.identity-functor',
        clauseOrder: 1,
        sourceOwner: functorHomCapped,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
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
                name: 'p',
                type: builder.template(homType(builder, A, x, y))
            }
        ],
        left: builder.pattern(fapp1(
            builder,
            A,
            A,
            identityFunctorAt(builder, A),
            x,
            y,
            p
        )),
        right: builder.template(p),
        provenance: source(
            'active id_func delta-specialization of: ' +
            'rule @fapp1_fapp0 $A $A (@id Cat_cat $A) $x $y $p'
        )
    };
};

const sharedBaseProductActionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const cat = builder.global(categoryOfCategories);
    const Bx = fapp0(builder, K, cat, B, x);
    const By = fapp0(builder, K, cat, B, y);
    const Cx = fapp0(builder, K, cat, C, x);
    const Cy = fapp0(builder, K, cat, C, y);
    const Bp = fapp1(builder, K, cat, B, x, y, p);
    const Cp = fapp1(builder, K, cat, C, x, y, p);
    return {
        order: 24,
        id: 'categorical.fibred-product.shared-base-arrow',
        groupId: 'categorical.fibred-product',
        clauseOrder: 0,
        sourceOwner: transforHomCapped,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'B',
                type: builder.template(functorType(builder, K, cat))
            },
            {
                name: 'C',
                type: builder.template(functorType(builder, K, cat))
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
        left: builder.pattern(tapp1(
            builder,
            cat,
            cat,
            partialProductAt(builder, Bx),
            partialProductAt(builder, By),
            Cx,
            Cy,
            productLeftActionAt(builder, Bx, By, Bp),
            Cp
        )),
        right: builder.template(productMapAt(
            builder,
            Bx,
            By,
            Cx,
            Cy,
            Bp,
            Cp
        )),
        provenance: source(
            'rule @tapp1_fapp0 Cat_cat Cat_cat _ _ _ _ ' +
            '(@Product_cat_fapp1_fapp0_functord _ _ ' +
            '(@fapp1_fapp0 $K Cat_cat $B $x $y $p)) ' +
            '(@fapp1_fapp0 $K Cat_cat $C $x $y $p)'
        )
    };
};

const runtimeRules = Object.freeze([
    compositionObjectRule(),
    compositionArrowRule(),
    homClassifierDeltaRule(),
    productHomCategoryRule(),
    pairedFunctorObjectRule(),
    pairedFunctorArrowRule(),
    internalProductFirstObjectRule(),
    internalProductSecondObjectRule(),
    internalProductArrowRule(),
    fixedRightProductObjectRule(),
    fixedRightProductArrowRule(),
    categoryUniverseHomRule(),
    functorHomCategoryRule(),
    transforClassifierDeltaRule(),
    evaluationObjectRule(),
    evaluationArrowRule(),
    evaluationCatArrowNormalizationRule(),
    identityFunctorObjectRule(),
    identityFunctorArrowRule(),
    postcompositionObjectRule(),
    postcompositionIdentityObjectNormalizationRule(),
    postcompositionArrowRule(),
    postcompositionIdentityArrowNormalizationRule(),
    uncurryObjectNormalizationRule(),
    sharedBaseProductActionRule()
]);

export const CORE_CATEGORICAL_FIBRED_PRODUCT_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'FIBRED-PRODUCT-1A-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'fibred-product-1a-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_FIBRED_PRODUCT_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        functorClassifier,
        homClassifier,
        homCategory,
        transforClassifier,
        transforCategory,
        categoryOfCategories,
        functorObject,
        functorHomCapped,
        transforHomCapped,
        functorCategory,
        identityFunctor,
        functorComposition,
        productCategory,
        productPair,
        productMap,
        evaluationFunctor,
        uncurryPackage,
        postcompositionAction,
        internalProductFunctor,
        partialProductFunctor,
        productLeftAction,
        fixedRightProductMap
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

const newRuleIds = Object.freeze([
    'categorical.postcomposition.arrow',
    'categorical.fibred-product.shared-base-arrow'
] as const);

const normalFormSpecializationRuleIds = Object.freeze([
    'categorical.identity-functor.arrow.delta',
    'categorical.evaluation.arrow.cat-normalize',
    'categorical.postcomposition.object.identity-target-normalize',
    'categorical.postcomposition.arrow.identity-target-normalize'
] as const);

export const CORE_CATEGORICAL_FIBRED_PRODUCT_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_FIBRED_PRODUCT_RUNTIME_MODULE,
    {
        revision: 'FIBRED-PRODUCT-1A-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_FIBRED_PRODUCT_RUNTIME_MODULE.revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence: (
                newRuleIds as readonly string[]
            ).includes(rule.id)
                ? 'Exact rule newly approved and active under ' +
                    'D-DTTLF-USABILITY-004'
                : (
                    normalFormSpecializationRuleIds as
                    readonly string[]
                ).includes(rule.id)
                    ? 'Typed explicit-Core normal-form specialization of ' +
                        'existing active computation'
                    : rule.id.endsWith('.delta') ||
                    rule.id.includes('.delta-normalize')
                    ? 'Checked delta-specialization of existing active ' +
                        'transparent computation'
                    : 'Exact existing active v3.2 prerequisite reduction'
        }))
    }
);

export const CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_BOUNDARY =
Object.freeze({
    status: 'root-only-approved-fibred-product-closure',
    familyPresentation:
        'transparent-uncurry-product-pair-composite',
    newMathematicalOwnerCount: 0,
    newKernelDeclarationCount: 0,
    existingPrerequisiteDeclarationCount: declarations.length,
    declarationNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    prerequisiteRuntimeRuleCount:
        runtimeRules.length - newRuleIds.length,
    newRuntimeRuleCount: newRuleIds.length,
    runtimeRuleCount: runtimeRules.length,
    newRuntimeRuleIds: newRuleIds,
    normalFormSpecializationRuleCount:
        normalFormSpecializationRuleIds.length,
    normalFormSpecializationRuleIds,
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    allEntriesUseGenericTransferEngines: true,
    allLocalRuntimeRulesSubjectChecked: true,
    wildcardOrNewPatternShapeRequired: false,
    warningsAreDiagnosticNotSelectionVetoes: true,
    necessityAudit: Object.freeze({
        reusedExistingConstructions: Object.freeze([
            'Product_cat_func',
            'uncurry_func_func',
            'Product_pair/Struct_sigma',
            'comp_cat_fapp0',
            'Product_cat_fapp1_fapp0_functord',
            'Product_cat_fapp1_tapp0_func',
            'Product_map_func',
            'Eval_func',
            'hom_postcomp_fapp0'
        ]),
        addedPrimitiveProductCatd: false,
        reasonForTwoNewRules:
            'the active transparent semantic product already computes ' +
            'fibres but lacked these two stable base-arrow projections'
    }),
    sameLiteralBaseArrowRequired: true,
    proofRulesInstalled: false,
    doesNotProvide: Object.freeze([
        'Product_catd-primitive-or-alias',
        'broad-arbitrary-product-off-diagonal-action',
        'full-base-two-cell-action',
        'global-Functord-product-conversion',
        'pullback-reindexing-stability',
        'displayed-projection-pairing-swap-or-diagonal',
        'generic-total-category-pullback',
        'browser-api',
        'lambdapi-string-parser',
        'bulk-library-transfer'
    ])
});

export interface CoreCategoricalFibredProductCompilation {
    readonly prerequisite: CoreCategoricalComprehensionCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
    readonly declarationContext: CoreLfMixedDeclarationContext;
}

export function compileCoreCategoricalFibredProductTransfer():
CoreCategoricalFibredProductCompilation {
    validateCoreLfScaleEngineReview();
    const prerequisite =
        compileCoreCategoricalComprehensionTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_MODULE,
        CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_POLICY,
        CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE,
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
        CORE_CATEGORICAL_FIBRED_PRODUCT_RUNTIME_MODULE,
        CORE_CATEGORICAL_FIBRED_PRODUCT_RUNTIME_POLICY,
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
        CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_MODULE,
        CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_POLICY,
        CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE,
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

export type CoreCategoricalFibredProductSymbolId =
    | 'postcomposition-action'
    | 'internal-product-functor'
    | 'partial-product-functor'
    | 'product-left-action'
    | 'fixed-right-product-map';

const symbolById:
Readonly<Record<
    CoreCategoricalFibredProductSymbolId,
    CoreLfQualifiedSymbol
>> = Object.freeze({
    'postcomposition-action': postcompositionAction,
    'internal-product-functor': internalProductFunctor,
    'partial-product-functor': partialProductFunctor,
    'product-left-action': productLeftAction,
    'fixed-right-product-map': fixedRightProductMap
});

export function coreCategoricalFibredProductCoreName(
    id: CoreCategoricalFibredProductSymbolId
): string {
    const symbol = symbolById[id];
    const link =
        CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE.entries.find(
            candidate =>
                candidate.symbol.moduleId === symbol.moduleId &&
                candidate.symbol.name === symbol.name
        );
    if (link === undefined || link.kind !== 'free-declaration') {
        throw new Error(
            `Categorical fibred-product declaration '${id}' has no ` +
            'free Core declaration'
        );
    }
    return link.coreName;
}
