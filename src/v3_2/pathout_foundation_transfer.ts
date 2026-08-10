/**
 * PATHOUT-LIBRARY-FOUNDATION-1B root-only existing-authority transfer.
 *
 * The trusted delta is deliberately small: five opaque declarations, thirteen
 * runtime rules, and two proof-time unification rules.  Nine ordinary
 * PathOut library names are then checked as transparent definitions.  This
 * file is intentionally absent from the public and browser barrels while the
 * profile is being qualified.
 */

import {
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS,
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE
} from './categorical_dependent_composition_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_SYMBOLS,
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE
} from './categorical_displayed_chain_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE
} from './categorical_displayed_nd_higher_foundation_transfer';
import {
    CORE_CATEGORICAL_FIBRED_STRUCTURE_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE
} from './categorical_fibred_structure_transfer';
import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE
} from './categorical_fibred_product_transfer';
import {
    CORE_CATEGORICAL_MIXED_ACTION_SYMBOLS,
    CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_LINKAGE
} from './categorical_mixed_action_transfer';
import {
    CoreCategoricalDirectMixedSourceActionCompilation,
    compileCoreCategoricalDirectMixedSourceActionTransfer
} from './categorical_direct_mixed_source_action_transfer';
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
    CoreLfTransferProofRule,
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
    CoreLfCompiledProofProgram,
    compileCoreLfProofProgram
} from './lf_transfer_proof';
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
    validateCorePathoutFoundation1b0Review
} from './pathout_foundation_review';

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_PATHOUT_FOUNDATION_1B_REVISION =
    'PATHOUT-LIBRARY-FOUNDATION-1B-TRANSFER-1' as const;

export const CORE_PATHOUT_FOUNDATION_SOURCE_SHA256 =
    'sha256:0a117742d326bad82fe72cc73c624a0c174e3b48dd4047ebd8f6ed6ff7837860';

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner =
    coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const homClassifier =
    coreDirectedContinuationTransferSymbol('hom-classifier');
const functorClassifier =
    coreDirectedContinuationTransferSymbol('functor-classifier');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-category-category'
    );
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const functorHomFull =
    coreDirectedContinuationTransferSymbol('functor-hom-full');
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const transforComponentCapped =
    coreDirectedContinuationTransferSymbol('transfor-component-capped');
const homCategory =
    coreDirectedContinuationTransferSymbol('hom-category');
const sigmaCategory =
    coreDirectedContinuationTransferSymbol('sigma-category');
const dependentPair =
    coreDirectedContinuationTransferSymbol('dependent-pair');
const sigmaTransportArrow =
    coreDirectedContinuationTransferSymbol('sigma-transport-arrow');

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const displayedFamilyClassifier = symbol('Catd');
const displayedFunctorClassifier = symbol('Functord');
const oppositeCategory = symbol('Op_cat');

const {
    identityArrow,
    internalHom
} = CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS;
const {
    representedHomFamily
} = CORE_CATEGORICAL_MIXED_ACTION_SYMBOLS;
const {
    precompositionAction
} = CORE_CATEGORICAL_FIBRED_STRUCTURE_SYMBOLS;
const {
    genericComposition
} = CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS;
const {
    identityFunctor,
    functorComposition
} = CORE_CATEGORICAL_STRUCTURAL_SYMBOLS;
const {
    sigmaMapFunctor
} = CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_SYMBOLS;
const {
    postcompositionAction
} = CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS;

export const CORE_PATHOUT_FOUNDATION_1B_SYMBOLS = Object.freeze({
    representedSourceTelescope:
        symbol('hom_int_precomp_tele_func'),
    representedSourceAction:
        symbol('hom_int_precomp_func'),
    sigmaTotalizationFunctor: symbol('Sigma_func'),
    homPostcompositionFunctor: symbol('hom_postcomp_func'),
    homPrecompositionFunctor: symbol('hom_precomp_along_func'),
    representableFamilyFunctor: symbol('Rep_catd_func'),
    representableFamily: symbol('Rep_catd'),
    representableTransport: symbol('Rep_transport_func'),
    pathoutCategory: symbol('PathOut_cat'),
    pathoutCategoryFunctor: symbol('PathOut_cat_func'),
    pathoutTransport: symbol('PathOut_transport_func'),
    pathoutObject: symbol('pathout_obj'),
    pathoutReflexiveObject: symbol('pathout_refl_obj'),
    pathoutReflexiveArrow: symbol('pathout_refl_arrow')
});

const {
    representedSourceTelescope,
    representedSourceAction,
    sigmaTotalizationFunctor,
    homPostcompositionFunctor,
    homPrecompositionFunctor,
    representableFamilyFunctor,
    representableFamily,
    representableTransport,
    pathoutCategory,
    pathoutCategoryFunctor,
    pathoutTransport,
    pathoutObject,
    pathoutReflexiveObject,
    pathoutReflexiveArrow
} = CORE_PATHOUT_FOUNDATION_1B_SYMBOLS;

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
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, displayedFunctorClassifier, [
        { plicity: 'implicit', value: base },
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

const identityFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, identityFunctor, [{
        plicity: 'implicit',
        value: base
    }]);

const identityAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, identityArrow, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: object }
    ]);

const internalHomAt = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, internalHom, [
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: source },
        { plicity: 'explicit', value: functor }
    ]);

const representedHomAt = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    representedSource: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, representedHomFamily, [
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: source },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: representedSource }
    ]);

const homPostcompositionFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    fixedSource: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, homPostcompositionFunctor, [
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: source },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: fixedSource },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: arrow }
    ]);

const homPrecompositionFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    fixedTarget: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, homPrecompositionFunctor, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: fixedTarget },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: arrow }
    ]);

const postcompositionActionAt = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    fixedSource: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression,
    incoming: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, postcompositionAction, [
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: source },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: fixedSource },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: arrow },
        { plicity: 'explicit', value: incoming }
    ]);

const representedSourceTelescopeAt = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    representedTarget: CoreLfTransferBuilderExpression,
    representedSource: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, representedSourceTelescope, [
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: source },
        { plicity: 'explicit', value: functor },
        { plicity: 'implicit', value: representedTarget },
        { plicity: 'implicit', value: representedSource }
    ]);

const representedSourceActionAt = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    representedTarget: CoreLfTransferBuilderExpression,
    representedSource: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, representedSourceAction, [
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: source },
        { plicity: 'explicit', value: functor },
        { plicity: 'implicit', value: representedTarget },
        { plicity: 'implicit', value: representedSource },
        { plicity: 'explicit', value: arrow }
    ]);

const precompositionActionAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    fixedTarget: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    precomposingArrow: CoreLfTransferBuilderExpression,
    incomingArrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, precompositionAction, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: fixedTarget },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: precomposingArrow },
        { plicity: 'explicit', value: incomingArrow }
    ]);

const compositionAt = (
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

const functorCompositionAt = (
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

const sigmaTotalAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const sigmaFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaTotalizationFunctor, [{
        plicity: 'explicit',
        value: base
    }]);

const sigmaMapAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    displayedFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaMapFunctor, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: displayedFunctor }
    ]);

const representableFamilyFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, representableFamilyFunctor, [{
        plicity: 'implicit',
        value: base
    }]);

const representableFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, representableFamily, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]);

const pathoutCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pathoutCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]);

const pathoutCategoryFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pathoutCategoryFunctor, [{
        plicity: 'implicit',
        value: base
    }]);

const pathoutObjectAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pathoutObject, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target },
        { plicity: 'explicit', value: arrow }
    ]);

const pathoutReflexiveObjectAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pathoutReflexiveObject, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]);

const sigmaPairAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    first: CoreLfTransferBuilderExpression,
    second: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression => {
    const familyClassifier = builder.lam(
        'pairPoint',
        objectType(builder, base),
        point => globalCall(builder, objectClassifier, [{
            plicity: 'explicit',
            value: functorObjectAt(
                builder,
                base,
                builder.global(categoryOfCategories),
                family,
                point
            )
        }]),
        explicitMode
    );
    return globalCall(builder, dependentPair, [
        {
            plicity: 'implicit',
            value: globalCall(builder, objectClassifier, [{
                plicity: 'explicit',
                value: base
            }])
        },
        { plicity: 'implicit', value: familyClassifier },
        { plicity: 'explicit', value: first },
        { plicity: 'explicit', value: second }
    ]);
};

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const modifiers = (
    rigidity: 'ordinary' | 'injective',
    sourceOpacity: 'transparent' | 'opaque'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity
});

const representedSourceTelescopeType =
(): CoreLfTransferExpression => {
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
                    'Y',
                    objectType(builder, A),
                    Y => builder.pi(
                        'X',
                        objectType(builder, A),
                        X => functorType(
                            builder,
                            homCategoryAt(
                                builder,
                                oppositeAt(builder, A),
                                Y,
                                X
                            ),
                            homCategoryAt(
                                builder,
                                displayedCategoryAt(builder, B),
                                representedHomAt(builder, A, B, F, Y),
                                representedHomAt(builder, A, B, F, X)
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
    ));
};

const representedSourceActionType = (): CoreLfTransferExpression => {
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
                    'Y',
                    objectType(builder, A),
                    Y => builder.pi(
                        'X',
                        objectType(builder, A),
                        X => builder.pi(
                            'p',
                            homType(
                                builder,
                                oppositeAt(builder, A),
                                Y,
                                X
                            ),
                            _p => homType(
                                builder,
                                displayedCategoryAt(builder, B),
                                representedHomAt(builder, A, B, F, Y),
                                representedHomAt(builder, A, B, F, X)
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
    ));
};

const homPostcompositionFunctorType = (): CoreLfTransferExpression => {
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
                                _f => functorType(
                                    builder,
                                    homCategoryAt(
                                        builder,
                                        A,
                                        W,
                                        functorObjectAt(
                                            builder,
                                            B,
                                            A,
                                            F,
                                            X
                                        )
                                    ),
                                    homCategoryAt(
                                        builder,
                                        A,
                                        W,
                                        functorObjectAt(
                                            builder,
                                            B,
                                            A,
                                            F,
                                            Y
                                        )
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
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const homPrecompositionFunctorType = (): CoreLfTransferExpression => {
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
                                _h => functorType(
                                    builder,
                                    homCategoryAt(
                                        builder,
                                        B,
                                        functorObjectAt(
                                            builder,
                                            A,
                                            B,
                                            F,
                                            X
                                        ),
                                        Z
                                    ),
                                    homCategoryAt(
                                        builder,
                                        B,
                                        functorObjectAt(
                                            builder,
                                            A,
                                            B,
                                            F,
                                            W
                                        ),
                                        Z
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
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const sigmaFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => functorType(
            builder,
            displayedCategoryAt(builder, K),
            builder.global(categoryOfCategories)
        ),
        explicitMode
    ));
};

const prerequisiteDeclarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: representedSourceTelescope,
        type: representedSourceTelescopeType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol hom_int_precomp_tele_func [A B : Cat]'
        )
    }),
    Object.freeze({
        order: 1,
        symbol: representedSourceAction,
        type: representedSourceActionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol hom_int_precomp_func [A B : Cat]'
        )
    }),
    Object.freeze({
        order: 2,
        symbol: sigmaTotalizationFunctor,
        type: sigmaFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source('injective symbol Sigma_func (K : Cat)')
    }),
    Object.freeze({
        order: 3,
        symbol: homPostcompositionFunctor,
        type: homPostcompositionFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source('symbol hom_postcomp_func [A B : Cat]')
    }),
    Object.freeze({
        order: 4,
        symbol: homPrecompositionFunctor,
        type: homPrecompositionFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source('symbol hom_precomp_along_func [A B : Cat]')
    })
]);

const prerequisiteExternalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    homClassifier,
    functorClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    homCategory,
    displayedFamilyClassifier,
    displayedFunctorClassifier,
    oppositeCategory,
    functorObject,
    representedHomFamily
]);

export const CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: `${CORE_PATHOUT_FOUNDATION_1B_REVISION}-PREREQUISITE`,
    moduleId: MODULE_ID,
    fragmentId: 'pathout-library-foundation-1b-prerequisite',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_PATHOUT_FOUNDATION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: prerequisiteExternalSymbols.map(target => ({
        symbol: target,
        availability: 'earlier-fragment' as const
    })),
    declarations: prerequisiteDeclarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_MODULE,
    {
        revision: `${CORE_PATHOUT_FOUNDATION_1B_REVISION}-` +
            'PREREQUISITE-POLICY-1',
        moduleRevision:
            CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_MODULE.revision,
        entries: prerequisiteDeclarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact active v3.2 prerequisite selected by reviewed ' +
                'PATHOUT-LIBRARY-FOUNDATION-1B0 proposal v9'
        }))
    }
);

const providerLinks = [
    ...CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE
        .entries,
    ...CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries,
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries
];

const symbolEquals = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId && left.name === right.name;

const dependencyLink = (
    target: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const inherited = providerLinks.find(candidate =>
        symbolEquals(candidate.symbol, target)
    );
    if (inherited === undefined) {
        throw new Error(
            `PATHOUT-LIBRARY-FOUNDATION-1B has no dependency link for ` +
                `${target.moduleId}.${target.name}`
        );
    }
    return Object.freeze({
        ...inherited,
        order,
        symbol: Object.freeze({ ...target })
    });
};

const prerequisiteCoreName = (target: CoreLfQualifiedSymbol): string => {
    const entry = [
        {
            symbol: representedSourceTelescope,
            coreName:
                'emdash_v3_2_pathout_foundation_' +
                'hom_int_precomp_tele_func'
        },
        {
            symbol: representedSourceAction,
            coreName:
                'emdash_v3_2_pathout_foundation_' +
                'hom_int_precomp_func'
        },
        {
            symbol: sigmaTotalizationFunctor,
            coreName: 'emdash_v3_2_pathout_foundation_Sigma_func'
        },
        {
            symbol: homPostcompositionFunctor,
            coreName:
                'emdash_v3_2_pathout_foundation_hom_postcomp_func'
        },
        {
            symbol: homPrecompositionFunctor,
            coreName:
                'emdash_v3_2_pathout_foundation_' +
                'hom_precomp_along_func'
        }
    ].find(candidate => symbolEquals(candidate.symbol, target));
    if (entry === undefined) {
        throw new Error(`Unknown PathOut prerequisite ${target.name}`);
    }
    return entry.coreName;
};

export const CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_MODULE,
        {
            revision: `${CORE_PATHOUT_FOUNDATION_1B_REVISION}-` +
                'PREREQUISITE-LINKAGE-1',
            moduleRevision:
                CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_MODULE.revision,
            entries: [
                ...prerequisiteExternalSymbols.map(dependencyLink),
                ...prerequisiteDeclarations.map((declaration, index) => ({
                    order: prerequisiteExternalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName: prerequisiteCoreName(declaration.symbol),
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

const representedHomCappedActionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const W = builder.capture('W');
    const X = builder.capture('X');
    const Y = builder.capture('Y');
    const f = builder.capture('f');
    return {
        order: 0,
        id: 'pathout.foundation.represented-hom-capped-action',
        groupId: 'pathout.foundation.represented-covariant-action',
        clauseOrder: 0,
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
                type: builder.template(functorType(builder, B, A))
            },
            {
                name: 'W',
                type: builder.template(objectType(builder, A))
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
                name: 'f',
                type: builder.template(homType(builder, B, X, Y))
            }
        ],
        left: builder.pattern(functorHomCappedAt(
            builder,
            B,
            builder.global(categoryOfCategories),
            representedHomAt(builder, A, B, F, W),
            X,
            Y,
            f
        )),
        right: builder.template(homPostcompositionFunctorAt(
            builder,
            A,
            B,
            F,
            W,
            X,
            Y,
            f
        )),
        provenance: source(
            'rule @fapp1_fapp0 $B Cat_cat ' +
                '(@hom_ $A $B $F $W) $X $Y $f'
        )
    };
};

const postcompositionObjectActionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const W = builder.capture('W');
    const X = builder.capture('X');
    const Y = builder.capture('Y');
    const f = builder.capture('f');
    const g = builder.capture('g');
    const FX = functorObjectAt(builder, B, A, F, X);
    const FY = functorObjectAt(builder, B, A, F, Y);
    return {
        order: 1,
        id: 'pathout.foundation.postcomposition-object-action',
        groupId: 'pathout.foundation.represented-covariant-action',
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
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, B, A))
            },
            {
                name: 'W',
                type: builder.template(objectType(builder, A))
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
                name: 'f',
                type: builder.template(homType(builder, B, X, Y))
            },
            {
                name: 'g',
                type: builder.template(homType(builder, A, W, FX))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            homCategoryAt(builder, A, W, FX),
            homCategoryAt(builder, A, W, FY),
            homPostcompositionFunctorAt(
                builder,
                A,
                B,
                F,
                W,
                X,
                Y,
                f
            ),
            g
        )),
        right: builder.template(postcompositionActionAt(
            builder,
            A,
            B,
            F,
            W,
            X,
            Y,
            f,
            g
        )),
        provenance: source(
            'rule fapp0 (@hom_postcomp_func $A $B $F $W ' +
                '$X $Y $f) $g'
        )
    };
};

/**
 * TypeScript executes this catalog at weak head and does not normalize the
 * nested functor argument before matching the surrounding object action.
 * This subject-checked rule is only the compiled fusion of active source
 * lines 7298 and 7302; it adds no mathematical computation principle.
 */
const representedHomObjectActionFusionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const W = builder.capture('W');
    const X = builder.capture('X');
    const Y = builder.capture('Y');
    const f = builder.capture('f');
    const g = builder.capture('g');
    const FX = functorObjectAt(builder, B, A, F, X);
    const FY = functorObjectAt(builder, B, A, F, Y);
    return {
        order: 2,
        id: 'pathout.foundation.represented-hom-object-action-fusion',
        groupId: 'pathout.foundation.represented-covariant-action',
        clauseOrder: 2,
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
                type: builder.template(functorType(builder, B, A))
            },
            {
                name: 'W',
                type: builder.template(objectType(builder, A))
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
                name: 'f',
                type: builder.template(homType(builder, B, X, Y))
            },
            {
                name: 'g',
                type: builder.template(homType(builder, A, W, FX))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            builder.wildcard(homCategoryAt(builder, A, W, FX)),
            builder.wildcard(homCategoryAt(builder, A, W, FY)),
            functorHomCappedAt(
                builder,
                B,
                builder.global(categoryOfCategories),
                representedHomAt(builder, A, B, F, W),
                X,
                Y,
                f
            ),
            g
        )),
        right: builder.template(postcompositionActionAt(
            builder,
            A,
            B,
            F,
            W,
            X,
            Y,
            f,
            g
        )),
        provenance: source(
            'derived TypeScript weak-head fusion of active lines 7298 ' +
                'and 7302: fapp0(fapp1_fapp0(hom_(F,W),f),g)'
        )
    };
};

const postcompositionIdentitySourceUnitRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const X = builder.capture('X');
    const Y = builder.capture('Y');
    const f = builder.capture('f');
    return {
        order: 3,
        id: 'pathout.foundation.postcomposition-identity-source-unit',
        groupId: 'pathout.foundation.represented-covariant-action',
        clauseOrder: 3,
        sourceOwner: postcompositionAction,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'X',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'Y',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'f',
                type: builder.template(homType(builder, A, X, Y))
            }
        ],
        left: builder.pattern(postcompositionActionAt(
            builder,
            A,
            A,
            identityAt(
                builder,
                builder.global(categoryOfCategories),
                A
            ),
            X,
            X,
            Y,
            f,
            identityAt(builder, A, X)
        )),
        right: builder.template(f),
        provenance: source(
            'with @hom_postcomp_fapp0 $A $A (@id Cat_cat $A) ' +
                '$X $X $Y $f (@id $A $X)'
        )
    };
};

const precompositionObjectActionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const Z = builder.capture('Z');
    const W = builder.capture('W');
    const X = builder.capture('X');
    const h = builder.capture('h');
    const g = builder.capture('g');
    const FW = functorObjectAt(builder, A, B, F, W);
    const FX = functorObjectAt(builder, A, B, F, X);
    return {
        order: 4,
        id: 'pathout.foundation.precomposition-object-action',
        groupId: 'pathout.foundation.represented-source-component-action',
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
                name: 'Z',
                type: builder.template(objectType(builder, B))
            },
            {
                name: 'W',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'X',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'h',
                type: builder.template(homType(builder, A, W, X))
            },
            {
                name: 'g',
                type: builder.template(homType(builder, B, FX, Z))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            builder.wildcard(homCategoryAt(builder, B, FX, Z)),
            builder.wildcard(homCategoryAt(builder, B, FW, Z)),
            homPrecompositionFunctorAt(
                builder,
                A,
                B,
                F,
                Z,
                W,
                X,
                h
            ),
            g
        )),
        right: builder.template(precompositionActionAt(
            builder,
            A,
            B,
            F,
            Z,
            W,
            X,
            h,
            g
        )),
        provenance: source(
            'rule fapp0 (@hom_precomp_along_func $A $B $F $Z ' +
                '$W $X $h) $g'
        )
    };
};

const precompositionIdentityIncomingRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const W = builder.capture('W');
    const X = builder.capture('X');
    const h = builder.capture('h');
    const FX = functorObjectAt(builder, A, B, F, X);
    return {
        order: 5,
        id: 'pathout.foundation.precomposition-identity-incoming',
        groupId: 'pathout.foundation.represented-source-component-action',
        clauseOrder: 1,
        sourceOwner: precompositionAction,
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
                name: 'W',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'X',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'h',
                type: builder.template(homType(builder, A, W, X))
            }
        ],
        left: builder.pattern(precompositionActionAt(
            builder,
            A,
            B,
            F,
            builder.wildcard(FX),
            W,
            X,
            h,
            identityAt(builder, B, builder.wildcard(FX))
        )),
        right: builder.template(functorHomCappedAt(
            builder,
            A,
            B,
            F,
            W,
            X,
            h
        )),
        provenance: source(
            'rule @hom_precomp_along_fapp0 $A $B $F _ $W $X ' +
                '$h (@id $B _) ↪ @fapp1_fapp0 $A $B $F $W $X $h'
        )
    };
};

const representedSourceComponentRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const Y = builder.capture('Y');
    const X = builder.capture('X');
    const f = builder.capture('f');
    const b = builder.capture('b');
    const representedY = representedHomAt(builder, A, B, F, Y);
    const representedX = representedHomAt(builder, A, B, F, X);
    return {
        order: 6,
        id: 'pathout.foundation.hom-int-precomp-component',
        groupId: 'pathout.foundation.represented-source-component-action',
        clauseOrder: 2,
        sourceOwner: transforComponentCapped,
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
                type: builder.template(functorType(builder, B, A))
            },
            {
                name: 'Y',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'X',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'f',
                type: builder.template(homType(
                    builder,
                    oppositeAt(builder, A),
                    Y,
                    X
                ))
            },
            {
                name: 'b',
                type: builder.template(objectType(builder, B))
            }
        ],
        left: builder.pattern(transforComponentAt(
            builder,
            B,
            builder.global(categoryOfCategories),
            builder.wildcard(representedY),
            builder.wildcard(representedX),
            b,
            representedSourceActionAt(builder, A, B, F, Y, X, f)
        )),
        right: builder.template(homPrecompositionFunctorAt(
            builder,
            A,
            A,
            identityFunctorAt(builder, A),
            functorObjectAt(builder, B, A, F, b),
            X,
            Y,
            f
        )),
        provenance: source(
            'rule @tapp0_fapp0 $B Cat_cat _ _ $b ' +
                '(@hom_int_precomp_func $A $B $F $Y $X $f)'
        )
    };
};

/** Derived only from active lines 9704 and 7977 for weak-head execution. */
const representedSourceComponentObjectFusionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const Y = builder.capture('Y');
    const X = builder.capture('X');
    const f = builder.capture('f');
    const b = builder.capture('b');
    const q = builder.capture('q');
    const representedY = representedHomAt(builder, A, B, F, Y);
    const representedX = representedHomAt(builder, A, B, F, X);
    const Fb = functorObjectAt(builder, B, A, F, b);
    return {
        order: 7,
        id:
            'pathout.foundation.' +
            'hom-int-precomp-component-object-fusion',
        groupId: 'pathout.foundation.represented-source-component-action',
        clauseOrder: 3,
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
                type: builder.template(functorType(builder, B, A))
            },
            {
                name: 'Y',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'X',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'f',
                type: builder.template(homType(
                    builder,
                    oppositeAt(builder, A),
                    Y,
                    X
                ))
            },
            {
                name: 'b',
                type: builder.template(objectType(builder, B))
            },
            {
                name: 'q',
                type: builder.template(homType(builder, A, Y, Fb))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            builder.wildcard(homCategoryAt(builder, A, Y, Fb)),
            builder.wildcard(homCategoryAt(builder, A, X, Fb)),
            transforComponentAt(
                builder,
                B,
                builder.global(categoryOfCategories),
                builder.wildcard(representedY),
                builder.wildcard(representedX),
                b,
                representedSourceActionAt(builder, A, B, F, Y, X, f)
            ),
            q
        )),
        right: builder.template(precompositionActionAt(
            builder,
            A,
            A,
            identityFunctorAt(builder, A),
            Fb,
            X,
            Y,
            f,
            q
        )),
        provenance: source(
            'derived TypeScript weak-head fusion of active lines 9704 ' +
                'and 7977: fapp0(tapp0_fapp0(' +
                'hom_int_precomp_func(f)),q)'
        )
    };
};

const representedSourceFullRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const Y = builder.capture('Y');
    const X = builder.capture('X');
    return {
        order: 8,
        id: 'pathout.foundation.hom-int-precomp-full-action',
        groupId: 'pathout.foundation.represented-source-action',
        clauseOrder: 0,
        sourceOwner: functorHomFull,
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
                type: builder.template(functorType(builder, B, A))
            },
            {
                name: 'Y',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'X',
                type: builder.template(objectType(builder, A))
            }
        ],
        left: builder.pattern(functorHomFullAt(
            builder,
            oppositeAt(builder, A),
            displayedCategoryAt(builder, B),
            internalHomAt(builder, A, B, F),
            Y,
            X
        )),
        right: builder.template(representedSourceTelescopeAt(
            builder,
            A,
            B,
            F,
            Y,
            X
        )),
        provenance: source(
            'rule @fapp1_func _ _ (@hom_int $A $B $F) $Y $X'
        )
    };
};

const representedSourceCappedRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const Y = builder.capture('Y');
    const X = builder.capture('X');
    const p = builder.capture('p');
    return {
        order: 9,
        id: 'pathout.foundation.hom-int-precomp-capped-action',
        groupId: 'pathout.foundation.represented-source-action',
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
                type: builder.template(functorType(builder, B, A))
            },
            {
                name: 'Y',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'X',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'p',
                type: builder.template(homType(
                    builder,
                    oppositeAt(builder, A),
                    Y,
                    X
                ))
            }
        ],
        left: builder.pattern(functorHomCappedAt(
            builder,
            oppositeAt(builder, A),
            displayedCategoryAt(builder, B),
            internalHomAt(builder, A, B, F),
            Y,
            X,
            p
        )),
        right: builder.template(representedSourceActionAt(
            builder,
            A,
            B,
            F,
            Y,
            X,
            p
        )),
        provenance: source(
            'rule @fapp1_fapp0 _ _ (@hom_int $A $B $F) ' +
                '$Y $X $p'
        )
    };
};

const representedSourceTelescopeApplicationRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const Y = builder.capture('Y');
    const X = builder.capture('X');
    const p = builder.capture('p');
    const sourceHom = homCategoryAt(
        builder,
        oppositeAt(builder, A),
        Y,
        X
    );
    const targetHom = homCategoryAt(
        builder,
        displayedCategoryAt(builder, B),
        representedHomAt(builder, A, B, F, Y),
        representedHomAt(builder, A, B, F, X)
    );
    return {
        order: 10,
        id: 'pathout.foundation.hom-int-precomp-tele-application',
        groupId: 'pathout.foundation.represented-source-action',
        clauseOrder: 2,
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
                type: builder.template(functorType(builder, B, A))
            },
            {
                name: 'Y',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'X',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'p',
                type: builder.template(homType(
                    builder,
                    oppositeAt(builder, A),
                    Y,
                    X
                ))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            sourceHom,
            targetHom,
            representedSourceTelescopeAt(builder, A, B, F, Y, X),
            p
        )),
        right: builder.template(representedSourceActionAt(
            builder,
            A,
            B,
            F,
            Y,
            X,
            p
        )),
        provenance: source(
            'rule @fapp0 _ _ ' +
                '(@hom_int_precomp_tele_func $A $B $F $Y $X) $p'
        )
    };
};

const sigmaFunctorObjectRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    return {
        order: 11,
        id: 'pathout.foundation.sigma-func-object',
        groupId: 'pathout.foundation.sigma-totalization-action',
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
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            displayedCategoryAt(builder, K),
            builder.global(categoryOfCategories),
            sigmaFunctorAt(builder, K),
            E
        )),
        right: builder.template(sigmaTotalAt(builder, K, E)),
        provenance: source(
            'rule @fapp0 _ Cat_cat (@Sigma_func $K) $E'
        )
    };
};

const sigmaFunctorCappedRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const eta = builder.capture('eta');
    return {
        order: 12,
        id: 'pathout.foundation.sigma-func-capped-action',
        groupId: 'pathout.foundation.sigma-totalization-action',
        clauseOrder: 1,
        sourceOwner: functorHomCapped,
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
                name: 'eta',
                type: builder.template(
                    displayedFunctorType(builder, K, E, D)
                )
            }
        ],
        left: builder.pattern(functorHomCappedAt(
            builder,
            displayedCategoryAt(builder, K),
            builder.global(categoryOfCategories),
            sigmaFunctorAt(builder, K),
            E,
            D,
            eta
        )),
        right: builder.template(sigmaMapAt(builder, K, E, D, eta)),
        provenance: source(
            'rule @fapp1_fapp0 _ Cat_cat (@Sigma_func $K) ' +
                '$E $D $eta'
        )
    };
};

const runtimeRules: readonly CoreLfTransferRuntimeRule[] = Object.freeze([
    representedHomCappedActionRule(),
    postcompositionObjectActionRule(),
    representedHomObjectActionFusionRule(),
    postcompositionIdentitySourceUnitRule(),
    precompositionObjectActionRule(),
    precompositionIdentityIncomingRule(),
    representedSourceComponentRule(),
    representedSourceComponentObjectFusionRule(),
    representedSourceFullRule(),
    representedSourceCappedRule(),
    representedSourceTelescopeApplicationRule(),
    sigmaFunctorObjectRule(),
    sigmaFunctorCappedRule()
]);

const runtimeExternalSymbols = Object.freeze([
    ...prerequisiteExternalSymbols,
    functorHomFull,
    functorHomCapped,
    transforComponentCapped,
    internalHom,
    identityArrow,
    identityFunctor,
    postcompositionAction,
    precompositionAction,
    sigmaCategory,
    sigmaMapFunctor,
    ...prerequisiteDeclarations.map(declaration => declaration.symbol)
]);

export const CORE_PATHOUT_FOUNDATION_1B_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: `${CORE_PATHOUT_FOUNDATION_1B_REVISION}-RUNTIME`,
    moduleId: MODULE_ID,
    fragmentId: 'pathout-library-foundation-1b-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_PATHOUT_FOUNDATION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: runtimeExternalSymbols.map(target => ({
        symbol: target,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const CORE_PATHOUT_FOUNDATION_1B_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_PATHOUT_FOUNDATION_1B_RUNTIME_MODULE,
    {
        revision: `${CORE_PATHOUT_FOUNDATION_1B_REVISION}-` +
            'RUNTIME-POLICY-1',
        moduleRevision: CORE_PATHOUT_FOUNDATION_1B_RUNTIME_MODULE.revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact active v3.2 computation selected by reviewed ' +
                'PATHOUT-LIBRARY-FOUNDATION-1B0 proposal v9'
        }))
    }
);

const precompositionIdentityFamilyProofRule =
(): CoreLfTransferProofRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const Z = builder.capture('Z');
    const W = builder.capture('W');
    const X = builder.capture('X');
    const h = builder.capture('h');
    const g = builder.capture('g');
    return {
        order: 0,
        id: 'pathout.foundation.precomposition-identity-family',
        sourceOwner: precompositionAction,
        variables: [
            {
                name: 'A',
                role: 'matched' as const,
                type: builder.template(builder.global(category))
            },
            {
                name: 'Z',
                role: 'matched' as const,
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'W',
                role: 'matched' as const,
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'X',
                role: 'matched' as const,
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'h',
                role: 'matched' as const,
                type: builder.template(homType(builder, A, W, X))
            },
            {
                name: 'g',
                role: 'matched' as const,
                type: builder.template(homType(builder, A, X, Z))
            }
        ],
        problem: {
            left: builder.pattern(precompositionActionAt(
                builder,
                A,
                A,
                identityFunctorAt(builder, A),
                Z,
                W,
                X,
                h,
                g
            )),
            right: builder.pattern(compositionAt(
                builder,
                A,
                W,
                X,
                Z,
                g,
                h
            ))
        },
        // TypeScript represents active source tt ≡ tt by reflexive A ≡ A.
        generatedConstraints: [{
            left: builder.template(A),
            right: builder.template(A)
        }],
        provenance: source(
            'unif_rule @hom_precomp_along_fapp0 $A $A ' +
                '(@id Cat_cat $A) $Z $W $X $h $g ≡ ' +
                '@comp_fapp0 $A _ _ $Z $g $h ↪ [ tt ≡ tt ]'
        )
    };
};

const representedSourceProjectionOrderProofRule =
(): CoreLfTransferProofRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const A0 = builder.capture('A0');
    const B0 = builder.capture('B0');
    const H = builder.capture('H');
    const Z = builder.capture('Z');
    const Y = builder.capture('Y');
    const X = builder.capture('X');
    const p = builder.capture('p');
    const g = builder.capture('g');
    const representedAction = representedSourceActionAt(
        builder,
        A,
        B,
        F,
        Y,
        X,
        p
    );
    return {
        order: 1,
        id: 'pathout.foundation.hom-int-precomp-projection-order',
        sourceOwner: precompositionAction,
        variables: [
            {
                name: 'A',
                role: 'matched' as const,
                type: builder.template(builder.global(category))
            },
            {
                name: 'B',
                role: 'matched' as const,
                type: builder.template(builder.global(category))
            },
            {
                name: 'F',
                role: 'matched' as const,
                type: builder.template(functorType(builder, B, A))
            },
            {
                name: 'A0',
                role: 'matched' as const,
                type: builder.template(builder.global(category))
            },
            {
                name: 'B0',
                role: 'matched' as const,
                type: builder.template(builder.global(category))
            },
            {
                name: 'H',
                role: 'matched' as const,
                type: builder.template(functorType(builder, A0, B0))
            },
            {
                name: 'Z',
                role: 'matched' as const,
                type: builder.template(objectType(builder, B0))
            },
            {
                name: 'Y',
                role: 'matched' as const,
                type: builder.template(objectType(builder, A0))
            },
            {
                name: 'X',
                role: 'matched' as const,
                type: builder.template(objectType(builder, A0))
            },
            {
                name: 'p',
                role: 'matched' as const,
                type: builder.template(homType(
                    builder,
                    A0,
                    Y,
                    X
                ))
            },
            {
                name: 'g',
                role: 'matched' as const,
                type: builder.template(homType(
                    builder,
                    B0,
                    functorObjectAt(builder, A0, B0, H, X),
                    Z
                ))
            }
        ],
        problem: {
            left: builder.pattern(precompositionActionAt(
                builder,
                A0,
                B0,
                H,
                Z,
                Y,
                X,
                p,
                g
            )),
            right: builder.pattern(compositionAt(
                builder,
                B0,
                representedHomAt(builder, A, B, F, Y),
                representedHomAt(builder, A, B, F, X),
                Z,
                g,
                representedAction
            ))
        },
        generatedConstraints: [
            {
                left: builder.template(oppositeAt(builder, A)),
                right: builder.template(A0)
            },
            {
                left: builder.template(displayedCategoryAt(builder, B)),
                right: builder.template(B0)
            },
            {
                left: builder.template(internalHomAt(builder, A, B, F)),
                right: builder.template(H)
            }
        ],
        provenance: source(
            'unif_rule @hom_precomp_along_fapp0 $A0 $B0 $H ' +
                '$Z $Y $X $p $g ≡ @comp_fapp0 $B0 _ _ $Z $g ' +
                '(@hom_int_precomp_func $A $B $F $Y $X $p)'
        )
    };
};

const identityFamilyProofRule =
    precompositionIdentityFamilyProofRule();
const projectionOrderProofRule =
    representedSourceProjectionOrderProofRule();
const proofRules = Object.freeze([
    identityFamilyProofRule,
    projectionOrderProofRule
]);

export const CORE_PATHOUT_FOUNDATION_1B_PROOF_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: `${CORE_PATHOUT_FOUNDATION_1B_REVISION}-PROOF`,
    moduleId: MODULE_ID,
    fragmentId: 'pathout-library-foundation-1b-proof',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_PATHOUT_FOUNDATION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        homClassifier,
        functorClassifier,
        displayedCategoryCategory,
        functorObject,
        identityFunctor,
        oppositeCategory,
        internalHom,
        representedHomFamily,
        precompositionAction,
        genericComposition,
        representedSourceAction
    ].map(target => ({
        symbol: target,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules: [],
    proofRules
});

export const CORE_PATHOUT_FOUNDATION_1B_PROOF_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_PATHOUT_FOUNDATION_1B_PROOF_MODULE,
    {
        revision: `${CORE_PATHOUT_FOUNDATION_1B_REVISION}-` +
            'PROOF-POLICY-1',
        moduleRevision: CORE_PATHOUT_FOUNDATION_1B_PROOF_MODULE.revision,
        entries: proofRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'proof-rule' as const,
                id: rule.id
            },
            policy: 'proof-unification' as const,
            evidence:
                'Exact active v3.2 PathOut foundation comparison ' +
                'selected by reviewed proposal v9'
        }))
    }
);

const representableFamilyFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => functorType(
            builder,
            oppositeAt(builder, Z),
            displayedCategoryAt(builder, Z)
        ),
        implicitMode
    ));
};

const representableFamilyFunctorBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => internalHomAt(
            builder,
            Z,
            Z,
            identityAt(builder, builder.global(categoryOfCategories), Z)
        ),
        implicitMode
    ));
};

const representableFamilyType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            _x => displayedFamilyType(builder, Z),
            explicitMode
        ),
        implicitMode
    ));
};

const representableFamilyBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => functorObjectAt(
                builder,
                oppositeAt(builder, Z),
                displayedCategoryAt(builder, Z),
                representableFamilyFunctorAt(builder, Z),
                x
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const representableTransportType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => builder.pi(
                'y',
                objectType(builder, Z),
                y => builder.pi(
                    'p',
                    homType(builder, Z, x, y),
                    _p => displayedFunctorType(
                        builder,
                        Z,
                        representableFamilyAt(builder, Z, y),
                        representableFamilyAt(builder, Z, x)
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

const representableTransportBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => builder.lam(
                'y',
                objectType(builder, Z),
                y => builder.lam(
                    'p',
                    homType(builder, Z, x, y),
                    p => representedSourceActionAt(
                        builder,
                        Z,
                        Z,
                        identityAt(
                            builder,
                            builder.global(categoryOfCategories),
                            Z
                        ),
                        y,
                        x,
                        p
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

const pathoutCategoryType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            _x => builder.global(category),
            explicitMode
        ),
        implicitMode
    ));
};

const pathoutCategoryBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => sigmaTotalAt(
                builder,
                Z,
                representableFamilyAt(builder, Z, x)
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const pathoutCategoryFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => functorType(
            builder,
            oppositeAt(builder, Z),
            builder.global(categoryOfCategories)
        ),
        implicitMode
    ));
};

const pathoutCategoryFunctorBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => functorCompositionAt(
            builder,
            oppositeAt(builder, Z),
            displayedCategoryAt(builder, Z),
            builder.global(categoryOfCategories),
            sigmaFunctorAt(builder, Z),
            representableFamilyFunctorAt(builder, Z)
        ),
        implicitMode
    ));
};

const pathoutTransportType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => builder.pi(
                'y',
                objectType(builder, Z),
                y => builder.pi(
                    'p',
                    homType(builder, Z, x, y),
                    _p => functorType(
                        builder,
                        pathoutCategoryAt(builder, Z, y),
                        pathoutCategoryAt(builder, Z, x)
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

const pathoutTransportBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => builder.lam(
                'y',
                objectType(builder, Z),
                y => builder.lam(
                    'p',
                    homType(builder, Z, x, y),
                    p => functorHomCappedAt(
                        builder,
                        oppositeAt(builder, Z),
                        builder.global(categoryOfCategories),
                        pathoutCategoryFunctorAt(builder, Z),
                        y,
                        x,
                        p
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

const pathoutObjectType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => builder.pi(
                'y',
                objectType(builder, Z),
                y => builder.pi(
                    'p',
                    homType(builder, Z, x, y),
                    _p => objectType(
                        builder,
                        pathoutCategoryAt(builder, Z, x)
                    ),
                    explicitMode
                ),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const pathoutObjectBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => builder.lam(
                'y',
                objectType(builder, Z),
                y => builder.lam(
                    'p',
                    homType(builder, Z, x, y),
                    p => sigmaPairAt(
                        builder,
                        Z,
                        representableFamilyAt(builder, Z, x),
                        y,
                        p
                    ),
                    explicitMode
                ),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const pathoutReflexiveObjectType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => objectType(builder, pathoutCategoryAt(builder, Z, x)),
            explicitMode
        ),
        implicitMode
    ));
};

const pathoutReflexiveObjectBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => pathoutObjectAt(
                builder,
                Z,
                x,
                x,
                identityAt(builder, Z, x)
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const pathoutReflexiveArrowType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => builder.pi(
                'y',
                objectType(builder, Z),
                y => builder.pi(
                    'p',
                    homType(builder, Z, x, y),
                    p => homType(
                        builder,
                        pathoutCategoryAt(builder, Z, x),
                        pathoutReflexiveObjectAt(builder, Z, x),
                        pathoutObjectAt(builder, Z, x, y, p)
                    ),
                    explicitMode
                ),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const pathoutReflexiveArrowBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => builder.lam(
                'y',
                objectType(builder, Z),
                y => builder.lam(
                    'p',
                    homType(builder, Z, x, y),
                    p => globalCall(builder, sigmaTransportArrow, [
                        { plicity: 'implicit', value: Z },
                        {
                            plicity: 'explicit',
                            value: representableFamilyAt(builder, Z, x)
                        },
                        { plicity: 'implicit', value: x },
                        { plicity: 'implicit', value: y },
                        { plicity: 'explicit', value: p },
                        {
                            plicity: 'explicit',
                            value: identityAt(builder, Z, x)
                        }
                    ]),
                    explicitMode
                ),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const libraryDeclarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: representableFamilyFunctor,
        type: representableFamilyFunctorType(),
        body: coreLfTransferExplicitBody(
            representableFamilyFunctorBody()
        ),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol Rep_catd_func [Z : Cat]')
    }),
    Object.freeze({
        order: 1,
        symbol: representableFamily,
        type: representableFamilyType(),
        body: coreLfTransferExplicitBody(representableFamilyBody()),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol Rep_catd [Z : Cat]')
    }),
    Object.freeze({
        order: 2,
        symbol: representableTransport,
        type: representableTransportType(),
        body: coreLfTransferExplicitBody(representableTransportBody()),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol Rep_transport_func [Z : Cat]')
    }),
    Object.freeze({
        order: 3,
        symbol: pathoutCategory,
        type: pathoutCategoryType(),
        body: coreLfTransferExplicitBody(pathoutCategoryBody()),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol PathOut_cat [Z : Cat]')
    }),
    Object.freeze({
        order: 4,
        symbol: pathoutCategoryFunctor,
        type: pathoutCategoryFunctorType(),
        body: coreLfTransferExplicitBody(pathoutCategoryFunctorBody()),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol PathOut_cat_func [Z : Cat]')
    }),
    Object.freeze({
        order: 5,
        symbol: pathoutTransport,
        type: pathoutTransportType(),
        body: coreLfTransferExplicitBody(pathoutTransportBody()),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol PathOut_transport_func [Z : Cat]')
    }),
    Object.freeze({
        order: 6,
        symbol: pathoutObject,
        type: pathoutObjectType(),
        body: coreLfTransferExplicitBody(pathoutObjectBody()),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol pathout_obj [Z : Cat]')
    }),
    Object.freeze({
        order: 7,
        symbol: pathoutReflexiveObject,
        type: pathoutReflexiveObjectType(),
        body: coreLfTransferExplicitBody(pathoutReflexiveObjectBody()),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol pathout_refl_obj [Z : Cat]')
    }),
    Object.freeze({
        order: 8,
        symbol: pathoutReflexiveArrow,
        type: pathoutReflexiveArrowType(),
        body: coreLfTransferExplicitBody(pathoutReflexiveArrowBody()),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol pathout_refl_arrow [Z : Cat]')
    })
]);

const libraryExternalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    homClassifier,
    functorClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    functorObject,
    functorHomCapped,
    displayedFamilyClassifier,
    displayedFunctorClassifier,
    oppositeCategory,
    identityArrow,
    internalHom,
    functorComposition,
    sigmaCategory,
    dependentPair,
    sigmaTransportArrow,
    ...prerequisiteDeclarations.map(declaration => declaration.symbol)
]);

export const CORE_PATHOUT_FOUNDATION_1B_LIBRARY_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: `${CORE_PATHOUT_FOUNDATION_1B_REVISION}-LIBRARY`,
    moduleId: MODULE_ID,
    fragmentId: 'pathout-library-foundation-1b-library',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_PATHOUT_FOUNDATION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: libraryExternalSymbols.map(target => ({
        symbol: target,
        availability: 'earlier-fragment' as const
    })),
    declarations: libraryDeclarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_PATHOUT_FOUNDATION_1B_LIBRARY_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_PATHOUT_FOUNDATION_1B_LIBRARY_MODULE,
    {
        revision: `${CORE_PATHOUT_FOUNDATION_1B_REVISION}-` +
            'LIBRARY-POLICY-1',
        moduleRevision: CORE_PATHOUT_FOUNDATION_1B_LIBRARY_MODULE.revision,
        entries: libraryDeclarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'checked-transparent-definition' as const,
            evidence:
                'Exact active v3.2 transparent PathOut definition selected ' +
                'by reviewed PATHOUT-LIBRARY-FOUNDATION-1B0 proposal v9'
        }))
    }
);

const prerequisiteDeclarationLinks =
    CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_LINKAGE.entries.filter(entry =>
        prerequisiteDeclarations.some(declaration =>
            symbolEquals(declaration.symbol, entry.symbol)
        )
    );

const libraryDependencyLink = (
    target: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const localPrerequisite = prerequisiteDeclarationLinks.find(candidate =>
        symbolEquals(candidate.symbol, target)
    );
    return localPrerequisite === undefined
        ? dependencyLink(target, order)
        : Object.freeze({
            ...localPrerequisite,
            order,
            symbol: Object.freeze({ ...target })
        });
};

const libraryCoreName = (target: CoreLfQualifiedSymbol): string => {
    const names = new Map<CoreLfQualifiedSymbol, string>([
        [
            representableFamilyFunctor,
            'emdash_v3_2_pathout_foundation_Rep_catd_func'
        ],
        [
            representableFamily,
            'emdash_v3_2_pathout_foundation_Rep_catd'
        ],
        [
            representableTransport,
            'emdash_v3_2_pathout_foundation_Rep_transport_func'
        ],
        [
            pathoutCategory,
            'emdash_v3_2_pathout_foundation_PathOut_cat'
        ],
        [
            pathoutCategoryFunctor,
            'emdash_v3_2_pathout_foundation_PathOut_cat_func'
        ],
        [
            pathoutTransport,
            'emdash_v3_2_pathout_foundation_PathOut_transport_func'
        ],
        [
            pathoutObject,
            'emdash_v3_2_pathout_foundation_pathout_obj'
        ],
        [
            pathoutReflexiveObject,
            'emdash_v3_2_pathout_foundation_pathout_refl_obj'
        ],
        [
            pathoutReflexiveArrow,
            'emdash_v3_2_pathout_foundation_pathout_refl_arrow'
        ]
    ]);
    const entry = [...names].find(([candidate]) =>
        symbolEquals(candidate, target)
    );
    if (entry === undefined) {
        throw new Error(`Unknown PathOut library name ${target.name}`);
    }
    return entry[1];
};

export const CORE_PATHOUT_FOUNDATION_1B_LIBRARY_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_PATHOUT_FOUNDATION_1B_LIBRARY_MODULE,
        {
            revision: `${CORE_PATHOUT_FOUNDATION_1B_REVISION}-` +
                'LIBRARY-LINKAGE-1',
            moduleRevision:
                CORE_PATHOUT_FOUNDATION_1B_LIBRARY_MODULE.revision,
            entries: [
                ...libraryExternalSymbols.map(libraryDependencyLink),
                ...libraryDeclarations.map((declaration, index) => ({
                    order: libraryExternalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName: libraryCoreName(declaration.symbol),
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

export const CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES = Object.freeze(
    Object.fromEntries(
        Object.entries(CORE_PATHOUT_FOUNDATION_1B_SYMBOLS).map(
            ([id, target]) => [
                id,
                prerequisiteDeclarations.some(declaration =>
                    symbolEquals(declaration.symbol, target)
                )
                    ? prerequisiteCoreName(target)
                    : libraryCoreName(target)
            ]
        )
    ) as {
        readonly [
            K in keyof typeof CORE_PATHOUT_FOUNDATION_1B_SYMBOLS
        ]: string;
    }
);

export type CorePathoutFoundation1bSymbolId =
    keyof typeof CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES;

export function corePathoutFoundation1bCoreName(
    id: CorePathoutFoundation1bSymbolId
): string {
    return CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES[id];
}

export type CorePathoutOrdinaryLibraryCapability =
    | 'checked-transparent-definition'
    | 'opaque-signature'
    | 'runtime-rewrite'
    | 'proof-unification';

export class CorePathoutOrdinaryLibraryCapabilityError extends Error {
    constructor(public readonly capability:
        CorePathoutOrdinaryLibraryCapability) {
        super(
            `Ordinary PathOut library code cannot request '${capability}'`
        );
        this.name = 'CorePathoutOrdinaryLibraryCapabilityError';
    }
}

/**
 * Root-only qualification guard for the future ordinary library facade.
 * Low-level LF authoring remains available elsewhere and explicitly trusted;
 * this guard records that ordinary definitions cannot silently widen it.
 */
export function assertCorePathoutOrdinaryLibraryCapability(
    capability: CorePathoutOrdinaryLibraryCapability
): 'checked-transparent-definition' {
    if (capability !== 'checked-transparent-definition') {
        throw new CorePathoutOrdinaryLibraryCapabilityError(capability);
    }
    return capability;
}

export const CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY =
Object.freeze({
    revision: CORE_PATHOUT_FOUNDATION_1B_REVISION,
    reviewedAuthorization:
        'PATHOUT-LIBRARY-FOUNDATION-1B0-REVIEWED-8',
    selectedPredecessor:
        'DIRECT-MIXED-SOURCE-ACTION-1E2-RUNTIME-1',
    prerequisiteDeclarationNames: Object.freeze(
        prerequisiteDeclarations.map(declaration =>
            declaration.symbol.name
        )
    ),
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    proofRuleIds: Object.freeze(proofRules.map(rule => rule.id)),
    transparentLibraryDefinitionNames: Object.freeze(
        libraryDeclarations.map(declaration => declaration.symbol.name)
    ),
    prerequisiteDeclarationCount: prerequisiteDeclarations.length,
    runtimeRuleCount: runtimeRules.length,
    proofRuleCount: proofRules.length,
    transparentLibraryDefinitionCount: libraryDeclarations.length,
    generatedProofConstraintCount:
        proofRules.reduce(
            (count, rule) => count + rule.generatedConstraints.length,
            0
        ),
    positiveConsumerCount: 7,
    negativeConsumerCount: 8,
    boundedOracleAssertionCount: 6,
    allEntriesUseGenericTransferEngines: true,
    ordinarySafeLibraryCanAddTransparentDefinitions: true,
    ordinarySafeLibraryCanAddOpaqueOwners: false,
    ordinarySafeLibraryCanAddRuntimeRules: false,
    ordinarySafeLibraryCanAddProofRules: false,
    rootOnlyQualification: true,
    browserOrPublicPackageExported: false,
    fixedSourcePathInductionIncluded: false,
    internalizedPathInductionIncluded: false,
    transitivityIncluded: false,
    sigmaMapHigherActionIncluded: false,
    intrinsicCoreOwnerDelta: 0,
    checkerBranchDelta: 0,
    evaluatorBranchDelta: 0,
    activeLambdapiOwnerDelta: 0,
    activeLambdapiRuleDelta: 0
});

export interface CorePathoutFoundation1bCompilation {
    readonly prerequisite:
        CoreCategoricalDirectMixedSourceActionCompilation;
    readonly prerequisiteCompiled: CoreLfCompiledDeclarationModule;
    readonly libraryCompiled: CoreLfCompiledDeclarationModule;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
    readonly proofProgram: CoreLfCompiledProofProgram;
}

let cachedCompilation: CorePathoutFoundation1bCompilation | undefined;

export function compileCorePathoutFoundation1bTransfer():
CorePathoutFoundation1bCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    validateCorePathoutFoundation1b0Review();
    const prerequisite =
        compileCoreCategoricalDirectMixedSourceActionTransfer();
    const prerequisiteCompiled = compileCoreLfDeclarations(
        CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_MODULE,
        CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_POLICY,
        CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: prerequisite.composedRuntime,
            comparisonStepLimit: 512
        }
    );
    const prerequisiteContext = new CoreLfMixedDeclarationContext(
        prerequisite.declarationContext,
        [prerequisiteCompiled]
    );
    const runtimeFragment = compileCoreLfRuntimeFragment(
        CORE_PATHOUT_FOUNDATION_1B_RUNTIME_MODULE,
        CORE_PATHOUT_FOUNDATION_1B_RUNTIME_POLICY,
        prerequisiteContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: prerequisite.runtimeFragment
            }],
            comparisonStepLimit: 512
        }
    );
    compileCoreLfProofProgram(
        CORE_PATHOUT_FOUNDATION_1B_PROOF_MODULE,
        CORE_PATHOUT_FOUNDATION_1B_PROOF_POLICY,
        prerequisiteContext,
        {
            runtimeProgram: runtimeFragment.runtime,
            comparisonStepLimit: 512,
            typingOracle: {
                authorityPath: 'emdash2/emdash3_2.lp',
                evidence:
                    'Active unif_rule checked by the bounded PathOut ' +
                    'foundation Lambdapi oracle',
                ruleIds: [projectionOrderProofRule.id]
            }
        }
    );
    const libraryCompiled = compileCoreLfDeclarations(
        CORE_PATHOUT_FOUNDATION_1B_LIBRARY_MODULE,
        CORE_PATHOUT_FOUNDATION_1B_LIBRARY_POLICY,
        CORE_PATHOUT_FOUNDATION_1B_LIBRARY_LINKAGE,
        {
            initialEnvironment: prerequisiteCompiled.environment,
            runtimeProgram: runtimeFragment.runtime,
            comparisonStepLimit: 512
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        prerequisite.declarationContext,
        [prerequisiteCompiled, libraryCompiled]
    );
    const proofProgram = compileCoreLfProofProgram(
        CORE_PATHOUT_FOUNDATION_1B_PROOF_MODULE,
        CORE_PATHOUT_FOUNDATION_1B_PROOF_POLICY,
        declarationContext,
        {
            runtimeProgram: runtimeFragment.runtime,
            comparisonStepLimit: 512,
            typingOracle: {
                authorityPath: 'emdash2/emdash3_2.lp',
                evidence:
                    'Active unif_rule checked by the bounded PathOut ' +
                    'foundation Lambdapi oracle',
                ruleIds: [projectionOrderProofRule.id]
            }
        }
    );
    cachedCompilation = Object.freeze({
        prerequisite,
        prerequisiteCompiled,
        libraryCompiled,
        compiled: libraryCompiled,
        declarationContext,
        runtimeFragment,
        runtime: runtimeFragment.localProgram,
        composedRuntime: runtimeFragment.runtime,
        proofProgram
    });
    return cachedCompilation;
}
