/**
 * DISPLAYED-CHAIN-1A generic declaration/runtime transfer.
 *
 * The prerequisite fragment transfers the D-012 through D-015 computation
 * closure: three chain-specific signatures, two ambient signatures, one
 * checked transparent `Obj_func` mirror, five exact existing equations, and
 * one typed `piapp0` normal-form specialization. The semantic delta remains
 * exactly `sigma_functord_sec` and the six runtime rules approved by D-012.
 * Every entry goes through the owner-agnostic LF declaration and runtime
 * compilers; no intrinsic Core case is added.
 */

import {
    CORE_CATEGORICAL_COMPREHENSION_TRANSFER_LINKAGE
} from './categorical_comprehension_transfer';
import {
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE
} from './categorical_dependent_composition_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_LINKAGE,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_LINKAGE,
    CoreCategoricalDisplayedEvaluationCompilation,
    compileCoreCategoricalDisplayedEvaluationTransfer
} from './categorical_displayed_evaluation_transfer';
import {
    validateCoreCategoricalDisplayedChainReview
} from './categorical_displayed_chain_review';
import {
    validateCoreCategoricalDisplayedChainTransferCorrectionReview
} from './categorical_displayed_chain_transfer_correction_review';
import {
    validateCoreCategoricalDisplayedChainConstantFunctorCorrectionReview
} from './categorical_displayed_chain_constant_functor_correction_review';
import {
    validateCoreCategoricalDisplayedChainComputationClosureCorrectionReview
} from './categorical_displayed_chain_computation_closure_correction_review';
import {
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_LINKAGE
} from './categorical_fibred_dependent_target_transfer';
import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE
} from './categorical_fibred_product_transfer';
import {
    CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE
} from './categorical_fibred_structure_transfer';
import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE
} from './categorical_fibred_transfd_transfer';
import {
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_LINKAGE
} from './categorical_fibred_weaken_reindex_transfer';
import {
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
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_REVISION =
    'DISPLAYED-CHAIN-1A-GENERIC-TRANSFER-1' as const;

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_SOURCE_SHA256 =
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
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const transforComponentCapped =
    coreDirectedContinuationTransferSymbol(
        'transfor-component-capped'
    );
const transforCategory =
    coreDirectedContinuationTransferSymbol('transfor-category');
const sigmaCategory =
    coreDirectedContinuationTransferSymbol('sigma-category');
const dependentPair =
    coreDirectedContinuationTransferSymbol('dependent-pair');
const constantDisplayedFamily =
    coreDirectedContinuationTransferSymbol(
        'constant-displayed-family'
    );
const sectionCategory =
    coreDirectedContinuationTransferSymbol('section-category');

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const terminalCategory = symbol('Terminal_cat');
const terminalObject = symbol('Terminal_obj');
const constantFunctor = symbol('Const_func');
const pointFunctor = symbol('Obj_func__displayed_chain_mirror');
const fibreCategory = symbol('Fibre_cat');
const displayedIdentity = symbol('id_funcd');
const displayedFibreFunctor = symbol('Fibre_func');
const identityFunctor = symbol('id_func');
const displayedTransportLeft =
    symbol('functord_transport_lhs_func');
const displayedTransportRight =
    symbol('functord_transport_rhs_func');
const sigmaArrow = symbol('sigma_arrow');
const sigmaFirstProjection = symbol('Sigma_proj1_func');
const sigmaProjectionPullback =
    symbol('Sigma_proj1_pullback_catd');
const sectionPullbackFunctor = symbol('section_pullback_func');
const sectionPullbackSection = symbol('section_pullback_sec');
const sectionObject = symbol('piapp0');
const {
    identityArrow,
    higherCell: displayedTransformationInternalCell
} = CORE_CATEGORICAL_FIBRED_TRANSFD_SYMBOLS;

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_SYMBOLS =
Object.freeze({
    sigmaMapFunctor: symbol('sigma_map_func'),
    displayedInternalCell: symbol('fdapp1_int_cell'),
    displayedInternalHomAction:
        symbol('fdapp1_int_hom_fapp0')
});

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_SYMBOLS =
Object.freeze({
    sigmaFunctordSection: symbol('sigma_functord_sec')
});

const {
    sigmaMapFunctor,
    displayedInternalCell,
    displayedInternalHomAction
} = CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_SYMBOLS;

const {
    sigmaFunctordSection
} = CORE_CATEGORICAL_DISPLAYED_CHAIN_SYMBOLS;

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

const functorClassifierAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorClassifier, [
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]);

const functorType = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, functorClassifierAt(builder, source, target));

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

const identityAt = (
    builder: CoreLfTransferScopedBuilder,
    category_: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, identityArrow, [
        { plicity: 'explicit', value: category_ },
        { plicity: 'explicit', value: object }
    ]);

const constantFamily = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    value: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, constantDisplayedFamily, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value }
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

const sigmaTotal = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const fibre = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorObject, [
        { plicity: 'implicit', value: base },
        {
            plicity: 'implicit',
            value: builder.global(categoryOfCategories)
        },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: point }
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

const functorArrowAt = (
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

const componentAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression,
    displayedFunctor_: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, transforComponentCapped, [
        { plicity: 'implicit', value: base },
        {
            plicity: 'implicit',
            value: builder.global(categoryOfCategories)
        },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: point },
        { plicity: 'explicit', value: displayedFunctor_ }
    ]);

const sigmaPair = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    first: CoreLfTransferBuilderExpression,
    second: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression => {
    const familyClassifier = builder.lam(
        'pairPoint',
        objectType(builder, base),
        pairPoint => objectClassifierAt(
            builder,
            fibre(builder, base, family, pairPoint)
        ),
        explicitMode
    );
    return globalCall(builder, dependentPair, [
        {
            plicity: 'implicit',
            value: objectClassifierAt(builder, base)
        },
        { plicity: 'implicit', value: familyClassifier },
        { plicity: 'explicit', value: first },
        { plicity: 'explicit', value: second }
    ]);
};

/**
 * Runtime-pattern view of Struct_sigma.
 *
 * Lambdapi source rules write the pair constructor with its decoded carrier
 * and family-classifier arguments inferred. They therefore do not constrain
 * those arguments as part of matching. The transfer must preserve that
 * behavior: composite transparent families can normalize their inferred
 * classifier differently while denoting the same explicit base/family data.
 * Typed wildcards retain subject checking without turning inferred slots into
 * accidental rigid owner positions.
 */
const sigmaPairPattern = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    first: CoreLfTransferBuilderExpression,
    second: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression => {
    const carrier = objectClassifierAt(builder, base);
    const familyClassifier = builder.lam(
        'pairPoint',
        objectType(builder, base),
        pairPoint => objectClassifierAt(
            builder,
            fibre(builder, base, family, pairPoint)
        ),
        explicitMode
    );
    return globalCall(builder, dependentPair, [
        {
            plicity: 'implicit',
            value: builder.wildcard(carrier)
        },
        {
            plicity: 'implicit',
            value: builder.wildcard(familyClassifier)
        },
        { plicity: 'explicit', value: first },
        { plicity: 'explicit', value: second }
    ]);
};

const sigmaArrowAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    targetPoint: CoreLfTransferBuilderExpression,
    sourceValue: CoreLfTransferBuilderExpression,
    targetValue: CoreLfTransferBuilderExpression,
    baseArrow: CoreLfTransferBuilderExpression,
    fibreArrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaArrow, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family },
        { plicity: 'implicit', value: sourcePoint },
        { plicity: 'implicit', value: targetPoint },
        { plicity: 'explicit', value: sourceValue },
        { plicity: 'explicit', value: targetValue },
        { plicity: 'explicit', value: baseArrow },
        { plicity: 'explicit', value: fibreArrow }
    ]);

const sigmaProjectionAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaFirstProjection, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const sigmaProjectionPullbackAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaProjectionPullback, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: sourceFamily },
        { plicity: 'explicit', value: targetFamily }
    ]);

const displayedFibreFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor_: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedFibreFunctor, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor_ },
        { plicity: 'explicit', value: point }
    ]);

const displayedTransportAt = (
    builder: CoreLfTransferScopedBuilder,
    family: CoreLfTransferBuilderExpression,
    base: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    targetPoint: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    functorArrowAt(
        builder,
        base,
        builder.global(categoryOfCategories),
        family,
        sourcePoint,
        targetPoint,
        arrow
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

const displayedInternalHomActionAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor_: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    targetPoint: CoreLfTransferBuilderExpression,
    baseArrow: CoreLfTransferBuilderExpression,
    sourceValue: CoreLfTransferBuilderExpression,
    targetValue: CoreLfTransferBuilderExpression,
    fibreArrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedInternalHomAction, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor_ },
        { plicity: 'implicit', value: sourcePoint },
        { plicity: 'implicit', value: targetPoint },
        { plicity: 'explicit', value: baseArrow },
        { plicity: 'explicit', value: sourceValue },
        { plicity: 'implicit', value: targetValue },
        { plicity: 'explicit', value: fibreArrow }
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

const displayedTransformationInternalCellAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression,
    transformation: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    targetPoint: CoreLfTransferBuilderExpression,
    baseArrow: CoreLfTransferBuilderExpression,
    sourceValue: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedTransformationInternalCell, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'implicit', value: sourceFunctor },
        { plicity: 'implicit', value: targetFunctor },
        { plicity: 'explicit', value: transformation },
        { plicity: 'implicit', value: sourcePoint },
        { plicity: 'implicit', value: targetPoint },
        { plicity: 'explicit', value: baseArrow },
        { plicity: 'explicit', value: sourceValue }
    ]);

const sigmaMapAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor_: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaMapFunctor, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor_ }
    ]);

const sigmaSectionAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor_: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaFunctordSection, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor_ }
    ]);

const sectionPullbackSectionAt = (
    builder: CoreLfTransferScopedBuilder,
    sourceBase: CoreLfTransferBuilderExpression,
    targetBase: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    section: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sectionPullbackSection, [
        { plicity: 'implicit', value: sourceBase },
        { plicity: 'implicit', value: targetBase },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: section }
    ]);

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

const constantFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, constantFunctor, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: object }
    ]);

const pointFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pointFunctor, [
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: object }
    ]);

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const modifiers = (
    rigidity: 'ordinary' | 'constant' | 'injective',
    sourceOpacity: 'transparent' | 'opaque'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity
});

const sigmaMapType = (): CoreLfTransferExpression => {
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
                    'eta',
                    displayedFunctorType(builder, K, E, D),
                    _eta => functorType(
                        builder,
                        sigmaTotal(builder, K, E),
                        sigmaTotal(builder, K, D)
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

const displayedInternalHomActionType =
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
                    FF => builder.pi(
                        'x',
                        objectType(builder, K),
                        x => builder.pi(
                            'y',
                            objectType(builder, K),
                            y => builder.pi(
                                'p',
                                homType(builder, K, x, y),
                                p => builder.pi(
                                    'u',
                                    objectType(
                                        builder,
                                        fibre(builder, K, E, x)
                                    ),
                                    u => builder.pi(
                                        'v',
                                        objectType(
                                            builder,
                                            fibre(builder, K, E, y)
                                        ),
                                        v => builder.pi(
                                            'alpha',
                                            homType(
                                                builder,
                                                fibre(builder, K, E, y),
                                                functorObjectAt(
                                                    builder,
                                                    fibre(builder, K, E, x),
                                                    fibre(builder, K, E, y),
                                                    displayedTransportAt(
                                                        builder,
                                                        E,
                                                        K,
                                                        x,
                                                        y,
                                                        p
                                                    ),
                                                    u
                                                ),
                                                v
                                            ),
                                            _alpha => homType(
                                                builder,
                                                fibre(builder, K, D, y),
                                                functorObjectAt(
                                                    builder,
                                                    fibre(builder, K, E, x),
                                                    fibre(builder, K, D, y),
                                                    displayedTransportSideAt(
                                                        builder,
                                                        displayedTransportLeft,
                                                        K,
                                                        E,
                                                        D,
                                                        FF,
                                                        x,
                                                        y,
                                                        p
                                                    ),
                                                    u
                                                ),
                                                functorObjectAt(
                                                    builder,
                                                    fibre(builder, K, E, y),
                                                    fibre(builder, K, D, y),
                                                    displayedFibreFunctorAt(
                                                        builder,
                                                        K,
                                                        E,
                                                        D,
                                                        FF,
                                                        y
                                                    ),
                                                    v
                                                )
                                            ),
                                            explicitMode
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

const displayedInternalCellType =
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
                    FF => builder.pi(
                        'x',
                        objectType(builder, K),
                        x => builder.pi(
                            'y',
                            objectType(builder, K),
                            y => builder.pi(
                                'p',
                                homType(builder, K, x, y),
                                p => builder.pi(
                                    'u',
                                    objectType(
                                        builder,
                                        fibre(builder, K, E, x)
                                    ),
                                    _u => homType(
                                        builder,
                                        fibre(builder, K, D, y),
                                        functorObjectAt(
                                            builder,
                                            fibre(builder, K, E, x),
                                            fibre(builder, K, D, y),
                                            displayedTransportSideAt(
                                                builder,
                                                displayedTransportLeft,
                                                K,
                                                E,
                                                D,
                                                FF,
                                                x,
                                                y,
                                                p
                                            ),
                                            _u
                                        ),
                                        functorObjectAt(
                                            builder,
                                            fibre(builder, K, E, x),
                                            fibre(builder, K, D, y),
                                            displayedTransportSideAt(
                                                builder,
                                                displayedTransportRight,
                                                K,
                                                E,
                                                D,
                                                FF,
                                                x,
                                                y,
                                                p
                                            ),
                                            _u
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
                implicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const terminalObjectType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(
        objectType(builder, builder.global(terminalCategory))
    );
};

const constantFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'b',
                objectType(builder, B),
                _b => functorType(builder, A, B),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const pointFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Y',
        builder.global(category),
        Y => builder.pi(
            'y',
            objectType(builder, Y),
            _y => functorType(
                builder,
                builder.global(terminalCategory),
                Y
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const pointFunctorBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Y',
        builder.global(category),
        Y => builder.lam(
            'y',
            objectType(builder, Y),
            y => constantFunctorAt(
                builder,
                builder.global(terminalCategory),
                Y,
                y
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const sigmaSectionType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'R',
            displayedFamilyType(builder, K),
            R => builder.pi(
                'D',
                displayedFamilyType(builder, K),
                D => builder.pi(
                    'FF',
                    displayedFunctorType(builder, K, R, D),
                    _FF => objectType(
                        builder,
                        sectionCategoryAt(
                            builder,
                            sigmaTotal(builder, K, R),
                            sigmaProjectionPullbackAt(
                                builder,
                                K,
                                R,
                                D
                            )
                        )
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

const ambientDeclarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: terminalObject,
        type: terminalObjectType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('constant', 'opaque'),
        provenance: source(
            'constant symbol Terminal_obj : τ (Obj Terminal_cat);'
        )
    }),
    Object.freeze({
        order: 1,
        symbol: constantFunctor,
        type: constantFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Const_func [A B : Cat] ' +
                '(b : τ (Obj B)) : τ (Functor A B);'
        )
    })
]);

const mirrorDeclarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 2,
        symbol: pointFunctor,
        type: pointFunctorType(),
        body: coreLfTransferExplicitBody(pointFunctorBody()),
        modifiers: modifiers('injective', 'transparent'),
        provenance: source(
            'checked transparent TypeScript mirror of active ' +
                'injective symbol Obj_func [Y : Cat] ' +
                '(y : τ (Obj Y)) ≔ @Const_func Terminal_cat Y y'
        )
    })
]);

const prerequisiteDeclarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 3,
        symbol: sigmaMapFunctor,
        type: sigmaMapType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol sigma_map_func [K : Cat] ' +
                '[E D : τ (Catd K)]'
        )
    }),
    Object.freeze({
        order: 4,
        symbol: displayedInternalCell,
        type: displayedInternalCellType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol fdapp1_int_cell [K : Cat] ' +
                '[E D : τ (Catd K)]'
        )
    }),
    Object.freeze({
        order: 5,
        symbol: displayedInternalHomAction,
        type: displayedInternalHomActionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol fdapp1_int_hom_fapp0 [K : Cat] ' +
                '[E D : τ (Catd K)]'
        )
    })
]);

const existingDeclarations = Object.freeze([
    ...ambientDeclarations,
    ...mirrorDeclarations,
    ...prerequisiteDeclarations
]);

const semanticDeclarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: sigmaFunctordSection,
        type: sigmaSectionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol sigma_functord_sec [K : Cat] ' +
                '[R D : τ (Catd K)]'
        )
    })
]);

const prerequisiteExternalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    functorClassifier,
    homClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    displayedFunctorCategory,
    functorObject,
    functorHomCapped,
    terminalCategory,
    constantDisplayedFamily,
    sigmaCategory,
    displayedFibreFunctor,
    displayedTransportLeft,
    displayedTransportRight
]);

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'DISPLAYED-CHAIN-1A-EXISTING-PREREQUISITES-1',
    moduleId: MODULE_ID,
    fragmentId: 'displayed-chain-1a-existing-prerequisites',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_DISPLAYED_CHAIN_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: prerequisiteExternalSymbols.map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations: existingDeclarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_MODULE,
    {
        revision:
            'DISPLAYED-CHAIN-1A-EXISTING-PREREQUISITES-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_MODULE
                .revision,
        entries: existingDeclarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy:
                declaration.symbol === pointFunctor
                    ? 'checked-transparent-definition' as const
                    : 'opaque-signature' as const,
            evidence:
                declaration.symbol === pointFunctor
                    ? 'Exact checked transparent TypeScript mirror of ' +
                        'active Obj_func; deterministic backend name remains ' +
                        'Obj_func'
                    : declaration.symbol.name === 'Terminal_obj'
                    ? 'Exact pre-existing ambient signature authorized by ' +
                        'D-DTTLF-USABILITY-013'
                    : declaration.symbol.name === 'Const_func'
                        ? 'Exact pre-existing ambient signature authorized ' +
                            'by D-DTTLF-USABILITY-014'
                    : 'Exact pre-existing active v3.2 signature required ' +
                        'by the reviewed D-DTTLF-USABILITY-012 closure'
        }))
    }
);

const earlierLinks = [
    ...CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_COMPREHENSION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries,
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries
];

const symbolEquals = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId &&
    left.name === right.name;

const dependencyLink = (
    links: readonly CoreLfTransferDeclarationLink[],
    target: CoreLfQualifiedSymbol,
    order: number,
    detail: string
): CoreLfTransferDeclarationLink => {
    const link = links.find(candidate =>
        symbolEquals(candidate.symbol, target)
    );
    if (link === undefined) {
        throw new Error(
            `${detail} has no dependency link for ` +
                `${target.moduleId}.${target.name}`
        );
    }
    return Object.freeze({
        ...link,
        order,
        symbol: Object.freeze({ ...link.symbol })
    });
};

const prerequisiteCoreName = (
    target: CoreLfQualifiedSymbol
): string =>
    `emdash_v3_2_displayed_chain_1a_prerequisite_${target.name}`;

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_MODULE,
        {
            revision:
                'DISPLAYED-CHAIN-1A-EXISTING-PREREQUISITES-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_MODULE
                    .revision,
            entries: [
                ...prerequisiteExternalSymbols.map((target, order) =>
                    dependencyLink(
                        earlierLinks,
                        target,
                        order,
                        'DISPLAYED-CHAIN-1A prerequisite'
                    )
                ),
                ...existingDeclarations.map(
                    (declaration, index) => ({
                        order:
                            prerequisiteExternalSymbols.length + index,
                        symbol: declaration.symbol,
                        kind: 'free-declaration' as const,
                        coreName:
                            prerequisiteCoreName(declaration.symbol),
                        backendName:
                            declaration.symbol === pointFunctor
                                ? 'Obj_func'
                                : declaration.symbol.name
                    })
                )
            ]
        }
    );

const sigmaMapObjectRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const eta = builder.capture('eta');
    const k = builder.capture('k');
    const u = builder.capture('u');
    const sourceFibre = fibre(builder, K, E, k);
    const targetFibre = fibre(builder, K, D, k);
    return {
        order: 0,
        id: 'categorical.displayed-chain.sigma-map-object',
        groupId:
            'categorical.displayed-chain.existing-sigma-map',
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
                name: 'D',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'eta',
                type: builder.template(
                    displayedFunctorType(builder, K, E, D)
                )
            },
            {
                name: 'k',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'u',
                type: builder.template(objectType(builder, sourceFibre))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            sigmaTotal(builder, K, E),
            sigmaTotal(builder, K, D),
            sigmaMapAt(builder, K, E, D, eta),
            sigmaPairPattern(builder, K, E, k, u)
        )),
        right: builder.template(sigmaPair(
            builder,
            K,
            D,
            k,
            functorObjectAt(
                builder,
                sourceFibre,
                targetFibre,
                componentAt(builder, K, E, D, k, eta),
                u
            )
        )),
        provenance: source(
            'rule @fapp0 _ _ (@sigma_map_func $K $E $D $eta) ' +
                '(Struct_sigma $k $u)'
        )
    };
};

const sigmaMapStructuredArrowRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const eta = builder.capture('eta');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const u = builder.capture('u');
    const v = builder.capture('v');
    const p = builder.capture('p');
    const alpha = builder.capture('alpha');
    const sourceFibreX = fibre(builder, K, E, x);
    const sourceFibreY = fibre(builder, K, E, y);
    const targetFibreX = fibre(builder, K, D, x);
    const targetFibreY = fibre(builder, K, D, y);
    const mappedU = functorObjectAt(
        builder,
        sourceFibreX,
        targetFibreX,
        componentAt(builder, K, E, D, x, eta),
        u
    );
    const mappedV = functorObjectAt(
        builder,
        sourceFibreY,
        targetFibreY,
        componentAt(builder, K, E, D, y, eta),
        v
    );
    return {
        order: 1,
        id: 'categorical.displayed-chain.sigma-map-structured-arrow',
        groupId:
            'categorical.displayed-chain.existing-sigma-map',
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
                name: 'u',
                type: builder.template(objectType(builder, sourceFibreX))
            },
            {
                name: 'v',
                type: builder.template(objectType(builder, sourceFibreY))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, K, x, y))
            },
            {
                name: 'alpha',
                type: builder.template(homType(
                    builder,
                    sourceFibreY,
                    functorObjectAt(
                        builder,
                        sourceFibreX,
                        sourceFibreY,
                        displayedTransportAt(builder, E, K, x, y, p),
                        u
                    ),
                    v
                ))
            }
        ],
        left: builder.pattern(functorArrowAt(
            builder,
            sigmaTotal(builder, K, E),
            sigmaTotal(builder, K, D),
            sigmaMapAt(builder, K, E, D, eta),
            sigmaPairPattern(builder, K, E, x, u),
            sigmaPairPattern(builder, K, E, y, v),
            sigmaArrowAt(builder, K, E, x, y, u, v, p, alpha)
        )),
        right: builder.template(sigmaArrowAt(
            builder,
            K,
            D,
            x,
            y,
            mappedU,
            mappedV,
            p,
            displayedInternalHomActionAt(
                builder,
                K,
                E,
                D,
                eta,
                x,
                y,
                p,
                u,
                v,
                alpha
            )
        )),
        provenance: source(
            'rule @fapp1_fapp0 _ _ ' +
                '(@sigma_map_func $K $E $D $eta) ' +
                '(Struct_sigma $x $u) (Struct_sigma $y $v) ' +
                '(Struct_sigma $p $alpha)'
        )
    };
};

const prerequisiteRuntimeRules = Object.freeze([
    sigmaMapObjectRule(),
    sigmaMapStructuredArrowRule(),
    (() => {
        const builder = new CoreLfTransferScopedBuilder();
        const K = builder.capture('K');
        const R = builder.capture('R');
        const D = builder.capture('D');
        const k = builder.capture('k');
        const r = builder.capture('r');
        return {
            order: 2,
            id:
                'categorical.displayed-chain.' +
                'sigma-projection-pullback-object-prerequisite',
            groupId:
                'categorical.displayed-chain.' +
                'sigma-projection-pullback-object-prerequisite',
            clauseOrder: 0,
            sourceOwner: functorObject,
            variables: [
                {
                    name: 'K',
                    type: builder.template(builder.global(category))
                },
                {
                    name: 'R',
                    type: builder.template(
                        displayedFamilyType(builder, K)
                    )
                },
                {
                    name: 'D',
                    type: builder.template(
                        displayedFamilyType(builder, K)
                    )
                },
                {
                    name: 'k',
                    type: builder.template(objectType(builder, K))
                },
                {
                    name: 'r',
                    type: builder.template(objectType(
                        builder,
                        fibre(builder, K, R, k)
                    ))
                }
            ],
            left: builder.pattern(functorObjectAt(
                builder,
                sigmaTotal(builder, K, R),
                builder.global(categoryOfCategories),
                sigmaProjectionPullbackAt(builder, K, R, D),
                sigmaPairPattern(builder, K, R, k, r)
            )),
            right: builder.template(fibre(builder, K, D, k)),
            provenance: source(
                'rule @fapp0 _ Cat_cat ' +
                    '(@Sigma_proj1_pullback_catd $K $R $D) ' +
                    '(Struct_sigma $k $r)'
            )
        };
    })(),
    (() => {
        const builder = new CoreLfTransferScopedBuilder();
        const A = builder.capture('A');
        const B = builder.capture('B');
        const b = builder.capture('b');
        const a = builder.capture('a');
        return {
            order: 3,
            id:
                'categorical.displayed-chain.' +
                'constant-functor-object-prerequisite',
            groupId:
                'categorical.displayed-chain.' +
                'constant-functor-object-prerequisite',
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
                    name: 'b',
                    type: builder.template(objectType(builder, B))
                },
                {
                    name: 'a',
                    type: builder.template(objectType(builder, A))
                }
            ],
            left: builder.pattern(functorObjectAt(
                builder,
                A,
                B,
                constantFunctorAt(builder, A, B, b),
                a
            )),
            right: builder.template(b),
            provenance: source(
                'rule @fapp0 $A $B ' +
                    '(@Const_func $A $B $b) $_ ↪ $b'
            )
        };
    })(),
    (() => {
        const builder = new CoreLfTransferScopedBuilder();
        const K = builder.capture('K');
        const A = builder.capture('A');
        const x = builder.capture('x');
        const y = builder.capture('y');
        const p = builder.capture('p');
        return {
            order: 4,
            id:
                'categorical.displayed-chain.' +
                'constant-family-structured-arrow-prerequisite',
            groupId:
                'categorical.displayed-chain.' +
                'constant-family-structured-arrow-prerequisite',
            clauseOrder: 0,
            sourceOwner: functorHomCapped,
            variables: [
                {
                    name: 'K',
                    type: builder.template(builder.global(category))
                },
                {
                    name: 'A',
                    type: builder.template(builder.global(category))
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
            left: builder.pattern(functorArrowAt(
                builder,
                K,
                builder.global(categoryOfCategories),
                constantFamily(builder, K, A),
                x,
                y,
                p
            )),
            right: builder.template(globalCall(
                builder,
                identityFunctor,
                [{ plicity: 'implicit', value: A }]
            )),
            provenance: source(
                'rule @fapp1_fapp0 $K Cat_cat ' +
                    '(@Const_catd $K $A) $x $y $_ ↪ @id_func $A'
            )
        };
    })(),
    (() => {
        const builder = new CoreLfTransferScopedBuilder();
        const K = builder.capture('K');
        const E = builder.capture('E');
        const s = builder.capture('s');
        const k = builder.capture('k');
        const sourceFamily = constantFamily(
            builder,
            K,
            builder.global(terminalCategory)
        );
        const targetFibre = fibre(builder, K, E, k);
        return {
            order: 5,
            id:
                'categorical.displayed-chain.' +
                'section-object.delta-normalize',
            groupId:
                'categorical.displayed-chain.' +
                'section-object.delta-normalize',
            clauseOrder: 0,
            sourceOwner: sectionObject,
            variables: [
                {
                    name: 'K',
                    type: builder.template(builder.global(category))
                },
                {
                    name: 'E',
                    type: builder.template(
                        displayedFamilyType(builder, K)
                    )
                },
                {
                    name: 's',
                    type: builder.template(
                        objectType(
                            builder,
                            sectionCategoryAt(builder, K, E)
                        )
                    )
                },
                {
                    name: 'k',
                    type: builder.template(objectType(builder, K))
                }
            ],
            left: builder.pattern(sectionAt(builder, K, E, s, k)),
            right: builder.template(functorObjectAt(
                builder,
                builder.global(terminalCategory),
                targetFibre,
                componentAt(
                    builder,
                    K,
                    sourceFamily,
                    E,
                    k,
                    s
                ),
                builder.global(terminalObject)
            )),
            provenance: source(
                'typed explicit-Core delta-normal form of the active ' +
                    'transparent piapp0/piapp0_func definitions through ' +
                    'existing composition, fapp0_func, and tapp0_fapp0 ' +
                    'computation'
            )
        };
    })()
]);

const prerequisiteNormalFormSpecializationRuleIds = Object.freeze([
    'categorical.displayed-chain.section-object.delta-normalize'
] as const);

const prerequisiteExactExistingRuntimeRuleIds = Object.freeze(
    prerequisiteRuntimeRules
        .map(rule => rule.id)
        .filter(id => !(
            prerequisiteNormalFormSpecializationRuleIds as
            readonly string[]
        ).includes(id))
);

const prerequisiteRuntimeExternalSymbols = Object.freeze([
    ...prerequisiteExternalSymbols,
    dependentPair,
    transforComponentCapped,
    sigmaArrow,
    sigmaProjectionPullback,
    identityFunctor,
    sectionCategory,
    sectionObject,
    ...existingDeclarations.map(declaration =>
        declaration.symbol
    )
]);

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        'DISPLAYED-CHAIN-1A-EXISTING-PREREQUISITE-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId:
        'displayed-chain-1a-existing-prerequisite-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_DISPLAYED_CHAIN_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: prerequisiteRuntimeExternalSymbols.map(
        symbol_ => ({
            symbol: symbol_,
            availability: 'earlier-fragment' as const
        })
    ),
    declarations: [],
    inductives: [],
    runtimeRules: prerequisiteRuntimeRules,
    proofRules: []
});

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_RUNTIME_MODULE,
    {
        revision:
            'DISPLAYED-CHAIN-1A-EXISTING-PREREQUISITE-' +
            'RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_RUNTIME_MODULE
                .revision,
        entries: prerequisiteRuntimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                (
                    prerequisiteNormalFormSpecializationRuleIds as
                    readonly string[]
                ).includes(rule.id)
                    ? 'Typed explicit-Core normal-form specialization of ' +
                        'the active transparent piapp0/piapp0_func ' +
                        'computation; no Lambdapi rule is added'
                    : 'Exact pre-existing active v3.2 runtime equation ' +
                        'required by the reviewed recursive substitution ' +
                        'closure'
        }))
    }
);

const semanticExternalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    functorClassifier,
    homClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    displayedFunctorCategory,
    functorObject,
    functorHomCapped,
    transforComponentCapped,
    transforCategory,
    sigmaCategory,
    dependentPair,
    constantDisplayedFamily,
    sectionCategory,
    terminalCategory,
    displayedIdentity,
    displayedFibreFunctor,
    displayedTransportLeft,
    displayedTransportRight,
    sigmaArrow,
    sigmaFirstProjection,
    sigmaProjectionPullback,
    sectionPullbackFunctor,
    sectionPullbackSection,
    sectionObject,
    identityArrow,
    displayedTransformationInternalCell,
    ...existingDeclarations.map(declaration =>
        declaration.symbol
    )
]);

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'displayed-chain-1a-signature',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_DISPLAYED_CHAIN_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: semanticExternalSymbols.map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations: semanticDeclarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_MODULE,
    {
        revision: 'DISPLAYED-CHAIN-1A-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_MODULE.revision,
        entries: semanticDeclarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact injective mathematical owner approved by ' +
                'D-DTTLF-USABILITY-012'
        }))
    }
);

const prerequisiteLinks = [
    ...CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_LINKAGE.entries,
    ...earlierLinks
];

const semanticCoreName = (
    target: CoreLfQualifiedSymbol
): string =>
    `emdash_v3_2_displayed_chain_1a_${target.name}`;

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_MODULE,
        {
            revision: 'DISPLAYED-CHAIN-1A-SIGNATURE-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_MODULE
                    .revision,
            entries: [
                ...semanticExternalSymbols.map((target, order) =>
                    dependencyLink(
                        prerequisiteLinks,
                        target,
                        order,
                        'DISPLAYED-CHAIN-1A semantic closure'
                    )
                ),
                ...semanticDeclarations.map(
                    (declaration, index) => ({
                        order: semanticExternalSymbols.length + index,
                        symbol: declaration.symbol,
                        kind: 'free-declaration' as const,
                        coreName: semanticCoreName(declaration.symbol),
                        backendName: declaration.symbol.name
                    })
                )
            ]
        }
    );

const projectionStructuredArrowRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const u = builder.capture('u');
    const v = builder.capture('v');
    const p = builder.capture('p');
    const alpha = builder.capture('alpha');
    const fibreX = fibre(builder, K, E, x);
    const fibreY = fibre(builder, K, E, y);
    return {
        order: 0,
        id:
            'categorical.displayed-chain.' +
            'sigma-first-projection-structured-arrow',
        groupId:
            'categorical.displayed-chain.sigma-first-projection',
        clauseOrder: 0,
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
                name: 'x',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'u',
                type: builder.template(objectType(builder, fibreX))
            },
            {
                name: 'v',
                type: builder.template(objectType(builder, fibreY))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, K, x, y))
            },
            {
                name: 'alpha',
                type: builder.template(homType(
                    builder,
                    fibreY,
                    functorObjectAt(
                        builder,
                        fibreX,
                        fibreY,
                        displayedTransportAt(builder, E, K, x, y, p),
                        u
                    ),
                    v
                ))
            }
        ],
        left: builder.pattern(functorArrowAt(
            builder,
            sigmaTotal(builder, K, E),
            K,
            sigmaProjectionAt(builder, K, E),
            sigmaPairPattern(builder, K, E, x, u),
            sigmaPairPattern(builder, K, E, y, v),
            sigmaArrowAt(builder, K, E, x, y, u, v, p, alpha)
        )),
        right: builder.template(p),
        provenance: source(
            'rule @fapp1_fapp0 (@Sigma_cat $K $E) $K ' +
                '(@Sigma_proj1_func $K $E) ' +
                '(Struct_sigma _ _) (Struct_sigma _ _) ' +
                '(Struct_sigma $p _)'
        )
    };
};

const projectionPullbackStructuredArrowRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const R = builder.capture('R');
    const D = builder.capture('D');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const u = builder.capture('u');
    const v = builder.capture('v');
    const p = builder.capture('p');
    const alpha = builder.capture('alpha');
    const fibreX = fibre(builder, K, R, x);
    const fibreY = fibre(builder, K, R, y);
    return {
        order: 1,
        id:
            'categorical.displayed-chain.' +
            'sigma-projection-pullback-structured-arrow',
        groupId:
            'categorical.displayed-chain.' +
            'sigma-projection-pullback',
        clauseOrder: 0,
        sourceOwner: functorHomCapped,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'R',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'D',
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
                name: 'u',
                type: builder.template(objectType(builder, fibreX))
            },
            {
                name: 'v',
                type: builder.template(objectType(builder, fibreY))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, K, x, y))
            },
            {
                name: 'alpha',
                type: builder.template(homType(
                    builder,
                    fibreY,
                    functorObjectAt(
                        builder,
                        fibreX,
                        fibreY,
                        displayedTransportAt(builder, R, K, x, y, p),
                        u
                    ),
                    v
                ))
            }
        ],
        left: builder.pattern(functorArrowAt(
            builder,
            sigmaTotal(builder, K, R),
            builder.global(categoryOfCategories),
            sigmaProjectionPullbackAt(builder, K, R, D),
            sigmaPairPattern(builder, K, R, x, u),
            sigmaPairPattern(builder, K, R, y, v),
            sigmaArrowAt(builder, K, R, x, y, u, v, p, alpha)
        )),
        right: builder.template(functorArrowAt(
            builder,
            K,
            builder.global(categoryOfCategories),
            D,
            x,
            y,
            p
        )),
        provenance: source(
            'rule @fapp1_fapp0 (@Sigma_cat $K $R) Cat_cat ' +
                '(@Sigma_proj1_pullback_catd $K $R $D) ' +
                '(Struct_sigma $x _) (Struct_sigma $y _) ' +
                '(Struct_sigma $p _)'
        )
    };
};

const sigmaSectionObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const R = builder.capture('R');
    const D = builder.capture('D');
    const FF = builder.capture('FF');
    const k = builder.capture('k');
    const r = builder.capture('r');
    const sourceFibre = fibre(builder, K, R, k);
    const targetFibre = fibre(builder, K, D, k);
    return {
        order: 2,
        id:
            'categorical.displayed-chain.' +
            'sigma-functord-section-object',
        groupId:
            'categorical.displayed-chain.sigma-functord-section',
        clauseOrder: 0,
        sourceOwner: transforComponentCapped,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'R',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'D',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'FF',
                type: builder.template(
                    displayedFunctorType(builder, K, R, D)
                )
            },
            {
                name: 'k',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'r',
                type: builder.template(objectType(builder, sourceFibre))
            }
        ],
        left: builder.pattern(componentAt(
            builder,
            sigmaTotal(builder, K, R),
            constantFamily(
                builder,
                sigmaTotal(builder, K, R),
                builder.global(terminalCategory)
            ),
            sigmaProjectionPullbackAt(builder, K, R, D),
            sigmaPairPattern(builder, K, R, k, r),
            sigmaSectionAt(builder, K, R, D, FF)
        )),
        right: builder.template(pointFunctorAt(
            builder,
            targetFibre,
            functorObjectAt(
                builder,
                sourceFibre,
                targetFibre,
                componentAt(builder, K, R, D, k, FF),
                r
            )
        )),
        provenance: source(
            'rule @tapp0_fapp0 (@Sigma_cat $K $R) Cat_cat ' +
                '(@Const_catd (@Sigma_cat $K $R) Terminal_cat) ' +
                '(@Sigma_proj1_pullback_catd $K $R $D) ' +
                '(Struct_sigma $k $r) ' +
                '(@sigma_functord_sec $K $R $D $FF)'
        )
    };
};

const sigmaSectionStructuredArrowRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const R = builder.capture('R');
    const D = builder.capture('D');
    const FF = builder.capture('FF');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const u = builder.capture('u');
    const v = builder.capture('v');
    const p = builder.capture('p');
    const alpha = builder.capture('alpha');
    const sourceFibreX = fibre(builder, K, R, x);
    const sourceFibreY = fibre(builder, K, R, y);
    const total = sigmaTotal(builder, K, R);
    const sourceFamily = constantFamily(
        builder,
        total,
        builder.global(terminalCategory)
    );
    const targetFamily =
        sigmaProjectionPullbackAt(builder, K, R, D);
    return {
        order: 3,
        id:
            'categorical.displayed-chain.' +
            'sigma-functord-section-structured-arrow',
        groupId:
            'categorical.displayed-chain.sigma-functord-section',
        clauseOrder: 1,
        sourceOwner: displayedInternalCell,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'R',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'D',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'FF',
                type: builder.template(
                    displayedFunctorType(builder, K, R, D)
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
                name: 'u',
                type: builder.template(objectType(builder, sourceFibreX))
            },
            {
                name: 'v',
                type: builder.template(objectType(builder, sourceFibreY))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, K, x, y))
            },
            {
                name: 'alpha',
                type: builder.template(homType(
                    builder,
                    sourceFibreY,
                    functorObjectAt(
                        builder,
                        sourceFibreX,
                        sourceFibreY,
                        displayedTransportAt(builder, R, K, x, y, p),
                        u
                    ),
                    v
                ))
            }
        ],
        left: builder.pattern(displayedInternalCellAt(
            builder,
            total,
            sourceFamily,
            targetFamily,
            sigmaSectionAt(builder, K, R, D, FF),
            sigmaPairPattern(builder, K, R, x, u),
            sigmaPairPattern(builder, K, R, y, v),
            sigmaArrowAt(builder, K, R, x, y, u, v, p, alpha),
            builder.global(terminalObject)
        )),
        right: builder.template(displayedInternalHomActionAt(
            builder,
            K,
            R,
            D,
            FF,
            x,
            y,
            p,
            u,
            v,
            alpha
        )),
        provenance: source(
            'rule @fdapp1_int_cell (@Sigma_cat $K $R) ' +
                '(@Const_catd (@Sigma_cat $K $R) Terminal_cat) ' +
                '(@Sigma_proj1_pullback_catd $K $R $D) ' +
                '(@sigma_functord_sec $K $R $D $FF) ' +
                '(Struct_sigma $x $u) (Struct_sigma $y $v) ' +
                '(Struct_sigma $p $alpha) Terminal_obj'
        )
    };
};

const sectionPullbackDirectObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const B = builder.capture('B');
    const R = builder.capture('R');
    const E = builder.capture('E');
    const s = builder.capture('s');
    const z = builder.capture('z');
    const total = sigmaTotal(builder, B, R);
    const projection = sigmaProjectionAt(builder, B, R);
    return {
        order: 4,
        id:
            'categorical.displayed-chain.' +
            'section-pullback-direct-object',
        groupId:
            'categorical.displayed-chain.section-pullback-direct',
        clauseOrder: 0,
        sourceOwner: transforComponentCapped,
        variables: [
            {
                name: 'B',
                type: builder.template(builder.global(category))
            },
            {
                name: 'R',
                type: builder.template(displayedFamilyType(builder, B))
            },
            {
                name: 'E',
                type: builder.template(displayedFamilyType(builder, B))
            },
            {
                name: 's',
                type: builder.template(objectType(
                    builder,
                    sectionCategoryAt(builder, B, E)
                ))
            },
            {
                name: 'z',
                type: builder.template(objectType(builder, B))
            }
        ],
        left: builder.pattern(componentAt(
            builder,
            B,
            R,
            E,
            z,
            sectionPullbackSectionAt(
                builder,
                total,
                B,
                projection,
                E,
                s
            )
        )),
        right: builder.template(constantFunctorAt(
            builder,
            fibre(builder, B, R, z),
            fibre(builder, B, E, z),
            sectionAt(builder, B, E, s, z)
        )),
        provenance: source(
            'rule @tapp0_fapp0 $B Cat_cat $R $E $z ' +
                '(@section_pullback_sec (@Sigma_cat $B $R) $B ' +
                '(@Sigma_proj1_func $B $R) $E $s)'
        )
    };
};

const sectionPullbackDirectArrowRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const B = builder.capture('B');
    const R = builder.capture('R');
    const E = builder.capture('E');
    const s = builder.capture('s');
    const z = builder.capture('z');
    const zPrime = builder.capture('zPrime');
    const q = builder.capture('q');
    const r = builder.capture('r');
    const total = sigmaTotal(builder, B, R);
    const projection = sigmaProjectionAt(builder, B, R);
    const weakened = sectionPullbackSectionAt(
        builder,
        total,
        B,
        projection,
        E,
        s
    );
    return {
        order: 5,
        id:
            'categorical.displayed-chain.' +
            'section-pullback-direct-arrow',
        groupId:
            'categorical.displayed-chain.section-pullback-direct',
        clauseOrder: 1,
        sourceOwner: displayedInternalCell,
        variables: [
            {
                name: 'B',
                type: builder.template(builder.global(category))
            },
            {
                name: 'R',
                type: builder.template(displayedFamilyType(builder, B))
            },
            {
                name: 'E',
                type: builder.template(displayedFamilyType(builder, B))
            },
            {
                name: 's',
                type: builder.template(objectType(
                    builder,
                    sectionCategoryAt(builder, B, E)
                ))
            },
            {
                name: 'z',
                type: builder.template(objectType(builder, B))
            },
            {
                name: 'zPrime',
                type: builder.template(objectType(builder, B))
            },
            {
                name: 'q',
                type: builder.template(
                    homType(builder, B, z, zPrime)
                )
            },
            {
                name: 'r',
                type: builder.template(
                    objectType(builder, fibre(builder, B, R, z))
                )
            }
        ],
        left: builder.pattern(displayedInternalCellAt(
            builder,
            B,
            R,
            E,
            weakened,
            z,
            zPrime,
            q,
            r
        )),
        right: builder.template(displayedInternalCellAt(
            builder,
            B,
            constantFamily(
                builder,
                B,
                builder.global(terminalCategory)
            ),
            E,
            s,
            z,
            zPrime,
            q,
            builder.global(terminalObject)
        )),
        provenance: source(
            'rule @fdapp1_int_cell $B $R $E ' +
                '(@section_pullback_sec (@Sigma_cat $B $R) $B ' +
                '(@Sigma_proj1_func $B $R) $E $s) ' +
                '$z $zPrime $q _'
        )
    };
};

const displayedInternalCellIdentityRule = (
    presentation: 'direct' | 'ordinary',
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
    const u = builder.capture('u');
    const direct = displayedFunctorCategoryAt(builder, K, E, D);
    const ordinary = transforCategoryAt(
        builder,
        K,
        builder.global(categoryOfCategories),
        E,
        D
    );
    return {
        order,
        id:
            `categorical.displayed-chain.internal-cell-identity.${presentation}`,
        groupId: 'categorical.displayed-chain.internal-cell-identity',
        clauseOrder: presentation === 'direct' ? 0 : 1,
        sourceOwner: displayedTransformationInternalCell,
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
                type: builder.template(
                    displayedFunctorType(builder, K, E, D)
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
                type: builder.template(homType(builder, K, x, y))
            },
            {
                name: 'u',
                type: builder.template(
                    objectType(builder, fibre(builder, K, E, x))
                )
            }
        ],
        left: builder.pattern(displayedTransformationInternalCellAt(
            builder,
            K,
            E,
            D,
            FF,
            FF,
            identityAt(
                builder,
                presentation === 'direct' ? direct : ordinary,
                FF
            ),
            x,
            y,
            p,
            u
        )),
        right: builder.template(displayedInternalCellAt(
            builder,
            K,
            E,
            D,
            FF,
            x,
            y,
            p,
            u
        )),
        provenance: source(
            'rule @tdapp1_int_cell $K $E $D $FF $FF ' +
                `(@id (@${presentation === 'direct'
                    ? 'Functord_cat'
                    : 'Transf_cat'} ...) $FF) $x $y $p $u ↪ ` +
                '@fdapp1_int_cell $K $E $D $FF $x $y $p $u'
        )
    };
};

const semanticRuntimeRules = Object.freeze([
    projectionStructuredArrowRule(),
    projectionPullbackStructuredArrowRule(),
    sigmaSectionObjectRule(),
    sigmaSectionStructuredArrowRule(),
    sectionPullbackDirectObjectRule(),
    sectionPullbackDirectArrowRule()
]);

const existingIdentityRuntimeRules = Object.freeze([
    displayedInternalCellIdentityRule('direct', 6),
    displayedInternalCellIdentityRule('ordinary', 7)
]);

const localRuntimeRules = Object.freeze([
    ...semanticRuntimeRules,
    ...existingIdentityRuntimeRules
]);

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'DISPLAYED-CHAIN-1A-RUNTIME-D057-1',
    moduleId: MODULE_ID,
    fragmentId: 'displayed-chain-1a-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_DISPLAYED_CHAIN_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        ...semanticExternalSymbols,
        ...semanticDeclarations.map(declaration =>
            declaration.symbol
        )
    ].map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules: localRuntimeRules,
    proofRules: []
});

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_CHAIN_RUNTIME_MODULE,
    {
        revision: 'DISPLAYED-CHAIN-1A-RUNTIME-POLICY-D057-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_RUNTIME_MODULE.revision,
        entries: localRuntimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence: existingIdentityRuntimeRules.includes(rule)
                ? 'Exact active identity internal-cell fold approved by ' +
                    'D-DTTLF-USABILITY-057'
                : 'Exact owner-position-tested runtime rule approved by ' +
                    'D-DTTLF-USABILITY-012'
        }))
    }
);

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_CORE_NAMES =
Object.freeze({
    sigmaMapFunctor:
        prerequisiteCoreName(sigmaMapFunctor),
    terminalObject:
        prerequisiteCoreName(terminalObject),
    constantFunctor:
        prerequisiteCoreName(constantFunctor),
    pointFunctorMirror:
        prerequisiteCoreName(pointFunctor),
    displayedInternalCell:
        prerequisiteCoreName(displayedInternalCell),
    displayedInternalHomAction:
        prerequisiteCoreName(displayedInternalHomAction),
    sigmaFunctordSection:
        semanticCoreName(sigmaFunctordSection)
});

export type CoreCategoricalDisplayedChainCoreId =
    keyof typeof CORE_CATEGORICAL_DISPLAYED_CHAIN_CORE_NAMES;

export function coreCategoricalDisplayedChainCoreName(
    id: CoreCategoricalDisplayedChainCoreId
): string {
    return CORE_CATEGORICAL_DISPLAYED_CHAIN_CORE_NAMES[id];
}

export const CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY =
Object.freeze({
    status: 'displayed-chain-1a-generic-transfer',
    semanticReviewRevision: 'DISPLAYED-CHAIN-0A-REVIEWED-1',
    computationClosureReviewRevision:
        'DISPLAYED-CHAIN-COMPUTATION-CLOSURE-CORRECTION-0A-REVIEWED-1',
    existingPrerequisiteDeclarationNames: Object.freeze(
        prerequisiteDeclarations.map(declaration =>
            declaration.symbol.name
        )
    ),
    ambientPrerequisiteDeclarationNames: Object.freeze(
        ambientDeclarations.map(declaration =>
            declaration.symbol.name
        )
    ),
    checkedTransparentMirrorDeclarationNames: Object.freeze(
        mirrorDeclarations.map(declaration =>
            declaration.symbol.name
        )
    ),
    existingPrerequisiteRuntimeRuleIds: Object.freeze(
        prerequisiteRuntimeRules.map(rule => rule.id)
    ),
    newOwnerNames: Object.freeze(
        semanticDeclarations.map(declaration =>
            declaration.symbol.name
        )
    ),
    newRuntimeRuleIds: Object.freeze(
        semanticRuntimeRules.map(rule => rule.id)
    ),
    transferredExistingIdentityRuntimeRuleIds: Object.freeze(
        existingIdentityRuntimeRules.map(rule => rule.id)
    ),
    transferredExistingIdentityRuntimeRuleCount:
        existingIdentityRuntimeRules.length,
    localRuntimeRuleCount: localRuntimeRules.length,
    existingPrerequisiteDeclarationCount:
        prerequisiteDeclarations.length,
    ambientPrerequisiteDeclarationCount:
        ambientDeclarations.length,
    checkedTransparentMirrorDeclarationCount:
        mirrorDeclarations.length,
    approvedExistingDeclarationPrerequisiteCount:
        prerequisiteDeclarations.length + ambientDeclarations.length,
    totalGenericTransferDeclarationCount:
        existingDeclarations.length,
    prerequisiteRuntimeRuleCount:
        prerequisiteRuntimeRules.length,
    exactExistingRuntimeRuleCount:
        prerequisiteExactExistingRuntimeRuleIds.length,
    exactExistingRuntimeRuleIds:
        prerequisiteExactExistingRuntimeRuleIds,
    normalFormSpecializationRuleCount:
        prerequisiteNormalFormSpecializationRuleIds.length,
    normalFormSpecializationRuleIds:
        prerequisiteNormalFormSpecializationRuleIds,
    checkedTransparentMirrorAddsBackendOwnerCount: 0,
    typedIgnoredTermCaptureCount: 1,
    restoredTransparentDefinitionNames: Object.freeze([
        displayedTransportLeft.name,
        displayedTransportRight.name
    ]),
    restoredTransparentDefinitionCount: 2,
    newMathematicalOwnerCount: semanticDeclarations.length,
    newMathematicalRuntimeRuleCount: semanticRuntimeRules.length,
    newMathematicalProofRuleCount: 0,
    newIntrinsicCoreOwnerCount: 0,
    genericFappTappCoherenceRuleCount: 0,
    objectLevelRuleCount: 2,
    structuredArrowOrBaseActionRuleCount: 4,
    allEntriesUseGenericTransferEngines: true
});

export interface CoreCategoricalDisplayedChainCompilation {
    readonly prerequisite:
        CoreCategoricalDisplayedEvaluationCompilation;
    readonly prerequisiteCompiled:
        CoreLfCompiledDeclarationModule;
    readonly prerequisiteDeclarationContext:
        CoreLfMixedDeclarationContext;
    readonly prerequisiteRuntimeFragment:
        CoreLfCompiledRuntimeFragment;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation:
    CoreCategoricalDisplayedChainCompilation | undefined;

export function compileCoreCategoricalDisplayedChainTransfer():
CoreCategoricalDisplayedChainCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    validateCoreLfScaleEngineReview();
    validateCoreCategoricalDisplayedChainReview();
    validateCoreCategoricalDisplayedChainTransferCorrectionReview();
    validateCoreCategoricalDisplayedChainConstantFunctorCorrectionReview();
    validateCoreCategoricalDisplayedChainComputationClosureCorrectionReview();
    const prerequisite =
        compileCoreCategoricalDisplayedEvaluationTransfer();
    const initialPrerequisiteCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_MODULE,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_POLICY,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: prerequisite.composedRuntime
        }
    );
    const initialPrerequisiteContext =
        new CoreLfMixedDeclarationContext(
            prerequisite.declarationContext,
            [initialPrerequisiteCompiled]
        );
    const inheritedRuntimeFragment =
        new CoreLfCompiledRuntimeFragment(
            prerequisite.runtimeFragment.localProgram,
            [],
            prerequisite.composedRuntime
        );
    const prerequisiteRuntimeFragment =
        compileCoreLfRuntimeFragment(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_RUNTIME_MODULE,
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_RUNTIME_POLICY,
            initialPrerequisiteContext,
            {
                dependencies: [{
                    relation: 'earlier-fragment',
                    fragment: inheritedRuntimeFragment
                }]
            }
        );
    const prerequisiteCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_MODULE,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_POLICY,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: prerequisiteRuntimeFragment.runtime
        }
    );
    const prerequisiteDeclarationContext =
        new CoreLfMixedDeclarationContext(
            prerequisite.declarationContext,
            [prerequisiteCompiled]
        );
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_MODULE,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_POLICY,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisiteCompiled.environment,
            runtimeProgram: prerequisiteRuntimeFragment.runtime
        }
    );
    const initialContext = new CoreLfMixedDeclarationContext(
        prerequisiteDeclarationContext,
        [initialCompiled]
    );
    const runtimeFragment = compileCoreLfRuntimeFragment(
        CORE_CATEGORICAL_DISPLAYED_CHAIN_RUNTIME_MODULE,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_RUNTIME_POLICY,
        initialContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: prerequisiteRuntimeFragment
            }]
        }
    );
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_MODULE,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_POLICY,
        CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisiteCompiled.environment,
            runtimeProgram: runtimeFragment.runtime
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        prerequisiteDeclarationContext,
        [compiled]
    );
    cachedCompilation = Object.freeze({
        prerequisite,
        prerequisiteCompiled,
        prerequisiteDeclarationContext,
        prerequisiteRuntimeFragment,
        compiled,
        declarationContext,
        runtimeFragment,
        runtime: runtimeFragment.localProgram,
        composedRuntime: runtimeFragment.runtime
    });
    return cachedCompilation;
}
