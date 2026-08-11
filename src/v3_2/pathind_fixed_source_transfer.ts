/**
 * PATHIND-TRUSTED-PROFILE-1C root-only existing-authority transfer.
 *
 * Exact local boundary: five opaque declarations, twelve runtime rules, no
 * proof rule, and six transparent definitions.  The module deliberately
 * stops before PathInd_func, PathInd_transfd, varying-source packaging,
 * transitivity, and public/browser/package presentation.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE
} from './categorical_displayed_chain_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS
} from './categorical_displayed_nd_higher_foundation_transfer';
import {
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_LINKAGE
} from './categorical_fibred_dependent_target_transfer';
import {
    CORE_CATEGORICAL_MIXED_ACTION_SYMBOLS,
    CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_LINKAGE
} from './categorical_mixed_action_transfer';
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
import {
    CORE_PATHOUT_FOUNDATION_1B_LIBRARY_LINKAGE,
    CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_LINKAGE,
    CORE_PATHOUT_FOUNDATION_1B_REVISION,
    CORE_PATHOUT_FOUNDATION_1B_SYMBOLS,
    CORE_PATHOUT_FOUNDATION_SOURCE_SHA256,
    CorePathoutFoundation1bCompilation,
    compileCorePathoutFoundation1bTransfer
} from './pathout_foundation_transfer';
import {
    validateCorePathindFixedSource1cReviewV8
} from './pathind_fixed_source_review_v8';

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_PATHIND_FIXED_SOURCE_1C_REVISION =
    'PATHIND-TRUSTED-PROFILE-1C-TRANSFER-1' as const;

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
const transforClassifier =
    coreDirectedContinuationTransferSymbol('transfor-classifier');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const functorCategory =
    coreLfQualifiedSymbol(MODULE_ID, 'Functor_cat');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol('displayed-category-category');
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const transforComponentCapped =
    coreDirectedContinuationTransferSymbol('transfor-component-capped');
const transforCategory =
    coreDirectedContinuationTransferSymbol('transfor-category');
const homCategory =
    coreDirectedContinuationTransferSymbol('hom-category');
const dependentPair =
    coreDirectedContinuationTransferSymbol('dependent-pair');

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const displayedFamilyClassifier = symbol('Catd');
const displayedFunctorClassifier = symbol('Functord');
const displayedFunctorCategory = symbol('Functord_cat');
const oppositeCategory = symbol('Op_cat');
const constantDisplayedFamily = symbol('Const_catd');
const terminalCategory = symbol('Terminal_cat');
const sectionCategory = symbol('Pi_cat');
const sectionCategoryFunctor = symbol('Pi_func');
const objectFunctor = symbol('Obj_func');
const sigmaProjectionPullback = symbol('Sigma_proj1_pullback_catd');

const {
    identityArrow,
    internalHom
} = CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS;
const {
    contravariantRepresentable,
    covariantFibreAction
} = CORE_CATEGORICAL_MIXED_ACTION_SYMBOLS;
const {
    fixedEvaluation
} = CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_SYMBOLS;
const {
    identityFunctor
} = CORE_CATEGORICAL_STRUCTURAL_SYMBOLS;
const {
    representableFamily,
    pathoutCategory,
    pathoutObject,
    pathoutReflexiveObject,
    pathoutReflexiveArrow
} = CORE_PATHOUT_FOUNDATION_1B_SYMBOLS;

export const CORE_PATHIND_FIXED_SOURCE_1C_SYMBOLS = Object.freeze({
    fibreCovariantTarget: symbol('FibCov_target_catd'),
    fibreCovariantInternal: symbol('fib_cov_int'),
    fibreCovariantSourceFunctor: symbol('fib_cov_src_func'),
    fibreCovariantTransformation: symbol('fib_cov_transf'),
    pathoutReflexiveEvaluation: symbol('pathout_refl_eval_func'),
    pathoutReflexiveBaseTransport:
        symbol('pathout_refl_eval_base_func'),
    pathInductionSection: symbol('path_ind_sec'),
    pathoutReflexiveArrowSection: symbol('pathout_refl_arrow_sec'),
    pathInductionSourceFamily: symbol('PathInd_src_catd'),
    pathInductionTargetFamily: symbol('PathInd_tgt_catd'),
    pathInductionComponentFunctor: symbol('path_ind_func_fapp0')
});

const {
    fibreCovariantTarget,
    fibreCovariantInternal,
    fibreCovariantSourceFunctor,
    fibreCovariantTransformation,
    pathoutReflexiveEvaluation,
    pathoutReflexiveBaseTransport,
    pathInductionSection,
    pathoutReflexiveArrowSection,
    pathInductionSourceFamily,
    pathInductionTargetFamily,
    pathInductionComponentFunctor
} = CORE_PATHIND_FIXED_SOURCE_1C_SYMBOLS;

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

const functorCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorCategory, [
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
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

const transforCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, transforCategory, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
    ]);

const transforClassifierAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, transforClassifier, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
    ]);

const oppositeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, oppositeCategory, [{
        plicity: 'explicit',
        value: base
    }]);

const constantFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    value: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, constantDisplayedFamily, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value }
    ]);

const fibreAt = (
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

const componentAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression,
    displayedFunctor: CoreLfTransferBuilderExpression
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
        { plicity: 'explicit', value: displayedFunctor }
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

const sectionCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sectionCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const sectionCategoryFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sectionCategoryFunctor, [{
        plicity: 'explicit',
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

const identityFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, identityFunctor, [{
        plicity: 'implicit',
        value: base
    }]);

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

const contravariantRepresentableAt = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, contravariantRepresentable, [
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: point },
        { plicity: 'implicit', value: source },
        { plicity: 'explicit', value: functor }
    ]);

const covariantFibreActionAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    targetPoint: CoreLfTransferBuilderExpression,
    sourceValue: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, covariantFibreAction, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family },
        { plicity: 'implicit', value: sourcePoint },
        { plicity: 'implicit', value: targetPoint },
        { plicity: 'explicit', value: sourceValue }
    ]);

const fixedEvaluationAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, fixedEvaluation, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: point }
    ]);

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

const pathoutReflexiveArrowAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pathoutReflexiveArrow, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target },
        { plicity: 'explicit', value: arrow }
    ]);

const fibreCovariantTargetAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, fibreCovariantTarget, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const fibreCovariantInternalAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, fibreCovariantInternal, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const fibreCovariantSourceFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, fibreCovariantSourceFunctor, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: source }
    ]);

const fibreCovariantTransformationAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    sourceValue: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, fibreCovariantTransformation, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: sourceValue }
    ]);

const pathoutReflexiveEvaluationAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pathoutReflexiveEvaluation, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]);

const pathInductionSectionAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    motive: CoreLfTransferBuilderExpression,
    datum: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pathInductionSection, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: motive },
        { plicity: 'explicit', value: datum }
    ]);

const pathInductionComponentFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    motive: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pathInductionComponentFunctor, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: motive }
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

const pointFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, objectFunctor, [
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: point }
    ]);

const sigmaPairPattern = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    first: CoreLfTransferBuilderExpression,
    second: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression => {
    const carrier = globalCall(builder, objectClassifier, [{
        plicity: 'explicit',
        value: base
    }]);
    const familyClassifier = builder.lam(
        'pairPoint',
        objectType(builder, base),
        pairPoint => globalCall(builder, objectClassifier, [{
            plicity: 'explicit',
            value: fibreAt(builder, base, family, pairPoint)
        }]),
        explicitMode
    );
    return globalCall(builder, dependentPair, [
        { plicity: 'implicit', value: builder.wildcard(carrier) },
        {
            plicity: 'implicit',
            value: builder.wildcard(familyClassifier)
        },
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

const fibreCovariantTargetType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            _E => displayedFamilyType(builder, K),
            explicitMode
        ),
        implicitMode
    ));
};

const fibreCovariantTargetBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'K',
        builder.global(category),
        K => builder.lam(
            'E',
            displayedFamilyType(builder, K),
            E => contravariantRepresentableAt(
                builder,
                displayedCategoryAt(builder, K),
                E,
                oppositeAt(builder, K),
                internalHomAt(
                    builder,
                    K,
                    K,
                    identityFunctorAt(builder, K)
                )
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const fibreCovariantInternalType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            E => displayedFunctorType(
                builder,
                K,
                E,
                fibreCovariantTargetAt(builder, K, E)
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const fibreCovariantSourceFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            E => builder.pi(
                'x',
                objectType(builder, K),
                x => functorType(
                    builder,
                    fibreAt(builder, K, E, x),
                    fibreAt(
                        builder,
                        K,
                        fibreCovariantTargetAt(builder, K, E),
                        x
                    )
                ),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const fibreCovariantTransformationType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            E => builder.pi(
                'x',
                objectType(builder, K),
                x => builder.pi(
                    'u',
                    objectType(builder, fibreAt(builder, K, E, x)),
                    _u => objectType(
                        builder,
                        fibreAt(
                            builder,
                            K,
                            fibreCovariantTargetAt(builder, K, E),
                            x
                        )
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

const pathInductionSectionType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => builder.pi(
                'E',
                displayedFamilyType(
                    builder,
                    pathoutCategoryAt(builder, Z, x)
                ),
                E => builder.pi(
                    'u',
                    objectType(
                        builder,
                        fibreAt(
                            builder,
                            pathoutCategoryAt(builder, Z, x),
                            E,
                            pathoutReflexiveObjectAt(builder, Z, x)
                        )
                    ),
                    _u => objectType(
                        builder,
                        sectionCategoryAt(
                            builder,
                            pathoutCategoryAt(builder, Z, x),
                            E
                        )
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

const pathInductionComponentFunctorType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => builder.pi(
                'E',
                displayedFamilyType(
                    builder,
                    pathoutCategoryAt(builder, Z, x)
                ),
                E => functorType(
                    builder,
                    fibreAt(
                        builder,
                        pathoutCategoryAt(builder, Z, x),
                        E,
                        pathoutReflexiveObjectAt(builder, Z, x)
                    ),
                    sectionCategoryAt(
                        builder,
                        pathoutCategoryAt(builder, Z, x),
                        E
                    )
                ),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const fibreTargetDeclaration: CoreLfTransferDeclaration = Object.freeze({
    order: 0,
    symbol: fibreCovariantTarget,
    type: fibreCovariantTargetType(),
    body: coreLfTransferExplicitBody(fibreCovariantTargetBody()),
    modifiers: modifiers('ordinary', 'transparent'),
    provenance: source('symbol FibCov_target_catd [K : Cat]')
});

const trustedDeclarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: fibreCovariantInternal,
        type: fibreCovariantInternalType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source('constant symbol fib_cov_int')
    }),
    Object.freeze({
        order: 1,
        symbol: fibreCovariantSourceFunctor,
        type: fibreCovariantSourceFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source('symbol fib_cov_src_func [K : Cat]')
    }),
    Object.freeze({
        order: 2,
        symbol: fibreCovariantTransformation,
        type: fibreCovariantTransformationType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source('injective symbol fib_cov_transf [K : Cat]')
    }),
    Object.freeze({
        order: 3,
        symbol: pathInductionSection,
        type: pathInductionSectionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source('symbol path_ind_sec [Z : Cat]')
    }),
    Object.freeze({
        order: 4,
        symbol: pathInductionComponentFunctor,
        type: pathInductionComponentFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source('symbol path_ind_func_fapp0 [Z : Cat]')
    })
]);

const contravariantRepresentableObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const W = builder.capture('W');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const x = builder.capture('x');
    return {
        order: 0,
        id: 'pathind.fixed-source.contravariant-representable-object',
        groupId: 'pathind.fixed-source.prerequisite-projection',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'W',
                type: builder.template(objectType(builder, A))
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
                name: 'x',
                type: builder.template(objectType(builder, B))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            builder.wildcard(oppositeAt(builder, B)),
            builder.global(categoryOfCategories),
            contravariantRepresentableAt(builder, A, W, B, F),
            x
        )),
        right: builder.template(homCategoryAt(
            builder,
            A,
            functorObjectAt(builder, B, A, F, x),
            W
        )),
        provenance: source(
            'rule @fapp0 _ Cat_cat (@hom_con $A $W $B $F) $x'
        )
    };
};

const displayedFunctorObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const objectClassifierAt = (
        target: CoreLfTransferBuilderExpression
    ): CoreLfTransferBuilderExpression =>
        globalCall(builder, objectClassifier, [{
            plicity: 'explicit',
            value: target
        }]);
    return {
        order: 1,
        id: 'pathind.fixed-source.displayed-functor-object',
        groupId: 'pathind.fixed-source.prerequisite-projection',
        clauseOrder: 1,
        sourceOwner: objectClassifier,
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
            }
        ],
        left: builder.pattern(objectClassifierAt(
            displayedFunctorCategoryAt(builder, K, E, D)
        )),
        right: builder.template(objectClassifierAt(transforCategoryAt(
            builder,
            K,
            builder.global(categoryOfCategories),
            E,
            D
        ))),
        provenance: source(
            'rule Obj (@Functord_cat $K $E $D) ' +
                '↪ Obj (@Transf_cat $K Cat_cat $E $D)'
        )
    };
};

const displayedHomObjectFusionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const objectClassifierAt = (
        target: CoreLfTransferBuilderExpression
    ): CoreLfTransferBuilderExpression =>
        globalCall(builder, objectClassifier, [{
            plicity: 'explicit',
            value: target
        }]);
    return {
        order: 2,
        id: 'pathind.fixed-source.displayed-hom-object-fusion',
        groupId: 'pathind.fixed-source.prerequisite-projection',
        clauseOrder: 2,
        sourceOwner: objectClassifier,
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
            }
        ],
        left: builder.pattern(objectClassifierAt(homCategoryAt(
            builder,
            displayedCategoryAt(builder, K),
            E,
            D
        ))),
        right: builder.template(objectClassifierAt(transforCategoryAt(
            builder,
            K,
            builder.global(categoryOfCategories),
            E,
            D
        ))),
        provenance: source(
            'derived TypeScript weak-head fusion of active lines ' +
                '5481 and 9177'
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
    const objectClassifierAt = (
        target: CoreLfTransferBuilderExpression
    ): CoreLfTransferBuilderExpression =>
        globalCall(builder, objectClassifier, [{
            plicity: 'explicit',
            value: target
        }]);
    return {
        order: 3,
        id: 'pathind.fixed-source.transfor-classifier-delta',
        groupId: 'pathind.fixed-source.prerequisite-projection',
        clauseOrder: 3,
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
        right: builder.template(objectClassifierAt(transforCategoryAt(
            builder,
            A,
            B,
            F,
            G
        ))),
        provenance: source(
            'active transparent definition at lines 9150-9151: ' +
                'Transf A B F G ≔ Obj (Transf_cat A B F G)'
        )
    };
};

const fibreCovariantTargetSectionFusionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const x = builder.capture('x');
    const objectClassifierAt = (
        target: CoreLfTransferBuilderExpression
    ): CoreLfTransferBuilderExpression =>
        globalCall(builder, objectClassifier, [{
            plicity: 'explicit',
            value: target
        }]);
    return {
        order: 4,
        id: 'pathind.fixed-source.fib-cov-target-section-fusion',
        groupId: 'pathind.fixed-source.prerequisite-projection',
        clauseOrder: 4,
        sourceOwner: objectClassifier,
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
        left: builder.pattern(objectClassifierAt(functorObjectAt(
            builder,
            K,
            builder.global(categoryOfCategories),
            fibreCovariantTargetAt(builder, K, E),
            x
        ))),
        right: builder.template(objectClassifierAt(transforCategoryAt(
            builder,
            K,
            builder.global(categoryOfCategories),
            representableFamilyAt(builder, K, x),
            E
        ))),
        provenance: source(
            'derived TypeScript weak-head fusion of active lines 5481, ' +
                '7865, 8419, 9177, 13765-13775, and 13923-13928'
        )
    };
};

const fixedEvaluationPostDeltaPresentationFusionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    return {
        order: 5,
        id:
            'pathind.fixed-source.' +
            'fixed-evaluation-post-delta-presentation-fusion',
        groupId: 'pathind.fixed-source.prerequisite-projection',
        clauseOrder: 5,
        sourceOwner: decodeOwner,
        variables: [{
            name: 'K',
            type: builder.template(builder.global(category))
        }],
        left: builder.pattern(objectType(
            builder,
            functorCategoryAt(
                builder,
                functorCategoryAt(
                    builder,
                    K,
                    builder.global(categoryOfCategories)
                ),
                builder.global(categoryOfCategories)
            )
        )),
        right: builder.template(objectType(
            builder,
            functorCategoryAt(
                builder,
                displayedCategoryAt(builder, K),
                builder.global(categoryOfCategories)
            )
        )),
        provenance: source(
            'derived stable post-delta presentation fusion of active lines ' +
                '3316-3317, 5457, and 19067-19072'
        )
    };
};

const fibreCovariantPackageComponentRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const x = builder.capture('x');
    return {
        order: 6,
        id: 'pathind.fixed-source.fib-cov-package-component',
        groupId: 'pathind.fixed-source.fib-cov-projections',
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
        left: builder.pattern(componentAt(
            builder,
            K,
            builder.wildcard(E),
            builder.wildcard(fibreCovariantTargetAt(builder, K, E)),
            x,
            fibreCovariantInternalAt(builder, K, E)
        )),
        right: builder.template(fibreCovariantSourceFunctorAt(
            builder,
            K,
            E,
            x
        )),
        provenance: source(
            'rule @tapp0_fapp0 $K Cat_cat _ _ $x ' +
                '(@fib_cov_int $K $E)'
        )
    };
};

const fibreCovariantComponentObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const x = builder.capture('x');
    const u = builder.capture('u');
    return {
        order: 7,
        id: 'pathind.fixed-source.fib-cov-component-object',
        groupId: 'pathind.fixed-source.fib-cov-projections',
        clauseOrder: 1,
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
                name: 'x',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'u',
                type: builder.template(objectType(
                    builder,
                    fibreAt(builder, K, E, x)
                ))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            fibreAt(builder, K, E, x),
            fibreAt(
                builder,
                K,
                fibreCovariantTargetAt(builder, K, E),
                x
            ),
            fibreCovariantSourceFunctorAt(builder, K, E, x),
            u
        )),
        right: builder.template(fibreCovariantTransformationAt(
            builder,
            K,
            E,
            x,
            u
        )),
        provenance: source(
            'rule fapp0 (@fib_cov_src_func $K $E $x) $u'
        )
    };
};

const fibreCovariantSectionPointRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const x = builder.capture('x');
    const u = builder.capture('u');
    const y = builder.capture('y');
    const represented = representableFamilyAt(builder, K, x);
    return {
        order: 8,
        id: 'pathind.fixed-source.fib-cov-section-point',
        groupId: 'pathind.fixed-source.fib-cov-projections',
        clauseOrder: 2,
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
            },
            {
                name: 'u',
                type: builder.template(objectType(
                    builder,
                    fibreAt(builder, K, E, x)
                ))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(componentAt(
            builder,
            K,
            builder.wildcard(represented),
            builder.wildcard(E),
            y,
            fibreCovariantTransformationAt(builder, K, E, x, u)
        )),
        right: builder.template(covariantFibreActionAt(
            builder,
            K,
            E,
            x,
            y,
            u
        )),
        provenance: source(
            'rule @tapp0_fapp0 $K Cat_cat _ _ $y ' +
                '(@fib_cov_transf $K $E $x $u)'
        )
    };
};

const pathInductionComponentObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const Z = builder.capture('Z');
    const x = builder.capture('x');
    const E = builder.capture('E');
    const u = builder.capture('u');
    const pathout = pathoutCategoryAt(builder, Z, x);
    const reflexive = pathoutReflexiveObjectAt(builder, Z, x);
    return {
        order: 9,
        id: 'pathind.fixed-source.path-ind-section-object-action',
        groupId: 'pathind.fixed-source.path-ind-computation',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'Z',
                type: builder.template(builder.global(category))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, Z))
            },
            {
                name: 'E',
                type: builder.template(displayedFamilyType(builder, pathout))
            },
            {
                name: 'u',
                type: builder.template(objectType(
                    builder,
                    fibreAt(builder, pathout, E, reflexive)
                ))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            fibreAt(builder, pathout, E, reflexive),
            sectionCategoryAt(builder, pathout, E),
            pathInductionComponentFunctorAt(builder, Z, x, E),
            u
        )),
        right: builder.template(pathInductionSectionAt(
            builder,
            Z,
            x,
            E,
            u
        )),
        provenance: source(
            'rule @fapp0 _ _ (@path_ind_func_fapp0 $Z $x $E) $u'
        )
    };
};

const pathInductionPointRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const Z = builder.capture('Z');
    const x = builder.capture('x');
    const E = builder.capture('E');
    const u = builder.capture('u');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const pathout = pathoutCategoryAt(builder, Z, x);
    const reflexive = pathoutReflexiveObjectAt(builder, Z, x);
    const point = sigmaPairPattern(
        builder,
        Z,
        representableFamilyAt(builder, Z, x),
        y,
        p
    );
    const displayedPoint = pathoutObjectAt(builder, Z, x, y, p);
    const targetFibre = fibreAt(builder, pathout, E, displayedPoint);
    const rho = pathoutReflexiveArrowAt(builder, Z, x, y, p);
    const transport = covariantFibreActionAt(
        builder,
        pathout,
        E,
        reflexive,
        displayedPoint,
        u
    );
    return {
        order: 10,
        id: 'pathind.fixed-source.path-ind-point-computation',
        groupId: 'pathind.fixed-source.path-ind-computation',
        clauseOrder: 1,
        sourceOwner: transforComponentCapped,
        variables: [
            {
                name: 'Z',
                type: builder.template(builder.global(category))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, Z))
            },
            {
                name: 'E',
                type: builder.template(displayedFamilyType(builder, pathout))
            },
            {
                name: 'u',
                type: builder.template(objectType(
                    builder,
                    fibreAt(builder, pathout, E, reflexive)
                ))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, Z))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, Z, x, y))
            }
        ],
        left: builder.pattern(componentAt(
            builder,
            pathout,
            constantFamilyAt(
                builder,
                pathout,
                builder.global(terminalCategory)
            ),
            E,
            point,
            pathInductionSectionAt(builder, Z, x, E, u)
        )),
        right: builder.template(pointFunctorAt(
            builder,
            targetFibre,
            functorObjectAt(
                builder,
                homCategoryAt(builder, pathout, reflexive, displayedPoint),
                targetFibre,
                transport,
                rho
            )
        )),
        provenance: source(
            'rule @tapp0_fapp0 (PathOut_cat $Z $x) Cat_cat ' +
                '(Const_catd _ Terminal_cat) $E (Struct_sigma $y $p) ' +
                '(@path_ind_sec $Z $x $E $u)'
        )
    };
};

const pathInductionSigmaPullbackRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const Z = builder.capture('Z');
    const D = builder.capture('D');
    const x = builder.capture('x');
    const u = builder.capture('u');
    const motive = sigmaProjectionPullbackAt(
        builder,
        Z,
        representableFamilyAt(builder, Z, x),
        D
    );
    return {
        order: 11,
        id: 'pathind.fixed-source.path-ind-sigma-pullback-computation',
        groupId: 'pathind.fixed-source.path-ind-computation',
        clauseOrder: 2,
        sourceOwner: pathInductionSection,
        variables: [
            {
                name: 'Z',
                type: builder.template(builder.global(category))
            },
            {
                name: 'D',
                type: builder.template(displayedFamilyType(builder, Z))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, Z))
            },
            {
                name: 'u',
                type: builder.template(objectType(
                    builder,
                    fibreAt(builder, Z, D, x)
                ))
            }
        ],
        left: builder.pattern(pathInductionSectionAt(
            builder,
            Z,
            x,
            motive,
            u
        )),
        right: builder.template(fibreCovariantTransformationAt(
            builder,
            Z,
            D,
            x,
            u
        )),
        provenance: source(
            'rule @path_ind_sec $Z $x ' +
                '(@Sigma_proj1_pullback_catd $Z (@Rep_catd $Z $x) $D) ' +
                '$u'
        )
    };
};

const runtimeRules: readonly CoreLfTransferRuntimeRule[] = Object.freeze([
    contravariantRepresentableObjectRule(),
    displayedFunctorObjectRule(),
    displayedHomObjectFusionRule(),
    transforClassifierDeltaRule(),
    fibreCovariantTargetSectionFusionRule(),
    fixedEvaluationPostDeltaPresentationFusionRule(),
    fibreCovariantPackageComponentRule(),
    fibreCovariantComponentObjectRule(),
    fibreCovariantSectionPointRule(),
    pathInductionComponentObjectRule(),
    pathInductionPointRule(),
    pathInductionSigmaPullbackRule()
]);

const pathoutReflexiveEvaluationType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => functorType(
                builder,
                displayedCategoryAt(
                    builder,
                    pathoutCategoryAt(builder, Z, x)
                ),
                builder.global(categoryOfCategories)
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const pathoutReflexiveEvaluationBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => fixedEvaluationAt(
                builder,
                pathoutCategoryAt(builder, Z, x),
                builder.global(categoryOfCategories),
                pathoutReflexiveObjectAt(builder, Z, x)
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const pathoutReflexiveBaseTransportType =
(): CoreLfTransferExpression => {
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
                    p => builder.pi(
                        'E',
                        displayedFamilyType(
                            builder,
                            pathoutCategoryAt(builder, Z, x)
                        ),
                        E => functorType(
                            builder,
                            fibreAt(
                                builder,
                                pathoutCategoryAt(builder, Z, x),
                                E,
                                pathoutReflexiveObjectAt(builder, Z, x)
                            ),
                            fibreAt(
                                builder,
                                pathoutCategoryAt(builder, Z, x),
                                E,
                                pathoutObjectAt(builder, Z, x, y, p)
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
    ));
};

const pathoutReflexiveBaseTransportBody =
(): CoreLfTransferExpression => {
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
                    p => builder.lam(
                        'E',
                        displayedFamilyType(
                            builder,
                            pathoutCategoryAt(builder, Z, x)
                        ),
                        E => functorHomCappedAt(
                            builder,
                            pathoutCategoryAt(builder, Z, x),
                            builder.global(categoryOfCategories),
                            E,
                            pathoutReflexiveObjectAt(builder, Z, x),
                            pathoutObjectAt(builder, Z, x, y, p),
                            pathoutReflexiveArrowAt(builder, Z, x, y, p)
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
    ));
};

const pathoutReflexiveArrowSectionType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => {
                const pathout = pathoutCategoryAt(builder, Z, x);
                const reflexive = pathoutReflexiveObjectAt(builder, Z, x);
                return objectType(
                    builder,
                    sectionCategoryAt(
                        builder,
                        pathout,
                        representableFamilyAt(builder, pathout, reflexive)
                    )
                );
            },
            explicitMode
        ),
        implicitMode
    ));
};

const pathoutReflexiveArrowSectionBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => {
                const pathout = pathoutCategoryAt(builder, Z, x);
                const reflexive = pathoutReflexiveObjectAt(builder, Z, x);
                return pathInductionSectionAt(
                    builder,
                    Z,
                    x,
                    representableFamilyAt(builder, pathout, reflexive),
                    identityAt(builder, pathout, reflexive)
                );
            },
            explicitMode
        ),
        implicitMode
    ));
};

const pathInductionSourceFamilyType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => displayedFamilyType(
                builder,
                displayedCategoryAt(
                    builder,
                    pathoutCategoryAt(builder, Z, x)
                )
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const pathInductionSourceFamilyBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => pathoutReflexiveEvaluationAt(builder, Z, x),
            explicitMode
        ),
        implicitMode
    ));
};

const pathInductionTargetFamilyBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => sectionCategoryFunctorAt(
                builder,
                pathoutCategoryAt(builder, Z, x)
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
        symbol: pathoutReflexiveEvaluation,
        type: pathoutReflexiveEvaluationType(),
        body: coreLfTransferExplicitBody(
            pathoutReflexiveEvaluationBody()
        ),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol pathout_refl_eval_func [Z : Cat]')
    }),
    Object.freeze({
        order: 1,
        symbol: pathoutReflexiveBaseTransport,
        type: pathoutReflexiveBaseTransportType(),
        body: coreLfTransferExplicitBody(
            pathoutReflexiveBaseTransportBody()
        ),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol pathout_refl_eval_base_func [Z : Cat]'
        )
    }),
    Object.freeze({
        order: 2,
        symbol: pathoutReflexiveArrowSection,
        type: pathoutReflexiveArrowSectionType(),
        body: coreLfTransferExplicitBody(
            pathoutReflexiveArrowSectionBody()
        ),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol pathout_refl_arrow_sec [Z : Cat]')
    }),
    Object.freeze({
        order: 3,
        symbol: pathInductionSourceFamily,
        type: pathInductionSourceFamilyType(),
        body: coreLfTransferExplicitBody(
            pathInductionSourceFamilyBody()
        ),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol PathInd_src_catd [Z : Cat]')
    }),
    Object.freeze({
        order: 4,
        symbol: pathInductionTargetFamily,
        type: pathInductionSourceFamilyType(),
        body: coreLfTransferExplicitBody(
            pathInductionTargetFamilyBody()
        ),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source('symbol PathInd_tgt_catd [Z : Cat]')
    })
]);

const fibreTargetExternalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    displayedFamilyClassifier,
    oppositeCategory,
    contravariantRepresentable,
    internalHom,
    identityFunctor
]);

export const CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: `${CORE_PATHIND_FIXED_SOURCE_1C_REVISION}-FIBRE-TARGET`,
    moduleId: MODULE_ID,
    fragmentId: 'pathind-fixed-source-1c-fibre-target',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_PATHOUT_FOUNDATION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: fibreTargetExternalSymbols.map(target => ({
        symbol: target,
        availability: 'earlier-fragment' as const
    })),
    declarations: [fibreTargetDeclaration],
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_MODULE,
    {
        revision: `${CORE_PATHIND_FIXED_SOURCE_1C_REVISION}-` +
            'FIBRE-TARGET-POLICY-1',
        moduleRevision:
            CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_MODULE.revision,
        entries: [{
            order: 0,
            target: {
                kind: 'declaration' as const,
                symbol: fibreCovariantTarget
            },
            policy: 'checked-transparent-definition' as const,
            evidence:
                'Exact active FibCov target selected by reviewed 1C'
        }]
    }
);

const trustedExternalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    functorClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    displayedFamilyClassifier,
    displayedFunctorClassifier,
    functorObject,
    sectionCategory,
    pathoutCategory,
    pathoutReflexiveObject,
    fibreCovariantTarget
]);

export const CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: `${CORE_PATHIND_FIXED_SOURCE_1C_REVISION}-TRUSTED`,
    moduleId: MODULE_ID,
    fragmentId: 'pathind-fixed-source-1c-trusted',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_PATHOUT_FOUNDATION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: trustedExternalSymbols.map(target => ({
        symbol: target,
        availability: 'earlier-fragment' as const
    })),
    declarations: trustedDeclarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_MODULE,
    {
        revision: `${CORE_PATHIND_FIXED_SOURCE_1C_REVISION}-` +
            'TRUSTED-POLICY-1',
        moduleRevision:
            CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_MODULE.revision,
        entries: trustedDeclarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact active v3.2 opaque interface selected by reviewed ' +
                'PATHIND-TRUSTED-PROFILE-1C proposal v8'
        }))
    }
);

const runtimeExternalSymbols = Object.freeze([
    ...trustedExternalSymbols,
    homClassifier,
    transforClassifier,
    functorCategory,
    oppositeCategory,
    contravariantRepresentable,
    displayedFunctorCategory,
    transforCategory,
    functorHomCapped,
    transforComponentCapped,
    homCategory,
    dependentPair,
    constantDisplayedFamily,
    terminalCategory,
    objectFunctor,
    representableFamily,
    pathoutObject,
    pathoutReflexiveArrow,
    sigmaProjectionPullback,
    covariantFibreAction,
    ...trustedDeclarations.map(declaration => declaration.symbol)
]);

export const CORE_PATHIND_FIXED_SOURCE_1C_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: `${CORE_PATHIND_FIXED_SOURCE_1C_REVISION}-RUNTIME`,
    moduleId: MODULE_ID,
    fragmentId: 'pathind-fixed-source-1c-runtime',
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

export const CORE_PATHIND_FIXED_SOURCE_1C_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_PATHIND_FIXED_SOURCE_1C_RUNTIME_MODULE,
    {
        revision: `${CORE_PATHIND_FIXED_SOURCE_1C_REVISION}-` +
            'RUNTIME-POLICY-1',
        moduleRevision:
            CORE_PATHIND_FIXED_SOURCE_1C_RUNTIME_MODULE.revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence: rule.id ===
                'pathind.fixed-source.displayed-hom-object-fusion'
                ? 'Subject-checked weak-head fusion derived only from ' +
                    'active lines 5481 and 9177 under reviewed proposal v8'
                : rule.id ===
                    'pathind.fixed-source.transfor-classifier-delta'
                    ? 'Active transparent Transf definition at lines ' +
                        '9150-9151 selected by reviewed proposal v8'
                    : rule.id ===
                        'pathind.fixed-source.fib-cov-target-section-fusion'
                        ? 'Subject-checked complete forward fusion of ' +
                            'active FibCov target and section path under ' +
                            'reviewed proposal v8'
                        : rule.id ===
                            'pathind.fixed-source.' +
                                'fixed-evaluation-post-delta-' +
                                'presentation-fusion'
                            ? 'Stable decoded-type fusion of active lines ' +
                                '3316-3317, 5457, and 19067-19072 under ' +
                                'reviewed proposal v8'
                            : 'Exact active v3.2 fixed-source PathInd ' +
                                'computation selected by reviewed proposal v8'
        }))
    }
);

const libraryExternalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    homClassifier,
    functorClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    displayedFamilyClassifier,
    functorObject,
    functorHomCapped,
    sectionCategory,
    sectionCategoryFunctor,
    fixedEvaluation,
    identityArrow,
    representableFamily,
    pathoutCategory,
    pathoutObject,
    pathoutReflexiveObject,
    pathoutReflexiveArrow,
    pathInductionSection
]);

export const CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: `${CORE_PATHIND_FIXED_SOURCE_1C_REVISION}-LIBRARY`,
    moduleId: MODULE_ID,
    fragmentId: 'pathind-fixed-source-1c-library',
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

export const CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_MODULE,
    {
        revision: `${CORE_PATHIND_FIXED_SOURCE_1C_REVISION}-` +
            'LIBRARY-POLICY-1',
        moduleRevision:
            CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_MODULE.revision,
        entries: libraryDeclarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'checked-transparent-definition' as const,
            evidence:
                'Exact active transparent fixed-source definition ' +
                'selected by reviewed proposal v8'
        }))
    }
);

const providerLinks = [
    ...CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_LINKAGE.entries,
    ...CORE_PATHOUT_FOUNDATION_1B_LIBRARY_LINKAGE.entries,
    ...CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE.entries,
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
    order: number,
    localLinks: readonly CoreLfTransferDeclarationLink[] = []
): CoreLfTransferDeclarationLink => {
    const inherited = [...localLinks, ...providerLinks].find(candidate =>
        symbolEquals(candidate.symbol, target)
    );
    if (inherited === undefined) {
        throw new Error(
            `PATHIND-TRUSTED-PROFILE-1C has no dependency link for ` +
                `${target.moduleId}.${target.name}`
        );
    }
    return Object.freeze({
        ...inherited,
        order,
        symbol: Object.freeze({ ...target })
    });
};

const localCoreName = (target: CoreLfQualifiedSymbol): string => {
    const names = new Map<CoreLfQualifiedSymbol, string>([
        [
            fibreCovariantTarget,
            'emdash_v3_2_pathind_fixed_source_FibCov_target_catd'
        ],
        [
            fibreCovariantInternal,
            'emdash_v3_2_pathind_fixed_source_fib_cov_int'
        ],
        [
            fibreCovariantSourceFunctor,
            'emdash_v3_2_pathind_fixed_source_fib_cov_src_func'
        ],
        [
            fibreCovariantTransformation,
            'emdash_v3_2_pathind_fixed_source_fib_cov_transf'
        ],
        [
            pathInductionSection,
            'emdash_v3_2_pathind_fixed_source_path_ind_sec'
        ],
        [
            pathInductionComponentFunctor,
            'emdash_v3_2_pathind_fixed_source_path_ind_func_fapp0'
        ],
        [
            pathoutReflexiveEvaluation,
            'emdash_v3_2_pathind_fixed_source_pathout_refl_eval_func'
        ],
        [
            pathoutReflexiveBaseTransport,
            'emdash_v3_2_pathind_fixed_source_' +
                'pathout_refl_eval_base_func'
        ],
        [
            pathoutReflexiveArrowSection,
            'emdash_v3_2_pathind_fixed_source_pathout_refl_arrow_sec'
        ],
        [
            pathInductionSourceFamily,
            'emdash_v3_2_pathind_fixed_source_PathInd_src_catd'
        ],
        [
            pathInductionTargetFamily,
            'emdash_v3_2_pathind_fixed_source_PathInd_tgt_catd'
        ]
    ]);
    const entry = [...names].find(([candidate]) =>
        symbolEquals(candidate, target)
    );
    if (entry === undefined) {
        throw new Error(`Unknown fixed-source PathInd symbol ${target.name}`);
    }
    return entry[1];
};

const localDeclarationLinks = (
    declarations: readonly CoreLfTransferDeclaration[],
    offset: number
): readonly CoreLfTransferDeclarationLink[] =>
    declarations.map((declaration, index) => Object.freeze({
        order: offset + index,
        symbol: declaration.symbol,
        kind: 'free-declaration' as const,
        coreName: localCoreName(declaration.symbol),
        backendName: declaration.symbol.name
    }));

export const CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_MODULE,
        {
            revision: `${CORE_PATHIND_FIXED_SOURCE_1C_REVISION}-` +
                'FIBRE-TARGET-LINKAGE-1',
            moduleRevision:
                CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_MODULE.revision,
            entries: [
                ...fibreTargetExternalSymbols.map((target, order) =>
                    dependencyLink(target, order)
                ),
                ...localDeclarationLinks(
                    [fibreTargetDeclaration],
                    fibreTargetExternalSymbols.length
                )
            ]
        }
    );

const fibreTargetLocalLinks =
    CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_LINKAGE.entries.filter(entry =>
        symbolEquals(entry.symbol, fibreCovariantTarget)
    );

export const CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_MODULE,
        {
            revision: `${CORE_PATHIND_FIXED_SOURCE_1C_REVISION}-` +
                'TRUSTED-LINKAGE-1',
            moduleRevision:
                CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_MODULE.revision,
            entries: [
                ...trustedExternalSymbols.map((target, order) =>
                    dependencyLink(target, order, fibreTargetLocalLinks)
                ),
                ...localDeclarationLinks(
                    trustedDeclarations,
                    trustedExternalSymbols.length
                )
            ]
        }
    );

const trustedLocalLinks = [
    ...fibreTargetLocalLinks,
    ...CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_LINKAGE.entries.filter(entry =>
        trustedDeclarations.some(declaration =>
            symbolEquals(declaration.symbol, entry.symbol)
        )
    )
];

export const CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_MODULE,
        {
            revision: `${CORE_PATHIND_FIXED_SOURCE_1C_REVISION}-` +
                'LIBRARY-LINKAGE-1',
            moduleRevision:
                CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_MODULE.revision,
            entries: [
                ...libraryExternalSymbols.map((target, order) =>
                    dependencyLink(target, order, trustedLocalLinks)
                ),
                ...localDeclarationLinks(
                    libraryDeclarations,
                    libraryExternalSymbols.length
                )
            ]
        }
    );

export const CORE_PATHIND_FIXED_SOURCE_1C_CORE_NAMES = Object.freeze(
    Object.fromEntries(
        Object.entries(CORE_PATHIND_FIXED_SOURCE_1C_SYMBOLS).map(
            ([id, target]) => [id, localCoreName(target)]
        )
    ) as {
        readonly [
            K in keyof typeof CORE_PATHIND_FIXED_SOURCE_1C_SYMBOLS
        ]: string;
    }
);

export type CorePathindFixedSource1cSymbolId =
    keyof typeof CORE_PATHIND_FIXED_SOURCE_1C_CORE_NAMES;

export function corePathindFixedSource1cCoreName(
    id: CorePathindFixedSource1cSymbolId
): string {
    return CORE_PATHIND_FIXED_SOURCE_1C_CORE_NAMES[id];
}

export type CorePathindOrdinaryLibraryCapability =
    | 'checked-transparent-definition'
    | 'opaque-signature'
    | 'runtime-rewrite'
    | 'proof-unification';

export class CorePathindOrdinaryLibraryCapabilityError extends Error {
    constructor(
        public readonly capability: CorePathindOrdinaryLibraryCapability
    ) {
        super(
            `Ordinary PathInd library code cannot request '${capability}'`
        );
        this.name = 'CorePathindOrdinaryLibraryCapabilityError';
    }
}

export function assertCorePathindOrdinaryLibraryCapability(
    capability: CorePathindOrdinaryLibraryCapability
): 'checked-transparent-definition' {
    if (capability !== 'checked-transparent-definition') {
        throw new CorePathindOrdinaryLibraryCapabilityError(capability);
    }
    return capability;
}

export const CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY =
Object.freeze({
    revision: CORE_PATHIND_FIXED_SOURCE_1C_REVISION,
    reviewedAuthorization:
        'PATHIND-TRUSTED-PROFILE-1C-REVIEWED-8',
    selectedPredecessor: CORE_PATHOUT_FOUNDATION_1B_REVISION,
    trustedDeclarationNames: Object.freeze(
        trustedDeclarations.map(declaration => declaration.symbol.name)
    ),
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    proofRuleIds: Object.freeze([] as string[]),
    transparentDefinitionNames: Object.freeze([
        fibreTargetDeclaration.symbol.name,
        ...libraryDeclarations.map(declaration => declaration.symbol.name)
    ]),
    trustedDeclarationCount: trustedDeclarations.length,
    runtimeRuleCount: runtimeRules.length,
    proofRuleCount: 0,
    transparentDefinitionCount: 1 + libraryDeclarations.length,
    typedLibraryConsumerCount: 1,
    negativeConsumerCount: 8,
    selectedRuntimeObservationCount: 5,
    boundedOracleAssertionCount: 9,
    allEntriesUseGenericTransferEngines: true,
    ordinarySafeLibraryCanAddTransparentDefinitions: true,
    ordinarySafeLibraryCanAddOpaqueOwners: false,
    ordinarySafeLibraryCanAddRuntimeRules: false,
    ordinarySafeLibraryCanAddProofRules: false,
    rootOnlyQualification: true,
    browserOrPublicPackageExported: false,
    PathIndFuncIncluded: false,
    PathIndTransfdIncluded: false,
    internalizedPathInductionIncluded: false,
    transitivityDefinitionsIncluded: false,
    pathCategoryProofBridgeIncluded: false,
    intrinsicCoreOwnerDelta: 0,
    checkerBranchDelta: 0,
    evaluatorBranchDelta: 0,
    activeLambdapiOwnerDelta: 0,
    activeLambdapiRuleDelta: 0
});

export interface CorePathindFixedSource1cCompilation {
    readonly predecessor: CorePathoutFoundation1bCompilation;
    readonly fibreTargetCompiled: CoreLfCompiledDeclarationModule;
    readonly trustedCompiled: CoreLfCompiledDeclarationModule;
    readonly libraryCompiled: CoreLfCompiledDeclarationModule;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation: CorePathindFixedSource1cCompilation | undefined;

export function compileCorePathindFixedSource1cTransfer():
CorePathindFixedSource1cCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    validateCorePathindFixedSource1cReviewV8();
    const predecessor = compileCorePathoutFoundation1bTransfer();
    const fibreTargetCompiled = compileCoreLfDeclarations(
        CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_MODULE,
        CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_POLICY,
        CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_LINKAGE,
        {
            initialEnvironment: predecessor.compiled.environment,
            runtimeProgram: predecessor.composedRuntime,
            comparisonStepLimit: 512
        }
    );
    const fibreTargetContext = new CoreLfMixedDeclarationContext(
        predecessor.declarationContext,
        [fibreTargetCompiled]
    );
    const trustedCompiled = compileCoreLfDeclarations(
        CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_MODULE,
        CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_POLICY,
        CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_LINKAGE,
        {
            initialEnvironment: fibreTargetCompiled.environment,
            runtimeProgram: predecessor.composedRuntime,
            comparisonStepLimit: 512
        }
    );
    const trustedContext = new CoreLfMixedDeclarationContext(
        predecessor.declarationContext,
        [fibreTargetCompiled, trustedCompiled]
    );
    const runtimeFragment = compileCoreLfRuntimeFragment(
        CORE_PATHIND_FIXED_SOURCE_1C_RUNTIME_MODULE,
        CORE_PATHIND_FIXED_SOURCE_1C_RUNTIME_POLICY,
        trustedContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: predecessor.runtimeFragment
            }],
            comparisonStepLimit: 512
        }
    );
    const libraryCompiled = compileCoreLfDeclarations(
        CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_MODULE,
        CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_POLICY,
        CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_LINKAGE,
        {
            initialEnvironment: trustedCompiled.environment,
            runtimeProgram: runtimeFragment.runtime,
            comparisonStepLimit: 512
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        predecessor.declarationContext,
        [fibreTargetCompiled, trustedCompiled, libraryCompiled]
    );
    cachedCompilation = Object.freeze({
        predecessor,
        fibreTargetCompiled,
        trustedCompiled,
        libraryCompiled,
        compiled: libraryCompiled,
        declarationContext,
        runtimeFragment,
        runtime: runtimeFragment.localProgram,
        composedRuntime: runtimeFragment.runtime
    });
    return cachedCompilation;
}
