/**
 * MIXED-NEST-ACTION-0B existing-authority transfer closure.
 *
 * The active Lambdapi kernel already owns the complete direct projection
 * cascade from `homd_int` to the endpoint family `homd_`. This fragment
 * imports the exact nine-declaration dependency closure and the twelve
 * source computation/projection rules. It adds no mathematical owner,
 * intrinsic Core form, checker branch, or external coherence evidence.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE
} from './categorical_displayed_nd_higher_foundation_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_LINKAGE
} from './categorical_displayed_nd_higher_target_transfer';
import {
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_LINKAGE
} from './categorical_fibred_weaken_reindex_transfer';
import {
    CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256,
    CORE_CATEGORICAL_MIXED_MODE_TRANSFER_LINKAGE,
    CoreCategoricalMixedModeCompilation,
    compileCoreCategoricalMixedModeTransfer
} from './categorical_mixed_mode_transfer';
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

export const CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_REVISION =
    'MIXED-NEST-ACTION-0B-GENERIC-TRANSFER-1' as const;

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner =
    coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const functorClassifier =
    coreDirectedContinuationTransferSymbol('functor-classifier');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-category-category'
    );
const constantDisplayedFamily =
    coreDirectedContinuationTransferSymbol(
        'constant-displayed-family'
    );
const sectionCategory =
    coreDirectedContinuationTransferSymbol('section-category');
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const functorHomFull =
    coreDirectedContinuationTransferSymbol('functor-hom-full');
const transforComponentCapped =
    coreDirectedContinuationTransferSymbol(
        'transfor-component-capped'
    );
const homCategory =
    coreDirectedContinuationTransferSymbol('hom-category');

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const displayedFamilyClassifier = symbol('Catd');
const displayedFunctorClassifier = symbol('Functord');
const oppositeCategory = symbol('Op_cat');
const functorCategory = symbol('Functor_cat');
const stableFunctorFamily = symbol('Functor_catd');
const functorComposition = symbol('comp_cat_fapp0');
const functorEvaluation = symbol('fapp0_func');
const objectFunctor = symbol('Obj_func');
const terminalCategory = symbol('Terminal_cat');

const {
    identityArrow,
    displayedOpposite,
    oppositeFunctor,
    displayedOppositeFunctor,
    internalHom,
    mixedFunctorFamily,
    homPresheafFamily,
    displayedHomTarget,
    displayedInternalHom
} = CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS;

export const CORE_CATEGORICAL_MIXED_ACTION_SYMBOLS = Object.freeze({
    contravariantRepresentable: symbol('hom_con'),
    representedHomFamily: symbol('hom_'),
    covariantFibreAction: symbol('fib_cov_tapp0_func'),
    displayedHomEndpoint: symbol('homd_'),
    mixedFunctorFamilyPartial: symbol('Functor_catd_fapp0_func'),
    displayedHomTargetSection: symbol('Homd_target_section_catd'),
    displayedHomSourceFunctor: symbol('homd_src_func'),
    displayedHomSourceSection: symbol('homd_src_sec'),
    displayedHomTargetFunctor: symbol('homd_tgt_func')
});

const {
    contravariantRepresentable,
    representedHomFamily,
    covariantFibreAction,
    displayedHomEndpoint,
    mixedFunctorFamilyPartial,
    displayedHomTargetSection,
    displayedHomSourceFunctor,
    displayedHomSourceSection,
    displayedHomTargetFunctor
} = CORE_CATEGORICAL_MIXED_ACTION_SYMBOLS;

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

const oppositeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, oppositeCategory, [{
        plicity: 'explicit',
        value: base
    }]);

const identityFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, identityArrow, [
        {
            plicity: 'explicit',
            value: builder.global(categoryOfCategories)
        },
        { plicity: 'explicit', value: base }
    ]);

const oppositeFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, oppositeFunctor, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: functor }
    ]);

const displayedOppositeFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedOppositeFunctor, [{
        plicity: 'explicit',
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

const displayedCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedCategoryCategory, [{
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

const sectionCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sectionCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
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

const componentAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression,
    displayedFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, transforComponentCapped, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: point },
        { plicity: 'explicit', value: displayedFunctor }
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

const functorEvaluationAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorEvaluation, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: point }
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

const mixedFunctorFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, mixedFunctorFamily, [{
        plicity: 'explicit',
        value: base
    }]);

const mixedFunctorFamilyPartialAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, mixedFunctorFamilyPartial, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: sourceFamily }
    ]);

const homPresheafFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, homPresheafFamily, [{
        plicity: 'implicit',
        value: base
    }]);

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
    displayedFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedInternalHom, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor }
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

const representedHomFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, representedHomFamily, [
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: source },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: point }
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

const displayedHomEndpointAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    sourceValue: CoreLfTransferBuilderExpression,
    targetPoint: CoreLfTransferBuilderExpression,
    targetValue: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedHomEndpoint, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor },
        { plicity: 'explicit', value: sourcePoint },
        { plicity: 'explicit', value: sourceValue },
        { plicity: 'explicit', value: targetPoint },
        { plicity: 'explicit', value: targetValue }
    ]);

const displayedHomTargetSectionAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedHomTargetSection, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: sourcePoint }
    ]);

const displayedHomSourceFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedHomSourceFunctor, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor },
        { plicity: 'explicit', value: sourcePoint }
    ]);

const displayedHomSourceSectionAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    sourceValue: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedHomSourceSection, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor },
        { plicity: 'explicit', value: sourcePoint },
        { plicity: 'explicit', value: sourceValue }
    ]);

const displayedHomTargetFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    sourceValue: CoreLfTransferBuilderExpression,
    targetPoint: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedHomTargetFunctor, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor },
        { plicity: 'explicit', value: sourcePoint },
        { plicity: 'explicit', value: sourceValue },
        { plicity: 'explicit', value: targetPoint }
    ]);

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const modifiers = (
    rigidity: 'ordinary' | 'injective',
    sourceOpacity: 'opaque' | 'transparent'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity
});

const contravariantRepresentableType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'W',
            objectType(builder, A),
            W => builder.pi(
                'B',
                builder.global(category),
                B => builder.pi(
                    'F',
                    functorType(builder, B, A),
                    () => functorType(
                        builder,
                        oppositeAt(builder, B),
                        builder.global(categoryOfCategories)
                    ),
                    explicitMode
                ),
                implicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const representedHomFamilyType =
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
                    'W',
                    objectType(builder, A),
                    () => functorType(
                        builder,
                        B,
                        builder.global(categoryOfCategories)
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

const covariantFibreActionType =
(): CoreLfTransferExpression => {
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
                    'y',
                    objectType(builder, K),
                    y => builder.pi(
                        'u',
                        objectType(builder, fibreAt(builder, K, E, x)),
                        () => functorType(
                            builder,
                            homCategoryAt(builder, K, x, y),
                            fibreAt(builder, K, E, y)
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
    ));
};

const covariantFibreActionBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'K',
        builder.global(category),
        K => builder.lam(
            'E',
            displayedFamilyType(builder, K),
            E => builder.lam(
                'x',
                objectType(builder, K),
                x => builder.lam(
                    'y',
                    objectType(builder, K),
                    y => builder.lam(
                        'u',
                        objectType(builder, fibreAt(builder, K, E, x)),
                        u => {
                            const sourceFibre =
                                fibreAt(builder, K, E, x);
                            const targetFibre =
                                fibreAt(builder, K, E, y);
                            const fibreFunctorCategory =
                                functorCategoryAt(
                                    builder,
                                    sourceFibre,
                                    targetFibre
                                );
                            return functorCompositionAt(
                                builder,
                                homCategoryAt(builder, K, x, y),
                                fibreFunctorCategory,
                                targetFibre,
                                functorEvaluationAt(
                                    builder,
                                    sourceFibre,
                                    targetFibre,
                                    u
                                ),
                                functorHomFullAt(
                                    builder,
                                    K,
                                    builder.global(
                                        categoryOfCategories
                                    ),
                                    E,
                                    x,
                                    y
                                )
                            );
                        },
                        explicitMode
                    ),
                    implicitMode
                ),
                implicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const displayedHomEndpointType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'D',
            displayedFamilyType(builder, Z),
            D => builder.pi(
                'E',
                displayedFamilyType(builder, Z),
                E => builder.pi(
                    'FF',
                    displayedFunctorType(builder, Z, D, E),
                    FF => builder.pi(
                        'x',
                        objectType(builder, Z),
                        x => builder.pi(
                            'u',
                            objectType(
                                builder,
                                fibreAt(builder, Z, E, x)
                            ),
                            u => builder.pi(
                                'y',
                                objectType(builder, Z),
                                y => builder.pi(
                                    'v',
                                    objectType(
                                        builder,
                                        fibreAt(builder, Z, D, y)
                                    ),
                                    () => functorType(
                                        builder,
                                        oppositeAt(
                                            builder,
                                            homCategoryAt(
                                                builder,
                                                Z,
                                                x,
                                                y
                                            )
                                        ),
                                        builder.global(
                                            categoryOfCategories
                                        )
                                    ),
                                    explicitMode
                                ),
                                explicitMode
                            ),
                            explicitMode
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

const displayedHomEndpointBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'D',
            displayedFamilyType(builder, Z),
            D => builder.lam(
                'E',
                displayedFamilyType(builder, Z),
                E => builder.lam(
                    'FF',
                    displayedFunctorType(builder, Z, D, E),
                    FF => builder.lam(
                        'x',
                        objectType(builder, Z),
                        x => builder.lam(
                            'u',
                            objectType(
                                builder,
                                fibreAt(builder, Z, E, x)
                            ),
                            u => builder.lam(
                                'y',
                                objectType(builder, Z),
                                y => builder.lam(
                                    'v',
                                    objectType(
                                        builder,
                                        fibreAt(builder, Z, D, y)
                                    ),
                                    v => {
                                        const sourceFibre =
                                            fibreAt(builder, Z, D, y);
                                        const targetFibre =
                                            fibreAt(builder, Z, E, y);
                                        const component = componentAt(
                                            builder,
                                            Z,
                                            builder.global(
                                                categoryOfCategories
                                            ),
                                            D,
                                            E,
                                            y,
                                            FF
                                        );
                                        return contravariantRepresentableAt(
                                            builder,
                                            targetFibre,
                                            functorObjectAt(
                                                builder,
                                                sourceFibre,
                                                targetFibre,
                                                component,
                                                v
                                            ),
                                            homCategoryAt(
                                                builder,
                                                Z,
                                                x,
                                                y
                                            ),
                                            covariantFibreActionAt(
                                                builder,
                                                Z,
                                                E,
                                                x,
                                                y,
                                                u
                                            )
                                        );
                                    },
                                    explicitMode
                                ),
                                explicitMode
                            ),
                            explicitMode
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

const mixedFunctorFamilyPartialType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'A',
            displayedFamilyType(builder, oppositeAt(builder, K)),
            () => functorType(
                builder,
                displayedCategoryAt(builder, K),
                displayedCategoryAt(builder, K)
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const displayedHomTargetSectionType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'E',
            displayedFamilyType(builder, Z),
            E => builder.pi(
                'x',
                objectType(builder, Z),
                () => displayedFamilyType(
                    builder,
                    oppositeAt(builder, Z)
                ),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const displayedHomTargetSectionBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'E',
            displayedFamilyType(builder, Z),
            E => builder.lam(
                'x',
                objectType(builder, Z),
                x => stableFunctorFamilyAt(
                    builder,
                    oppositeAt(builder, Z),
                    E,
                    functorObjectAt(
                        builder,
                        Z,
                        displayedCategoryAt(
                            builder,
                            oppositeAt(builder, Z)
                        ),
                        homPresheafFamilyAt(builder, Z),
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

const displayedHomSourceFunctorType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'D',
            displayedFamilyType(builder, Z),
            D => builder.pi(
                'E',
                displayedFamilyType(builder, Z),
                E => builder.pi(
                    'FF',
                    displayedFunctorType(builder, Z, D, E),
                    () => builder.pi(
                        'x',
                        objectType(builder, Z),
                        x => functorType(
                            builder,
                            fibreAt(
                                builder,
                                Z,
                                displayedOppositeAt(builder, Z, E),
                                x
                            ),
                            sectionCategoryAt(
                                builder,
                                oppositeAt(builder, Z),
                                displayedHomTargetSectionAt(
                                    builder,
                                    Z,
                                    D,
                                    x
                                )
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

const displayedHomSourceSectionType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'D',
            displayedFamilyType(builder, Z),
            D => builder.pi(
                'E',
                displayedFamilyType(builder, Z),
                E => builder.pi(
                    'FF',
                    displayedFunctorType(builder, Z, D, E),
                    FF => builder.pi(
                        'x',
                        objectType(builder, Z),
                        x => builder.pi(
                            'u',
                            objectType(
                                builder,
                                fibreAt(builder, Z, E, x)
                            ),
                            () => objectType(
                                builder,
                                sectionCategoryAt(
                                    builder,
                                    oppositeAt(builder, Z),
                                    displayedHomTargetSectionAt(
                                        builder,
                                        Z,
                                        D,
                                        x
                                    )
                                )
                            ),
                            explicitMode
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

const displayedHomTargetFunctorType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'D',
            displayedFamilyType(builder, Z),
            D => builder.pi(
                'E',
                displayedFamilyType(builder, Z),
                E => builder.pi(
                    'FF',
                    displayedFunctorType(builder, Z, D, E),
                    FF => builder.pi(
                        'x',
                        objectType(builder, Z),
                        x => builder.pi(
                            'u',
                            objectType(
                                builder,
                                fibreAt(builder, Z, E, x)
                            ),
                            () => builder.pi(
                                'y',
                                objectType(builder, Z),
                                y => functorType(
                                    builder,
                                    fibreAt(builder, Z, D, y),
                                    functorCategoryAt(
                                        builder,
                                        oppositeAt(
                                            builder,
                                            homCategoryAt(
                                                builder,
                                                Z,
                                                x,
                                                y
                                            )
                                        ),
                                        builder.global(
                                            categoryOfCategories
                                        )
                                    )
                                ),
                                explicitMode
                            ),
                            explicitMode
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

const declarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: contravariantRepresentable,
        type: contravariantRepresentableType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol hom_con [A : Cat] ' +
                '(W : τ (Obj A)) [B : Cat]'
        )
    }),
    Object.freeze({
        order: 1,
        symbol: representedHomFamily,
        type: representedHomFamilyType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol hom_ [A B : Cat] ' +
                '(F : τ (Functor B A))'
        )
    }),
    Object.freeze({
        order: 2,
        symbol: covariantFibreAction,
        type: covariantFibreActionType(),
        body: coreLfTransferExplicitBody(
            covariantFibreActionBody()
        ),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol fib_cov_tapp0_func [K : Cat] ' +
                '(E : τ (Catd K))'
        )
    }),
    Object.freeze({
        order: 3,
        symbol: displayedHomEndpoint,
        type: displayedHomEndpointType(),
        body: coreLfTransferExplicitBody(
            displayedHomEndpointBody()
        ),
        modifiers: modifiers('injective', 'transparent'),
        provenance: source(
            'injective symbol homd_ [Z : Cat] ' +
                '[D E : τ (Catd Z)]'
        )
    }),
    Object.freeze({
        order: 4,
        symbol: mixedFunctorFamilyPartial,
        type: mixedFunctorFamilyPartialType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Functor_catd_fapp0_func [K : Cat] ' +
                '(A : τ (Catd (Op_cat K)))'
        )
    }),
    Object.freeze({
        order: 5,
        symbol: displayedHomTargetSection,
        type: displayedHomTargetSectionType(),
        body: coreLfTransferExplicitBody(
            displayedHomTargetSectionBody()
        ),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol Homd_target_section_catd [Z : Cat] ' +
                '(E : τ (Catd Z))'
        )
    }),
    Object.freeze({
        order: 6,
        symbol: displayedHomSourceFunctor,
        type: displayedHomSourceFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol homd_src_func [Z : Cat] ' +
                '[D E : τ (Catd Z)]'
        )
    }),
    Object.freeze({
        order: 7,
        symbol: displayedHomSourceSection,
        type: displayedHomSourceSectionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol homd_src_sec [Z : Cat] ' +
                '[D E : τ (Catd Z)]'
        )
    }),
    Object.freeze({
        order: 8,
        symbol: displayedHomTargetFunctor,
        type: displayedHomTargetFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol homd_tgt_func [Z : Cat] ' +
                '[D E : τ (Catd Z)]'
        )
    })
]);

const externalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    functorClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    constantDisplayedFamily,
    sectionCategory,
    functorObject,
    functorHomFull,
    transforComponentCapped,
    homCategory,
    displayedFamilyClassifier,
    displayedFunctorClassifier,
    oppositeCategory,
    functorCategory,
    stableFunctorFamily,
    mixedFunctorFamily,
    functorComposition,
    functorEvaluation,
    objectFunctor,
    terminalCategory,
    identityArrow,
    displayedOpposite,
    oppositeFunctor,
    displayedOppositeFunctor,
    internalHom,
    homPresheafFamily,
    displayedHomTarget,
    displayedInternalHom
]);

export const CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'mixed-nest-action-0b-signatures',
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

export const CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_MODULE,
    {
        revision: 'MIXED-NEST-ACTION-0B-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_MODULE.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: declaration.body.kind === 'explicit-term'
                ? 'checked-transparent-definition' as const
                : 'opaque-signature' as const,
            evidence:
                'Exact active v3.2 existing-authority homd action ' +
                'declaration selected by the approved mixed-action plan'
        }))
    }
);

const prerequisiteLinks = [
    ...CORE_CATEGORICAL_MIXED_MODE_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE
        .entries,
    ...CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_TARGET_TRANSFER_LINKAGE
        .entries,
    ...CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_LINKAGE.entries,
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
            `MIXED-NEST-ACTION-0B has no dependency link for ` +
                target.name
        );
    }
    return Object.freeze({
        ...inherited,
        order,
        symbol: Object.freeze({ ...target })
    });
};

const mixedActionCoreName = (
    target: CoreLfQualifiedSymbol
): string =>
    `emdash_v3_2_mixed_nest_action_0b_${target.name}`;

export const CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_MODULE,
        {
            revision: 'MIXED-NEST-ACTION-0B-SIGNATURE-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_MODULE.revision,
            entries: [
                ...externalSymbols.map(dependencyLink),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName: mixedActionCoreName(declaration.symbol),
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

const functorClassifierDefinitionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    return {
        order: 0,
        id:
            'categorical.mixed-action.' +
            'functor-classifier-definition',
        groupId:
            'categorical.mixed-action.' +
            'functor-classifier-definition',
        clauseOrder: 0,
        sourceOwner: decodeOwner,
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
        left: builder.pattern(functorType(builder, A, B)),
        right: builder.template(objectType(
            builder,
            functorCategoryAt(builder, A, B)
        )),
        provenance: source(
            'injective symbol Functor (A B : Cat) : Grpd ' +
                '≔ Obj (Functor_cat A B)'
        )
    };
};

const oppositeFunctorObjectProjectionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const x = builder.capture('x');
    return {
        order: 2,
        id:
            'categorical.mixed-action.' +
            'opposite-functor-object-projection',
        groupId:
            'categorical.mixed-action.' +
            'hom-presheaf-projections',
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
                type: builder.template(functorType(builder, A, B))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, A))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            builder.wildcard(oppositeAt(builder, A)),
            builder.wildcard(oppositeAt(builder, B)),
            oppositeFunctorAt(builder, A, B, F),
            x
        )),
        right: builder.template(functorObjectAt(
            builder,
            A,
            B,
            F,
            x
        )),
        provenance: source(
            'rule @fapp0 _ _ (@Op_func $A $B $F) $xA ' +
                '↪ @fapp0 $A $B $F $xA'
        )
    };
};

const displayedOppositeFunctorObjectProjectionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    return {
        order: 1,
        id:
            'categorical.mixed-action.' +
            'displayed-opposite-functor-object-projection',
        groupId:
            'categorical.mixed-action.' +
            'hom-presheaf-projections',
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
            displayedCategoryAt(builder, K),
            displayedOppositeFunctorAt(builder, K),
            E
        )),
        right: builder.template(displayedOppositeAt(
            builder,
            K,
            E
        )),
        provenance: source(
            'rule @fapp0 _ _ (@Op_catd_func $K) $E ' +
                '↪ @Op_catd $K $E'
        )
    };
};

const internalHomObjectProjectionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const W = builder.capture('W');
    return {
        order: 3,
        id:
            'categorical.mixed-action.' +
            'internal-hom-object-projection',
        groupId:
            'categorical.mixed-action.' +
            'hom-presheaf-projections',
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
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            oppositeAt(builder, A),
            displayedCategoryAt(builder, B),
            internalHomAt(builder, A, B, F),
            W
        )),
        right: builder.template(representedHomFamilyAt(
            builder,
            A,
            B,
            F,
            W
        )),
        provenance: source(
            'rule @fapp0 _ _ (@hom_int $A $B $F) $W ' +
                '↪ @hom_ $A $B $F $W'
        )
    };
};

const representedHomObjectProjectionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const W = builder.capture('W');
    const y = builder.capture('y');
    return {
        order: 4,
        id:
            'categorical.mixed-action.' +
            'represented-hom-object-projection',
        groupId:
            'categorical.mixed-action.' +
            'hom-presheaf-projections',
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
                name: 'W',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, B))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            B,
            builder.global(categoryOfCategories),
            representedHomFamilyAt(builder, A, B, F, W),
            y
        )),
        right: builder.template(homCategoryAt(
            builder,
            A,
            W,
            functorObjectAt(builder, B, A, F, y)
        )),
        provenance: source(
            'rule @fapp0 $B Cat_cat (@hom_ $A $B $F $W) $y ' +
                '↪ Hom_cat $A $W (@fapp0 $B $A $F $y)'
        )
    };
};

const identityFunctorObjectProjectionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const x = builder.capture('x');
    return {
        order: 5,
        id:
            'categorical.mixed-action.' +
            'identity-functor-object-projection',
        groupId:
            'categorical.mixed-action.' +
            'hom-presheaf-projections',
        clauseOrder: 4,
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
        left: builder.pattern(functorObjectAt(
            builder,
            A,
            A,
            identityFunctorAt(builder, A),
            x
        )),
        right: builder.template(x),
        provenance: source(
            'rule @fapp0 $A $A (@id Cat_cat $A) $xA ↪ $xA'
        )
    };
};

const mixedFunctorFirstProjectionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const oppositeK = oppositeAt(builder, K);
    const displayedK = displayedCategoryAt(builder, K);
    const sourceCategory = oppositeAt(
        builder,
        displayedCategoryAt(builder, oppositeK)
    );
    const targetCategory = functorCategoryAt(
        builder,
        displayedK,
        displayedK
    );
    return {
        order: 6,
        id:
            'categorical.mixed-action.' +
            'mixed-functor-first-projection',
        groupId:
            'categorical.mixed-action.' +
            'mixed-functor-constructor-projections',
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
                    displayedFamilyType(builder, oppositeK)
                )
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            builder.wildcard(sourceCategory),
            builder.wildcard(targetCategory),
            mixedFunctorFamilyAt(builder, K),
            A
        )),
        right: builder.template(mixedFunctorFamilyPartialAt(
            builder,
            K,
            A
        )),
        provenance: source(
            'rule @fapp0 _ _ (@Functor_catd_func $K) $A ' +
                '↪ @Functor_catd_fapp0_func $K $A'
        )
    };
};

const mixedFunctorSecondProjectionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const displayedK = displayedCategoryAt(builder, K);
    return {
        order: 7,
        id:
            'categorical.mixed-action.' +
            'mixed-functor-second-projection',
        groupId:
            'categorical.mixed-action.' +
            'mixed-functor-constructor-projections',
        clauseOrder: 1,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'A',
                type: builder.template(
                    displayedFamilyType(
                        builder,
                        oppositeAt(builder, K)
                    )
                )
            },
            {
                name: 'B',
                type: builder.template(
                    displayedFamilyType(builder, K)
                )
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            displayedK,
            displayedK,
            mixedFunctorFamilyPartialAt(builder, K, A),
            B
        )),
        right: builder.template(stableFunctorFamilyAt(
            builder,
            K,
            A,
            B
        )),
        provenance: source(
            'rule @fapp0 _ _ ' +
                '(@Functor_catd_fapp0_func $K $A) $B ' +
                '↪ @Functor_catd $K $A $B'
        )
    };
};

const firstProjectionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const Z = builder.capture('Z');
    const D = builder.capture('D');
    const E = builder.capture('E');
    const FF = builder.capture('FF');
    const x = builder.capture('x');
    return {
        order: 8,
        id: 'categorical.mixed-action.homd-first-projection',
        groupId: 'categorical.mixed-action.homd-first-projection',
        clauseOrder: 0,
        sourceOwner: transforComponentCapped,
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
                name: 'E',
                type: builder.template(displayedFamilyType(builder, Z))
            },
            {
                name: 'FF',
                type: builder.template(
                    displayedFunctorType(builder, Z, D, E)
                )
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, Z))
            }
        ],
        left: builder.pattern(componentAt(
            builder,
            Z,
            builder.global(categoryOfCategories),
            builder.wildcard(displayedOppositeAt(builder, Z, E)),
            builder.wildcard(displayedHomTargetAt(builder, Z, D)),
            x,
            displayedInternalHomAt(builder, Z, D, E, FF)
        )),
        right: builder.template(displayedHomSourceFunctorAt(
            builder,
            Z,
            D,
            E,
            FF,
            x
        )),
        provenance: source(
            'rule @tapp0_fapp0 $Z Cat_cat _ _ $x ' +
                '(@homd_int $Z $D $E $FF)'
        )
    };
};

const secondProjectionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const Z = builder.capture('Z');
    const D = builder.capture('D');
    const E = builder.capture('E');
    const FF = builder.capture('FF');
    const x = builder.capture('x');
    const u = builder.capture('u');
    return {
        order: 9,
        id: 'categorical.mixed-action.homd-second-projection',
        groupId: 'categorical.mixed-action.homd-second-projection',
        clauseOrder: 0,
        sourceOwner: functorObject,
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
                name: 'E',
                type: builder.template(displayedFamilyType(builder, Z))
            },
            {
                name: 'FF',
                type: builder.template(
                    displayedFunctorType(builder, Z, D, E)
                )
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, Z))
            },
            {
                name: 'u',
                type: builder.template(
                    objectType(builder, fibreAt(builder, Z, E, x))
                )
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            fibreAt(
                builder,
                Z,
                displayedOppositeAt(builder, Z, E),
                x
            ),
            sectionCategoryAt(
                builder,
                oppositeAt(builder, Z),
                displayedHomTargetSectionAt(builder, Z, D, x)
            ),
            displayedHomSourceFunctorAt(builder, Z, D, E, FF, x),
            u
        )),
        right: builder.template(displayedHomSourceSectionAt(
            builder,
            Z,
            D,
            E,
            FF,
            x,
            u
        )),
        provenance: source(
            'rule fapp0 (@homd_src_func $Z $D $E $FF $x) $u'
        )
    };
};

const thirdProjectionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const Z = builder.capture('Z');
    const D = builder.capture('D');
    const E = builder.capture('E');
    const FF = builder.capture('FF');
    const x = builder.capture('x');
    const u = builder.capture('u');
    const y = builder.capture('y');
    const targetSection =
        displayedHomTargetSectionAt(builder, Z, D, x);
    const oppositeZ = oppositeAt(builder, Z);
    const sourceSection = constantFamilyAt(
        builder,
        oppositeZ,
        builder.global(terminalCategory)
    );
    const targetFibre = fibreAt(
        builder,
        oppositeAt(builder, Z),
        targetSection,
        y
    );
    return {
        order: 10,
        id: 'categorical.mixed-action.homd-third-projection',
        groupId: 'categorical.mixed-action.homd-third-projection',
        clauseOrder: 0,
        sourceOwner: transforComponentCapped,
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
                name: 'E',
                type: builder.template(displayedFamilyType(builder, Z))
            },
            {
                name: 'FF',
                type: builder.template(
                    displayedFunctorType(builder, Z, D, E)
                )
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, Z))
            },
            {
                name: 'u',
                type: builder.template(
                    objectType(builder, fibreAt(builder, Z, E, x))
                )
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, Z))
            }
        ],
        left: builder.pattern(componentAt(
            builder,
            builder.wildcard(oppositeZ),
            builder.global(categoryOfCategories),
            builder.wildcard(sourceSection),
            builder.wildcard(targetSection),
            y,
            displayedHomSourceSectionAt(
                builder,
                Z,
                D,
                E,
                FF,
                x,
                u
            )
        )),
        right: builder.template(pointFunctorAt(
            builder,
            targetFibre,
            displayedHomTargetFunctorAt(
                builder,
                Z,
                D,
                E,
                FF,
                x,
                u,
                y
            )
        )),
        provenance: source(
            'rule @tapp0_fapp0 _ Cat_cat _ _ $y ' +
                '(@homd_src_sec $Z $D $E $FF $x $u)'
        )
    };
};

const finalProjectionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const Z = builder.capture('Z');
    const D = builder.capture('D');
    const E = builder.capture('E');
    const FF = builder.capture('FF');
    const x = builder.capture('x');
    const u = builder.capture('u');
    const y = builder.capture('y');
    const v = builder.capture('v');
    const sourceFibre = fibreAt(builder, Z, D, y);
    const targetCategory = functorCategoryAt(
        builder,
        oppositeAt(builder, homCategoryAt(builder, Z, x, y)),
        builder.global(categoryOfCategories)
    );
    return {
        order: 11,
        id: 'categorical.mixed-action.homd-final-projection',
        groupId: 'categorical.mixed-action.homd-final-projection',
        clauseOrder: 0,
        sourceOwner: functorObject,
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
                name: 'E',
                type: builder.template(displayedFamilyType(builder, Z))
            },
            {
                name: 'FF',
                type: builder.template(
                    displayedFunctorType(builder, Z, D, E)
                )
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, Z))
            },
            {
                name: 'u',
                type: builder.template(
                    objectType(builder, fibreAt(builder, Z, E, x))
                )
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, Z))
            },
            {
                name: 'v',
                type: builder.template(
                    objectType(builder, sourceFibre)
                )
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            sourceFibre,
            targetCategory,
            displayedHomTargetFunctorAt(
                builder,
                Z,
                D,
                E,
                FF,
                x,
                u,
                y
            ),
            v
        )),
        right: builder.template(displayedHomEndpointAt(
            builder,
            Z,
            D,
            E,
            FF,
            x,
            u,
            y,
            v
        )),
        provenance: source(
            'rule fapp0 ' +
                '(@homd_tgt_func $Z $D $E $FF $x $u $y) $v'
        )
    };
};

const runtimeRules = Object.freeze([
    functorClassifierDefinitionRule(),
    displayedOppositeFunctorObjectProjectionRule(),
    oppositeFunctorObjectProjectionRule(),
    internalHomObjectProjectionRule(),
    representedHomObjectProjectionRule(),
    identityFunctorObjectProjectionRule(),
    mixedFunctorFirstProjectionRule(),
    mixedFunctorSecondProjectionRule(),
    firstProjectionRule(),
    secondProjectionRule(),
    thirdProjectionRule(),
    finalProjectionRule()
]);

export const CORE_CATEGORICAL_MIXED_ACTION_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'MIXED-NEST-ACTION-0B-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'mixed-nest-action-0b-runtime',
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

export const CORE_CATEGORICAL_MIXED_ACTION_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_MIXED_ACTION_RUNTIME_MODULE,
    {
        revision: 'MIXED-NEST-ACTION-0B-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_MIXED_ACTION_RUNTIME_MODULE.revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact active v3.2 existing-authority homd projection ' +
                'selected by the approved mixed-action plan'
        }))
    }
);

export const CORE_CATEGORICAL_MIXED_ACTION_CORE_NAMES =
Object.freeze(
    Object.fromEntries(
        Object.entries(CORE_CATEGORICAL_MIXED_ACTION_SYMBOLS)
            .map(([id, target]) => [id, mixedActionCoreName(target)])
    ) as {
        readonly [
            K in keyof typeof CORE_CATEGORICAL_MIXED_ACTION_SYMBOLS
        ]: string;
    }
);

export type CoreCategoricalMixedActionSymbolId =
    keyof typeof CORE_CATEGORICAL_MIXED_ACTION_CORE_NAMES;

export function coreCategoricalMixedActionCoreName(
    id: CoreCategoricalMixedActionSymbolId
): string {
    return CORE_CATEGORICAL_MIXED_ACTION_CORE_NAMES[id];
}

export const CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY =
Object.freeze({
    revision: CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_REVISION,
    decision: 'D-DTTLF-USABILITY-023-delegated-approval-2026-07-31',
    declarationNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    transparentDefinitionNames: Object.freeze(
        declarations
            .filter(declaration =>
                declaration.body.kind === 'explicit-term'
            )
            .map(declaration => declaration.symbol.name)
    ),
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    reusedProofRuleIds: Object.freeze([]),
    declarationCount: declarations.length,
    runtimeRuleCount: runtimeRules.length,
    proofRuleCount: 0,
    reusedProofRuleCount: 0,
    activeLambdapiOwnerDelta: 0,
    activeLambdapiRuleDelta: 0,
    intrinsicCoreOwnerDelta: 0,
    ownerSpecificCheckerOrEvaluatorDelta: 0,
    externalCoherenceEvidenceDelta: 0,
    nestedAbstractionLowererDelta: 0,
    textOrBrowserDelta: 0,
    allEntriesUseGenericTransferEngines: true
});

export interface CoreCategoricalMixedActionCompilation {
    readonly prerequisite: CoreCategoricalMixedModeCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation:
    CoreCategoricalMixedActionCompilation | undefined;

export function compileCoreCategoricalMixedActionTransfer():
CoreCategoricalMixedActionCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    const prerequisite = compileCoreCategoricalMixedModeTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_MODULE,
        CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_POLICY,
        CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_LINKAGE,
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
        CORE_CATEGORICAL_MIXED_ACTION_RUNTIME_MODULE,
        CORE_CATEGORICAL_MIXED_ACTION_RUNTIME_POLICY,
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
        CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_MODULE,
        CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_POLICY,
        CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_LINKAGE,
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
