/**
 * DIRECT-MIXED-INTRODUCTION-1D one-rule generic runtime continuation.
 *
 * The active kernel adds no declaration here.  It only projects the existing
 * covariant action of `Functor_catd(A,-)` to the already transferred
 * Cat-valued postcomposition functor after a fibre functor `H` is consumed.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS
} from './categorical_displayed_nd_higher_foundation_transfer';
import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS
} from './categorical_fibred_product_transfer';
import {
    CORE_CATEGORICAL_MIXED_ACTION_SYMBOLS,
    CoreCategoricalMixedActionCompilation,
    compileCoreCategoricalMixedActionTransfer
} from './categorical_mixed_action_transfer';
import {
    CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256
} from './categorical_mixed_mode_transfer';
import {
    coreDirectedContinuationTransferSymbol
} from './directed_continuation_transfer';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferBuilderExpression,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferRuntimeRule,
    CoreLfTransferScopedBuilder,
    coreLfQualifiedSymbol,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    CoreLfCompiledDeclarationModule
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

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_TRANSFER_REVISION =
    'DIRECT-MIXED-INTRODUCTION-1D-RUNTIME-1' as const;

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner = coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-category-category'
    );
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const transforComponentCapped =
    coreDirectedContinuationTransferSymbol(
        'transfor-component-capped'
    );

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const displayedFamilyClassifier = symbol('Catd');
const displayedFunctorClassifier = symbol('Functord');
const oppositeCategory = symbol('Op_cat');
const functorCategory = symbol('Functor_cat');
const stableFunctorFamily = symbol('Functor_catd');

const {
    identityArrow
} = CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS;
const {
    mixedFunctorFamilyPartial
} = CORE_CATEGORICAL_MIXED_ACTION_SYMBOLS;
const {
    postcompositionAction
} = CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS;

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

const mixedFunctorFamilyPartialAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, mixedFunctorFamilyPartial, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: sourceFamily }
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

const identityCategoryFunctor = (
    builder: CoreLfTransferScopedBuilder
): CoreLfTransferBuilderExpression =>
    globalCall(builder, identityArrow, [
        {
            plicity: 'explicit',
            value: builder.global(categoryOfCategories)
        },
        {
            plicity: 'explicit',
            value: builder.global(categoryOfCategories)
        }
    ]);

const postcompositionAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    middle: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    outer: CoreLfTransferBuilderExpression,
    inner: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, postcompositionAction, [
        {
            plicity: 'implicit',
            value: builder.global(categoryOfCategories)
        },
        {
            plicity: 'implicit',
            value: builder.global(categoryOfCategories)
        },
        { plicity: 'explicit', value: identityCategoryFunctor(builder) },
        { plicity: 'explicit', value: source },
        { plicity: 'implicit', value: middle },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: outer },
        { plicity: 'explicit', value: inner }
    ]);

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const directMixedPostcompositionProjectionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const D = builder.capture('D');
    const G = builder.capture('G');
    const k = builder.capture('k');
    const H = builder.capture('H');
    const displayedK = displayedCategoryAt(builder, K);
    const sourceFibre = fibreAt(
        builder,
        oppositeAt(builder, K),
        A,
        k
    );
    const middleFibre = fibreAt(builder, K, B, k);
    const targetFibre = fibreAt(builder, K, D, k);
    const sourceFunctorCategory = functorCategoryAt(
        builder,
        sourceFibre,
        middleFibre
    );
    const targetFunctorCategory = functorCategoryAt(
        builder,
        sourceFibre,
        targetFibre
    );
    const constructorAction = functorHomCappedAt(
        builder,
        displayedK,
        displayedK,
        mixedFunctorFamilyPartialAt(builder, K, A),
        B,
        D,
        G
    );
    return {
        order: 0,
        id:
            'categorical.direct-mixed-introduction.' +
            'target-postcomposition-projection',
        groupId:
            'categorical.direct-mixed-introduction.' +
            'target-postcomposition-projection',
        clauseOrder: 0,
        sourceOwner: functorObject,
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
                name: 'D',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'G',
                type: builder.template(displayedFunctorType(
                    builder,
                    K,
                    B,
                    D
                ))
            },
            {
                name: 'k',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'H',
                type: builder.template(objectType(
                    builder,
                    sourceFunctorCategory
                ))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            builder.wildcard(sourceFunctorCategory),
            builder.wildcard(targetFunctorCategory),
            componentAt(
                builder,
                K,
                builder.wildcard(stableFunctorFamilyAt(
                    builder,
                    K,
                    A,
                    B
                )),
                builder.wildcard(stableFunctorFamilyAt(
                    builder,
                    K,
                    A,
                    D
                )),
                k,
                constructorAction
            ),
            H
        )),
        right: builder.template(postcompositionAt(
            builder,
            sourceFibre,
            middleFibre,
            targetFibre,
            componentAt(builder, K, B, D, k, G),
            H
        )),
        provenance: source(
            'rule @fapp0 _ _ (@tapp0_fapp0 $K Cat_cat _ _ $k ' +
                '(@fapp1_fapp0 (Catd_cat $K) (Catd_cat $K) ' +
                '(@Functor_catd_fapp0_func $K $A) $B $D $G)) $H'
        )
    };
};

const runtimeRules = Object.freeze([
    directMixedPostcompositionProjectionRule()
]);

export const CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'direct-mixed-introduction-1d-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        categoryOfCategories,
        displayedCategoryCategory,
        functorObject,
        functorHomCapped,
        transforComponentCapped,
        displayedFamilyClassifier,
        displayedFunctorClassifier,
        oppositeCategory,
        functorCategory,
        identityArrow,
        stableFunctorFamily,
        mixedFunctorFamilyPartial,
        postcompositionAction
    ].map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_RUNTIME_MODULE,
    {
        revision: 'DIRECT-MIXED-INTRODUCTION-1D-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_RUNTIME_MODULE
                .revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact D-DTTLF-USABILITY-043 existing-owner projection'
        }))
    }
);

export const CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_BOUNDARY =
Object.freeze({
    decision: 'D-DTTLF-USABILITY-043',
    declarationCount: 0,
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    runtimeRuleCount: runtimeRules.length,
    activeLambdapiOwnerDelta: 0,
    activeLambdapiRuleDelta: 1,
    intrinsicCoreOwnerDelta: 0,
    ownerSpecificCheckerOrEvaluatorDelta: 0,
    externalCoherenceEvidenceDelta: 0,
    contextualBinderDelta: 1,
    textOrBrowserDelta: 0,
    transfersContextualCurry: false,
    allEntriesUseGenericTransferEngines: true
});

export interface CoreCategoricalDirectMixedIntroductionCompilation {
    readonly prerequisite: CoreCategoricalMixedActionCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation:
    CoreCategoricalDirectMixedIntroductionCompilation | undefined;

export function compileCoreCategoricalDirectMixedIntroductionTransfer():
CoreCategoricalDirectMixedIntroductionCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    const prerequisite = compileCoreCategoricalMixedActionTransfer();
    const runtimeFragment = compileCoreLfRuntimeFragment(
        CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_RUNTIME_MODULE,
        CORE_CATEGORICAL_DIRECT_MIXED_INTRODUCTION_RUNTIME_POLICY,
        prerequisite.declarationContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: prerequisite.runtimeFragment
            }],
            comparisonStepLimit: 512
        }
    );
    cachedCompilation = Object.freeze({
        prerequisite,
        compiled: prerequisite.compiled,
        declarationContext: prerequisite.declarationContext,
        runtimeFragment,
        runtime: runtimeFragment.localProgram,
        composedRuntime: runtimeFragment.runtime
    });
    return cachedCompilation;
}
