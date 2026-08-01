/**
 * DIRECT-MIXED-WEAKENING-1J generic transfer.
 *
 * This fragment transfers the direct displayed weakening
 * `Functor_catd_const_funcd : Functord B (Functor_catd A B)` and the one
 * pre-existing generic `hom_postcomp_func` signature used by its transparent
 * full-action normal form. The direct nested binder remains the introduction
 * mechanism; no contextual curry or total-context section is involved.
 */

import {
    CoreCategoricalDirectMixedProductDistributionCompilation,
    CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_LINKAGE,
    compileCoreCategoricalDirectMixedProductDistributionTransfer
} from './categorical_direct_mixed_product_distribution_transfer';
import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE
} from './categorical_fibred_product_transfer';
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

export const CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_REVISION =
    'DIRECT-MIXED-WEAKENING-1J-GENERIC-TRANSFER-1' as const;

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
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

const displayedFunctorClassifier = symbol('Functord');
const oppositeCategory = symbol('Op_cat');
const stableFunctorFamily = symbol('Functor_catd');

const {
    functorCategory,
    identityFunctor,
    functorComposition,
    constantFunctorAbstraction
} = CORE_CATEGORICAL_STRUCTURAL_SYMBOLS;

export const CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_SYMBOLS =
Object.freeze({
    homPostcomposition: symbol('hom_postcomp_func'),
    weakening: symbol('Functor_catd_const_funcd')
});

const {
    homPostcomposition,
    weakening
} = CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_SYMBOLS;

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

const identityFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, identityFunctor, [{
        plicity: 'implicit',
        value: base
    }]);

const constantFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, constantFunctorAbstraction, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target }
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

const homPostcompositionAt = (
    builder: CoreLfTransferScopedBuilder,
    targetCategory: CoreLfTransferBuilderExpression,
    sourceCategory: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    fixedSource: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, homPostcomposition, [
        { plicity: 'implicit', value: targetCategory },
        { plicity: 'implicit', value: sourceCategory },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: fixedSource },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: arrow }
    ]);

const weakeningAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, weakening, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily }
    ]);

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const homPostcompositionType = (): CoreLfTransferExpression => {
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

const weakeningType = (): CoreLfTransferExpression => {
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
                B => displayedFunctorType(
                    builder,
                    K,
                    B,
                    stableFunctorFamilyAt(builder, K, A, B)
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
        symbol: homPostcomposition,
        type: homPostcompositionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'ordinary',
            sourceOpacity: 'opaque'
        },
        provenance: source('symbol hom_postcomp_func [A B : Cat]')
    },
    {
        order: 1,
        symbol: weakening,
        type: weakeningType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'injective',
            sourceOpacity: 'opaque'
        },
        provenance: source(
            'injective symbol Functor_catd_const_funcd [K : Cat]'
        )
    }
]);

const externalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    functorClassifier,
    homClassifier,
    homCategory,
    categoryOfCategories,
    displayedCategoryCategory,
    functorObject,
    functorHomFull,
    functorHomCapped,
    transforComponentCapped,
    transforHomFull,
    transforHomCapped,
    displayedFunctorClassifier,
    oppositeCategory,
    stableFunctorFamily,
    functorCategory,
    identityFunctor,
    functorComposition,
    constantFunctorAbstraction
]);

export const CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'direct-mixed-weakening-1j-signatures',
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

export const CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_MODULE,
    {
        revision: 'DIRECT-MIXED-WEAKENING-1J-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_MODULE.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence: declaration.symbol.name === 'hom_postcomp_func'
                ? 'Pre-existing generic full-action prerequisite'
                : 'Exact D-DTTLF-USABILITY-050 active injective owner'
        }))
    }
);

const dependencyLinks = Object.freeze([
    ...CORE_CATEGORICAL_DIRECT_MIXED_PRODUCT_DISTRIBUTION_TRANSFER_LINKAGE
        .entries,
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
            'DIRECT-MIXED-WEAKENING-1J has no dependency link for ' +
                `${target.moduleId}.${target.name}`
        );
    }
    return Object.freeze({
        ...link,
        order,
        symbol: Object.freeze({ ...link.symbol })
    });
};

export const CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage = createCoreLfTransferDeclarationLinkage(
    CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_MODULE,
    {
        revision: 'DIRECT-MIXED-WEAKENING-1J-LINKAGE-1',
        moduleRevision:
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_MODULE.revision,
        entries: [
            ...externalSymbols.map(dependencyLink),
            {
                order: externalSymbols.length,
                symbol: homPostcomposition,
                kind: 'free-declaration' as const,
                coreName:
                    'emdash_v3_2_direct_mixed_weakening_1j_' +
                    'hom_postcomp_func',
                backendName: homPostcomposition.name
            },
            {
                order: externalSymbols.length + 1,
                symbol: weakening,
                kind: 'free-declaration' as const,
                coreName:
                    'emdash_v3_2_direct_mixed_weakening_1j_' +
                    'Functor_catd_const_funcd',
                backendName: weakening.name
            }
        ]
    }
);

const pointRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const k = builder.capture('k');
    const cat = builder.global(categoryOfCategories);
    const target = stableFunctorFamilyAt(builder, K, A, B);
    return {
        order: 0,
        id: 'categorical.direct-mixed-weakening.point',
        groupId: 'categorical.direct-mixed-weakening',
        clauseOrder: 0,
        sourceOwner: transforComponentCapped,
        variables: [
            { name: 'K', type: builder.template(builder.global(category)) },
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
            cat,
            builder.wildcard(B),
            builder.wildcard(target),
            k,
            weakeningAt(builder, K, A, B)
        )),
        right: builder.template(constantFunctorAt(
            builder,
            fibreAt(builder, oppositeAt(builder, K), A, k),
            fibreAt(builder, K, B, k)
        )),
        provenance: source(
            'rule @tapp0_fapp0 $K Cat_cat _ _ $k ' +
                '(@Functor_catd_const_funcd $K $A $B)'
        )
    };
};

const fullRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const cat = builder.global(categoryOfCategories);
    const target = stableFunctorFamilyAt(builder, K, A, B);
    const Bx = fibreAt(builder, K, B, x);
    const By = fibreAt(builder, K, B, y);
    const Ay = fibreAt(builder, oppositeAt(builder, K), A, y);
    const constantTarget = functorCategoryAt(builder, Ay, By);
    const baseActionCategory = functorCategoryAt(builder, Bx, By);
    const resultCategory = functorCategoryAt(
        builder,
        Bx,
        constantTarget
    );
    return {
        order: 1,
        id: 'categorical.direct-mixed-weakening.full-action',
        groupId: 'categorical.direct-mixed-weakening',
        clauseOrder: 1,
        sourceOwner: transforHomFull,
        variables: [
            { name: 'K', type: builder.template(builder.global(category)) },
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
            cat,
            builder.wildcard(B),
            builder.wildcard(target),
            x,
            y,
            weakeningAt(builder, K, A, B)
        )),
        right: builder.template(composeFunctorsAt(
            builder,
            homCategoryAt(builder, K, x, y),
            baseActionCategory,
            resultCategory,
            homPostcompositionAt(
                builder,
                cat,
                cat,
                identityFunctorAt(builder, cat),
                Bx,
                By,
                constantTarget,
                constantFunctorAt(builder, Ay, By)
            ),
            functorHomFullAt(builder, K, cat, B, x, y)
        )),
        provenance: source(
            'rule @tapp1_func $K Cat_cat _ _ $x $y ' +
                '(@Functor_catd_const_funcd $K $A $B)'
        )
    };
};

const cappedRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const cat = builder.global(categoryOfCategories);
    const target = stableFunctorFamilyAt(builder, K, A, B);
    const Bx = fibreAt(builder, K, B, x);
    const By = fibreAt(builder, K, B, y);
    const Ay = fibreAt(builder, oppositeAt(builder, K), A, y);
    return {
        order: 2,
        id: 'categorical.direct-mixed-weakening.capped-action',
        groupId: 'categorical.direct-mixed-weakening',
        clauseOrder: 2,
        sourceOwner: transforHomCapped,
        variables: [
            { name: 'K', type: builder.template(builder.global(category)) },
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
            cat,
            builder.wildcard(B),
            builder.wildcard(target),
            x,
            y,
            weakeningAt(builder, K, A, B),
            p
        )),
        right: builder.template(composeFunctorsAt(
            builder,
            Bx,
            By,
            functorCategoryAt(builder, Ay, By),
            constantFunctorAt(builder, Ay, By),
            functorHomCappedAt(builder, K, cat, B, x, y, p)
        )),
        provenance: source(
            'rule @tapp1_fapp0 $K Cat_cat _ _ $x $y ' +
                '(@Functor_catd_const_funcd $K $A $B) $p'
        )
    };
};

const runtimeRules = Object.freeze([
    pointRule(),
    fullRule(),
    cappedRule()
]);

export const CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'DIRECT-MIXED-WEAKENING-1J-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'direct-mixed-weakening-1j-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        ...externalSymbols,
        homPostcomposition,
        weakening
    ].map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_RUNTIME_MODULE,
    {
        revision: 'DIRECT-MIXED-WEAKENING-1J-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_RUNTIME_MODULE.revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence: 'Exact D-DTTLF-USABILITY-050 active projection'
        }))
    }
);

const declarationCoreName = (target: CoreLfQualifiedSymbol): string => {
    const entry =
        CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_LINKAGE.entries
            .find(candidate =>
                candidate.symbol.moduleId === target.moduleId &&
                candidate.symbol.name === target.name
            );
    if (entry === undefined || entry.kind !== 'free-declaration') {
        throw new Error(
            `DIRECT-MIXED-WEAKENING-1J lost ${target.name} linkage`
        );
    }
    return entry.coreName;
};

export const CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_CORE_NAMES =
Object.freeze({
    homPostcomposition: declarationCoreName(homPostcomposition),
    weakening: declarationCoreName(weakening)
});

export type CoreCategoricalDirectMixedWeakeningSymbolId =
    keyof typeof CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_CORE_NAMES;

export function coreCategoricalDirectMixedWeakeningCoreName(
    id: CoreCategoricalDirectMixedWeakeningSymbolId
): string {
    return CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_CORE_NAMES[id];
}

export const CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_BOUNDARY =
Object.freeze({
    decision: 'D-DTTLF-USABILITY-050',
    declarationNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    declarationCount: declarations.length,
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    runtimeRuleCount: runtimeRules.length,
    activeLambdapiOwnerDelta: 1,
    activeLambdapiRuleDelta: 3,
    preExistingSignatureAcquisitionDelta: 1,
    intrinsicCoreOwnerDelta: 0,
    ownerSpecificCheckerOrEvaluatorDelta: 0,
    externalOracleDelta: 0,
    externalCoherenceEvidenceDelta: 0,
    contextualIrNodeDelta: 0,
    recursiveFactorizationCaseDelta: 1,
    textOrBrowserDelta: 0,
    transfersContextualCurry: false,
    directNestedIntroductionRemainsFundamental: true,
    allEntriesUseGenericTransferEngines: true
});

export interface CoreCategoricalDirectMixedWeakeningCompilation {
    readonly prerequisite:
        CoreCategoricalDirectMixedProductDistributionCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation:
    CoreCategoricalDirectMixedWeakeningCompilation | undefined;

export function compileCoreCategoricalDirectMixedWeakeningTransfer():
CoreCategoricalDirectMixedWeakeningCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    const prerequisite =
        compileCoreCategoricalDirectMixedProductDistributionTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_MODULE,
        CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_POLICY,
        CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_LINKAGE,
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
        CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_RUNTIME_MODULE,
        CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_RUNTIME_POLICY,
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
        CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_MODULE,
        CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_POLICY,
        CORE_CATEGORICAL_DIRECT_MIXED_WEAKENING_TRANSFER_LINKAGE,
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
