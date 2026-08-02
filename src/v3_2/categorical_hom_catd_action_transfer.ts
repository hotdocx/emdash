/**
 * HOM-CATD-ACTION-TRANSFER-1AF existing-authority transfer closure.
 *
 * The active Lambdapi kernel owns three stable stages for the generic base
 * action of `Hom_catd`, together with identity/composition, `Transf_catd`
 * specialization, and the iterable projection ladder. This fragment imports
 * exactly those three opaque signatures and the dependency-closed nine-rule
 * runtime profile selected by D-DTTLF-USABILITY-064. The wider constant-Cat
 * specialization and proof-time Unit_prof comparison remain outside this
 * runtime profile.
 */

import {
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE
} from './categorical_dependent_composition_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_LINKAGE,
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_SYMBOLS
} from './categorical_displayed_evaluation_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS,
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE
} from './categorical_displayed_nd_higher_foundation_transfer';
import {
    CORE_CATEGORICAL_MIXED_MODE_SYMBOLS,
    CORE_CATEGORICAL_MIXED_MODE_TRANSFER_LINKAGE,
    CoreCategoricalMixedModeCompilation,
    compileCoreCategoricalMixedModeTransfer
} from './categorical_mixed_mode_transfer';
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
export const CORE_CATEGORICAL_HOM_CATD_ACTION_SOURCE_SHA256 =
    'sha256:ef3e77ccc1750d2d7fd5f15df80953679e62f69433ad03eed1615d430c8e2f44';

export const CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_REVISION =
    'HOM-CATD-ACTION-TRANSFER-1AF-GENERIC-TRANSFER-1' as const;

const category = coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner = coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const functorClassifier =
    coreDirectedContinuationTransferSymbol('functor-classifier');
const homClassifier =
    coreDirectedContinuationTransferSymbol('hom-classifier');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol('displayed-category-category');
const sectionCategory =
    coreDirectedContinuationTransferSymbol('section-category');
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const functorHomFull =
    coreDirectedContinuationTransferSymbol('functor-hom-full');
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const homCategory =
    coreDirectedContinuationTransferSymbol('hom-category');

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const oppositeCategory = symbol('Op_cat');
const identityFunctor = symbol('id_func');
const ordinaryComposition = symbol('comp_fapp0');
const functorCategory = symbol('Functor_cat');

const {
    identityArrow,
    displayedOpposite
} = CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS;
const {
    stableFunctorFamily
} = CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_SYMBOLS;
const {
    displayedHomFamily,
    displayedTransforFamily
} = CORE_CATEGORICAL_MIXED_MODE_SYMBOLS;

export const CORE_CATEGORICAL_HOM_CATD_ACTION_SYMBOLS = Object.freeze({
    full: symbol('Hom_catd_fapp1_func'),
    capped: symbol('Hom_catd_fapp1_fapp0'),
    point: symbol('Hom_catd_fapp1_fapp0_point')
});

const actionSymbols = CORE_CATEGORICAL_HOM_CATD_ACTION_SYMBOLS;

export const CORE_CATEGORICAL_HOM_CATD_ACTION_CORE_NAMES = Object.freeze({
    full: 'emdash_v3_2_hom_catd_action_1af_Hom_catd_fapp1_func',
    capped: 'emdash_v3_2_hom_catd_action_1af_Hom_catd_fapp1_fapp0',
    point: 'emdash_v3_2_hom_catd_action_1af_Hom_catd_fapp1_fapp0_point'
});

export type CoreCategoricalHomCatdActionSymbolId =
    keyof typeof CORE_CATEGORICAL_HOM_CATD_ACTION_SYMBOLS;

export const coreCategoricalHomCatdActionCoreName = (
    id: CoreCategoricalHomCatdActionSymbolId
): string => CORE_CATEGORICAL_HOM_CATD_ACTION_CORE_NAMES[id];

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
): CoreLfTransferBuilderExpression => builder.call(callee, arguments_);

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

const oppositeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, oppositeCategory, [{
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

const sectionCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sectionCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const sectionType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    objectType(builder, sectionCategoryAt(builder, base, family));

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

const fibreAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorObject, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: builder.global(categoryOfCategories) },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: point }
    ]);

const sectionAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    section: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, symbol('piapp0'), [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: family },
        { plicity: 'explicit', value: section },
        { plicity: 'explicit', value: point }
    ]);

const stableFunctorFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, stableFunctorFamily, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]);

const displayedHomFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedHomFamily, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]);

const displayedTransforFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedTransforFamily, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: sourceFamily },
        { plicity: 'explicit', value: targetFamily },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]);

const identityAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, identityArrow, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: point }
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
    globalCall(builder, ordinaryComposition, [
        { plicity: 'implicit', value: base },
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

const homAt = (
    builder: CoreLfTransferScopedBuilder,
    K: CoreLfTransferBuilderExpression,
    E: CoreLfTransferBuilderExpression,
    X: CoreLfTransferBuilderExpression,
    Y: CoreLfTransferBuilderExpression,
    k: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    homCategoryAt(
        builder,
        fibreAt(builder, K, E, k),
        sectionAt(builder, K, displayedOppositeAt(builder, K, E), X, k),
        sectionAt(builder, K, E, Y, k)
    );

const fullActionAt = (
    builder: CoreLfTransferScopedBuilder,
    K: CoreLfTransferBuilderExpression,
    E: CoreLfTransferBuilderExpression,
    X: CoreLfTransferBuilderExpression,
    Y: CoreLfTransferBuilderExpression,
    x: CoreLfTransferBuilderExpression,
    y: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, actionSymbols.full, [
        { plicity: 'implicit', value: K },
        { plicity: 'implicit', value: E },
        { plicity: 'implicit', value: X },
        { plicity: 'implicit', value: Y },
        { plicity: 'explicit', value: x },
        { plicity: 'explicit', value: y }
    ]);

const cappedActionAt = (
    builder: CoreLfTransferScopedBuilder,
    K: CoreLfTransferBuilderExpression,
    E: CoreLfTransferBuilderExpression,
    X: CoreLfTransferBuilderExpression,
    Y: CoreLfTransferBuilderExpression,
    x: CoreLfTransferBuilderExpression,
    y: CoreLfTransferBuilderExpression,
    p: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, actionSymbols.capped, [
        { plicity: 'implicit', value: K },
        { plicity: 'implicit', value: E },
        { plicity: 'implicit', value: X },
        { plicity: 'implicit', value: Y },
        { plicity: 'implicit', value: x },
        { plicity: 'implicit', value: y },
        { plicity: 'explicit', value: p }
    ]);

const pointActionAt = (
    builder: CoreLfTransferScopedBuilder,
    K: CoreLfTransferBuilderExpression,
    E: CoreLfTransferBuilderExpression,
    X: CoreLfTransferBuilderExpression,
    Y: CoreLfTransferBuilderExpression,
    x: CoreLfTransferBuilderExpression,
    y: CoreLfTransferBuilderExpression,
    p: CoreLfTransferBuilderExpression,
    h: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, actionSymbols.point, [
        { plicity: 'implicit', value: K },
        { plicity: 'implicit', value: E },
        { plicity: 'implicit', value: X },
        { plicity: 'implicit', value: Y },
        { plicity: 'implicit', value: x },
        { plicity: 'implicit', value: y },
        { plicity: 'explicit', value: p },
        { plicity: 'explicit', value: h }
    ]);

const actionType = (
    stage: 'full' | 'capped' | 'point'
): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K', builder.global(category), K => builder.pi(
            'E', displayedFamilyType(builder, K), E => {
                const opE = displayedOppositeAt(builder, K, E);
                return builder.pi(
                    'X', sectionType(builder, K, opE), X => builder.pi(
                        'Y', sectionType(builder, K, E), Y => builder.pi(
                            'x', objectType(builder, K), x => builder.pi(
                                'y', objectType(builder, K), y => {
                                    if (stage === 'full') {
                                        return functorType(
                                            builder,
                                            homCategoryAt(builder, K, x, y),
                                            functorCategoryAt(
                                                builder,
                                                homAt(builder, K, E, X, Y, x),
                                                homAt(builder, K, E, X, Y, y)
                                            )
                                        );
                                    }
                                    return builder.pi(
                                        'p', homType(builder, K, x, y), p => {
                                            if (stage === 'capped') {
                                                return functorType(
                                                    builder,
                                                    homAt(builder, K, E, X, Y, x),
                                                    homAt(builder, K, E, X, Y, y)
                                                );
                                            }
                                            return builder.pi(
                                                'h',
                                                homType(
                                                    builder,
                                                    fibreAt(builder, K, E, x),
                                                    sectionAt(builder, K, opE, X, x),
                                                    sectionAt(builder, K, E, Y, x)
                                                ),
                                                () => homType(
                                                    builder,
                                                    fibreAt(builder, K, E, y),
                                                    sectionAt(builder, K, opE, X, y),
                                                    sectionAt(builder, K, E, Y, y)
                                                ),
                                                explicitMode
                                            );
                                        },
                                        explicitMode
                                    );
                                },
                                stage === 'full' ? explicitMode : implicitMode
                            ),
                            stage === 'full' ? explicitMode : implicitMode
                        ),
                        implicitMode
                    ),
                    implicitMode
                );
            },
            implicitMode
        ),
        implicitMode
    ));
};

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const declarations: readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: actionSymbols.full,
        type: actionType('full'),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public' as const,
            rigidity: 'injective' as const,
            sourceOpacity: 'opaque' as const
        },
        provenance: source('injective symbol Hom_catd_fapp1_func')
    }),
    Object.freeze({
        order: 1,
        symbol: actionSymbols.capped,
        type: actionType('capped'),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public' as const,
            rigidity: 'injective' as const,
            sourceOpacity: 'opaque' as const
        },
        provenance: source('injective symbol Hom_catd_fapp1_fapp0')
    }),
    Object.freeze({
        order: 2,
        symbol: actionSymbols.point,
        type: actionType('point'),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public' as const,
            rigidity: 'injective' as const,
            sourceOpacity: 'opaque' as const
        },
        provenance: source('injective symbol Hom_catd_fapp1_fapp0_point')
    })
]);

const externalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    functorClassifier,
    homClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    sectionCategory,
    functorObject,
    functorHomFull,
    functorHomCapped,
    homCategory,
    oppositeCategory,
    identityFunctor,
    ordinaryComposition,
    functorCategory,
    identityArrow,
    displayedOpposite,
    stableFunctorFamily,
    displayedHomFamily,
    displayedTransforFamily,
    symbol('piapp0')
]);

export const CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'hom-catd-action-1af-signatures',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_HOM_CATD_ACTION_SOURCE_SHA256,
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

export const CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_POLICY =
createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_MODULE,
    {
        revision: 'HOM-CATD-ACTION-1AF-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_MODULE.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact active v3.2 displayed Hom action signature ' +
                'approved by D-DTTLF-USABILITY-064'
        }))
    }
);

const prerequisiteLinks = [
    ...CORE_CATEGORICAL_MIXED_MODE_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_LINKAGE.entries,
    ...CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries,
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries
];

const dependencyLink = (
    target: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const inherited = prerequisiteLinks.find(candidate =>
        candidate.symbol.moduleId === target.moduleId &&
        candidate.symbol.name === target.name
    );
    if (inherited === undefined) {
        throw new Error(`No prerequisite link for ${target.name}`);
    }
    return Object.freeze({
        ...inherited,
        order,
        symbol: Object.freeze({ ...target })
    });
};

const actionCoreName = (
    target: CoreLfQualifiedSymbol
): string => {
    const entry = Object.entries(actionSymbols).find(([, symbol_]) =>
        symbol_.moduleId === target.moduleId &&
        symbol_.name === target.name
    );
    if (entry === undefined) {
        throw new Error(
            `Displayed Hom action declaration '${target.name}' has no ` +
            'Core name contract entry'
        );
    }
    return coreCategoricalHomCatdActionCoreName(
        entry[0] as CoreCategoricalHomCatdActionSymbolId
    );
};

export const CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
createCoreLfTransferDeclarationLinkage(
    CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_MODULE,
    {
        revision: 'HOM-CATD-ACTION-1AF-SIGNATURE-LINKAGE-1',
        moduleRevision:
            CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_MODULE.revision,
        entries: [
            ...externalSymbols.map(dependencyLink),
            ...declarations.map((declaration, index) => ({
                order: externalSymbols.length + index,
                symbol: declaration.symbol,
                kind: 'free-declaration' as const,
                coreName: actionCoreName(declaration.symbol),
                backendName: declaration.symbol.name
            }))
        ]
    }
);

const common = (builder: CoreLfTransferScopedBuilder) => {
    const K = builder.capture('K');
    const E = builder.capture('E');
    const X = builder.capture('X');
    const Y = builder.capture('Y');
    const opE = displayedOppositeAt(builder, K, E);
    return {
        K,
        E,
        X,
        Y,
        variables: [
            { name: 'K', type: builder.template(builder.global(category)) },
            { name: 'E', type: builder.template(displayedFamilyType(builder, K)) },
            { name: 'X', type: builder.template(sectionType(builder, K, opE)) },
            { name: 'Y', type: builder.template(sectionType(builder, K, E)) }
        ]
    };
};

const identityRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const context = common(builder);
    const x = builder.capture('x');
    return {
        order: 0,
        id: 'categorical.hom-catd-action.capped-identity',
        groupId: 'categorical.hom-catd-action.capped-laws',
        clauseOrder: 0,
        sourceOwner: actionSymbols.capped,
        variables: [
            ...context.variables,
            { name: 'x', type: builder.template(objectType(builder, context.K)) }
        ],
        left: builder.pattern(cappedActionAt(
            builder, context.K, context.E, context.X, context.Y,
            x, x, identityAt(builder, context.K, x)
        )),
        right: builder.template(identityFunctorAt(
            builder,
            homAt(builder, context.K, context.E, context.X, context.Y, x)
        )),
        provenance: source('rule @Hom_catd_fapp1_fapp0 ... (@id $K $x)')
    };
};

const cappedCompositionRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const context = common(builder);
    const x = builder.capture('x');
    const y = builder.capture('y');
    const z = builder.capture('z');
    const p = builder.capture('p');
    const q = builder.capture('q');
    const hx = homAt(builder, context.K, context.E, context.X, context.Y, x);
    const hy = homAt(builder, context.K, context.E, context.X, context.Y, y);
    const hz = homAt(builder, context.K, context.E, context.X, context.Y, z);
    return {
        order: 1,
        id: 'categorical.hom-catd-action.capped-composition',
        groupId: 'categorical.hom-catd-action.capped-laws',
        clauseOrder: 1,
        sourceOwner: ordinaryComposition,
        variables: [
            ...context.variables,
            { name: 'x', type: builder.template(objectType(builder, context.K)) },
            { name: 'y', type: builder.template(objectType(builder, context.K)) },
            { name: 'z', type: builder.template(objectType(builder, context.K)) },
            { name: 'p', type: builder.template(homType(builder, context.K, x, y)) },
            { name: 'q', type: builder.template(homType(builder, context.K, y, z)) }
        ],
        left: builder.pattern(composeAt(
            builder,
            builder.global(categoryOfCategories),
            builder.wildcard(hx),
            builder.wildcard(hy),
            builder.wildcard(hz),
            cappedActionAt(builder, context.K, context.E, context.X, context.Y, y, z, q),
            cappedActionAt(builder, context.K, context.E, context.X, context.Y, x, y, p)
        )),
        right: builder.template(cappedActionAt(
            builder, context.K, context.E, context.X, context.Y, x, z,
            composeAt(builder, context.K, x, y, z, q, p)
        )),
        provenance: source('rule @comp_fapp0 Cat_cat _ _ _ ...')
    };
};

const pointCompositionRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const context = common(builder);
    const x = builder.capture('x');
    const y = builder.capture('y');
    const z = builder.capture('z');
    const p = builder.capture('p');
    const q = builder.capture('q');
    const h = builder.capture('h');
    return {
        order: 2,
        id: 'categorical.hom-catd-action.point-composition',
        groupId: 'categorical.hom-catd-action.point-laws',
        clauseOrder: 0,
        sourceOwner: actionSymbols.point,
        variables: [
            ...context.variables,
            { name: 'x', type: builder.template(objectType(builder, context.K)) },
            { name: 'y', type: builder.template(objectType(builder, context.K)) },
            { name: 'z', type: builder.template(objectType(builder, context.K)) },
            { name: 'p', type: builder.template(homType(builder, context.K, x, y)) },
            { name: 'q', type: builder.template(homType(builder, context.K, y, z)) },
            {
                name: 'h',
                type: builder.template(homType(
                    builder,
                    fibreAt(builder, context.K, context.E, x),
                    sectionAt(builder, context.K, displayedOppositeAt(builder, context.K, context.E), context.X, x),
                    sectionAt(builder, context.K, context.E, context.Y, x)
                ))
            }
        ],
        left: builder.pattern(pointActionAt(
            builder, context.K, context.E, context.X, context.Y, y, z, q,
            pointActionAt(builder, context.K, context.E, context.X, context.Y, x, y, p, h)
        )),
        right: builder.template(pointActionAt(
            builder, context.K, context.E, context.X, context.Y, x, z,
            composeAt(builder, context.K, x, y, z, q, p), h
        )),
        provenance: source('rule @Hom_catd_fapp1_fapp0_point ...')
    };
};

const transforContext = (builder: CoreLfTransferScopedBuilder) => {
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const FF = builder.capture('FF');
    const GG = builder.capture('GG');
    const family = stableFunctorFamilyAt(builder, K, A, B);
    return {
        K, A, B, FF, GG, family,
        variables: [
            { name: 'K', type: builder.template(builder.global(category)) },
            { name: 'A', type: builder.template(displayedFamilyType(builder, oppositeAt(builder, K))) },
            { name: 'B', type: builder.template(displayedFamilyType(builder, K)) },
            { name: 'FF', type: builder.template(sectionType(builder, K, displayedOppositeAt(builder, K, family))) },
            { name: 'GG', type: builder.template(sectionType(builder, K, family)) }
        ]
    };
};

const transforActionRule = (
    stage: 'full' | 'capped',
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const context = transforContext(builder);
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const target = displayedTransforFamilyAt(
        builder, context.K, context.A, context.B, context.FF, context.GG
    );
    return {
        order,
        id: `categorical.hom-catd-action.transfor-${stage}`,
        groupId: 'categorical.hom-catd-action.transfor-specialization',
        clauseOrder: stage === 'full' ? 0 : 1,
        sourceOwner: stage === 'full' ? functorHomFull : functorHomCapped,
        variables: [
            ...context.variables,
            { name: 'x', type: builder.template(objectType(builder, context.K)) },
            { name: 'y', type: builder.template(objectType(builder, context.K)) },
            ...(stage === 'capped' ? [{
                name: 'p',
                type: builder.template(homType(builder, context.K, x, y))
            }] : [])
        ],
        left: builder.pattern(stage === 'full'
            ? functorHomFullAt(builder, context.K, builder.global(categoryOfCategories), target, x, y)
            : functorHomCappedAt(builder, context.K, builder.global(categoryOfCategories), target, x, y, p)),
        right: builder.template(stage === 'full'
            ? fullActionAt(builder, context.K, context.family, context.FF, context.GG, x, y)
            : cappedActionAt(builder, context.K, context.family, context.FF, context.GG, x, y, p)),
        provenance: source(`rule @fapp1_${stage === 'full' ? 'func' : 'fapp0'} ... Transf_catd`)
    };
};

const genericActionRule = (
    stage: 'full' | 'capped',
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const context = common(builder);
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const target = displayedHomFamilyAt(
        builder, context.K, context.E, context.X, context.Y
    );
    return {
        order,
        id: `categorical.hom-catd-action.generic-${stage}`,
        groupId: 'categorical.hom-catd-action.generic-projection',
        clauseOrder: stage === 'full' ? 0 : 1,
        sourceOwner: stage === 'full' ? functorHomFull : functorHomCapped,
        variables: [
            ...context.variables,
            { name: 'x', type: builder.template(objectType(builder, context.K)) },
            { name: 'y', type: builder.template(objectType(builder, context.K)) },
            ...(stage === 'capped' ? [{
                name: 'p',
                type: builder.template(homType(builder, context.K, x, y))
            }] : [])
        ],
        left: builder.pattern(stage === 'full'
            ? functorHomFullAt(builder, context.K, builder.global(categoryOfCategories), target, x, y)
            : functorHomCappedAt(builder, context.K, builder.global(categoryOfCategories), target, x, y, p)),
        right: builder.template(stage === 'full'
            ? fullActionAt(builder, context.K, context.E, context.X, context.Y, x, y)
            : cappedActionAt(builder, context.K, context.E, context.X, context.Y, x, y, p)),
        provenance: source(`rule @fapp1_${stage === 'full' ? 'func' : 'fapp0'} ... Hom_catd`)
    };
};

const projectionRule = (
    stage: 'full-to-capped' | 'capped-to-point',
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const context = common(builder);
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const h = builder.capture('h');
    const hx = homAt(builder, context.K, context.E, context.X, context.Y, x);
    const hy = homAt(builder, context.K, context.E, context.X, context.Y, y);
    return {
        order,
        id: `categorical.hom-catd-action.${stage}`,
        groupId: 'categorical.hom-catd-action.projection-ladder',
        clauseOrder: stage === 'full-to-capped' ? 0 : 1,
        sourceOwner: functorObject,
        variables: [
            ...context.variables,
            { name: 'x', type: builder.template(objectType(builder, context.K)) },
            { name: 'y', type: builder.template(objectType(builder, context.K)) },
            { name: 'p', type: builder.template(homType(builder, context.K, x, y)) },
            ...(stage === 'capped-to-point' ? [{
                name: 'h',
                type: builder.template(homType(
                    builder,
                    fibreAt(builder, context.K, context.E, x),
                    sectionAt(builder, context.K, displayedOppositeAt(builder, context.K, context.E), context.X, x),
                    sectionAt(builder, context.K, context.E, context.Y, x)
                ))
            }] : [])
        ],
        left: builder.pattern(stage === 'full-to-capped'
            ? functorObjectAt(
                builder,
                builder.wildcard(homCategoryAt(builder, context.K, x, y)),
                builder.wildcard(functorCategoryAt(builder, hx, hy)),
                fullActionAt(builder, context.K, context.E, context.X, context.Y, x, y),
                p
            )
            : functorObjectAt(
                builder,
                builder.wildcard(hx),
                builder.wildcard(hy),
                cappedActionAt(builder, context.K, context.E, context.X, context.Y, x, y, p),
                h
            )),
        right: builder.template(stage === 'full-to-capped'
            ? cappedActionAt(builder, context.K, context.E, context.X, context.Y, x, y, p)
            : pointActionAt(builder, context.K, context.E, context.X, context.Y, x, y, p, h)),
        provenance: source(`rule fapp0 (@Hom_catd_${stage})`)
    };
};

const runtimeRules = Object.freeze([
    identityRule(),
    cappedCompositionRule(),
    pointCompositionRule(),
    transforActionRule('full', 3),
    transforActionRule('capped', 4),
    genericActionRule('full', 5),
    genericActionRule('capped', 6),
    projectionRule('full-to-capped', 7),
    projectionRule('capped-to-point', 8)
]);

export const CORE_CATEGORICAL_HOM_CATD_ACTION_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'HOM-CATD-ACTION-1AF-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'hom-catd-action-1af-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_HOM_CATD_ACTION_SOURCE_SHA256,
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

export const CORE_CATEGORICAL_HOM_CATD_ACTION_RUNTIME_POLICY =
    createCoreLfTransferPolicyOverlay(
        CORE_CATEGORICAL_HOM_CATD_ACTION_RUNTIME_MODULE,
        {
            revision: 'HOM-CATD-ACTION-1AF-RUNTIME-POLICY-1',
            moduleRevision:
                CORE_CATEGORICAL_HOM_CATD_ACTION_RUNTIME_MODULE.revision,
            entries: runtimeRules.map(rule => ({
                order: rule.order,
                target: {
                    kind: 'runtime-rule' as const,
                    id: rule.id
                },
                policy: 'runtime-rewrite' as const,
                evidence:
                    'Exact active v3.2 displayed Hom action runtime clause ' +
                    'approved by D-DTTLF-USABILITY-064'
            }))
        }
    );

export const CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY =
Object.freeze({
    revision: CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_REVISION,
    decision: 'D-DTTLF-USABILITY-064',
    declarationNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    declarationCount: declarations.length,
    runtimeRuleCount: runtimeRules.length,
    proofRuleCount: 0,
    omittedConstantCatRuntimeRuleCount: 2,
    importedProfunctorDeclarationCount: 0,
    activeLambdapiOwnerDelta: 0,
    activeLambdapiRuleDelta: 0,
    intrinsicCoreOwnerDelta: 0,
    ownerSpecificCheckerOrEvaluatorDelta: 0,
    contextualBinderDelta: 0,
    externalCoherenceEvidenceDelta: 0,
    textOrBrowserDelta: 0,
    allEntriesUseGenericTransferEngines: true
});

export interface CoreCategoricalHomCatdActionCompilation {
    readonly prerequisite: CoreCategoricalMixedModeCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation:
    CoreCategoricalHomCatdActionCompilation | undefined;

export function compileCoreCategoricalHomCatdActionTransfer():
CoreCategoricalHomCatdActionCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    const prerequisite = compileCoreCategoricalMixedModeTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_MODULE,
        CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_POLICY,
        CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_LINKAGE,
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
        CORE_CATEGORICAL_HOM_CATD_ACTION_RUNTIME_MODULE,
        CORE_CATEGORICAL_HOM_CATD_ACTION_RUNTIME_POLICY,
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
        CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_MODULE,
        CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_POLICY,
        CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_LINKAGE,
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
