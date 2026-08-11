/**
 * PATHOUT-LIBRARY-TRANSITIVITY-1E root-only derived-library transfer.
 *
 * Exact local boundary: no opaque declaration, one derived runtime support,
 * no local proof rule, and five checked transparent definitions over
 * already-qualified providers. One existing Sigma/Pi proof provider is
 * rechecked lazily against the final environment. The active source's
 * `injective` modifier on CompTarget_catd remains provenance metadata only.
 */

import {
    CoreCategoricalFibredBinderCompilation,
    compileCoreCategoricalFibredBinderProof,
    compileCoreCategoricalFibredBinderTransfer
} from './categorical_fibred_binder_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE
} from './categorical_displayed_chain_transfer';
import {
    CORE_CATEGORICAL_FIBRED_STRUCTURE_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE
} from './categorical_fibred_structure_transfer';
import {
    CORE_CATEGORICAL_MIXED_ACTION_SYMBOLS,
    CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_LINKAGE
} from './categorical_mixed_action_transfer';
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
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import { CoreLfMixedDeclarationContext } from './lf_transfer_mixed';
import {
    CoreLfCompiledRuntimeFragment,
    CoreLfCompiledRuntimeProgram,
    CoreLfComposedRuntimeProgram,
    compileCoreLfRuntimeFragment
} from './lf_transfer_runtime';
import { binderMode } from './kernel';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_LINKAGE,
    CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_LINKAGE,
    CORE_PATHIND_FIXED_SOURCE_1C_SYMBOLS,
    CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_LINKAGE
} from './pathind_fixed_source_transfer';
import {
    CORE_PATHIND_INTERNALIZED_1D_PREFIX_LIBRARY_LINKAGE,
    CORE_PATHIND_INTERNALIZED_1D_PRELUDE_LINKAGE,
    CORE_PATHIND_INTERNALIZED_1D_SIGMA_LINKAGE,
    CORE_PATHIND_INTERNALIZED_1D_SUFFIX_LIBRARY_LINKAGE,
    CORE_PATHIND_INTERNALIZED_1D_TRUSTED_LINKAGE,
    CorePathindInternalized1dCompilation,
    compileCorePathindInternalized1dTransfer
} from './pathind_internalized_transfer';
import {
    CORE_PATHOUT_FOUNDATION_1B_LIBRARY_LINKAGE,
    CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_LINKAGE,
    CORE_PATHOUT_FOUNDATION_1B_SYMBOLS,
    CORE_PATHOUT_FOUNDATION_SOURCE_SHA256
} from './pathout_foundation_transfer';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID
} from './pathout_transitivity_proposal_v4';
import {
    validateCorePathoutTransitivity1eReviewV4
} from './pathout_transitivity_review_v4';

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_PATHOUT_TRANSITIVITY_1E_REVISION =
    'PATHOUT-LIBRARY-TRANSITIVITY-1E-TRANSFER-4' as const;

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner = coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const homClassifier =
    coreDirectedContinuationTransferSymbol('hom-classifier');
const functorClassifier =
    coreDirectedContinuationTransferSymbol('functor-classifier');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol('displayed-category-category');
const displayedFunctorCategory =
    coreDirectedContinuationTransferSymbol('displayed-functor-category');
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const transforComponentCapped =
    coreDirectedContinuationTransferSymbol('transfor-component-capped');
const homCategory =
    coreDirectedContinuationTransferSymbol('hom-category');

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const displayedFamilyClassifier = symbol('Catd');
const displayedFunctorClassifier = symbol('Functord');
const oppositeCategory = symbol('Op_cat');
const sigmaProjectionPullback = symbol('Sigma_proj1_pullback_catd');

const {
    contravariantRepresentable
} = CORE_CATEGORICAL_MIXED_ACTION_SYMBOLS;
const {
    displayedIdentity
} = CORE_CATEGORICAL_FIBRED_STRUCTURE_SYMBOLS;
const {
    fibreCovariantTransformation
} = CORE_PATHIND_FIXED_SOURCE_1C_SYMBOLS;
const {
    representableFamilyFunctor,
    representableFamily,
    pathoutCategory
} = CORE_PATHOUT_FOUNDATION_1B_SYMBOLS;

export const CORE_PATHOUT_TRANSITIVITY_1E_SYMBOLS = Object.freeze({
    compositionTargetFamily: symbol('CompTarget_catd'),
    compositionTargetAction: symbol('CompTarget_fapp1_func'),
    compositionMotive: symbol('CompMotive_catd'),
    pathCompositionSection: symbol('path_comp_sec'),
    pathCompositionFunctor: symbol('path_comp_func')
});

const {
    compositionTargetFamily,
    compositionTargetAction,
    compositionMotive,
    pathCompositionSection,
    pathCompositionFunctor
} = CORE_PATHOUT_TRANSITIVITY_1E_SYMBOLS;

const implicitMode = binderMode('implicit', 'functorial');
const explicitMode = binderMode('explicit', 'functorial');

interface BuilderArgument {
    readonly plicity: 'explicit' | 'implicit';
    readonly value: CoreLfTransferBuilderExpression;
}

const globalCall = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfQualifiedSymbol,
    arguments_: readonly BuilderArgument[]
): CoreLfTransferBuilderExpression =>
    builder.call(builder.global(target), arguments_);

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

const displayedCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedCategoryCategory, [{
        plicity: 'explicit',
        value: base
    }]);

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

const oppositeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, oppositeCategory, [{
        plicity: 'explicit',
        value: base
    }]);

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

const displayedIdentityAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedIdentity, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: family }
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

const compositionTargetFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, compositionTargetFamily, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]);

const pathCompositionSectionAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pathCompositionSection, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]);

const pathCompositionFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    path: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pathCompositionFunctor, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: path }
    ]);

const source = (sourceFragment: string) => Object.freeze({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const modifiers = (
    rigidity: 'ordinary' | 'injective'
) => Object.freeze({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity: 'transparent' as const
});

const compositionTargetFamilyType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            () => displayedFamilyType(builder, Z),
            explicitMode
        ),
        implicitMode
    ));
};

const compositionTargetFamilyBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => contravariantRepresentableAt(
                builder,
                displayedCategoryAt(builder, Z),
                representableFamilyAt(builder, Z, x),
                oppositeAt(builder, Z),
                representableFamilyFunctorAt(builder, Z)
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const compositionTargetActionType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => builder.pi(
                'a',
                objectType(builder, Z),
                a => builder.pi(
                    'b',
                    objectType(builder, Z),
                    b => builder.pi(
                        'p',
                        homType(builder, Z, a, b),
                        () => functorType(
                            builder,
                            displayedFunctorCategoryAt(
                                builder,
                                Z,
                                representableFamilyAt(builder, Z, a),
                                representableFamilyAt(builder, Z, x)
                            ),
                            displayedFunctorCategoryAt(
                                builder,
                                Z,
                                representableFamilyAt(builder, Z, b),
                                representableFamilyAt(builder, Z, x)
                            )
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

const compositionTargetActionBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => builder.lam(
                'a',
                objectType(builder, Z),
                a => builder.lam(
                    'b',
                    objectType(builder, Z),
                    b => builder.lam(
                        'p',
                        homType(builder, Z, a, b),
                        p => functorHomCappedAt(
                            builder,
                            Z,
                            builder.global(categoryOfCategories),
                            compositionTargetFamilyAt(builder, Z, x),
                            a,
                            b,
                            p
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

const compositionMotiveType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => displayedFamilyType(
                builder,
                pathoutCategoryAt(builder, Z, x)
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const compositionMotiveBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => sigmaProjectionPullbackAt(
                builder,
                Z,
                representableFamilyAt(builder, Z, x),
                compositionTargetFamilyAt(builder, Z, x)
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const pathCompositionSectionType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'x',
            objectType(builder, Z),
            x => objectType(
                builder,
                displayedFunctorCategoryAt(
                    builder,
                    Z,
                    representableFamilyAt(builder, Z, x),
                    compositionTargetFamilyAt(builder, Z, x)
                )
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const pathCompositionSectionBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'x',
            objectType(builder, Z),
            x => fibreCovariantTransformationAt(
                builder,
                Z,
                compositionTargetFamilyAt(builder, Z, x),
                x,
                displayedIdentityAt(
                    builder,
                    Z,
                    representableFamilyAt(builder, Z, x)
                )
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const pathCompositionFunctorType = (): CoreLfTransferExpression => {
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
                    () => displayedFunctorType(
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

const pathCompositionFunctorBody = (): CoreLfTransferExpression => {
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
                        displayedCategoryAt(builder, Z),
                        representableFamilyFunctorAt(builder, Z),
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

const fixedSourceSelectedComponentConsumerParentFusionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const Z = builder.capture('Z');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const repX = representableFamilyAt(builder, Z, x);
    const repY = representableFamilyAt(builder, Z, y);
    return {
        order: 0,
        id: CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID,
        groupId: 'pathout.transitivity.runtime-local-support',
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
                name: 'y',
                type: builder.template(objectType(builder, Z))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, Z, x, y))
            }
        ],
        left: builder.pattern(functorObjectAt(
            builder,
            homCategoryAt(builder, Z, x, y),
            displayedFunctorCategoryAt(builder, Z, repY, repX),
            componentAt(
                builder,
                Z,
                repX,
                compositionTargetFamilyAt(builder, Z, x),
                y,
                pathCompositionSectionAt(builder, Z, x)
            ),
            p
        )),
        right: builder.template(pathCompositionFunctorAt(
            builder,
            Z,
            x,
            y,
            p
        )),
        provenance: source(
            'derived transitivity original selected-component ' +
            'complete consumer-parent presentation fusion ' +
            'from active lines 5484-5497, ' +
            '7955-7972, 8445-8453, 19363-19413, and 19687-19710'
        )
    };
};

const runtimeRules: readonly CoreLfTransferRuntimeRule[] = Object.freeze([
    fixedSourceSelectedComponentConsumerParentFusionRule()
]);

const declarations: readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: compositionTargetFamily,
        type: compositionTargetFamilyType(),
        body: coreLfTransferExplicitBody(compositionTargetFamilyBody()),
        modifiers: modifiers('injective'),
        provenance: source('injective symbol CompTarget_catd [Z : Cat]')
    }),
    Object.freeze({
        order: 1,
        symbol: compositionTargetAction,
        type: compositionTargetActionType(),
        body: coreLfTransferExplicitBody(compositionTargetActionBody()),
        modifiers: modifiers('ordinary'),
        provenance: source(
            'symbol CompTarget_fapp1_func [Z : Cat] [x a b : Obj Z]'
        )
    }),
    Object.freeze({
        order: 2,
        symbol: compositionMotive,
        type: compositionMotiveType(),
        body: coreLfTransferExplicitBody(compositionMotiveBody()),
        modifiers: modifiers('ordinary'),
        provenance: source('symbol CompMotive_catd [Z : Cat]')
    }),
    Object.freeze({
        order: 3,
        symbol: pathCompositionSection,
        type: pathCompositionSectionType(),
        body: coreLfTransferExplicitBody(pathCompositionSectionBody()),
        modifiers: modifiers('ordinary'),
        provenance: source('symbol path_comp_sec [Z : Cat]')
    }),
    Object.freeze({
        order: 4,
        symbol: pathCompositionFunctor,
        type: pathCompositionFunctorType(),
        body: coreLfTransferExplicitBody(pathCompositionFunctorBody()),
        modifiers: modifiers('ordinary'),
        provenance: source('symbol path_comp_func [Z : Cat]')
    })
]);

const externalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    homClassifier,
    functorClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    displayedFunctorCategory,
    displayedFamilyClassifier,
    displayedFunctorClassifier,
    functorHomCapped,
    contravariantRepresentable,
    representableFamily,
    oppositeCategory,
    representableFamilyFunctor,
    pathoutCategory,
    sigmaProjectionPullback,
    fibreCovariantTransformation,
    displayedIdentity
]);

export const CORE_PATHOUT_TRANSITIVITY_1E_MODULE: CoreLfModuleSpec =
createCoreLfModuleSpec({
    revision: CORE_PATHOUT_TRANSITIVITY_1E_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'pathout-transitivity-1e-derived-library',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_PATHOUT_FOUNDATION_SOURCE_SHA256,
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

export const CORE_PATHOUT_TRANSITIVITY_1E_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_PATHOUT_TRANSITIVITY_1E_MODULE,
    {
        revision: `${CORE_PATHOUT_TRANSITIVITY_1E_REVISION}-POLICY-1`,
        moduleRevision: CORE_PATHOUT_TRANSITIVITY_1E_MODULE.revision,
        entries: declarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'checked-transparent-definition' as const,
            evidence:
                'Exact active v3.2 transparent definition selected by ' +
                'reviewed PATHOUT-LIBRARY-TRANSITIVITY-1E proposal v4'
        }))
    }
);

const runtimeExternalSymbols = Object.freeze([
    ...externalSymbols,
    functorObject,
    transforComponentCapped,
    homCategory,
    ...declarations.map(declaration => declaration.symbol)
]);

export const CORE_PATHOUT_TRANSITIVITY_1E_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: `${CORE_PATHOUT_TRANSITIVITY_1E_REVISION}-RUNTIME-1`,
    moduleId: MODULE_ID,
    fragmentId: 'pathout-transitivity-1e-runtime-local-support',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_PATHOUT_FOUNDATION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: runtimeExternalSymbols.map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const CORE_PATHOUT_TRANSITIVITY_1E_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_PATHOUT_TRANSITIVITY_1E_RUNTIME_MODULE,
    {
        revision:
            `${CORE_PATHOUT_TRANSITIVITY_1E_REVISION}-RUNTIME-POLICY-1`,
        moduleRevision:
            CORE_PATHOUT_TRANSITIVITY_1E_RUNTIME_MODULE.revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Derived original complete consumer-parent support ' +
                'selected by reviewed ' +
                'PATHOUT-LIBRARY-TRANSITIVITY-1E proposal v4'
        }))
    }
);

const dependencyLinks = Object.freeze([
    ...CORE_PATHIND_INTERNALIZED_1D_SUFFIX_LIBRARY_LINKAGE.entries,
    ...CORE_PATHIND_INTERNALIZED_1D_PREFIX_LIBRARY_LINKAGE.entries,
    ...CORE_PATHIND_INTERNALIZED_1D_TRUSTED_LINKAGE.entries,
    ...CORE_PATHIND_INTERNALIZED_1D_PRELUDE_LINKAGE.entries,
    ...CORE_PATHIND_INTERNALIZED_1D_SIGMA_LINKAGE.entries,
    ...CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_LINKAGE.entries,
    ...CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_LINKAGE.entries,
    ...CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_LINKAGE.entries,
    ...CORE_PATHOUT_FOUNDATION_1B_LIBRARY_LINKAGE.entries,
    ...CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_LINKAGE.entries,
    ...CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_LINKAGE.entries,
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries
]);

const dependencyLink = (
    target: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const inherited = dependencyLinks.find(candidate =>
        candidate.symbol.moduleId === target.moduleId &&
        candidate.symbol.name === target.name
    );
    if (inherited === undefined) {
        throw new Error(
            'PATHOUT-LIBRARY-TRANSITIVITY-1E has no dependency link for ' +
                `${target.moduleId}.${target.name}`
        );
    }
    return Object.freeze({
        ...inherited,
        order,
        symbol: Object.freeze({ ...target })
    });
};

export const CORE_PATHOUT_TRANSITIVITY_1E_LINKAGE:
CoreLfTransferDeclarationLinkage = createCoreLfTransferDeclarationLinkage(
    CORE_PATHOUT_TRANSITIVITY_1E_MODULE,
    {
        revision: `${CORE_PATHOUT_TRANSITIVITY_1E_REVISION}-LINKAGE-1`,
        moduleRevision: CORE_PATHOUT_TRANSITIVITY_1E_MODULE.revision,
        entries: [
            ...externalSymbols.map(dependencyLink),
            ...declarations.map((declaration, index) => Object.freeze({
                order: externalSymbols.length + index,
                symbol: declaration.symbol,
                kind: 'free-declaration' as const,
                coreName:
                    'emdash_v3_2_pathout_transitivity_' +
                    declaration.symbol.name,
                backendName: declaration.symbol.name
            }))
        ]
    }
);

export const CORE_PATHOUT_TRANSITIVITY_1E_CORE_NAMES = Object.freeze(
    Object.fromEntries(declarations.map(declaration => [
        declaration.symbol.name,
        'emdash_v3_2_pathout_transitivity_' + declaration.symbol.name
    ])) as Readonly<Record<string, string>>
);

export type CorePathoutTransitivityOrdinaryLibraryCapability =
    | 'checked-transparent-definition'
    | 'opaque-signature'
    | 'runtime-rewrite'
    | 'proof-unification';

export class CorePathoutTransitivityOrdinaryLibraryCapabilityError
    extends Error {
    constructor(
        public readonly capability:
            CorePathoutTransitivityOrdinaryLibraryCapability
    ) {
        super(
            `Ordinary PathOut transitivity library code cannot request ` +
            `'${capability}'`
        );
        this.name =
            'CorePathoutTransitivityOrdinaryLibraryCapabilityError';
    }
}

export function assertCorePathoutTransitivityOrdinaryLibraryCapability(
    capability: CorePathoutTransitivityOrdinaryLibraryCapability
): 'checked-transparent-definition' {
    if (capability !== 'checked-transparent-definition') {
        throw new CorePathoutTransitivityOrdinaryLibraryCapabilityError(
            capability
        );
    }
    return capability;
}

export const CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY = Object.freeze({
    revision: CORE_PATHOUT_TRANSITIVITY_1E_REVISION,
    reviewedAuthorization:
        'PATHOUT-LIBRARY-TRANSITIVITY-1E-REVIEWED-4',
    proposalCheckpoint: '2498053',
    proposalSha256:
        '820df96e9a0b889172c2e74fbcdc77cd16329dcaf36105d3c53076807e76394b',
    reviewCheckpoint: 'fc9a323',
    reviewSha256:
        '9d37f7fd66c2fb61ce9ebf1dc1c7f5b83ba7558e0457f78252eb8dacb14a48aa',
    exactBoundary: '0/1/0/5',
    trustedDeclarationNames: Object.freeze([] as string[]),
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    proofRuleIds: Object.freeze([] as string[]),
    inheritedProofProviderIds: Object.freeze([
        'stress.sigma-pi.uncurrying'
    ]),
    transparentDefinitionNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    trustedDeclarationCount: 0,
    runtimeRuleCount: runtimeRules.length,
    mathematicalRuntimeRuleCount: 0,
    derivedRuntimeSupportRuleCount: runtimeRules.length,
    proofRuleCount: 0,
    inheritedProofProviderCount: 1,
    transparentDefinitionCount: declarations.length,
    requiredExistingProviderNames: Object.freeze([
        'Catd_cat',
        'Functord_cat',
        'hom_con',
        'Rep_catd',
        'Op_cat',
        'Rep_catd_func',
        'fapp1_fapp0',
        'PathOut_cat',
        'Sigma_proj1_pullback_catd',
        'fib_cov_transf',
        'id_funcd'
    ]),
    requiredExistingProviderCount: 11,
    typedLibraryConsumerCount: 2,
    selectedDefinitionalObservationCount: 8,
    selectedRuntimeDefinitionalObservationCount: 7,
    selectedInheritedProofTimeObservationCount: 1,
    negativeConsumerCount: 8,
    boundedOracleAssertionCount: 8,
    allDefinitionsUseCheckedTransparentPolicy: true,
    allDefinitionsUseFreeDeclarationLinks: true,
    sourceOrderPreserved: true,
    comparisonStepLimit: 512,
    sourceInjectiveModifierRecordedAsMetadata: true,
    typescriptInjectivityOrUnificationBehaviorAdded: false,
    intrinsicCoreOwnerDelta: 0,
    checkerBranchDelta: 0,
    evaluatorBranchDelta: 0,
    genericRuntimeMatcherDelta: 0,
    genericComparisonDelta: 0,
    activeLambdapiOwnerDelta: 0,
    activeLambdapiRuleDelta: 0,
    localSupportRuleCompilesAfterFiveDefinitions: true,
    localSupportRuleIsCompleteParent: true,
    v2PreDeltaLocalSupportRetained: false,
    v3StablePostCompTargetDeltaLocalSupportRetained: false,
    v4OriginalConsumerParentLocalSupportSelected: true,
    localSupportRuleMatchesBeforeDescendantDelta: true,
    localSupportRuleMustSubjectCheck: true,
    broadHomConRuntimeImportIncluded: false,
    wholeDisplayedIdentityDeltaIncluded: false,
    wholeRepresentableFamilyDeltaIncluded: false,
    runtimePiToFunctordCollapseIncluded: false,
    inheritedProofRecheckedAgainstFinalEnvironment: true,
    pathCategoryBridgeIncluded: false,
    rawCompositionRuntimeCollapseIncluded: false,
    rootOnlyQualification: true,
    browserOrPublicPackageExported: false
});

export interface CorePathoutTransitivity1eCompilation {
    readonly predecessor: CorePathindInternalized1dCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

export interface CorePathoutTransitivity1eInheritedProof {
    readonly provider: CoreCategoricalFibredBinderCompilation;
    readonly proofProgram: ReturnType<
        typeof compileCoreCategoricalFibredBinderProof
    >;
}

let cachedCompilation: CorePathoutTransitivity1eCompilation | undefined;

export function compileCorePathoutTransitivity1eTransfer():
CorePathoutTransitivity1eCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    validateCorePathoutTransitivity1eReviewV4();
    const predecessor = compileCorePathindInternalized1dTransfer();
    const compiled = compileCoreLfDeclarations(
        CORE_PATHOUT_TRANSITIVITY_1E_MODULE,
        CORE_PATHOUT_TRANSITIVITY_1E_POLICY,
        CORE_PATHOUT_TRANSITIVITY_1E_LINKAGE,
        {
            initialEnvironment: predecessor.compiled.environment,
            runtimeProgram: predecessor.composedRuntime,
            comparisonStepLimit: 512
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        predecessor.declarationContext,
        [compiled]
    );
    const runtimeFragment = compileCoreLfRuntimeFragment(
        CORE_PATHOUT_TRANSITIVITY_1E_RUNTIME_MODULE,
        CORE_PATHOUT_TRANSITIVITY_1E_RUNTIME_POLICY,
        declarationContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: predecessor.runtimeFragment
            }],
            comparisonStepLimit: 512
        }
    );
    cachedCompilation = Object.freeze({
        predecessor,
        compiled,
        declarationContext,
        runtimeFragment,
        runtime: runtimeFragment.localProgram,
        composedRuntime: runtimeFragment.runtime
    });
    return cachedCompilation;
}

/**
 * Lazily recheck the exact inherited Sigma/Pi proof provider in the final
 * transitivity environment. This installs no local proof rule and does not
 * turn the proof-time category comparison into runtime conversion.
 */
export function compileCorePathoutTransitivity1eInheritedProof(
    compilation: CorePathoutTransitivity1eCompilation =
        compileCorePathoutTransitivity1eTransfer(),
    environment: CoreLfDeclarationEnvironment =
        compilation.compiled.environment
): CorePathoutTransitivity1eInheritedProof {
    const provider = compileCoreCategoricalFibredBinderTransfer();
    const proofProgram = compileCoreCategoricalFibredBinderProof(
        provider,
        environment
    );
    return Object.freeze({ provider, proofProgram });
}
