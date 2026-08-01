/**
 * FIBRED-TRANSFD-1 transfer closure for direct displayed transformations.
 *
 * This module selects six exact active v3.2 declarations, seven existing
 * runtime rules, and the direct second-hom proof rule. It introduces no new
 * mathematical owner or equation. The three declarations already reviewed by
 * SCALE-STRESS-2B3 retain their reviewed Core names; the additional transport
 * and higher-cell signatures are checked through the same generic engines.
 */

import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT,
    validateCoreCategoricalFibredTransfdContract
} from './categorical_fibred_transfd_contract';
import {
    CORE_CATEGORICAL_DEPENDENT_SYMBOLS,
    CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE
} from './categorical_dependent_transfer';
import {
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS,
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE
} from './categorical_dependent_composition_transfer';
import {
    CORE_CATEGORICAL_FIBRED_BINDER_CORE_NAMES,
    CoreCategoricalFibredBinderCompilation,
    compileCoreCategoricalFibredBinderTransfer
} from './categorical_fibred_binder_transfer';
import {
    CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE
} from './categorical_fibred_structure_transfer';
import {
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE
} from './categorical_structural_transfer';
import {
    CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE,
    coreDirectedContinuationTransferSymbol
} from './directed_continuation_transfer';
import {
    CORE_DIRECTED_1A_PRIMITIVE_NAMES
} from './directed_1a';
import {
    KernelExpression,
    Provenance,
    binderMode,
    kernelApplication,
    kernelCall,
    kernelFree
} from './kernel';
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
    CoreLfDeclarationEnvironment
} from './lf_declarations';
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
    CORE_LF_SCALE_STRESS_2A_LINKAGE,
    CORE_LF_SCALE_STRESS_2A_MODULE
} from './scale_stress_2_representation';
import {
    CORE_LF_SCALE_STRESS_2B3_LINKAGE,
    CORE_LF_SCALE_STRESS_2B3_SYMBOLS
} from './scale_stress_2b3_representation';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_REVISION =
    'FIBRED-TRANSFD-1-DIRECT-NEXT-HOM-TRANSFER-1' as const;

export const CORE_CATEGORICAL_FIBRED_TRANSFD_SOURCE_SHA256 =
    'sha256:7fe3f4c706bea0f9fc0ae9c11865a2c464abc4aa9df1ab434d08710dbaf360fe';

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const groupoid =
    coreDirectedContinuationTransferSymbol('groupoid-universe');
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
const sigmaCategory =
    coreDirectedContinuationTransferSymbol('sigma-category');
const displayedFunctorCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-functor-category'
    );
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const {
    functorCategory
} = CORE_CATEGORICAL_STRUCTURAL_SYMBOLS;
const {
    terminalCategory,
    genericComposition
} = CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS;
const {
    fibreFunctor
} = CORE_CATEGORICAL_DEPENDENT_SYMBOLS;

const displayedFamilyClassifier =
    CORE_LF_SCALE_STRESS_2A_MODULE.declarations[0].symbol;
const sigmaProjectionPullback =
    CORE_LF_SCALE_STRESS_2A_MODULE.declarations[1].symbol;
const {
    displayedTransformationCategory,
    displayedTransformationClassifier,
    displayedComponent
} = CORE_LF_SCALE_STRESS_2B3_SYMBOLS;

export const CORE_CATEGORICAL_FIBRED_TRANSFD_SYMBOLS =
Object.freeze({
    displayedTransformationCategory,
    displayedTransformationClassifier,
    displayedComponent,
    transportLhs:
        coreLfQualifiedSymbol(
            MODULE_ID,
            'functord_transport_lhs_func'
        ),
    transportRhs:
        coreLfQualifiedSymbol(
            MODULE_ID,
            'functord_transport_rhs_func'
        ),
    higherCell:
        coreLfQualifiedSymbol(MODULE_ID, 'tdapp1_int_cell')
});

const {
    transportLhs,
    transportRhs,
    higherCell
} = CORE_CATEGORICAL_FIBRED_TRANSFD_SYMBOLS;

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

const transforType = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, transforClassifier, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: sourceFunctor },
        { plicity: 'explicit', value: targetFunctor }
    ]));

const displayedFamilyType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, displayedFamilyClassifier, [{
        plicity: 'explicit',
        value: base
    }]));

const displayedFunctorCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedFunctorCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: sourceFamily },
        { plicity: 'explicit', value: targetFamily }
    ]);

const displayedFunctorType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    objectType(builder, displayedFunctorCategoryAt(
        builder,
        base,
        sourceFamily,
        targetFamily
    ));

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

const displayedTransformationCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedTransformationCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: sourceFunctor },
        { plicity: 'explicit', value: targetFunctor }
    ]);

const displayedTransformationType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(
        builder,
        displayedTransformationClassifier,
        [
            { plicity: 'implicit', value: base },
            { plicity: 'implicit', value: sourceFamily },
            { plicity: 'implicit', value: targetFamily },
            { plicity: 'explicit', value: sourceFunctor },
            { plicity: 'explicit', value: targetFunctor }
        ]
    ));

const fibreCategoryAt = (
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

const fibreFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, fibreFunctor, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: point }
    ]);

const fapp0At = (
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

const transportAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    targetPoint: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorHomCapped, [
        { plicity: 'implicit', value: base },
        {
            plicity: 'implicit',
            value: builder.global(categoryOfCategories)
        },
        { plicity: 'explicit', value: family },
        { plicity: 'implicit', value: sourcePoint },
        { plicity: 'implicit', value: targetPoint },
        { plicity: 'explicit', value: arrow }
    ]);

const displayedComponentAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression,
    transformation: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedComponent, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'implicit', value: sourceFunctor },
        { plicity: 'implicit', value: targetFunctor },
        { plicity: 'explicit', value: point },
        { plicity: 'explicit', value: transformation }
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

const sigmaCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
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

const composeAt = (
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

const source = (
    sourceFragment: string,
    canonicalCommandOrdinal?: number
) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment,
    canonicalCommandOrdinal
});

const publicModifiers = (
    rigidity: 'ordinary' | 'constant' | 'injective',
    sourceOpacity: 'transparent' | 'opaque'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity
});

const displayedTransformationCategoryType =
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
                    _FF => builder.pi(
                        'GG',
                        displayedFunctorType(builder, K, E, D),
                        _GG => builder.global(category),
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

const displayedTransformationClassifierType =
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
                    _FF => builder.pi(
                        'GG',
                        displayedFunctorType(builder, K, E, D),
                        _GG => builder.global(groupoid),
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

const displayedTransformationClassifierBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'K',
        builder.global(category),
        K => builder.lam(
            'E',
            displayedFamilyType(builder, K),
            E => builder.lam(
                'D',
                displayedFamilyType(builder, K),
                D => builder.lam(
                    'FF',
                    displayedFunctorType(builder, K, E, D),
                    FF => builder.lam(
                        'GG',
                        displayedFunctorType(builder, K, E, D),
                        GG => objectClassifierAt(
                            builder,
                            displayedTransformationCategoryAt(
                                builder,
                                K,
                                E,
                                D,
                                FF,
                                GG
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

const displayedComponentType =
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
                        'GG',
                        displayedFunctorType(builder, K, E, D),
                        GG => builder.pi(
                            'z',
                            objectType(builder, K),
                            z => builder.pi(
                                'epsilon',
                                displayedTransformationType(
                                    builder,
                                    K,
                                    E,
                                    D,
                                    FF,
                                    GG
                                ),
                                _epsilon => transforType(
                                    builder,
                                    fibreCategoryAt(builder, K, E, z),
                                    fibreCategoryAt(builder, K, D, z),
                                    fibreFunctorAt(
                                        builder,
                                        K,
                                        E,
                                        D,
                                        FF,
                                        z
                                    ),
                                    fibreFunctorAt(
                                        builder,
                                        K,
                                        E,
                                        D,
                                        GG,
                                        z
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
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const transportType = (
    _owner: CoreLfQualifiedSymbol
): CoreLfTransferExpression => {
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
                    _FF => builder.pi(
                        'x',
                        objectType(builder, K),
                        _x => builder.pi(
                            'y',
                            objectType(builder, K),
                            _y => builder.pi(
                                'p',
                                homType(builder, K, _x, _y),
                                _p => functorType(
                                    builder,
                                    fibreCategoryAt(builder, K, E, _x),
                                    fibreCategoryAt(builder, K, D, _y)
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

const transportBody = (
    side: 'lhs' | 'rhs'
): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'K',
        builder.global(category),
        K => builder.lam(
            'E',
            displayedFamilyType(builder, K),
            E => builder.lam(
                'D',
                displayedFamilyType(builder, K),
                D => builder.lam(
                    'FF',
                    displayedFunctorType(builder, K, E, D),
                    FF => builder.lam(
                        'x',
                        objectType(builder, K),
                        x => builder.lam(
                            'y',
                            objectType(builder, K),
                            y => builder.lam(
                                'p',
                                homType(builder, K, x, y),
                                p => {
                                    const fibreEx =
                                        fibreCategoryAt(builder, K, E, x);
                                    const fibreEy =
                                        fibreCategoryAt(builder, K, E, y);
                                    const fibreDx =
                                        fibreCategoryAt(builder, K, D, x);
                                    const fibreDy =
                                        fibreCategoryAt(builder, K, D, y);
                                    return side === 'lhs'
                                        ? composeAt(
                                            builder,
                                            builder.global(
                                                categoryOfCategories
                                            ),
                                            fibreEx,
                                            fibreDx,
                                            fibreDy,
                                            transportAt(
                                                builder,
                                                K,
                                                D,
                                                x,
                                                y,
                                                p
                                            ),
                                            fibreFunctorAt(
                                                builder,
                                                K,
                                                E,
                                                D,
                                                FF,
                                                x
                                            )
                                        )
                                        : composeAt(
                                            builder,
                                            builder.global(
                                                categoryOfCategories
                                            ),
                                            fibreEx,
                                            fibreEy,
                                            fibreDy,
                                            fibreFunctorAt(
                                                builder,
                                                K,
                                                E,
                                                D,
                                                FF,
                                                y
                                            ),
                                            transportAt(
                                                builder,
                                                K,
                                                E,
                                                x,
                                                y,
                                                p
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
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const higherCellType = (): CoreLfTransferExpression => {
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
                        'GG',
                        displayedFunctorType(builder, K, E, D),
                        GG => builder.pi(
                            'epsilon',
                            displayedTransformationType(
                                builder,
                                K,
                                E,
                                D,
                                FF,
                                GG
                            ),
                            _epsilon => builder.pi(
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
                                                fibreCategoryAt(
                                                    builder,
                                                    K,
                                                    E,
                                                    x
                                                )
                                            ),
                                            u => {
                                                const sourceFunctor =
                                                    globalCall(
                                                        builder,
                                                        transportLhs,
                                                        [
                                                            {
                                                                plicity:
                                                                    'implicit',
                                                                value: K
                                                            },
                                                            {
                                                                plicity:
                                                                    'implicit',
                                                                value: E
                                                            },
                                                            {
                                                                plicity:
                                                                    'implicit',
                                                                value: D
                                                            },
                                                            {
                                                                plicity:
                                                                    'explicit',
                                                                value: FF
                                                            },
                                                            {
                                                                plicity:
                                                                    'implicit',
                                                                value: x
                                                            },
                                                            {
                                                                plicity:
                                                                    'implicit',
                                                                value: y
                                                            },
                                                            {
                                                                plicity:
                                                                    'explicit',
                                                                value: p
                                                            }
                                                        ]
                                                    );
                                                const targetFunctor =
                                                    globalCall(
                                                        builder,
                                                        transportRhs,
                                                        [
                                                            {
                                                                plicity:
                                                                    'implicit',
                                                                value: K
                                                            },
                                                            {
                                                                plicity:
                                                                    'implicit',
                                                                value: E
                                                            },
                                                            {
                                                                plicity:
                                                                    'implicit',
                                                                value: D
                                                            },
                                                            {
                                                                plicity:
                                                                    'explicit',
                                                                value: GG
                                                            },
                                                            {
                                                                plicity:
                                                                    'implicit',
                                                                value: x
                                                            },
                                                            {
                                                                plicity:
                                                                    'implicit',
                                                                value: y
                                                            },
                                                            {
                                                                plicity:
                                                                    'explicit',
                                                                value: p
                                                            }
                                                        ]
                                                    );
                                                return homType(
                                                    builder,
                                                    fibreCategoryAt(
                                                        builder,
                                                        K,
                                                        D,
                                                        y
                                                    ),
                                                    fapp0At(
                                                        builder,
                                                        fibreCategoryAt(
                                                            builder,
                                                            K,
                                                            E,
                                                            x
                                                        ),
                                                        fibreCategoryAt(
                                                            builder,
                                                            K,
                                                            D,
                                                            y
                                                        ),
                                                        sourceFunctor,
                                                        u
                                                    ),
                                                    fapp0At(
                                                        builder,
                                                        fibreCategoryAt(
                                                            builder,
                                                            K,
                                                            E,
                                                            x
                                                        ),
                                                        fibreCategoryAt(
                                                            builder,
                                                            K,
                                                            D,
                                                            y
                                                        ),
                                                        targetFunctor,
                                                        u
                                                    )
                                                );
                                            },
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
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const declarations: readonly CoreLfTransferDeclaration[] = Object.freeze([
    {
        order: 0,
        symbol: displayedTransformationCategory,
        type: displayedTransformationCategoryType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Transfd_cat [K : Cat]',
            401
        )
    },
    {
        order: 1,
        symbol: displayedTransformationClassifier,
        type: displayedTransformationClassifierType(),
        body: coreLfTransferExplicitBody(
            displayedTransformationClassifierBody()
        ),
        modifiers: publicModifiers('injective', 'transparent'),
        provenance: source(
            'injective symbol Transfd [K : Cat]',
            402
        )
    },
    {
        order: 2,
        symbol: displayedComponent,
        type: displayedComponentType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol tdapp0_fapp0 [K : Cat]',
            1058
        )
    },
    {
        order: 3,
        symbol: transportLhs,
        type: transportType(transportLhs),
        body: coreLfTransferExplicitBody(transportBody('lhs')),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol functord_transport_lhs_func [K : Cat] ' +
            '[E D : τ (Catd K)]',
            1121
        )
    },
    {
        order: 4,
        symbol: transportRhs,
        type: transportType(transportRhs),
        body: coreLfTransferExplicitBody(transportBody('rhs')),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol functord_transport_rhs_func [K : Cat] ' +
            '[E D : τ (Catd K)]',
            1122
        )
    },
    {
        order: 5,
        symbol: higherCell,
        type: higherCellType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol tdapp1_int_cell [K : Cat] [E D : τ (Catd K)]',
            1174
        )
    }
]);

const declarationExternalSymbols = Object.freeze([
    category,
    groupoid,
    decodeOwner,
    objectClassifier,
    functorClassifier,
    homClassifier,
    transforClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    displayedFunctorCategory,
    functorObject,
    functorHomCapped,
    displayedFamilyClassifier,
    fibreFunctor,
    genericComposition
]);

export const CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'fibred-transfd-1-signatures',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_FIBRED_TRANSFD_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: declarationExternalSymbols.map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_MODULE,
    {
        revision: 'FIBRED-TRANSFD-1-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_MODULE.revision,
        entries: declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy:
                declaration.symbol ===
                    displayedTransformationClassifier
                    || declaration.symbol === transportLhs
                    || declaration.symbol === transportRhs
                    ? 'checked-transparent-definition' as const
                    : 'opaque-signature' as const,
            evidence: declaration.order < 3
                ? 'Exact declaration reused from reviewed ' +
                    'SCALE-STRESS-2B3 evidence'
                : 'Exact active v3.2 higher-cell prerequisite signature'
        }))
    }
);

const earlierLinks = [
    ...CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries,
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries,
    ...CORE_LF_SCALE_STRESS_2A_LINKAGE.entries
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
            `FIBRED-TRANSFD-1 has no dependency link for ` +
            `${symbol.moduleId}.${symbol.name}`
        );
    }
    return Object.freeze({
        ...link,
        order,
        symbol: Object.freeze({ ...link.symbol })
    });
};

const reusedCoreName = (
    symbol: CoreLfQualifiedSymbol
): string => {
    const link = CORE_LF_SCALE_STRESS_2B3_LINKAGE.entries.find(
        candidate =>
            candidate.symbol.moduleId === symbol.moduleId &&
            candidate.symbol.name === symbol.name
    );
    if (link === undefined || link.kind !== 'free-declaration') {
        throw new Error(
            `FIBRED-TRANSFD-1 has no reviewed 2B3 Core name for ` +
            `${symbol.moduleId}.${symbol.name}`
        );
    }
    return link.coreName;
};

export const CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_MODULE,
        {
            revision: 'FIBRED-TRANSFD-1-SIGNATURE-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_MODULE
                    .revision,
            entries: [
                ...declarationExternalSymbols.map(dependencyLink),
                ...declarations.map((declaration, index) => ({
                    order:
                        declarationExternalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName: declaration.order < 3
                        ? reusedCoreName(declaration.symbol)
                        : `emdash_v3_2_fibred_transfd_1_` +
                            declaration.symbol.name,
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

const homDisplayedFunctorRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const FF = builder.capture('FF');
    const GG = builder.capture('GG');
    const functord = displayedFunctorCategoryAt(builder, K, E, D);
    return {
        order: 0,
        id: 'categorical.transfd.direct-hom',
        groupId: 'categorical.transfd.direct-hom',
        clauseOrder: 0,
        sourceOwner: homCategory,
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
                name: 'GG',
                type: builder.template(
                    displayedFunctorType(builder, K, E, D)
                )
            }
        ],
        left: builder.pattern(homCategoryAt(
            builder,
            functord,
            FF,
            GG
        )),
        right: builder.template(
            displayedTransformationCategoryAt(
                builder,
                K,
                E,
                D,
                FF,
                GG
            )
        ),
        provenance: source(
            'rule Hom_cat (@Functord_cat $K $E $D) $FF $GG ' +
            '↪ @Transfd_cat $K $E $D $FF $GG'
        )
    };
};

const transfdObjectBridgeRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const FF = builder.capture('FF');
    const GG = builder.capture('GG');
    const variables = [
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
            name: 'GG',
            type: builder.template(
                displayedFunctorType(builder, K, E, D)
            )
        }
    ];
    const ordinary = transforCategoryAt(
        builder,
        K,
        builder.global(categoryOfCategories),
        E,
        D
    );
    return {
        order: 1,
        id: 'categorical.transfd.object-ordinary-next-hom',
        groupId: 'categorical.transfd.object-ordinary-next-hom',
        clauseOrder: 0,
        sourceOwner: objectClassifier,
        variables,
        left: builder.pattern(objectClassifierAt(
            builder,
            displayedTransformationCategoryAt(
                builder,
                K,
                E,
                D,
                FF,
                GG
            )
        )),
        right: builder.template(objectClassifierAt(
            builder,
            homCategoryAt(builder, ordinary, FF, GG)
        )),
        provenance: source(
            'rule Obj (@Transfd_cat $K $E $D $FF $GG) ↪ ' +
            'Obj (Hom_cat (@Transf_cat $K Cat_cat $E $D) $FF $GG)'
        )
    };
};

const sectionNextHomRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const s = builder.capture('s');
    const t = builder.capture('t');
    const pi = sectionCategoryAt(builder, K, E);
    const constantTerminal = constantFamilyAt(
        builder,
        K,
        builder.global(terminalCategory)
    );
    return {
        order: 2,
        id: 'categorical.transfd.section-next-hom',
        groupId: 'categorical.transfd.section-next-hom',
        clauseOrder: 0,
        sourceOwner: homCategory,
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
                name: 's',
                type: builder.template(objectType(builder, pi))
            },
            {
                name: 't',
                type: builder.template(objectType(builder, pi))
            }
        ],
        left: builder.pattern(homCategoryAt(builder, pi, s, t)),
        right: builder.template(
            displayedTransformationCategoryAt(
                builder,
                K,
                constantTerminal,
                E,
                s,
                t
            )
        ),
        provenance: source(
            'rule Hom_cat (@Pi_cat $K $E) $s $t ↪ ' +
            '@Transfd_cat $K (@Const_catd $K Terminal_cat) $E $s $t'
        )
    };
};

const sigmaPiObjectJoinRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const R = builder.capture('R');
    const D = builder.capture('D');
    const sigma = sigmaCategoryAt(builder, K, R);
    const constantTerminal = constantFamilyAt(
        builder,
        sigma,
        builder.global(terminalCategory)
    );
    const pullback = globalCall(
        builder,
        sigmaProjectionPullback,
        [
            { plicity: 'implicit', value: K },
            { plicity: 'explicit', value: R },
            { plicity: 'explicit', value: D }
        ]
    );
    return {
        order: 3,
        id: 'categorical.transfd.sigma-pi-object-join',
        groupId: 'categorical.transfd.sigma-pi-object-join',
        clauseOrder: 0,
        sourceOwner: objectClassifier,
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
            }
        ],
        left: builder.pattern(objectClassifierAt(
            builder,
            transforCategoryAt(
                builder,
                sigma,
                builder.global(categoryOfCategories),
                constantTerminal,
                pullback
            )
        )),
        right: builder.template(objectClassifierAt(
            builder,
            transforCategoryAt(
                builder,
                K,
                builder.global(categoryOfCategories),
                R,
                D
            )
        )),
        provenance: source(
            'rule Obj (@Transf_cat (@Sigma_cat $K $R) Cat_cat ' +
            '(@Const_catd (@Sigma_cat $K $R) Terminal_cat) ' +
            '(@Sigma_proj1_pullback_catd $K $R $D)) ↪ ' +
            'Obj (@Transf_cat $K Cat_cat $R $D)'
        )
    };
};

const sigmaPiNextHomRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const R = builder.capture('R');
    const D = builder.capture('D');
    const s = builder.capture('s');
    const t = builder.capture('t');
    const sigma = sigmaCategoryAt(builder, K, R);
    const constantTerminal = constantFamilyAt(
        builder,
        sigma,
        builder.global(terminalCategory)
    );
    const pullback = globalCall(
        builder,
        sigmaProjectionPullback,
        [
            { plicity: 'implicit', value: K },
            { plicity: 'explicit', value: R },
            { plicity: 'explicit', value: D }
        ]
    );
    const pi = sectionCategoryAt(builder, sigma, pullback);
    return {
        order: 4,
        id: 'categorical.transfd.sigma-pi-next-hom',
        groupId: 'categorical.transfd.sigma-pi-next-hom',
        clauseOrder: 0,
        sourceOwner: displayedTransformationCategory,
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
                name: 's',
                type: builder.template(objectType(builder, pi))
            },
            {
                name: 't',
                type: builder.template(objectType(builder, pi))
            }
        ],
        left: builder.pattern(
            displayedTransformationCategoryAt(
                builder,
                sigma,
                constantTerminal,
                pullback,
                s,
                t
            )
        ),
        right: builder.template(
            displayedTransformationCategoryAt(
                builder,
                K,
                R,
                D,
                s,
                t
            )
        ),
        provenance: source(
            'rule @Transfd_cat (@Sigma_cat $K $R) ' +
            '(@Const_catd (@Sigma_cat $K $R) Terminal_cat) ' +
            '(@Sigma_proj1_pullback_catd $K $R $D) $s $t ↪ ' +
            '@Transfd_cat $K $R $D $s $t'
        )
    };
};

const displayedComponentCompositionRule = (
    presentation: 'direct' | 'ordinary',
    order: number
): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const FF = builder.capture('FF');
    const GG = builder.capture('GG');
    const HH = builder.capture('HH');
    const z = builder.capture('z');
    const eta = builder.capture('eta');
    const epsilon = builder.capture('epsilon');
    const displayedFunctor = displayedFunctorCategoryAt(
        builder,
        K,
        E,
        D
    );
    const ordinary = transforCategoryAt(
        builder,
        K,
        builder.global(categoryOfCategories),
        E,
        D
    );
    const compositionBase =
        presentation === 'direct' ? displayedFunctor : ordinary;
    const fibreE = fibreCategoryAt(builder, K, E, z);
    const fibreD = fibreCategoryAt(builder, K, D, z);
    const fibreFunctorCategory = globalCall(
        builder,
        functorCategory,
        [
            { plicity: 'explicit', value: fibreE },
            { plicity: 'explicit', value: fibreD }
        ]
    );
    return {
        order,
        id:
            `categorical.transfd.component-composition.${presentation}`,
        groupId: 'categorical.transfd.component-composition',
        clauseOrder: presentation === 'direct' ? 0 : 1,
        sourceOwner: displayedComponent,
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
                name: 'GG',
                type: builder.template(
                    displayedFunctorType(builder, K, E, D)
                )
            },
            {
                name: 'HH',
                type: builder.template(
                    displayedFunctorType(builder, K, E, D)
                )
            },
            {
                name: 'z',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'eta',
                type: builder.template(
                    displayedTransformationType(
                        builder,
                        K,
                        E,
                        D,
                        GG,
                        HH
                    )
                )
            },
            {
                name: 'epsilon',
                type: builder.template(
                    displayedTransformationType(
                        builder,
                        K,
                        E,
                        D,
                        FF,
                        GG
                    )
                )
            }
        ],
        left: builder.pattern(displayedComponentAt(
            builder,
            K,
            E,
            D,
            FF,
            HH,
            z,
            composeAt(
                builder,
                compositionBase,
                FF,
                GG,
                HH,
                eta,
                epsilon
            )
        )),
        right: builder.template(composeAt(
            builder,
            fibreFunctorCategory,
            fibreFunctorAt(builder, K, E, D, FF, z),
            fibreFunctorAt(builder, K, E, D, GG, z),
            fibreFunctorAt(builder, K, E, D, HH, z),
            displayedComponentAt(
                builder,
                K,
                E,
                D,
                GG,
                HH,
                z,
                eta
            ),
            displayedComponentAt(
                builder,
                K,
                E,
                D,
                FF,
                GG,
                z,
                epsilon
            )
        )),
        provenance: source(
            `rule @tdapp0_fapp0 _ _ _ _ _ $z ` +
            `(@comp_fapp0 (@${
                presentation === 'direct'
                    ? 'Functord_cat'
                    : 'Transf_cat'
            } ...) $FF $GG $HH $eta $epsilon)`
        )
    };
};

const runtimeRules = Object.freeze([
    homDisplayedFunctorRule(),
    transfdObjectBridgeRule(),
    sectionNextHomRule(),
    sigmaPiObjectJoinRule(),
    sigmaPiNextHomRule(),
    displayedComponentCompositionRule('direct', 5),
    displayedComponentCompositionRule('ordinary', 6)
]);

const runtimeExternalSymbols = Object.freeze([
    ...declarationExternalSymbols,
    homCategory,
    transforCategory,
    constantDisplayedFamily,
    sectionCategory,
    sigmaCategory,
    functorCategory,
    terminalCategory,
    sigmaProjectionPullback,
    displayedTransformationCategory,
    displayedTransformationClassifier,
    displayedComponent
]);

export const CORE_CATEGORICAL_FIBRED_TRANSFD_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'FIBRED-TRANSFD-1-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'fibred-transfd-1-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_FIBRED_TRANSFD_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: runtimeExternalSymbols.map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const CORE_CATEGORICAL_FIBRED_TRANSFD_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_FIBRED_TRANSFD_RUNTIME_MODULE,
    {
        revision: 'FIBRED-TRANSFD-1-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_FIBRED_TRANSFD_RUNTIME_MODULE.revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact existing active v3.2 displayed-transfor closure'
        }))
    }
);

const directSecondHomProofRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const FF = builder.capture('FF');
    const GG = builder.capture('GG');
    const K2 = builder.capture('K2');
    const E2 = builder.capture('E2');
    const D2 = builder.capture('D2');
    const FF2 = builder.capture('FF2');
    const GG2 = builder.capture('GG2');
    const ordinary = transforCategoryAt(
        builder,
        K,
        builder.global(categoryOfCategories),
        E,
        D
    );
    return {
        order: 0,
        id: 'categorical.transfd.direct-second-hom',
        sourceOwner: homCategory,
        variables: [
            {
                name: 'K',
                role: 'matched' as const,
                type: builder.template(builder.global(category))
            },
            {
                name: 'E',
                role: 'matched' as const,
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'D',
                role: 'matched' as const,
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'FF',
                role: 'matched' as const,
                type: builder.template(
                    displayedFunctorType(builder, K, E, D)
                )
            },
            {
                name: 'GG',
                role: 'matched' as const,
                type: builder.template(
                    displayedFunctorType(builder, K, E, D)
                )
            },
            {
                name: 'K2',
                role: 'matched' as const,
                type: builder.template(builder.global(category))
            },
            {
                name: 'E2',
                role: 'matched' as const,
                type: builder.template(displayedFamilyType(builder, K2))
            },
            {
                name: 'D2',
                role: 'matched' as const,
                type: builder.template(displayedFamilyType(builder, K2))
            },
            {
                name: 'FF2',
                role: 'matched' as const,
                type: builder.template(
                    displayedFunctorType(builder, K2, E2, D2)
                )
            },
            {
                name: 'GG2',
                role: 'matched' as const,
                type: builder.template(
                    displayedFunctorType(builder, K2, E2, D2)
                )
            }
        ],
        problem: {
            left: builder.pattern(homCategoryAt(
                builder,
                ordinary,
                FF,
                GG
            )),
            right: builder.pattern(
                displayedTransformationCategoryAt(
                    builder,
                    K2,
                    E2,
                    D2,
                    FF2,
                    GG2
                )
            )
        },
        generatedConstraints: [
            {
                left: builder.template(K),
                right: builder.template(K2)
            },
            {
                left: builder.template(E),
                right: builder.template(E2)
            },
            {
                left: builder.template(D),
                right: builder.template(D2)
            },
            {
                left: builder.template(FF),
                right: builder.template(FF2)
            },
            {
                left: builder.template(GG),
                right: builder.template(GG2)
            }
        ],
        provenance: source(
            'unif_rule Hom_cat (@Transf_cat $K Cat_cat $E $D) ' +
            '$FF $GG ≡ @Transfd_cat $K2 $E2 $D2 $FF2 $GG2'
        )
    };
};

const proofRule = directSecondHomProofRule();

export const CORE_CATEGORICAL_FIBRED_TRANSFD_PROOF_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'FIBRED-TRANSFD-1-PROOF-1',
    moduleId: MODULE_ID,
    fragmentId: 'fibred-transfd-1-proof',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_FIBRED_TRANSFD_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: runtimeExternalSymbols.map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules: [],
    proofRules: [proofRule]
});

export const CORE_CATEGORICAL_FIBRED_TRANSFD_PROOF_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_FIBRED_TRANSFD_PROOF_MODULE,
    {
        revision: 'FIBRED-TRANSFD-1-PROOF-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_FIBRED_TRANSFD_PROOF_MODULE.revision,
        entries: [{
            order: 0,
            target: {
                kind: 'proof-rule' as const,
                id: proofRule.id
            },
            policy: 'proof-unification' as const,
            evidence:
                'Exact active direct second-hom comparison; category ' +
                'presentations remain distinct at runtime'
        }]
    }
);

export const CORE_CATEGORICAL_FIBRED_TRANSFD_CORE_NAMES =
Object.freeze({
    displayedTransformationCategory:
        reusedCoreName(displayedTransformationCategory),
    displayedTransformationClassifier:
        reusedCoreName(displayedTransformationClassifier),
    displayedComponent: reusedCoreName(displayedComponent),
    transportLhs:
        'emdash_v3_2_fibred_transfd_1_' + transportLhs.name,
    transportRhs:
        'emdash_v3_2_fibred_transfd_1_' + transportRhs.name,
    higherCell:
        'emdash_v3_2_fibred_transfd_1_' + higherCell.name
});

export type CoreCategoricalFibredTransfdSymbolId =
    | 'displayed-transformation-category'
    | 'displayed-transformation-classifier'
    | 'displayed-component'
    | 'transport-lhs'
    | 'transport-rhs'
    | 'higher-cell';

const coreNameById:
Readonly<Record<
    CoreCategoricalFibredTransfdSymbolId,
    string
>> = Object.freeze({
    'displayed-transformation-category':
        CORE_CATEGORICAL_FIBRED_TRANSFD_CORE_NAMES
            .displayedTransformationCategory,
    'displayed-transformation-classifier':
        CORE_CATEGORICAL_FIBRED_TRANSFD_CORE_NAMES
            .displayedTransformationClassifier,
    'displayed-component':
        CORE_CATEGORICAL_FIBRED_TRANSFD_CORE_NAMES.displayedComponent,
    'transport-lhs':
        CORE_CATEGORICAL_FIBRED_TRANSFD_CORE_NAMES.transportLhs,
    'transport-rhs':
        CORE_CATEGORICAL_FIBRED_TRANSFD_CORE_NAMES.transportRhs,
    'higher-cell':
        CORE_CATEGORICAL_FIBRED_TRANSFD_CORE_NAMES.higherCell
});

export function coreCategoricalFibredTransfdCoreName(
    id: CoreCategoricalFibredTransfdSymbolId
): string {
    return coreNameById[id];
}

export interface CoreCategoricalFibredTransfdClassifiers {
    readonly direct: KernelExpression;
    readonly ordinaryNextHom: KernelExpression;
    readonly sigmaPiNextHom: KernelExpression;
    readonly directObjectClassifier: KernelExpression;
    readonly ordinaryObjectClassifier: KernelExpression;
}

export function coreCategoricalFibredTransfdClassifiers(
    base: KernelExpression,
    sourceFamily: KernelExpression,
    targetFamily: KernelExpression,
    sourceFunctor: KernelExpression,
    targetFunctor: KernelExpression,
    nodeProvenance: Provenance
): CoreCategoricalFibredTransfdClassifiers {
    const direct = kernelCall(
        kernelFree(
            CORE_CATEGORICAL_FIBRED_TRANSFD_CORE_NAMES
                .displayedTransformationCategory,
            nodeProvenance
        ),
        [
            { plicity: 'implicit', value: base },
            { plicity: 'implicit', value: sourceFamily },
            { plicity: 'implicit', value: targetFamily },
            { plicity: 'explicit', value: sourceFunctor },
            { plicity: 'explicit', value: targetFunctor }
        ],
        nodeProvenance
    );
    const ordinaryTransfor = kernelApplication(
        'transfor-category',
        [
            { value: base },
            {
                value: kernelApplication(
                    'category-of-categories',
                    [],
                    nodeProvenance
                )
            },
            { value: sourceFamily },
            { value: targetFamily }
        ],
        nodeProvenance
    );
    const ordinaryNextHom = kernelApplication(
        'hom-category',
        [
            { value: ordinaryTransfor },
            { value: sourceFunctor },
            { value: targetFunctor }
        ],
        nodeProvenance
    );
    const sigma = kernelCall(
        kernelFree(
            CORE_DIRECTED_1A_PRIMITIVE_NAMES['sigma-category'],
            nodeProvenance
        ),
        [
            { plicity: 'implicit', value: base },
            { plicity: 'explicit', value: sourceFamily }
        ],
        nodeProvenance
    );
    const pullback = kernelCall(
        kernelFree(
            CORE_CATEGORICAL_FIBRED_BINDER_CORE_NAMES
                .sigmaProjectionPullback,
            nodeProvenance
        ),
        [
            { plicity: 'implicit', value: base },
            { plicity: 'explicit', value: sourceFamily },
            { plicity: 'explicit', value: targetFamily }
        ],
        nodeProvenance
    );
    const pi = kernelApplication(
        'section-category',
        [
            { value: sigma },
            { value: pullback }
        ],
        nodeProvenance
    );
    const sigmaPiNextHom = kernelApplication(
        'hom-category',
        [
            { value: pi },
            { value: sourceFunctor },
            { value: targetFunctor }
        ],
        nodeProvenance
    );
    const object = (value: KernelExpression) => kernelApplication(
        'object-classifier',
        [{ value }],
        nodeProvenance
    );
    return Object.freeze({
        direct,
        ordinaryNextHom,
        sigmaPiNextHom,
        directObjectClassifier: object(direct),
        ordinaryObjectClassifier: object(ordinaryNextHom)
    });
}

export const CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY =
Object.freeze({
    status: 'root-only-existing-authority-displayed-transfor-closure',
    contractRevision:
        CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT.revision,
    declarationNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    reusedScaleStress2b3DeclarationNames: Object.freeze([
        'Transfd_cat',
        'Transfd',
        'tdapp0_fapp0'
    ]),
    declarationCount: declarations.length,
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    runtimeRuleCount: runtimeRules.length,
    proofRuleIds: Object.freeze([proofRule.id]),
    proofRuleCount: 1,
    newMathematicalOwnerCount: 0,
    newMathematicalRuntimeRuleCount: 0,
    newMathematicalProofRuleCount: 0,
    directOrdinaryRuntimeCategoryCollapseInstalled: false,
    directOrdinaryObjectClassifierBridgeInstalled: true,
    sigmaPiRuntimeNextHomBridgeInstalled: true,
    allEntriesUseGenericTransferEngines: true,
    doesNotProvide: Object.freeze([
        'arbitrary-pointwise-coherence-synthesis',
        'general-dependent-displayed-bracket',
        'whole-displayed-functor-laxity',
        'runtime-direct-ordinary-category-collapse',
        'browser-profile',
        'bulk-transfer'
    ])
});

export interface CoreCategoricalFibredTransfdCompilation {
    readonly prerequisite: CoreCategoricalFibredBinderCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
    readonly proofProgram: CoreLfCompiledProofProgram;
}

export function compileCoreCategoricalFibredTransfdTransfer():
CoreCategoricalFibredTransfdCompilation {
    validateCoreCategoricalFibredTransfdContract();
    validateCoreLfScaleEngineReview();
    const prerequisite =
        compileCoreCategoricalFibredBinderTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_MODULE,
        CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_POLICY,
        CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE,
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
        CORE_CATEGORICAL_FIBRED_TRANSFD_RUNTIME_MODULE,
        CORE_CATEGORICAL_FIBRED_TRANSFD_RUNTIME_POLICY,
        initialContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: prerequisiteFragment
            }]
        }
    );
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_MODULE,
        CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_POLICY,
        CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: runtimeFragment.runtime
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        prerequisite.declarationContext,
        [compiled]
    );
    const proofProgram = compileCoreLfProofProgram(
        CORE_CATEGORICAL_FIBRED_TRANSFD_PROOF_MODULE,
        CORE_CATEGORICAL_FIBRED_TRANSFD_PROOF_POLICY,
        {
            environment: compiled.environment,
            declaration: symbol =>
                declarationContext.declaration(symbol)
        },
        {
            runtimeProgram: runtimeFragment.runtime
        }
    );
    return Object.freeze({
        prerequisite,
        compiled,
        declarationContext,
        runtimeFragment,
        runtime: runtimeFragment.localProgram,
        composedRuntime: runtimeFragment.runtime,
        proofProgram
    });
}

/**
 * Recheck the direct second-hom proof rule in a descendant user environment.
 * Qualified authority declarations remain fixed; only user assumptions are
 * added.
 */
export function compileCoreCategoricalFibredTransfdProof(
    compilation: CoreCategoricalFibredTransfdCompilation,
    environment: CoreLfDeclarationEnvironment
): CoreLfCompiledProofProgram {
    return compileCoreLfProofProgram(
        CORE_CATEGORICAL_FIBRED_TRANSFD_PROOF_MODULE,
        CORE_CATEGORICAL_FIBRED_TRANSFD_PROOF_POLICY,
        {
            environment,
            declaration: symbol =>
                compilation.declarationContext.declaration(symbol)
        },
        {
            runtimeProgram: compilation.composedRuntime
        }
    );
}
