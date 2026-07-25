/**
 * Representation-only SCALE-STRESS-2B3 transfer of Sigma-total
 * displayed-transfor uncurrying.
 *
 * This fragment extends the exact 2B2 declaration/runtime lineage. The
 * reviewed continuation already owns `Sigma_catd_functord_catd` and its
 * fibre computation; this module adds only the five missing declarations
 * and the later object-component rule.
 */

import {
    CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE,
    coreDirectedContinuationTransferSymbol
} from './directed_continuation_transfer';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferBuilderExpression,
    CoreLfTransferExpression,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferScopedBuilder,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreLfTransferExplicitBody,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    CoreLfTransferDeclarationLink
} from './lf_transfer_compiler';
import {
    CoreLfCompiledMixedModule,
    CoreLfMixedDeclarationLinkage,
    CoreLfMixedPhasePlan,
    compileCoreLfMixedPhases,
    createCoreLfMixedDeclarationLinkage,
    planCoreLfMixedPhases
} from './lf_transfer_mixed';
import { binderMode } from './kernel';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';
import {
    CORE_LF_SCALE_STRESS_2_SIGMA_TRANSFOR_ACQUISITION
} from './scale_stress_2_acquisition';
import {
    CORE_LF_SCALE_STRESS_2A_LINKAGE
} from './scale_stress_2_representation';
import {
    CORE_LF_SCALE_STRESS_2B1_LINKAGE,
    CORE_LF_SCALE_STRESS_2B1_SYMBOLS
} from './scale_stress_2b_representation';
import {
    CORE_LF_SCALE_STRESS_2B2_LINKAGE,
    CORE_LF_SCALE_STRESS_2B2_SYMBOLS,
    CoreLfScaleStress2b2Compilation,
    compileCoreLfScaleStress2b2Representation
} from './scale_stress_2b2_representation';

const moduleId = 'emdash.emdash3_2';

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
const transforClassifier =
    coreDirectedContinuationTransferSymbol('transfor-classifier');
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
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const transforComponentCapped =
    coreDirectedContinuationTransferSymbol(
        'transfor-component-capped'
    );
const displayedFunctorCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-functor-category'
    );
const sigmaCategory =
    coreDirectedContinuationTransferSymbol('sigma-category');
const sigmaTelescopeFamily =
    coreDirectedContinuationTransferSymbol(
        'sigma-telescope-family'
    );
const dependentPair =
    coreDirectedContinuationTransferSymbol('dependent-pair');

const displayedFamilyClassifier =
    coreLfQualifiedSymbol(moduleId, 'Catd');
const { displayedFunctorClassifier } =
    CORE_LF_SCALE_STRESS_2B1_SYMBOLS;
const { fibreCategory } =
    CORE_LF_SCALE_STRESS_2B2_SYMBOLS;

export const CORE_LF_SCALE_STRESS_2B3_SYMBOLS = Object.freeze({
    displayedTransformationCategory:
        coreLfQualifiedSymbol(moduleId, 'Transfd_cat'),
    displayedTransformationClassifier:
        coreLfQualifiedSymbol(moduleId, 'Transfd'),
    sigmaDisplayedTransformation:
        coreLfQualifiedSymbol(moduleId, 'Sigma_transfd_funcd'),
    fibreFunctor:
        coreLfQualifiedSymbol(moduleId, 'Fibre_func'),
    displayedComponent:
        coreLfQualifiedSymbol(moduleId, 'tdapp0_fapp0')
});

const {
    displayedTransformationCategory,
    displayedTransformationClassifier,
    sigmaDisplayedTransformation,
    fibreFunctor,
    displayedComponent
} = CORE_LF_SCALE_STRESS_2B3_SYMBOLS;

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

const displayedFamilyClassifierAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedFamilyClassifier, [{
        plicity: 'explicit',
        value: base
    }]);

const displayedFamilyType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, displayedFamilyClassifierAt(builder, base));

const functorType = (
    builder: CoreLfTransferScopedBuilder,
    source_: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, functorClassifier, [
        { plicity: 'explicit', value: source_ },
        { plicity: 'explicit', value: target }
    ]));

const transforType = (
    builder: CoreLfTransferScopedBuilder,
    source_: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, transforClassifier, [
        { plicity: 'implicit', value: source_ },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: sourceFunctor },
        { plicity: 'explicit', value: targetFunctor }
    ]));

const constantFamily = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    fibre: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, constantDisplayedFamily, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: fibre }
    ]);

const displayedFunctorType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source_: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, displayedFunctorClassifier, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source_ },
        { plicity: 'explicit', value: target }
    ]));

const sigmaTotal = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const sigmaFamily = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    telescope: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaTelescopeFamily, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: family },
        { plicity: 'explicit', value: telescope }
    ]);

const fapp0 = (
    builder: CoreLfTransferScopedBuilder,
    source_: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorObject, [
        { plicity: 'implicit', value: source_ },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: object }
    ]);

const tapp0 = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression,
    transfor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, transforComponentCapped, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: object },
        { plicity: 'explicit', value: transfor }
    ]);

const fibre = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, fibreCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: object }
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

const displayedTransformationClassifierAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedTransformationClassifier, [
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
    decode(builder, displayedTransformationClassifierAt(
        builder,
        base,
        sourceFamily,
        targetFamily,
        sourceFunctor,
        targetFunctor
    ));

const fibreFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, fibreFunctor, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: object }
    ]);

const displayedComponentAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression,
    transfor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedComponent, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'implicit', value: sourceFunctor },
        { plicity: 'implicit', value: targetFunctor },
        { plicity: 'explicit', value: object },
        { plicity: 'explicit', value: transfor }
    ]);

const sigmaDisplayedTransformationAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression,
    transfor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaDisplayedTransformation, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: family },
        { plicity: 'implicit', value: sourceFunctor },
        { plicity: 'implicit', value: targetFunctor },
        { plicity: 'explicit', value: transfor }
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

const source = (
    sourceFragment: string,
    canonicalCommandOrdinal: number
) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment,
    canonicalCommandOrdinal
});

const modifiers = (
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
                    FF => builder.pi(
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
                    FF => builder.pi(
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

const sigmaDisplayedTransformationType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'R',
            displayedFamilyType(builder, K),
            R => {
                const constantCategories = constantFamily(
                    builder,
                    K,
                    builder.global(categoryOfCategories)
                );
                return builder.pi(
                    'S',
                    displayedFunctorType(
                        builder,
                        K,
                        R,
                        constantCategories
                    ),
                    S => builder.pi(
                        'T',
                        displayedFunctorType(
                            builder,
                            K,
                            R,
                            constantCategories
                        ),
                        T => builder.pi(
                            'eta',
                            displayedTransformationType(
                                builder,
                                K,
                                R,
                                constantCategories,
                                S,
                                T
                            ),
                            _eta => displayedFunctorType(
                                builder,
                                sigmaTotal(builder, K, R),
                                sigmaFamily(builder, K, R, S),
                                sigmaFamily(builder, K, R, T)
                            ),
                            explicitMode
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

const fibreFunctorType = (): CoreLfTransferExpression => {
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
                        'z',
                        objectType(builder, K),
                        z => functorType(
                            builder,
                            fibre(builder, K, E, z),
                            fibre(builder, K, D, z)
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

const displayedComponentType = (): CoreLfTransferExpression => {
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
                                    fibre(builder, K, E, z),
                                    fibre(builder, K, D, z),
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

const sigmaObjectComponentRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const R = builder.capture('R');
    const S = builder.capture('S');
    const T = builder.capture('T');
    const eta = builder.capture('eta');
    const k = builder.capture('k');
    const r = builder.capture('r');
    const constantCategories = constantFamily(
        builder,
        K,
        builder.global(categoryOfCategories)
    );
    return {
        order: 5,
        id: 'stress.sigma-transfor.object-component',
        groupId: 'stress.sigma-transfor.object-component',
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
                name: 'S',
                type: builder.template(displayedFunctorType(
                    builder,
                    K,
                    R,
                    constantCategories
                ))
            },
            {
                name: 'T',
                type: builder.template(displayedFunctorType(
                    builder,
                    K,
                    R,
                    constantCategories
                ))
            },
            {
                name: 'eta',
                type: builder.template(
                    displayedTransformationType(
                        builder,
                        K,
                        R,
                        constantCategories,
                        S,
                        T
                    )
                )
            },
            {
                name: 'k',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'r',
                type: builder.template(
                    objectType(builder, fibre(builder, K, R, k))
                )
            }
        ],
        left: builder.pattern(tapp0(
            builder,
            sigmaTotal(builder, K, R),
            builder.global(categoryOfCategories),
            sigmaFamily(builder, K, R, S),
            sigmaFamily(builder, K, R, T),
            sigmaPair(builder, K, R, k, r),
            sigmaDisplayedTransformationAt(
                builder,
                K,
                R,
                S,
                T,
                eta
            )
        )),
        right: builder.template(tapp0(
            builder,
            fibre(builder, K, R, k),
            builder.global(categoryOfCategories),
            fibreFunctorAt(builder, K, R, constantCategories, S, k),
            fibreFunctorAt(builder, K, R, constantCategories, T, k),
            r,
            displayedComponentAt(
                builder,
                K,
                R,
                constantCategories,
                S,
                T,
                k,
                eta
            )
        )),
        provenance: source(
            '(@Sigma_transfd_funcd $K $R $S $T $eta)',
            1068
        )
    };
};

const declarations = [
    {
        order: 0,
        symbol: displayedTransformationCategory,
        type: displayedTransformationCategoryType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
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
        modifiers: modifiers('injective', 'transparent'),
        provenance: source(
            'injective symbol Transfd [K : Cat]',
            402
        )
    },
    {
        order: 2,
        symbol: sigmaDisplayedTransformation,
        type: sigmaDisplayedTransformationType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('constant', 'opaque'),
        provenance: source(
            'constant symbol Sigma_transfd_funcd [K : Cat]',
            1009
        )
    },
    {
        order: 3,
        symbol: fibreFunctor,
        type: fibreFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol Fibre_func [K : Cat]',
            1056
        )
    },
    {
        order: 4,
        symbol: displayedComponent,
        type: displayedComponentType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol tdapp0_fapp0 [K : Cat]',
            1058
        )
    }
] as const;

const runtimeRules = [sigmaObjectComponentRule()] as const;

export const CORE_LF_SCALE_STRESS_2B3_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'SCALE-STRESS-2B3-SIGMA-TRANSFOR-REPRESENTATION-1',
    moduleId,
    fragmentId: 'scale-stress-2b3-sigma-transfor',
    authorityPath:
        CORE_LF_SCALE_STRESS_2_SIGMA_TRANSFOR_ACQUISITION
            .authorityPath,
    sourceSha256:
        CORE_LF_SCALE_STRESS_2_SIGMA_TRANSFOR_ACQUISITION
            .sourceSha256,
    canonicalExport: {
        exporterVersion:
            CORE_LF_SCALE_STRESS_2_SIGMA_TRANSFOR_ACQUISITION
                .canonicalExport.exporterVersion,
        sha256:
            CORE_LF_SCALE_STRESS_2_SIGMA_TRANSFOR_ACQUISITION
                .canonicalExport.sha256
    },
    dependencies: [],
    externalSymbols: [
        category,
        groupoid,
        decodeOwner,
        objectClassifier,
        functorClassifier,
        transforClassifier,
        categoryOfCategories,
        displayedCategoryCategory,
        constantDisplayedFamily,
        functorObject,
        transforComponentCapped,
        displayedFunctorCategory,
        sigmaCategory,
        sigmaTelescopeFamily,
        dependentPair,
        displayedFamilyClassifier,
        displayedFunctorClassifier,
        fibreCategory
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const CORE_LF_SCALE_STRESS_2B3_POLICY:
CoreLfTransferPolicyOverlay =
    createCoreLfTransferPolicyOverlay(
        CORE_LF_SCALE_STRESS_2B3_MODULE,
        {
            revision:
                'SCALE-STRESS-2B3-SIGMA-TRANSFOR-POLICY-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_2B3_MODULE.revision,
            entries: [
                ...declarations.map((declaration, order) => ({
                    order,
                    target: {
                        kind: 'declaration' as const,
                        symbol: declaration.symbol
                    },
                    policy:
                        declaration.symbol ===
                            displayedTransformationClassifier
                            ? 'checked-transparent-definition' as const
                            : 'opaque-signature' as const,
                    evidence:
                        'Exact active declaration in isolated 2B3 evidence'
                })),
                {
                    order: declarations.length,
                    target: {
                        kind: 'runtime-rule' as const,
                        id: runtimeRules[0].id
                    },
                    policy: 'runtime-rewrite' as const,
                    evidence:
                        'Exact active runtime rule in isolated 2B3 evidence'
                }
            ]
        }
    );

export const CORE_LF_SCALE_STRESS_2B3_PLAN:
CoreLfMixedPhasePlan = planCoreLfMixedPhases(
    CORE_LF_SCALE_STRESS_2B3_MODULE,
    CORE_LF_SCALE_STRESS_2B3_POLICY
);

const linkForExternal = (
    symbol: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const link = [
        ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries,
        ...CORE_LF_SCALE_STRESS_2A_LINKAGE.entries,
        ...CORE_LF_SCALE_STRESS_2B1_LINKAGE.entries,
        ...CORE_LF_SCALE_STRESS_2B2_LINKAGE.entries
    ].find(candidate =>
        candidate.symbol.moduleId === symbol.moduleId &&
        candidate.symbol.name === symbol.name
    );
    if (link === undefined) {
        throw new Error(
            `No reviewed prerequisite link for ` +
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
    CORE_LF_SCALE_STRESS_2B3_MODULE.externalSymbols.map(
        external => external.symbol
    );

export const CORE_LF_SCALE_STRESS_2B3_LINKAGE:
CoreLfMixedDeclarationLinkage =
    createCoreLfMixedDeclarationLinkage(
        CORE_LF_SCALE_STRESS_2B3_PLAN,
        {
            revision:
                'SCALE-STRESS-2B3-SIGMA-TRANSFOR-LINKAGE-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_2B3_MODULE.revision,
            entries: [
                ...externalSymbols.map(linkForExternal),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `emdash_v3_2_scale_stress_2b3_` +
                        declaration.symbol.name,
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

export const CORE_LF_SCALE_STRESS_2B3_BOUNDARY = Object.freeze({
    semanticStatus: 'isolated-representation-only',
    reusedPrerequisiteCommands: Object.freeze([
        'Sigma_catd_functord_catd',
        'directed.sigma-telescope-fibre.evaluate'
    ]),
    selectedTransparentBodies: Object.freeze([
        displayedTransformationClassifier
    ]),
    withheldTransparentBodies: Object.freeze([
        Object.freeze({
            symbol: fibreFunctor,
            reason:
                'Exact Cat-valued Transf/Functord body conversion is ' +
                'outside the inherited runtime closure'
        })
    ]),
    runtimeSubjectOracleRuleIds: Object.freeze([
        'stress.sigma-transfor.object-component'
    ]),
    doesNotProvide: Object.freeze([
        'active-policy-selection',
        'complete-Fibre_func-transparent-body',
        'Transfd-proof-unification',
        'Transfd-category-hom-runtime-bridge',
        'tdapp0-functor-or-identity-composition-rules',
        'Sigma-total-arrow-action',
        'browser-api',
        'mechanical-transfer-qualification'
    ])
});

const subjectOracleIds = new Set(
    CORE_LF_SCALE_STRESS_2B3_BOUNDARY
        .runtimeSubjectOracleRuleIds
);

export interface CoreLfScaleStress2b3Compilation {
    readonly prerequisite: CoreLfScaleStress2b2Compilation;
    readonly compiled: CoreLfCompiledMixedModule;
}

export function compileCoreLfScaleStress2b3Representation():
CoreLfScaleStress2b3Compilation {
    validateCoreLfScaleEngineReview();
    const prerequisite =
        compileCoreLfScaleStress2b2Representation();
    const priorRuntime = prerequisite.compiled.latestRuntime;
    if (priorRuntime === undefined) {
        throw new Error(
            'SCALE-STRESS-2B2 did not produce its required runtime'
        );
    }
    const compiled = compileCoreLfMixedPhases(
        CORE_LF_SCALE_STRESS_2B3_PLAN,
        CORE_LF_SCALE_STRESS_2B3_LINKAGE,
        {
            initialDeclarations:
                prerequisite.compiled.declarations,
            runtimeDependencies: [{
                relation: 'earlier-fragment',
                fragment: priorRuntime
            }],
            runtimeOptions: phase => {
                const ruleIds = phase.module.runtimeRules
                    .map(rule => rule.id)
                    .filter(ruleId => subjectOracleIds.has(ruleId));
                return ruleIds.length === 0
                    ? {}
                    : {
                        subjectReductionOracle: {
                            authorityPath:
                                'emdash2/emdash3_2.lp',
                            ruleIds,
                            evidence:
                                'Exact active subject reduction; ' +
                                'Fibre_func Cat-valued conversion body ' +
                                'is explicitly outside 2B3'
                        }
                    };
            }
        }
    );
    return Object.freeze({
        prerequisite,
        compiled
    });
}
