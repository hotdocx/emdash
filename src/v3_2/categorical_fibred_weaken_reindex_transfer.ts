/**
 * FIBRED-WEAKEN-REINDEX-1 existing-authority transfer closure.
 *
 * The four declarations and six runtime clauses below are literal active
 * v3.2 ingredients: two source-prior prerequisites and four consumer
 * clauses. They compile on top of FIBRED-TRANSFD-1 through the generic
 * declaration/runtime engines and install no new kernel mathematics.
 */

import {
    CORE_CATEGORICAL_COMPREHENSION_TRANSFER_LINKAGE
} from './categorical_comprehension_transfer';
import {
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS,
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE
} from './categorical_dependent_composition_transfer';
import {
    CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE
} from './categorical_dependent_transfer';
import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_SOURCE_SHA256,
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE,
    CoreCategoricalFibredTransfdCompilation,
    compileCoreCategoricalFibredTransfdTransfer
} from './categorical_fibred_transfd_transfer';
import {
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT,
    validateCoreCategoricalFibredWeakenReindexContract
} from './categorical_fibred_weaken_reindex_contract';
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
import {
    CORE_LF_SCALE_STRESS_2A_LINKAGE,
    CORE_LF_SCALE_STRESS_2A_MODULE
} from './scale_stress_2_representation';
import {
    CORE_LF_SCALE_STRESS_2B1_LINKAGE,
    CORE_LF_SCALE_STRESS_2B1_MODULE,
    CORE_LF_SCALE_STRESS_2B1_SYMBOLS
} from './scale_stress_2b_representation';
import {
    CORE_LF_SCALE_STRESS_2B2_LINKAGE,
    CORE_LF_SCALE_STRESS_2B2_MODULE,
    CORE_LF_SCALE_STRESS_2B2_SYMBOLS
} from './scale_stress_2b2_representation';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';

export const
CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_REVISION =
    'FIBRED-WEAKEN-REINDEX-1-EXISTING-AUTHORITY-TRANSFER-1' as const;

const MODULE_ID = 'emdash.emdash3_2';

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
const sigmaCategory =
    coreDirectedContinuationTransferSymbol('sigma-category');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-category-category'
    );
const constantDisplayedFamily =
    coreDirectedContinuationTransferSymbol(
        'constant-displayed-family'
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
const pullbackDisplayedFamily =
    coreLfQualifiedSymbol(MODULE_ID, 'Pullback_catd');
const sigmaProjection =
    coreLfQualifiedSymbol(MODULE_ID, 'Sigma_proj1_func');
const sigmaProjectionPullback =
    CORE_LF_SCALE_STRESS_2A_MODULE.declarations[1].symbol;
const sectionObjectEvaluation =
    coreLfQualifiedSymbol(MODULE_ID, 'piapp0');
const {
    terminalCategory
} = CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS;

const {
    pullbackDisplayedFamilyFunctor
} = CORE_LF_SCALE_STRESS_2B1_SYMBOLS;
const {
    sectionPullback
} = CORE_LF_SCALE_STRESS_2B2_SYMBOLS;
const pointFunctor =
    coreLfQualifiedSymbol(MODULE_ID, 'Obj_func');
const sectionPullbackSection =
    coreLfQualifiedSymbol(MODULE_ID, 'section_pullback_sec');

export const CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_SYMBOLS =
Object.freeze({
    pullbackDisplayedFamilyFunctor,
    pointFunctor,
    sectionPullback,
    sectionPullbackSection
});

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
        displayedFunctorCategoryAt(
            builder,
            base,
            source,
            target
        )
    );

const constantFamily = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    fibre: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, constantDisplayedFamily, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: fibre }
    ]);

const pullbackFamily = (
    builder: CoreLfTransferScopedBuilder,
    sourceBase: CoreLfTransferBuilderExpression,
    targetBase: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pullbackDisplayedFamily, [
        { plicity: 'implicit', value: sourceBase },
        { plicity: 'implicit', value: targetBase },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: functor }
    ]);

const pullbackFunctor = (
    builder: CoreLfTransferScopedBuilder,
    sourceBase: CoreLfTransferBuilderExpression,
    targetBase: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, pullbackDisplayedFamilyFunctor, [
        { plicity: 'implicit', value: sourceBase },
        { plicity: 'implicit', value: targetBase },
        { plicity: 'explicit', value: functor }
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

const fapp0 = (
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

const fapp1 = (
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

const component = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    point: CoreLfTransferBuilderExpression,
    transformation: CoreLfTransferBuilderExpression
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
        { plicity: 'explicit', value: transformation }
    ]);

const sectionPullbackAt = (
    builder: CoreLfTransferScopedBuilder,
    sourceBase: CoreLfTransferBuilderExpression,
    targetBase: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sectionPullback, [
        { plicity: 'implicit', value: sourceBase },
        { plicity: 'implicit', value: targetBase },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: family }
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
    globalCall(builder, sectionObjectEvaluation, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: family },
        { plicity: 'explicit', value: section },
        { plicity: 'explicit', value: point }
    ]);

const source = (
    sourceFragment: string
) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const publicModifiers = (
    rigidity: 'ordinary' | 'constant' | 'injective',
    sourceOpacity: 'transparent' | 'opaque'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity
});

const selectedDeclaration = (
    module: CoreLfModuleSpec,
    name: string,
    order: number
) => {
    const declaration = module.declarations.find(
        candidate => candidate.symbol.name === name
    );
    if (declaration === undefined) {
        throw new Error(
            `FIBRED-WEAKEN-REINDEX-1 cannot reuse declaration '${name}'`
        );
    }
    return Object.freeze({
        ...declaration,
        order
    });
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

const sectionPullbackSectionType =
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
                functorType(builder, A, B),
                F => builder.pi(
                    'E',
                    displayedFamilyType(builder, B),
                    E => builder.pi(
                        's',
                        objectType(
                            builder,
                            displayedFunctorCategoryAt(
                                builder,
                                B,
                                constantFamily(
                                    builder,
                                    B,
                                    builder.global(terminalCategory)
                                ),
                                E
                            )
                        ),
                        _s => objectType(
                            builder,
                            displayedFunctorCategoryAt(
                                builder,
                                A,
                                constantFamily(
                                    builder,
                                    A,
                                    builder.global(terminalCategory)
                                ),
                                pullbackFamily(
                                    builder,
                                    A,
                                    B,
                                    E,
                                    F
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
    ));
};

const declarations = Object.freeze([
    selectedDeclaration(
        CORE_LF_SCALE_STRESS_2B1_MODULE,
        'Pullback_catd_func',
        0
    ),
    {
        order: 1,
        symbol: pointFunctor,
        type: pointFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'transparent'),
        provenance: source(
            'injective symbol Obj_func [Y : Cat] ' +
            '(y : τ (Obj Y)) : τ (Functor Terminal_cat Y)'
        )
    },
    selectedDeclaration(
        CORE_LF_SCALE_STRESS_2B2_MODULE,
        'section_pullback_func',
        2
    ),
    {
        order: 3,
        symbol: sectionPullbackSection,
        type: sectionPullbackSectionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol section_pullback_sec [A B : Cat] ' +
            '(F : τ (Functor A B)) (E : τ (Catd B))'
        )
    }
] as const);

const reusedPullbackObjectRule = (): CoreLfTransferRuntimeRule => {
    const rule = CORE_LF_SCALE_STRESS_2B1_MODULE.runtimeRules.find(
        candidate =>
            candidate.id ===
                'stress.internal-pi.pullback-functor-object'
    );
    if (rule === undefined) {
        throw new Error(
            'FIBRED-WEAKEN-REINDEX-1 lost the reviewed pullback object rule'
        );
    }
    return Object.freeze({
        ...rule,
        order: 2,
        id: 'categorical.weaken-reindex.pullback-functor-object',
        groupId:
            'categorical.weaken-reindex.pullback-functor-object'
    });
};

const constantFamilyObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const k = builder.capture('k');
    return {
        order: 0,
        id:
            'categorical.weaken-reindex.' +
            'constant-family-object-prerequisite',
        groupId:
            'categorical.weaken-reindex.' +
            'constant-family-object-prerequisite',
        clauseOrder: 0,
        sourceOwner: functorObject,
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
                name: 'k',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            K,
            builder.global(categoryOfCategories),
            constantFamily(builder, K, A),
            k
        )),
        right: builder.template(A),
        provenance: source(
            'rule @fapp0 $K Cat_cat (@Const_catd $K $A) $_ ↪ $A'
        )
    };
};

const pullbackHomComponentRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const eta = builder.capture('eta');
    const a = builder.capture('a');
    const pulledE = pullbackFamily(builder, A, B, E, F);
    const pulledD = pullbackFamily(builder, A, B, D, F);
    const pulledEta = fapp1(
        builder,
        displayedCategoryAt(builder, B),
        displayedCategoryAt(builder, A),
        pullbackFunctor(builder, A, B, F),
        E,
        D,
        eta
    );
    return {
        order: 3,
        id: 'categorical.weaken-reindex.pullback-hom-component',
        groupId:
            'categorical.weaken-reindex.pullback-hom-component',
        clauseOrder: 0,
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
                type: builder.template(functorType(builder, A, B))
            },
            {
                name: 'E',
                type: builder.template(displayedFamilyType(builder, B))
            },
            {
                name: 'D',
                type: builder.template(displayedFamilyType(builder, B))
            },
            {
                name: 'eta',
                type: builder.template(
                    displayedFunctorType(builder, B, E, D)
                )
            },
            {
                name: 'a',
                type: builder.template(objectType(builder, A))
            }
        ],
        left: builder.pattern(component(
            builder,
            A,
            pulledE,
            pulledD,
            a,
            pulledEta
        )),
        right: builder.template(component(
            builder,
            B,
            E,
            D,
            fapp0(builder, A, B, F, a),
            eta
        )),
        provenance: source(
            'rule @tapp0_fapp0 $A Cat_cat _ _ $a ' +
            '(@fapp1_fapp0 (@Catd_cat $B) (@Catd_cat $A) ' +
            '(@Pullback_catd_func $A $B $F) $E $D $eta)'
        )
    };
};

const sectionPullbackObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const E = builder.capture('E');
    const s = builder.capture('s');
    const sourceFamily = constantFamily(
        builder,
        B,
        builder.global(terminalCategory)
    );
    return {
        order: 4,
        id: 'categorical.weaken-reindex.section-pullback-object',
        groupId:
            'categorical.weaken-reindex.section-pullback-object',
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
                name: 'E',
                type: builder.template(displayedFamilyType(builder, B))
            },
            {
                name: 's',
                type: builder.template(
                    objectType(
                        builder,
                        displayedFunctorCategoryAt(
                            builder,
                            B,
                            sourceFamily,
                            E
                        )
                    )
                )
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            displayedFunctorCategoryAt(
                builder,
                B,
                sourceFamily,
                E
            ),
            displayedFunctorCategoryAt(
                builder,
                A,
                constantFamily(
                    builder,
                    A,
                    builder.global(terminalCategory)
                ),
                pullbackFamily(builder, A, B, E, F)
            ),
            sectionPullbackAt(builder, A, B, F, E),
            s
        )),
        right: builder.template(
            sectionPullbackSectionAt(builder, A, B, F, E, s)
        ),
        provenance: source(
            'rule @fapp0 _ _ ' +
            '(@section_pullback_func $A $B $F $E) $s ' +
            '↪ @section_pullback_sec $A $B $F $E $s'
        )
    };
};

const sectionPullbackComponentRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const E = builder.capture('E');
    const s = builder.capture('s');
    const a = builder.capture('a');
    const pulled = pullbackFamily(builder, A, B, E, F);
    const pulledFibre = fibre(builder, A, pulled, a);
    const sourceFamily = constantFamily(
        builder,
        B,
        builder.global(terminalCategory)
    );
    return {
        order: 5,
        id: 'categorical.weaken-reindex.section-pullback-component',
        groupId:
            'categorical.weaken-reindex.section-pullback-component',
        clauseOrder: 0,
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
                type: builder.template(functorType(builder, A, B))
            },
            {
                name: 'E',
                type: builder.template(displayedFamilyType(builder, B))
            },
            {
                name: 's',
                type: builder.template(
                    objectType(
                        builder,
                        displayedFunctorCategoryAt(
                            builder,
                            B,
                            sourceFamily,
                            E
                        )
                    )
                )
            },
            {
                name: 'a',
                type: builder.template(objectType(builder, A))
            }
        ],
        left: builder.pattern(component(
            builder,
            A,
            constantFamily(
                builder,
                A,
                builder.global(terminalCategory)
            ),
            pulled,
            a,
            sectionPullbackSectionAt(builder, A, B, F, E, s)
        )),
        right: builder.template(globalCall(builder, pointFunctor, [
            { plicity: 'implicit', value: pulledFibre },
            {
                plicity: 'explicit',
                value: sectionAt(
                    builder,
                    B,
                    E,
                    s,
                    fapp0(builder, A, B, F, a)
                )
            }
        ])),
        provenance: source(
            'rule @tapp0_fapp0 $A Cat_cat _ _ $a ' +
            '(@section_pullback_sec $A $B $F $E $s) ' +
            '↪ @Obj_func (Fibre_cat ' +
            '(@Pullback_catd $A $B $E $F) $a) ' +
            '(@piapp0 $B $E $s (@fapp0 $A $B $F $a))'
        )
    };
};

const sigmaProjectionPullbackFoldRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const R = builder.capture('R');
    const D = builder.capture('D');
    const total = globalCall(builder, sigmaCategory, [
        { plicity: 'implicit', value: K },
        { plicity: 'explicit', value: R }
    ]);
    const projection = globalCall(builder, sigmaProjection, [
        { plicity: 'implicit', value: K },
        { plicity: 'explicit', value: R }
    ]);
    return {
        order: 1,
        id:
            'categorical.weaken-reindex.' +
            'sigma-projection-pullback-fold-prerequisite',
        groupId:
            'categorical.weaken-reindex.' +
            'sigma-projection-pullback-fold-prerequisite',
        clauseOrder: 0,
        sourceOwner: pullbackDisplayedFamily,
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
        left: builder.pattern(pullbackFamily(
            builder,
            total,
            K,
            D,
            projection
        )),
        right: builder.template(globalCall(
            builder,
            sigmaProjectionPullback,
            [
                { plicity: 'implicit', value: K },
                { plicity: 'explicit', value: R },
                { plicity: 'explicit', value: D }
            ]
        )),
        provenance: source(
            'rule @Pullback_catd _ $K $D ' +
                '(@Sigma_proj1_func $K $R) ' +
                '↪ @Sigma_proj1_pullback_catd $K $R $D'
        )
    };
};

const runtimeRules = Object.freeze([
    constantFamilyObjectRule(),
    sigmaProjectionPullbackFoldRule(),
    reusedPullbackObjectRule(),
    pullbackHomComponentRule(),
    sectionPullbackObjectRule(),
    sectionPullbackComponentRule()
]);

const externalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    functorClassifier,
    categoryOfCategories,
    sigmaCategory,
    displayedCategoryCategory,
    constantDisplayedFamily,
    displayedFunctorCategory,
    functorObject,
    functorHomCapped,
    transforComponentCapped,
    pullbackDisplayedFamily,
    sigmaProjection,
    sigmaProjectionPullback,
    sectionObjectEvaluation,
    terminalCategory
]);

export const
CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'fibred-weaken-reindex-1-signatures',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        CORE_CATEGORICAL_FIBRED_TRANSFD_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: externalSymbols.map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const
CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_MODULE,
    {
        revision:
            'FIBRED-WEAKEN-REINDEX-1-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_MODULE
                .revision,
        entries: declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                declaration.symbol === pointFunctor
                    ? 'Exact active transparent Obj_func signature; its ' +
                        'body is outside this literal rule prerequisite'
                    : 'Exact active v3.2 signature required by the frozen ' +
                        'weakening/reindexing consumer'
        }))
    }
);

const earlierLinks = [
    ...CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_COMPREHENSION_TRANSFER_LINKAGE.entries,
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries,
    ...CORE_LF_SCALE_STRESS_2A_LINKAGE.entries,
    ...CORE_LF_SCALE_STRESS_2B1_LINKAGE.entries,
    ...CORE_LF_SCALE_STRESS_2B2_LINKAGE.entries
];

const symbolEquals = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId &&
    left.name === right.name;

const dependencyLink = (
    symbol: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const link = earlierLinks.find(candidate =>
        symbolEquals(candidate.symbol, symbol)
    );
    if (link === undefined) {
        throw new Error(
            `FIBRED-WEAKEN-REINDEX-1 has no dependency link for ` +
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
): string | undefined => {
    const link = earlierLinks.find(candidate =>
        symbolEquals(candidate.symbol, symbol) &&
        candidate.kind === 'free-declaration' &&
        (
            candidate.coreName.startsWith(
                'emdash_v3_2_scale_stress_2b1_'
            ) ||
            candidate.coreName.startsWith(
                'emdash_v3_2_scale_stress_2b2_'
            )
        )
    );
    return link?.kind === 'free-declaration'
        ? link.coreName
        : undefined;
};

const localCoreName = (
    symbol: CoreLfQualifiedSymbol
): string =>
    reusedCoreName(symbol) ??
    `emdash_v3_2_fibred_weaken_reindex_1_${symbol.name}`;

export const
CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_MODULE,
        {
            revision:
                'FIBRED-WEAKEN-REINDEX-1-SIGNATURE-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_MODULE
                    .revision,
            entries: [
                ...externalSymbols.map(dependencyLink),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName: localCoreName(declaration.symbol),
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

export const
CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'FIBRED-WEAKEN-REINDEX-1-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'fibred-weaken-reindex-1-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        CORE_CATEGORICAL_FIBRED_TRANSFD_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        ...externalSymbols,
        ...declarations.map(declaration => declaration.symbol)
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const
CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_RUNTIME_MODULE,
    {
        revision: 'FIBRED-WEAKEN-REINDEX-1-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_RUNTIME_MODULE
                .revision,
        entries: runtimeRules.map((rule, order) => ({
            order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact active v3.2 object/component projection required ' +
                'by the frozen weakening/reindexing consumer'
        }))
    }
);

export const
CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CORE_NAMES =
Object.freeze({
    pullbackDisplayedFamilyFunctor:
        localCoreName(pullbackDisplayedFamilyFunctor),
    pointFunctor: localCoreName(pointFunctor),
    sectionPullback: localCoreName(sectionPullback),
    sectionPullbackSection:
        localCoreName(sectionPullbackSection)
});

export type CoreCategoricalFibredWeakenReindexCoreId =
    keyof typeof CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CORE_NAMES;

export function coreCategoricalFibredWeakenReindexCoreName(
    id: CoreCategoricalFibredWeakenReindexCoreId
): string {
    return CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CORE_NAMES[id];
}

export const
CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_BOUNDARY =
Object.freeze({
    status: 'root-only-existing-authority-weakening-reindexing',
    contractRevision:
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT.revision,
    declarationNames:
        Object.freeze(declarations.map(entry => entry.symbol.name)),
    runtimeRuleIds:
        Object.freeze(runtimeRules.map(rule => rule.id)),
    declarationCount: declarations.length,
    runtimeRuleCount: runtimeRules.length,
    prerequisiteRuntimeRuleCount: 2,
    consumerRuntimeRuleCount: 4,
    proofRuleCount: 0,
    newMathematicalOwnerCount: 0,
    newMathematicalRuntimeRuleCount: 0,
    newMathematicalProofRuleCount: 0,
    allEntriesUseGenericTransferEngines: true,
    doesNotProvide:
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT.doesNotProvide
});

export interface CoreCategoricalFibredWeakenReindexCompilation {
    readonly prerequisite: CoreCategoricalFibredTransfdCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

export function compileCoreCategoricalFibredWeakenReindexTransfer():
CoreCategoricalFibredWeakenReindexCompilation {
    validateCoreCategoricalFibredWeakenReindexContract();
    validateCoreLfScaleEngineReview();
    const prerequisite =
        compileCoreCategoricalFibredTransfdTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_MODULE,
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_POLICY,
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_LINKAGE,
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
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_RUNTIME_MODULE,
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_RUNTIME_POLICY,
        initialContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: prerequisiteFragment
            }]
        }
    );
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_MODULE,
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_POLICY,
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: runtimeFragment.runtime
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        prerequisite.declarationContext,
        [compiled]
    );
    return Object.freeze({
        prerequisite,
        compiled,
        declarationContext,
        runtimeFragment,
        runtime: runtimeFragment.localProgram,
        composedRuntime: runtimeFragment.runtime
    });
}
