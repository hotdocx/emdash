/**
 * Representation-only SCALE-STRESS-2B1 transfer of the active
 * internal/pullback dependent-Pi package.
 *
 * The fragment extends the exact SCALE-STRESS-2A declaration context and
 * consumes the reviewed continuation runtime as an explicit same-module
 * earlier fragment. It installs nothing in the default, browser, MVP, or
 * reviewed directed profiles.
 */

import {
    CORE_DIRECTED_CONTINUATION_RUNTIME_SUBJECT_ORACLE,
    CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE,
    CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_POLICY
} from './directed_continuation_runtime_transfer';
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
import {
    CoreLfCompiledRuntimeFragment,
    compileCoreLfRuntimeFragment
} from './lf_transfer_runtime';
import { binderMode } from './kernel';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';
import {
    CORE_LF_SCALE_STRESS_2_INTERNAL_PI_ACQUISITION
} from './scale_stress_2_acquisition';
import {
    CORE_LF_SCALE_STRESS_2A_LINKAGE,
    CoreLfScaleStress2aCompilation,
    compileCoreLfScaleStress2aRepresentation
} from './scale_stress_2_representation';

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
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const transforComponentCapped =
    coreDirectedContinuationTransferSymbol(
        'transfor-component-capped'
    );
const displayedFunctorCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-functor-category'
    );

export const CORE_LF_SCALE_STRESS_2B1_SYMBOLS = Object.freeze({
    oppositeCategory: coreLfQualifiedSymbol(moduleId, 'Op_cat'),
    displayedFunctorClassifier:
        coreLfQualifiedSymbol(moduleId, 'Functord'),
    displayedCategoryFunctor:
        coreLfQualifiedSymbol(moduleId, 'Catd_cat_func'),
    pullbackDisplayedFamily:
        coreLfQualifiedSymbol(moduleId, 'Pullback_catd'),
    pullbackDisplayedFamilyFunctor:
        coreLfQualifiedSymbol(moduleId, 'Pullback_catd_func'),
    sectionCategoryFunctor:
        coreLfQualifiedSymbol(moduleId, 'Pi_func'),
    internalPi:
        coreLfQualifiedSymbol(moduleId, 'Pi_int_funcd'),
    pullbackPi:
        coreLfQualifiedSymbol(moduleId, 'Pi_pullback_funcd')
});

const {
    oppositeCategory,
    displayedFunctorClassifier,
    displayedCategoryFunctor,
    pullbackDisplayedFamily,
    pullbackDisplayedFamilyFunctor,
    sectionCategoryFunctor,
    internalPi,
    pullbackPi
} = CORE_LF_SCALE_STRESS_2B1_SYMBOLS;

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

const opposite = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, oppositeCategory, [{
        plicity: 'explicit',
        value: base
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
    source_: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, functorClassifier, [
        { plicity: 'explicit', value: source_ },
        { plicity: 'explicit', value: target }
    ]));

const displayedFamilyType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, objectClassifier, [{
        plicity: 'explicit',
        value: displayedCategory(builder, base)
    }]));

const displayedCategory = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedCategoryCategory, [{
        plicity: 'explicit',
        value: base
    }]);

const constantFamily = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    fibre: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, constantDisplayedFamily, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: fibre }
    ]);

const displayedFunctor = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source_: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedFunctorClassifier, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source_ },
        { plicity: 'explicit', value: target }
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

const pullbackFamilyFunctor = (
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

const fapp1 = (
    builder: CoreLfTransferScopedBuilder,
    source_: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorHomCapped, [
        { plicity: 'implicit', value: source_ },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: functor },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: arrow }
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

const oppositeCategoryType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        _A => builder.global(category),
        explicitMode
    ));
};

const displayedFunctorClassifierType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            _E => builder.pi(
                'D',
                displayedFamilyType(builder, K),
                _D => builder.global(groupoid),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const displayedFunctorClassifierBody =
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
                D => globalCall(builder, objectClassifier, [{
                    plicity: 'explicit',
                    value: globalCall(
                        builder,
                        displayedFunctorCategory,
                        [
                            { plicity: 'implicit', value: K },
                            { plicity: 'explicit', value: E },
                            { plicity: 'explicit', value: D }
                        ]
                    )
                }]),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const displayedCategoryFunctorType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(functorType(
        builder,
        opposite(builder, builder.global(categoryOfCategories)),
        builder.global(categoryOfCategories)
    ));
};

const pullbackDisplayedFamilyType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'E',
                displayedFamilyType(builder, B),
                _E => builder.pi(
                    'F',
                    functorType(builder, A, B),
                    _F => displayedFamilyType(builder, A),
                    explicitMode
                ),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const pullbackDisplayedFamilyFunctorType =
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
                _F => functorType(
                    builder,
                    displayedCategory(builder, B),
                    displayedCategory(builder, A)
                ),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const sectionCategoryFunctorType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => functorType(
            builder,
            displayedCategory(builder, K),
            builder.global(categoryOfCategories)
        ),
        explicitMode
    ));
};

const internalPiType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    const base =
        opposite(builder, builder.global(categoryOfCategories));
    return builder.term(decode(builder, displayedFunctor(
        builder,
        base,
        builder.global(displayedCategoryFunctor),
        constantFamily(
            builder,
            base,
            builder.global(categoryOfCategories)
        )
    )));
};

const pullbackPiType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'G',
            functorType(
                builder,
                K,
                opposite(
                    builder,
                    builder.global(categoryOfCategories)
                )
            ),
            G => decode(builder, displayedFunctor(
                builder,
                K,
                pullbackFamily(
                    builder,
                    K,
                    opposite(
                        builder,
                        builder.global(categoryOfCategories)
                    ),
                    builder.global(displayedCategoryFunctor),
                    G
                ),
                constantFamily(
                    builder,
                    K,
                    builder.global(categoryOfCategories)
                )
            )),
            explicitMode
        ),
        implicitMode
    ));
};

const oppositeObjectRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    return {
        order: 1,
        id: 'stress.internal-pi.opposite-object',
        groupId: 'stress.internal-pi.opposite-object',
        clauseOrder: 0,
        sourceOwner: objectClassifier,
        variables: [{
            name: 'A',
            type: builder.template(builder.global(category))
        }],
        left: builder.pattern(globalCall(
            builder,
            objectClassifier,
            [{
                plicity: 'explicit',
                value: opposite(builder, A)
            }]
        )),
        right: builder.template(globalCall(
            builder,
            objectClassifier,
            [{ plicity: 'explicit', value: A }]
        )),
        provenance: source(
            'rule Obj (Op_cat $A) ↪ Obj $A;',
            238
        )
    };
};

const pullbackFibreRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const E = builder.capture('E');
    const F = builder.capture('F');
    const a = builder.capture('a');
    return {
        order: 5,
        id: 'stress.internal-pi.pullback-fibre',
        groupId: 'stress.internal-pi.pullback-fibre',
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
                name: 'E',
                type: builder.template(
                    displayedFamilyType(builder, B)
                )
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, A, B))
            },
            {
                name: 'a',
                type: builder.template(objectType(builder, A))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            A,
            builder.global(categoryOfCategories),
            pullbackFamily(builder, A, B, E, F),
            a
        )),
        right: builder.template(fapp0(
            builder,
            B,
            builder.global(categoryOfCategories),
            E,
            fapp0(builder, A, B, F, a)
        )),
        provenance: source(
            'rule @fapp0 _ Cat_cat ' +
                '(@Pullback_catd $A $B $E $F) $a',
            927
        )
    };
};

const pullbackFunctorObjectRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const F = builder.capture('F');
    const E = builder.capture('E');
    return {
        order: 7,
        id: 'stress.internal-pi.pullback-functor-object',
        groupId: 'stress.internal-pi.pullback-functor-object',
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
                type: builder.template(
                    displayedFamilyType(builder, B)
                )
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            displayedCategory(builder, B),
            displayedCategory(builder, A),
            pullbackFamilyFunctor(builder, A, B, F),
            E
        )),
        right: builder.template(
            pullbackFamily(builder, A, B, E, F)
        ),
        provenance: source(
            '(@Pullback_catd_func $A $B $F) $E',
            931
        )
    };
};

const constantFibreRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const x = builder.capture('x');
    return {
        order: 8,
        id: 'stress.internal-pi.constant-fibre',
        groupId: 'stress.internal-pi.constant-fibre',
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
                name: 'x',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            K,
            builder.global(categoryOfCategories),
            constantFamily(builder, K, A),
            x
        )),
        right: builder.template(A),
        provenance: source(
            'rule @fapp0 $K Cat_cat ' +
                '(@Const_catd $K $A) $_ ↪ $A;',
            939
        )
    };
};

const constantPullbackRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const F = builder.capture('F');
    return {
        order: 9,
        id: 'stress.internal-pi.constant-pullback',
        groupId: 'stress.internal-pi.constant-pullback',
        clauseOrder: 0,
        sourceOwner: pullbackDisplayedFamily,
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
                name: 'C',
                type: builder.template(builder.global(category))
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, A, B))
            }
        ],
        left: builder.pattern(pullbackFamily(
            builder,
            A,
            B,
            constantFamily(builder, B, C),
            F
        )),
        right: builder.template(constantFamily(builder, A, C)),
        provenance: source(
            'rule @Pullback_catd $A $B ' +
                '(@Const_catd $B $C) $F',
            941
        )
    };
};

const sectionFunctorObjectRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    return {
        order: 11,
        id: 'stress.internal-pi.section-functor-object',
        groupId: 'stress.internal-pi.section-functor-object',
        clauseOrder: 0,
        sourceOwner: functorObject,
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
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            displayedCategory(builder, K),
            builder.global(categoryOfCategories),
            globalCall(builder, sectionCategoryFunctor, [{
                plicity: 'explicit',
                value: K
            }]),
            E
        )),
        right: builder.template(globalCall(
            builder,
            sectionCategory,
            [
                { plicity: 'implicit', value: K },
                { plicity: 'explicit', value: E }
            ]
        )),
        provenance: source(
            'rule @fapp0 _ Cat_cat (@Pi_func $K) $E',
            970
        )
    };
};

const internalPiComponentRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const base =
        opposite(builder, builder.global(categoryOfCategories));
    const sourceFamily = builder.global(displayedCategoryFunctor);
    const targetFamily = constantFamily(
        builder,
        base,
        builder.global(categoryOfCategories)
    );
    return {
        order: 13,
        id: 'stress.internal-pi.package-component',
        groupId: 'stress.internal-pi.package-component',
        clauseOrder: 0,
        sourceOwner: transforComponentCapped,
        variables: [{
            name: 'K',
            type: builder.template(builder.global(category))
        }],
        left: builder.pattern(tapp0(
            builder,
            base,
            builder.global(categoryOfCategories),
            sourceFamily,
            targetFamily,
            K,
            builder.global(internalPi)
        )),
        right: builder.template(globalCall(
            builder,
            sectionCategoryFunctor,
            [{ plicity: 'explicit', value: K }]
        )),
        provenance: source(
            '(Op_cat Cat_cat)\n' +
                '      Cat_cat\n' +
                '      _\n' +
                '      _\n' +
                '      $K\n' +
                '      Pi_int_funcd',
            973
        )
    };
};

const pullbackPiFoldRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const G = builder.capture('G');
    const oppositeCategories =
        opposite(builder, builder.global(categoryOfCategories));
    const sourceFamily = builder.global(displayedCategoryFunctor);
    const targetFamily = constantFamily(
        builder,
        oppositeCategories,
        builder.global(categoryOfCategories)
    );
    return {
        order: 15,
        id: 'stress.internal-pi.pullback-fold',
        groupId: 'stress.internal-pi.pullback-fold',
        clauseOrder: 0,
        sourceOwner: functorHomCapped,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'G',
                type: builder.template(functorType(
                    builder,
                    K,
                    oppositeCategories
                ))
            }
        ],
        left: builder.pattern(fapp1(
            builder,
            displayedCategory(builder, oppositeCategories),
            displayedCategory(builder, K),
            pullbackFamilyFunctor(
                builder,
                K,
                oppositeCategories,
                G
            ),
            sourceFamily,
            targetFamily,
            builder.global(internalPi)
        )),
        right: builder.template(globalCall(
            builder,
            pullbackPi,
            [
                { plicity: 'implicit', value: K },
                { plicity: 'explicit', value: G }
            ]
        )),
        provenance: source(
            '(@Pullback_catd_func $K (Op_cat Cat_cat) $G)',
            975
        )
    };
};

const pullbackPiComponentRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const G = builder.capture('G');
    const x = builder.capture('x');
    const oppositeCategories =
        opposite(builder, builder.global(categoryOfCategories));
    const sourceFamily = pullbackFamily(
        builder,
        K,
        oppositeCategories,
        builder.global(displayedCategoryFunctor),
        G
    );
    const targetFamily = constantFamily(
        builder,
        K,
        builder.global(categoryOfCategories)
    );
    return {
        order: 16,
        id: 'stress.internal-pi.pullback-component',
        groupId: 'stress.internal-pi.pullback-component',
        clauseOrder: 0,
        sourceOwner: transforComponentCapped,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'G',
                type: builder.template(functorType(
                    builder,
                    K,
                    oppositeCategories
                ))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(tapp0(
            builder,
            K,
            builder.global(categoryOfCategories),
            sourceFamily,
            targetFamily,
            x,
            globalCall(builder, pullbackPi, [
                { plicity: 'implicit', value: K },
                { plicity: 'explicit', value: G }
            ])
        )),
        right: builder.template(globalCall(
            builder,
            sectionCategoryFunctor,
            [{
                plicity: 'explicit',
                value: fapp0(
                    builder,
                    K,
                    oppositeCategories,
                    G,
                    x
                )
            }]
        )),
        provenance: source(
            '(@Pi_pullback_funcd $K $G)\n' +
                '  ↪ @Pi_func ' +
                '(@fapp0 $K (Op_cat Cat_cat) $G $x);',
            976
        )
    };
};

const declarations = [
    {
        order: 0,
        symbol: oppositeCategory,
        type: oppositeCategoryType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Op_cat : Cat → Cat;',
            236
        )
    },
    {
        order: 2,
        symbol: displayedFunctorClassifier,
        type: displayedFunctorClassifierType(),
        body: coreLfTransferExplicitBody(
            displayedFunctorClassifierBody()
        ),
        modifiers: modifiers('injective', 'transparent'),
        provenance: source(
            'injective symbol Functord [K : Cat] ' +
                '(E D : τ (Catd K)) : Grpd',
            394
        )
    },
    {
        order: 3,
        symbol: displayedCategoryFunctor,
        type: displayedCategoryFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol Catd_cat_func : ' +
                'τ (Functor (Op_cat Cat_cat) Cat_cat)',
            538
        )
    },
    {
        order: 4,
        symbol: pullbackDisplayedFamily,
        type: pullbackDisplayedFamilyType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Pullback_catd [A B : Cat]',
            926
        )
    },
    {
        order: 6,
        symbol: pullbackDisplayedFamilyFunctor,
        type: pullbackDisplayedFamilyFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Pullback_catd_func [A B : Cat]',
            930
        )
    },
    {
        order: 10,
        symbol: sectionCategoryFunctor,
        type: sectionCategoryFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Pi_func (K : Cat) ' +
                ': τ (Functor (Catd_cat K) Cat_cat);',
            969
        )
    },
    {
        order: 12,
        symbol: internalPi,
        type: internalPiType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('constant', 'opaque'),
        provenance: source(
            'constant symbol Pi_int_funcd',
            972
        )
    },
    {
        order: 14,
        symbol: pullbackPi,
        type: pullbackPiType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Pi_pullback_funcd [K : Cat]',
            974
        )
    }
] as const;

const runtimeRules = [
    oppositeObjectRule(),
    pullbackFibreRule(),
    pullbackFunctorObjectRule(),
    constantFibreRule(),
    constantPullbackRule(),
    sectionFunctorObjectRule(),
    internalPiComponentRule(),
    pullbackPiFoldRule(),
    pullbackPiComponentRule()
] as const;

export const CORE_LF_SCALE_STRESS_2B1_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'SCALE-STRESS-2B1-INTERNAL-PI-REPRESENTATION-1',
    moduleId,
    fragmentId: 'scale-stress-2b1-internal-pi',
    authorityPath:
        CORE_LF_SCALE_STRESS_2_INTERNAL_PI_ACQUISITION.authorityPath,
    sourceSha256:
        CORE_LF_SCALE_STRESS_2_INTERNAL_PI_ACQUISITION.sourceSha256,
    canonicalExport: {
        exporterVersion:
            CORE_LF_SCALE_STRESS_2_INTERNAL_PI_ACQUISITION
                .canonicalExport.exporterVersion,
        sha256:
            CORE_LF_SCALE_STRESS_2_INTERNAL_PI_ACQUISITION
                .canonicalExport.sha256
    },
    dependencies: [],
    externalSymbols: [
        category,
        groupoid,
        decodeOwner,
        objectClassifier,
        functorClassifier,
        categoryOfCategories,
        displayedCategoryCategory,
        constantDisplayedFamily,
        sectionCategory,
        functorObject,
        functorHomCapped,
        transforComponentCapped,
        displayedFunctorCategory
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules,
    proofRules: []
});

const policySources = [
    ...declarations.map(declaration => ({
        sourceOrder: declaration.order,
        target: {
            kind: 'declaration' as const,
            symbol: declaration.symbol
        },
        policy:
            declaration.symbol === displayedFunctorClassifier
                ? 'checked-transparent-definition' as const
                : 'opaque-signature' as const,
        evidence:
            declaration.symbol === displayedCategoryFunctor
                ? 'Exact active type; transparent body dependency closure ' +
                    'is explicitly withheld in 2B1'
                : 'Exact active declaration in isolated 2B1 evidence'
    })),
    ...runtimeRules.map(rule => ({
        sourceOrder: rule.order,
        target: {
            kind: 'runtime-rule' as const,
            id: rule.id
        },
        policy: 'runtime-rewrite' as const,
        evidence:
            'Exact active runtime rule in isolated 2B1 evidence'
    }))
].sort((left, right) => left.sourceOrder - right.sourceOrder);

export const CORE_LF_SCALE_STRESS_2B1_POLICY:
CoreLfTransferPolicyOverlay =
    createCoreLfTransferPolicyOverlay(
        CORE_LF_SCALE_STRESS_2B1_MODULE,
        {
            revision: 'SCALE-STRESS-2B1-INTERNAL-PI-POLICY-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_2B1_MODULE.revision,
            entries: policySources.map((entry, order) => ({
                order,
                target: entry.target,
                policy: entry.policy,
                evidence: entry.evidence
            }))
        }
    );

export const CORE_LF_SCALE_STRESS_2B1_PLAN:
CoreLfMixedPhasePlan = planCoreLfMixedPhases(
    CORE_LF_SCALE_STRESS_2B1_MODULE,
    CORE_LF_SCALE_STRESS_2B1_POLICY
);

const linkForExternal = (
    symbol: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const link = [
        ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries,
        ...CORE_LF_SCALE_STRESS_2A_LINKAGE.entries
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
    CORE_LF_SCALE_STRESS_2B1_MODULE.externalSymbols.map(
        external => external.symbol
    );

export const CORE_LF_SCALE_STRESS_2B1_LINKAGE:
CoreLfMixedDeclarationLinkage =
    createCoreLfMixedDeclarationLinkage(
        CORE_LF_SCALE_STRESS_2B1_PLAN,
        {
            revision: 'SCALE-STRESS-2B1-INTERNAL-PI-LINKAGE-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_2B1_MODULE.revision,
            entries: [
                ...externalSymbols.map(linkForExternal),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `emdash_v3_2_scale_stress_2b1_` +
                        declaration.symbol.name,
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

/**
 * `Catd_cat_func` is transparent in Lambdapi, but its explicit body opens a
 * separate composition/functor-category dependency closure. 2B1 selects its
 * exact type opaquely; that closure plus the standalone displayed-hom/decode
 * normalization boundary leaves three exact subject checks explicit.
 */
export const CORE_LF_SCALE_STRESS_2B1_BOUNDARY = Object.freeze({
    semanticStatus: 'isolated-representation-only',
    selectedTransparentBody: Object.freeze({
        symbol: displayedCategoryFunctor,
        treatment: 'opaque-type-only',
        reason:
            'Exact comp_cat_fapp0/Functor_cat_func body closure is outside ' +
            'the bounded internal-Pi runtime slice'
    }),
    runtimeSubjectOracleRuleIds: Object.freeze([
        'stress.internal-pi.package-component',
        'stress.internal-pi.pullback-fold',
        'stress.internal-pi.pullback-component'
    ]),
    doesNotProvide: Object.freeze([
        'active-policy-selection',
        'complete-Catd_cat_func-transparent-body',
        'internal-Pi-base-arrow-action',
        'Sigma-transfor-uncurrying',
        'browser-api',
        'mechanical-transfer-qualification'
    ])
});

const subjectOracleIds = new Set(
    CORE_LF_SCALE_STRESS_2B1_BOUNDARY
        .runtimeSubjectOracleRuleIds
);

export interface CoreLfScaleStress2b1Compilation {
    readonly prerequisite: CoreLfScaleStress2aCompilation;
    readonly continuationRuntime:
        CoreLfCompiledRuntimeFragment;
    readonly compiled: CoreLfCompiledMixedModule;
}

export function compileCoreLfScaleStress2b1Representation():
CoreLfScaleStress2b1Compilation {
    validateCoreLfScaleEngineReview();
    const prerequisite =
        compileCoreLfScaleStress2aRepresentation();
    const continuationRuntime = compileCoreLfRuntimeFragment(
        CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE,
        CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_POLICY,
        prerequisite.compiled.declarations,
        {
            dependencies: [],
            subjectReductionOracle:
                CORE_DIRECTED_CONTINUATION_RUNTIME_SUBJECT_ORACLE
        }
    );
    const compiled = compileCoreLfMixedPhases(
        CORE_LF_SCALE_STRESS_2B1_PLAN,
        CORE_LF_SCALE_STRESS_2B1_LINKAGE,
        {
            initialDeclarations:
                prerequisite.compiled.declarations,
            runtimeDependencies: [{
                relation: 'earlier-fragment',
                fragment: continuationRuntime
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
                                'Catd_cat_func/composition and ' +
                                'displayed-hom normalization closure ' +
                                'are explicitly outside 2B1'
                        }
                    };
            }
        }
    );
    return Object.freeze({
        prerequisite,
        continuationRuntime,
        compiled
    });
}
