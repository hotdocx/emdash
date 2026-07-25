/**
 * Representation-only SCALE-STRESS-2B2 transfer of internal dependent-Pi
 * base-arrow action.
 *
 * This fragment extends the exact 2B1 declaration/runtime lineage. It adds
 * only the six declaration types required by the two active
 * `fdapp1_int_cell` rules and installs nothing in a default, browser, MVP, or
 * reviewed directed profile.
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
    CORE_LF_SCALE_STRESS_2_PI_BASE_ACTION_ACQUISITION
} from './scale_stress_2_acquisition';
import {
    CORE_LF_SCALE_STRESS_2A_LINKAGE
} from './scale_stress_2_representation';
import {
    CORE_LF_SCALE_STRESS_2B1_LINKAGE,
    CORE_LF_SCALE_STRESS_2B1_SYMBOLS,
    CoreLfScaleStress2b1Compilation,
    compileCoreLfScaleStress2b1Representation
} from './scale_stress_2b_representation';

const moduleId = 'emdash.emdash3_2';

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner =
    coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const functorClassifier =
    coreDirectedContinuationTransferSymbol('functor-classifier');
const homClassifier =
    coreDirectedContinuationTransferSymbol('hom-classifier');
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
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const displayedFunctorCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-functor-category'
    );

const {
    oppositeCategory,
    displayedFunctorClassifier,
    displayedCategoryFunctor,
    pullbackDisplayedFamily,
    internalPi,
    pullbackPi
} = CORE_LF_SCALE_STRESS_2B1_SYMBOLS;

export const CORE_LF_SCALE_STRESS_2B2_SYMBOLS = Object.freeze({
    terminalCategory:
        coreLfQualifiedSymbol(moduleId, 'Terminal_cat'),
    fibreCategory:
        coreLfQualifiedSymbol(moduleId, 'Fibre_cat'),
    displayedTransportLeft:
        coreLfQualifiedSymbol(
            moduleId,
            'functord_transport_lhs_func'
        ),
    displayedTransportRight:
        coreLfQualifiedSymbol(
            moduleId,
            'functord_transport_rhs_func'
        ),
    displayedInternalCell:
        coreLfQualifiedSymbol(moduleId, 'fdapp1_int_cell'),
    sectionPullback:
        coreLfQualifiedSymbol(moduleId, 'section_pullback_func')
});

const {
    terminalCategory,
    fibreCategory,
    displayedTransportLeft,
    displayedTransportRight,
    displayedInternalCell,
    sectionPullback
} = CORE_LF_SCALE_STRESS_2B2_SYMBOLS;

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

const displayedCategory = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedCategoryCategory, [{
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

const displayedFamilyType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    objectType(builder, displayedCategory(builder, base));

const functorType = (
    builder: CoreLfTransferScopedBuilder,
    source_: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, functorClassifier, [
        { plicity: 'explicit', value: source_ },
        { plicity: 'explicit', value: target }
    ]));

const homType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source_: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, homClassifier, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: source_ },
        { plicity: 'explicit', value: target }
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

const displayedFunctorCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source_: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedFunctorCategory, [
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

const displayedTransport = (
    builder: CoreLfTransferScopedBuilder,
    symbol: CoreLfQualifiedSymbol,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor_: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, symbol, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor_ },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: arrow }
    ]);

const internalCell = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression,
    displayedFunctor_: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedInternalCell, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: sourceFamily },
        { plicity: 'implicit', value: targetFamily },
        { plicity: 'explicit', value: displayedFunctor_ },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: arrow },
        { plicity: 'explicit', value: object }
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

const terminalCategoryType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.global(category));
};

const fibreCategoryType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            E => builder.pi(
                'k',
                objectType(builder, K),
                _k => builder.global(category),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const fibreCategoryBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'K',
        builder.global(category),
        K => builder.lam(
            'E',
            displayedFamilyType(builder, K),
            E => builder.lam(
                'k',
                objectType(builder, K),
                k => fapp0(
                    builder,
                    K,
                    builder.global(categoryOfCategories),
                    E,
                    k
                ),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const displayedTransportType = (): CoreLfTransferExpression => {
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
                    decode(builder, displayedFunctor(
                        builder,
                        K,
                        E,
                        D
                    )),
                    _FF => builder.pi(
                        'x',
                        objectType(builder, K),
                        x => builder.pi(
                            'y',
                            objectType(builder, K),
                            y => builder.pi(
                                'p',
                                homType(builder, K, x, y),
                                _p => functorType(
                                    builder,
                                    fibre(builder, K, E, x),
                                    fibre(builder, K, D, y)
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

const displayedInternalCellType =
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
                    decode(builder, displayedFunctor(
                        builder,
                        K,
                        E,
                        D
                    )),
                    FF => builder.pi(
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
                                        fibre(builder, K, E, x)
                                    ),
                                    u => homType(
                                        builder,
                                        fibre(builder, K, D, y),
                                        fapp0(
                                            builder,
                                            fibre(builder, K, E, x),
                                            fibre(builder, K, D, y),
                                            displayedTransport(
                                                builder,
                                                displayedTransportLeft,
                                                K,
                                                E,
                                                D,
                                                FF,
                                                x,
                                                y,
                                                p
                                            ),
                                            u
                                        ),
                                        fapp0(
                                            builder,
                                            fibre(builder, K, E, x),
                                            fibre(builder, K, D, y),
                                            displayedTransport(
                                                builder,
                                                displayedTransportRight,
                                                K,
                                                E,
                                                D,
                                                FF,
                                                x,
                                                y,
                                                p
                                            ),
                                            u
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
                    explicitMode
                ),
                implicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const sectionPullbackType = (): CoreLfTransferExpression => {
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
                    E => functorType(
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
                        )
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

const internalPiBaseActionRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const B = builder.capture('B');
    const A = builder.capture('A');
    const F = builder.capture('F');
    const E = builder.capture('E');
    const base =
        opposite(builder, builder.global(categoryOfCategories));
    const sourceFamily = builder.global(displayedCategoryFunctor);
    const targetFamily = constantFamily(
        builder,
        base,
        builder.global(categoryOfCategories)
    );
    return {
        order: 6,
        id: 'stress.internal-pi.base-action',
        groupId: 'stress.internal-pi.base-action',
        clauseOrder: 0,
        sourceOwner: displayedInternalCell,
        variables: [
            {
                name: 'B',
                type: builder.template(builder.global(category))
            },
            {
                name: 'A',
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
        left: builder.pattern(internalCell(
            builder,
            base,
            sourceFamily,
            targetFamily,
            builder.global(internalPi),
            B,
            A,
            F,
            E
        )),
        right: builder.template(sectionPullbackAt(
            builder,
            A,
            B,
            F,
            E
        )),
        provenance: source(
            'rule @fdapp1_int_cell _ _ _ ' +
                'Pi_int_funcd $B $A $F $E',
            1195
        )
    };
};

const pullbackPiBaseActionRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const G = builder.capture('G');
    const x = builder.capture('x');
    const y = builder.capture('y');
    const p = builder.capture('p');
    const E = builder.capture('E');
    const oppositeCategories =
        opposite(builder, builder.global(categoryOfCategories));
    const Gx = fapp0(builder, K, oppositeCategories, G, x);
    const Gy = fapp0(builder, K, oppositeCategories, G, y);
    const Gp = fapp1(
        builder,
        K,
        oppositeCategories,
        G,
        x,
        y,
        p
    );
    const displayedFamiliesAtGx = fapp0(
        builder,
        oppositeCategories,
        builder.global(categoryOfCategories),
        builder.global(displayedCategoryFunctor),
        Gx
    );
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
        order: 7,
        id: 'stress.internal-pi.pullback-base-action',
        groupId: 'stress.internal-pi.pullback-base-action',
        clauseOrder: 0,
        sourceOwner: displayedInternalCell,
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
            },
            {
                name: 'y',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, K, x, y))
            },
            {
                name: 'E',
                type: builder.template(
                    objectType(builder, displayedFamiliesAtGx)
                )
            }
        ],
        left: builder.pattern(internalCell(
            builder,
            K,
            sourceFamily,
            targetFamily,
            globalCall(builder, pullbackPi, [
                { plicity: 'implicit', value: K },
                { plicity: 'explicit', value: G }
            ]),
            x,
            y,
            p,
            E
        )),
        right: builder.template(sectionPullbackAt(
            builder,
            Gy,
            Gx,
            Gp,
            E
        )),
        provenance: source(
            'rule @fdapp1_int_cell\n' +
                '      $K\n' +
                '      _\n' +
                '      _\n' +
                '      (@Pi_pullback_funcd $K $G)',
            1196
        )
    };
};

const declarations = [
    {
        order: 0,
        symbol: terminalCategory,
        type: terminalCategoryType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('constant', 'opaque'),
        provenance: source(
            'constant symbol Terminal_cat : Cat;',
            512
        )
    },
    {
        order: 1,
        symbol: fibreCategory,
        type: fibreCategoryType(),
        body: coreLfTransferExplicitBody(fibreCategoryBody()),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol Fibre_cat [K : Cat] ' +
                '(E : τ (Catd K)) (k : τ (Obj K)) : Cat',
            925
        )
    },
    {
        order: 2,
        symbol: displayedTransportLeft,
        type: displayedTransportType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol functord_transport_lhs_func [K : Cat]',
            1074
        )
    },
    {
        order: 3,
        symbol: displayedTransportRight,
        type: displayedTransportType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol functord_transport_rhs_func [K : Cat]',
            1075
        )
    },
    {
        order: 4,
        symbol: displayedInternalCell,
        type: displayedInternalCellType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol fdapp1_int_cell [K : Cat]',
            1095
        )
    },
    {
        order: 5,
        symbol: sectionPullback,
        type: sectionPullbackType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol section_pullback_func [A B : Cat]',
            1189
        )
    }
] as const;

const runtimeRules = [
    internalPiBaseActionRule(),
    pullbackPiBaseActionRule()
] as const;

export const CORE_LF_SCALE_STRESS_2B2_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'SCALE-STRESS-2B2-PI-BASE-ACTION-REPRESENTATION-1',
    moduleId,
    fragmentId: 'scale-stress-2b2-pi-base-action',
    authorityPath:
        CORE_LF_SCALE_STRESS_2_PI_BASE_ACTION_ACQUISITION.authorityPath,
    sourceSha256:
        CORE_LF_SCALE_STRESS_2_PI_BASE_ACTION_ACQUISITION.sourceSha256,
    canonicalExport: {
        exporterVersion:
            CORE_LF_SCALE_STRESS_2_PI_BASE_ACTION_ACQUISITION
                .canonicalExport.exporterVersion,
        sha256:
            CORE_LF_SCALE_STRESS_2_PI_BASE_ACTION_ACQUISITION
                .canonicalExport.sha256
    },
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        functorClassifier,
        homClassifier,
        categoryOfCategories,
        displayedCategoryCategory,
        constantDisplayedFamily,
        functorObject,
        functorHomCapped,
        displayedFunctorCategory,
        oppositeCategory,
        displayedFunctorClassifier,
        displayedCategoryFunctor,
        pullbackDisplayedFamily,
        internalPi,
        pullbackPi
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
            declaration.symbol === fibreCategory
                ? 'checked-transparent-definition' as const
                : 'opaque-signature' as const,
        evidence:
            declaration.symbol === displayedTransportLeft ||
            declaration.symbol === displayedTransportRight
                ? 'Exact active type; transparent composition/transport ' +
                    'body closure is explicitly withheld in 2B2'
                : 'Exact active declaration in isolated 2B2 evidence'
    })),
    ...runtimeRules.map(rule => ({
        sourceOrder: rule.order,
        target: {
            kind: 'runtime-rule' as const,
            id: rule.id
        },
        policy: 'runtime-rewrite' as const,
        evidence:
            'Exact active runtime rule in isolated 2B2 evidence'
    }))
].sort((left, right) => left.sourceOrder - right.sourceOrder);

export const CORE_LF_SCALE_STRESS_2B2_POLICY:
CoreLfTransferPolicyOverlay =
    createCoreLfTransferPolicyOverlay(
        CORE_LF_SCALE_STRESS_2B2_MODULE,
        {
            revision: 'SCALE-STRESS-2B2-PI-BASE-ACTION-POLICY-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_2B2_MODULE.revision,
            entries: policySources.map((entry, order) => ({
                order,
                target: entry.target,
                policy: entry.policy,
                evidence: entry.evidence
            }))
        }
    );

export const CORE_LF_SCALE_STRESS_2B2_PLAN:
CoreLfMixedPhasePlan = planCoreLfMixedPhases(
    CORE_LF_SCALE_STRESS_2B2_MODULE,
    CORE_LF_SCALE_STRESS_2B2_POLICY
);

const linkForExternal = (
    symbol: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const link = [
        ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries,
        ...CORE_LF_SCALE_STRESS_2A_LINKAGE.entries,
        ...CORE_LF_SCALE_STRESS_2B1_LINKAGE.entries
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
    CORE_LF_SCALE_STRESS_2B2_MODULE.externalSymbols.map(
        external => external.symbol
    );

export const CORE_LF_SCALE_STRESS_2B2_LINKAGE:
CoreLfMixedDeclarationLinkage =
    createCoreLfMixedDeclarationLinkage(
        CORE_LF_SCALE_STRESS_2B2_PLAN,
        {
            revision: 'SCALE-STRESS-2B2-PI-BASE-ACTION-LINKAGE-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_2B2_MODULE.revision,
            entries: [
                ...externalSymbols.map(linkForExternal),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `emdash_v3_2_scale_stress_2b2_` +
                        declaration.symbol.name,
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

/**
 * The active transport-left/right definitions open the separate
 * composition, fibre-functor, and displayed-transport closure. Their exact
 * types suffice to state the cell owner; both selected semantic reductions
 * remain exact subject-oracle cases until that body closure is represented.
 */
export const CORE_LF_SCALE_STRESS_2B2_BOUNDARY = Object.freeze({
    semanticStatus: 'isolated-representation-only',
    selectedTransparentBodies: Object.freeze([
        Object.freeze({
            symbol: displayedTransportLeft,
            treatment: 'opaque-type-only',
            reason:
                'Exact comp_cat_fapp0/catd_transport_func/Fibre_func ' +
                'body closure is outside 2B2'
        }),
        Object.freeze({
            symbol: displayedTransportRight,
            treatment: 'opaque-type-only',
            reason:
                'Exact comp_cat_fapp0/catd_transport_func/Fibre_func ' +
                'body closure is outside 2B2'
        })
    ]),
    runtimeSubjectOracleRuleIds: Object.freeze([
        'stress.internal-pi.base-action',
        'stress.internal-pi.pullback-base-action'
    ]),
    doesNotProvide: Object.freeze([
        'active-policy-selection',
        'complete-displayed-transport-transparent-bodies',
        'section-pullback-object-or-component-action',
        'Sigma-transfor-uncurrying',
        'browser-api',
        'mechanical-transfer-qualification'
    ])
});

const subjectOracleIds = new Set(
    CORE_LF_SCALE_STRESS_2B2_BOUNDARY
        .runtimeSubjectOracleRuleIds
);

export interface CoreLfScaleStress2b2Compilation {
    readonly prerequisite: CoreLfScaleStress2b1Compilation;
    readonly compiled: CoreLfCompiledMixedModule;
}

export function compileCoreLfScaleStress2b2Representation():
CoreLfScaleStress2b2Compilation {
    validateCoreLfScaleEngineReview();
    const prerequisite =
        compileCoreLfScaleStress2b1Representation();
    const priorRuntime = prerequisite.compiled.latestRuntime;
    if (priorRuntime === undefined) {
        throw new Error(
            'SCALE-STRESS-2B1 did not produce its required runtime'
        );
    }
    const compiled = compileCoreLfMixedPhases(
        CORE_LF_SCALE_STRESS_2B2_PLAN,
        CORE_LF_SCALE_STRESS_2B2_LINKAGE,
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
                                'displayed transport transparent-body ' +
                                'closure is explicitly outside 2B2'
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
