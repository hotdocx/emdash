/**
 * FIBRED-COMPREHENSION-1A transfer of asymmetric base-change
 * totalization.
 *
 * The active kernel already owns displayed-family reindexing
 * `Pullback_catd`, Sigma totals, dependent pairs, and canonical Sigma
 * arrows. This fragment transfers the two existing pullback projections,
 * the existing `sigma_arrow` signature, and the newly approved
 * `sigma_pullback_total_func` owner with its two computation rules.
 *
 * The transferred arrow rule uses the transparent canonical
 * `sigma_arrow` presentation. In the active kernel `sigma_arrow` unfolds to
 * the raw `Struct_sigma p alpha` matched by the production rule, so this is
 * a delta-specialization of that rule rather than a new equation.
 */

import {
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE,
    CoreCategoricalDependentCompositionCompilation,
    compileCoreCategoricalDependentCompositionTransfer
} from './categorical_dependent_composition_transfer';
import {
    CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE
} from './categorical_dependent_transfer';
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
    validateCoreLfScaleEngineReview
} from './scale_engine_review';

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_CATEGORICAL_COMPREHENSION_TRANSFER_REVISION =
    'FIBRED-COMPREHENSION-1A-BASE-CHANGE-TOTALIZATION-1' as const;

export const CORE_CATEGORICAL_COMPREHENSION_SOURCE_SHA256 =
    'sha256:1f741d471474eeea93ed6f89685fefd283d1b5bc3c40657a6e290d7c40c9136a';

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
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const sigmaCategory =
    coreDirectedContinuationTransferSymbol('sigma-category');
const dependentPair =
    coreDirectedContinuationTransferSymbol('dependent-pair');

/**
 * `Pullback_catd` is an already checked intrinsic Core owner, but it was
 * deliberately outside the frozen reviewed 29-signature continuation.
 * Link it directly to that existing owner instead of manufacturing a second
 * free declaration.
 */
const displayedPullback =
    coreLfQualifiedSymbol(MODULE_ID, 'Pullback_catd');

export const CORE_CATEGORICAL_COMPREHENSION_SYMBOLS = Object.freeze({
    displayedPullback,
    sigmaArrow:
        coreLfQualifiedSymbol(MODULE_ID, 'sigma_arrow'),
    sigmaPullbackTotalFunctor:
        coreLfQualifiedSymbol(
            MODULE_ID,
            'sigma_pullback_total_func'
        )
});

const {
    sigmaArrow,
    sigmaPullbackTotalFunctor
} = CORE_CATEGORICAL_COMPREHENSION_SYMBOLS;

export type CoreCategoricalComprehensionPrerequisiteId =
    | 'displayed-pullback-owner'
    | 'displayed-pullback-fibre-reduction'
    | 'displayed-pullback-arrow-reduction'
    | 'canonical-sigma-arrow';

export interface CoreCategoricalComprehensionPrerequisite {
    readonly id: CoreCategoricalComprehensionPrerequisiteId;
    readonly authorityName: string;
    readonly activeAuthority:
        | 'existing-intrinsic-owner'
        | 'active-runtime-rule'
        | 'checked-transparent-definition';
}

export const CORE_CATEGORICAL_COMPREHENSION_PREREQUISITES:
readonly CoreCategoricalComprehensionPrerequisite[] = Object.freeze([
    Object.freeze({
        id: 'displayed-pullback-owner' as const,
        authorityName: 'Pullback_catd',
        activeAuthority: 'existing-intrinsic-owner' as const
    }),
    Object.freeze({
        id: 'displayed-pullback-fibre-reduction' as const,
        authorityName: 'fapp0(Pullback_catd)',
        activeAuthority: 'active-runtime-rule' as const
    }),
    Object.freeze({
        id: 'displayed-pullback-arrow-reduction' as const,
        authorityName: 'fapp1_fapp0(Pullback_catd)',
        activeAuthority: 'active-runtime-rule' as const
    }),
    Object.freeze({
        id: 'canonical-sigma-arrow' as const,
        authorityName: 'sigma_arrow',
        activeAuthority: 'checked-transparent-definition' as const
    })
]);

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
    decode(
        builder,
        globalCall(builder, functorClassifier, [
            { plicity: 'explicit', value: source },
            { plicity: 'explicit', value: target }
        ])
    );

const homType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(
        builder,
        globalCall(builder, homClassifier, [
            { plicity: 'explicit', value: base },
            { plicity: 'explicit', value: source },
            { plicity: 'explicit', value: target }
        ])
    );

const displayedFamilyType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    objectType(
        builder,
        globalCall(builder, displayedCategoryCategory, [{
            plicity: 'explicit',
            value: base
        }])
    );

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

const functorArrowAt = (
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

const pullback = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedPullback, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: functor }
    ]);

const sigmaTotal = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaCategory, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
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

const sigmaArrowAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    sourcePoint: CoreLfTransferBuilderExpression,
    targetPoint: CoreLfTransferBuilderExpression,
    sourceValue: CoreLfTransferBuilderExpression,
    targetValue: CoreLfTransferBuilderExpression,
    baseArrow: CoreLfTransferBuilderExpression,
    fibreArrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaArrow, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family },
        { plicity: 'implicit', value: sourcePoint },
        { plicity: 'implicit', value: targetPoint },
        { plicity: 'explicit', value: sourceValue },
        { plicity: 'explicit', value: targetValue },
        { plicity: 'explicit', value: baseArrow },
        { plicity: 'explicit', value: fibreArrow }
    ]);

const pullbackTotal = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaPullbackTotalFunctor, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: family }
    ]);

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const sigmaArrowType = (): CoreLfTransferExpression => {
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
                        objectType(builder, fibre(builder, K, E, x)),
                        u => builder.pi(
                            'v',
                            objectType(
                                builder,
                                fibre(builder, K, E, y)
                            ),
                            v => builder.pi(
                                'p',
                                homType(builder, K, x, y),
                                p => {
                                    const transport = functorArrowAt(
                                        builder,
                                        K,
                                        builder.global(
                                            categoryOfCategories
                                        ),
                                        E,
                                        x,
                                        y,
                                        p
                                    );
                                    return builder.pi(
                                        'alpha',
                                        homType(
                                            builder,
                                            fibre(builder, K, E, y),
                                            functorObjectAt(
                                                builder,
                                                fibre(
                                                    builder,
                                                    K,
                                                    E,
                                                    x
                                                ),
                                                fibre(
                                                    builder,
                                                    K,
                                                    E,
                                                    y
                                                ),
                                                transport,
                                                u
                                            ),
                                            v
                                        ),
                                        _alpha => homType(
                                            builder,
                                            sigmaTotal(
                                                builder,
                                                K,
                                                E
                                            ),
                                            sigmaPair(
                                                builder,
                                                K,
                                                E,
                                                x,
                                                u
                                            ),
                                            sigmaPair(
                                                builder,
                                                K,
                                                E,
                                                y,
                                                v
                                            )
                                        ),
                                        explicitMode
                                    );
                                },
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
            explicitMode
        ),
        implicitMode
    ));
};

const displayedPullbackType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'K',
            builder.global(category),
            K => builder.pi(
                'D',
                displayedFamilyType(builder, K),
                _D => builder.pi(
                    'F',
                    functorType(builder, A, K),
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

const sigmaPullbackTotalType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'K',
            builder.global(category),
            K => builder.pi(
                'F',
                functorType(builder, A, K),
                F => builder.pi(
                    'D',
                    displayedFamilyType(builder, K),
                    D => functorType(
                        builder,
                        sigmaTotal(
                            builder,
                            A,
                            pullback(builder, A, K, D, F)
                        ),
                        sigmaTotal(builder, K, D)
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

const declarations: readonly CoreLfTransferDeclaration[] = [
    {
        order: 0,
        symbol: displayedPullback,
        type: displayedPullbackType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'injective',
            sourceOpacity: 'opaque'
        },
        provenance: source(
            'injective symbol Pullback_catd [A B : Cat]'
        )
    },
    {
        order: 1,
        symbol: sigmaArrow,
        type: sigmaArrowType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'ordinary',
            sourceOpacity: 'transparent'
        },
        provenance: source(
            'symbol sigma_arrow [K : Cat] (E : τ (Catd K))'
        )
    },
    {
        order: 2,
        symbol: sigmaPullbackTotalFunctor,
        type: sigmaPullbackTotalType(),
        body: coreLfTransferAbsentBody(),
        modifiers: {
            visibility: 'public',
            rigidity: 'injective',
            sourceOpacity: 'opaque'
        },
        provenance: source(
            'injective symbol sigma_pullback_total_func [A K : Cat]'
        )
    }
];

export const CORE_CATEGORICAL_COMPREHENSION_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_COMPREHENSION_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'fibred-comprehension-1a-signatures',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_COMPREHENSION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        functorClassifier,
        homClassifier,
        categoryOfCategories,
        displayedCategoryCategory,
        functorObject,
        functorHomCapped,
        sigmaCategory,
        dependentPair
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_CATEGORICAL_COMPREHENSION_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_COMPREHENSION_TRANSFER_MODULE,
    {
        revision:
            'FIBRED-COMPREHENSION-1A-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_COMPREHENSION_TRANSFER_MODULE.revision,
        entries: declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy:
                declaration.symbol === displayedPullback
                    ? 'conformance-only' as const
                    : 'opaque-signature' as const,
            evidence:
                declaration.symbol === displayedPullback
                    ? 'Existing checked intrinsic Core owner reused as the ' +
                        'active family-reindexing prerequisite'
                    : declaration.symbol === sigmaArrow
                    ? 'Exact active transparent sigma_arrow type, imported ' +
                        'opaquely because only its canonical presentation is ' +
                        'required by this bounded transfer'
                    : 'Exact approved active base-change totalization owner'
        }))
    }
);

const earlierLinks = [
    ...CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DEPENDENT_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries,
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries
];

const dependencyLink = (
    symbol: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    if (
        symbol.moduleId === displayedPullback.moduleId &&
        symbol.name === displayedPullback.name
    ) {
        return Object.freeze({
            order,
            symbol: Object.freeze({ ...symbol }),
            kind: 'core-owner' as const,
            owner: 'displayed-pullback' as const
        });
    }
    const link = earlierLinks.find(candidate =>
        candidate.symbol.moduleId === symbol.moduleId &&
        candidate.symbol.name === symbol.name
    );
    if (link === undefined) {
        throw new Error(
            `FIBRED-COMPREHENSION-1A has no dependency link for ` +
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
    CORE_CATEGORICAL_COMPREHENSION_TRANSFER_MODULE
        .externalSymbols
        .map(external => external.symbol);

export const CORE_CATEGORICAL_COMPREHENSION_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_COMPREHENSION_TRANSFER_MODULE,
        {
            revision:
                'FIBRED-COMPREHENSION-1A-SIGNATURE-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_COMPREHENSION_TRANSFER_MODULE
                    .revision,
            entries: [
                ...externalSymbols.map(dependencyLink),
                ...declarations.map((declaration, index) =>
                    declaration.symbol === displayedPullback
                        ? dependencyLink(
                            declaration.symbol,
                            externalSymbols.length + index
                        )
                        : {
                            order: externalSymbols.length + index,
                            symbol: declaration.symbol,
                            kind: 'free-declaration' as const,
                            coreName:
                                `emdash_v3_2_fibred_comprehension_1a_` +
                                declaration.symbol.name,
                            backendName: declaration.symbol.name
                        }
                )
            ]
        }
    );

const pullbackFibreRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const K = builder.capture('K');
    const D = builder.capture('D');
    const F = builder.capture('F');
    const a = builder.capture('a');
    return {
        order: 0,
        id: 'categorical.pullback.fibre',
        groupId: 'categorical.pullback',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'D',
                type: builder.template(
                    displayedFamilyType(builder, K)
                )
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, A, K))
            },
            {
                name: 'a',
                type: builder.template(objectType(builder, A))
            }
        ],
        left: builder.pattern(
            fibre(
                builder,
                A,
                pullback(builder, A, K, D, F),
                a
            )
        ),
        right: builder.template(
            fibre(
                builder,
                K,
                D,
                functorObjectAt(builder, A, K, F, a)
            )
        ),
        provenance: source(
            'rule @fapp0 _ Cat_cat ' +
            '(@Pullback_catd $A $B $E $F) $a'
        )
    };
};

const pullbackArrowRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const K = builder.capture('K');
    const D = builder.capture('D');
    const F = builder.capture('F');
    const a = builder.capture('a');
    const b = builder.capture('b');
    const p = builder.capture('p');
    const Fa = functorObjectAt(builder, A, K, F, a);
    const Fb = functorObjectAt(builder, A, K, F, b);
    return {
        order: 1,
        id: 'categorical.pullback.arrow',
        groupId: 'categorical.pullback',
        clauseOrder: 1,
        sourceOwner: functorHomCapped,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'D',
                type: builder.template(
                    displayedFamilyType(builder, K)
                )
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, A, K))
            },
            {
                name: 'a',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'b',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'p',
                type: builder.template(homType(builder, A, a, b))
            }
        ],
        left: builder.pattern(
            functorArrowAt(
                builder,
                A,
                builder.global(categoryOfCategories),
                pullback(builder, A, K, D, F),
                a,
                b,
                p
            )
        ),
        right: builder.template(
            functorArrowAt(
                builder,
                K,
                builder.global(categoryOfCategories),
                D,
                Fa,
                Fb,
                functorArrowAt(builder, A, K, F, a, b, p)
            )
        ),
        provenance: source(
            'rule @fapp1_fapp0 _ Cat_cat ' +
            '(@Pullback_catd $A $B $E $F) $a $a_prime $p'
        )
    };
};

const pullbackTotalObjectRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const K = builder.capture('K');
    const F = builder.capture('F');
    const D = builder.capture('D');
    const a = builder.capture('a');
    const u = builder.capture('u');
    const reindexed = pullback(builder, A, K, D, F);
    return {
        order: 2,
        id: 'categorical.sigma-pullback-total.object',
        groupId: 'categorical.sigma-pullback-total',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, A, K))
            },
            {
                name: 'D',
                type: builder.template(
                    displayedFamilyType(builder, K)
                )
            },
            {
                name: 'a',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'u',
                type: builder.template(
                    objectType(
                        builder,
                        fibre(builder, A, reindexed, a)
                    )
                )
            }
        ],
        left: builder.pattern(
            functorObjectAt(
                builder,
                sigmaTotal(builder, A, reindexed),
                sigmaTotal(builder, K, D),
                pullbackTotal(builder, A, K, F, D),
                sigmaPair(builder, A, reindexed, a, u)
            )
        ),
        right: builder.template(
            sigmaPair(
                builder,
                K,
                D,
                functorObjectAt(builder, A, K, F, a),
                u
            )
        ),
        provenance: source(
            'rule @fapp0 _ _ ' +
            '(@sigma_pullback_total_func $A $K $F _) ' +
            '(Struct_sigma $a $u)'
        )
    };
};

const pullbackTotalArrowRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const K = builder.capture('K');
    const F = builder.capture('F');
    const D = builder.capture('D');
    const a = builder.capture('a');
    const b = builder.capture('b');
    const u = builder.capture('u');
    const v = builder.capture('v');
    const p = builder.capture('p');
    const alpha = builder.capture('alpha');
    const reindexed = pullback(builder, A, K, D, F);
    const Fa = functorObjectAt(builder, A, K, F, a);
    const Fb = functorObjectAt(builder, A, K, F, b);
    const Fp = functorArrowAt(builder, A, K, F, a, b, p);
    const sourceTransport = functorArrowAt(
        builder,
        A,
        builder.global(categoryOfCategories),
        reindexed,
        a,
        b,
        p
    );
    return {
        order: 3,
        id: 'categorical.sigma-pullback-total.arrow',
        groupId: 'categorical.sigma-pullback-total',
        clauseOrder: 1,
        sourceOwner: functorHomCapped,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, A, K))
            },
            {
                name: 'D',
                type: builder.template(
                    displayedFamilyType(builder, K)
                )
            },
            {
                name: 'a',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'b',
                type: builder.template(objectType(builder, A))
            },
            {
                name: 'u',
                type: builder.template(
                    objectType(
                        builder,
                        fibre(builder, A, reindexed, a)
                    )
                )
            },
            {
                name: 'v',
                type: builder.template(
                    objectType(
                        builder,
                        fibre(builder, A, reindexed, b)
                    )
                )
            },
            {
                name: 'p',
                type: builder.template(homType(builder, A, a, b))
            },
            {
                name: 'alpha',
                type: builder.template(
                    homType(
                        builder,
                        fibre(builder, A, reindexed, b),
                        functorObjectAt(
                            builder,
                            fibre(builder, A, reindexed, a),
                            fibre(builder, A, reindexed, b),
                            sourceTransport,
                            u
                        ),
                        v
                    )
                )
            }
        ],
        left: builder.pattern(
            functorArrowAt(
                builder,
                sigmaTotal(builder, A, reindexed),
                sigmaTotal(builder, K, D),
                pullbackTotal(builder, A, K, F, D),
                sigmaPair(builder, A, reindexed, a, u),
                sigmaPair(builder, A, reindexed, b, v),
                sigmaArrowAt(
                    builder,
                    A,
                    reindexed,
                    a,
                    b,
                    u,
                    v,
                    p,
                    alpha
                )
            )
        ),
        right: builder.template(
            sigmaArrowAt(
                builder,
                K,
                D,
                Fa,
                Fb,
                u,
                v,
                Fp,
                alpha
            )
        ),
        provenance: source(
            'active delta-specialization of: rule @fapp1_fapp0 _ _ ' +
            '(@sigma_pullback_total_func $A $K $F $D) ' +
            '(Struct_sigma $a $u) (Struct_sigma $b $v) ' +
            '(Struct_sigma $p $alpha)'
        )
    };
};

const runtimeRules = Object.freeze([
    pullbackFibreRule(),
    pullbackArrowRule(),
    pullbackTotalObjectRule(),
    pullbackTotalArrowRule()
]);

export const CORE_CATEGORICAL_COMPREHENSION_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        'FIBRED-COMPREHENSION-1A-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'fibred-comprehension-1a-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_COMPREHENSION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        functorClassifier,
        homClassifier,
        categoryOfCategories,
        displayedCategoryCategory,
        functorObject,
        functorHomCapped,
        sigmaCategory,
        dependentPair,
        displayedPullback,
        sigmaArrow,
        sigmaPullbackTotalFunctor
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const CORE_CATEGORICAL_COMPREHENSION_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_COMPREHENSION_RUNTIME_MODULE,
    {
        revision:
            'FIBRED-COMPREHENSION-1A-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_COMPREHENSION_RUNTIME_MODULE.revision,
        entries: runtimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                rule.id ===
                    'categorical.sigma-pullback-total.arrow'
                    ? 'Exact active raw-pair rule at its transparent ' +
                        'canonical sigma_arrow presentation'
                    : 'Exact active v3.2 runtime reduction'
        }))
    }
);

export const CORE_CATEGORICAL_COMPREHENSION_TRANSFER_BOUNDARY =
Object.freeze({
    status: 'root-only-approved-fibred-comprehension-closure',
    existingIntrinsicOwnerCount: 1,
    existingPrerequisiteDeclarationCount: 2,
    newMathematicalOwnerCount: 1,
    declarationNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    runtimeRuleCount: runtimeRules.length,
    prerequisiteRuntimeRuleCount: 2,
    newOwnerRuntimeRuleCount: 2,
    runtimeRuleIds: Object.freeze(runtimeRules.map(rule => rule.id)),
    allEntriesUseGenericTransferEngines: true,
    arrowRulePresentation:
        'active-delta-specialized-canonical-sigma-arrow',
    warningsAreDiagnosticNotSelectionVetoes: true,
    necessityAudit: Object.freeze({
        reusedExistingOwners: Object.freeze([
            'Pullback_catd',
            'Sigma_cat',
            'Struct_sigma',
            'sigma_arrow'
        ]),
        auditedButInsufficientForGeneralBaseChangeTotalization:
            Object.freeze([
                'Sigma_func',
                'sigma_map_func',
                'sigma_intro_transf'
            ])
    }),
    proofRulesInstalled: false,
    doesNotProvide: Object.freeze([
        'generic-total-category-pullback',
        'second-contextual-pair-owner',
        'general-dependent-bracket-abstraction',
        'displayed-fibrewise-product',
        'browser-api',
        'lambdapi-string-parser',
        'bulk-library-transfer'
    ])
});

export interface CoreCategoricalComprehensionCompilation {
    readonly prerequisite:
        CoreCategoricalDependentCompositionCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
    readonly declarationContext: CoreLfMixedDeclarationContext;
}

export function compileCoreCategoricalComprehensionTransfer():
CoreCategoricalComprehensionCompilation {
    validateCoreLfScaleEngineReview();
    const prerequisite =
        compileCoreCategoricalDependentCompositionTransfer();
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_COMPREHENSION_TRANSFER_MODULE,
        CORE_CATEGORICAL_COMPREHENSION_TRANSFER_POLICY,
        CORE_CATEGORICAL_COMPREHENSION_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: prerequisite.composedRuntime
        }
    );
    const initialContext = new CoreLfMixedDeclarationContext(
        prerequisite.declarationContext,
        [initialCompiled]
    );

    /*
     * Preserve the already composed continuation runtime as one immutable
     * earlier-fragment dependency. This lets the generic runtime compiler
     * subject-check the new rules against exactly the prior reviewed prefix.
     */
    const prerequisiteFragment = new CoreLfCompiledRuntimeFragment(
        prerequisite.runtime,
        [],
        prerequisite.composedRuntime
    );
    const runtimeFragment = compileCoreLfRuntimeFragment(
        CORE_CATEGORICAL_COMPREHENSION_RUNTIME_MODULE,
        CORE_CATEGORICAL_COMPREHENSION_RUNTIME_POLICY,
        initialContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: prerequisiteFragment
            }]
        }
    );
    const runtime = runtimeFragment.localProgram;
    const composedRuntime = runtimeFragment.runtime;
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_COMPREHENSION_TRANSFER_MODULE,
        CORE_CATEGORICAL_COMPREHENSION_TRANSFER_POLICY,
        CORE_CATEGORICAL_COMPREHENSION_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: composedRuntime
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        prerequisite.declarationContext,
        [compiled]
    );
    return Object.freeze({
        prerequisite,
        compiled,
        runtimeFragment,
        runtime,
        composedRuntime,
        declarationContext
    });
}

export function coreCategoricalComprehensionCoreName(
    declaration: 'sigma-arrow' | 'sigma-pullback-total-functor'
): string {
    const symbol = declaration === 'sigma-arrow'
        ? sigmaArrow
        : sigmaPullbackTotalFunctor;
    const link =
        CORE_CATEGORICAL_COMPREHENSION_TRANSFER_LINKAGE
            .entries
            .find(candidate =>
                candidate.symbol.moduleId === symbol.moduleId &&
                candidate.symbol.name === symbol.name
            );
    if (link === undefined || link.kind !== 'free-declaration') {
        throw new Error(
            `Categorical comprehension declaration '${declaration}' ` +
            'has no free Core declaration'
        );
    }
    return link.coreName;
}
