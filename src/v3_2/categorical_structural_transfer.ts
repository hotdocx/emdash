/**
 * USABILITY-1C typed transfer of the ordinary categorical structural basis.
 *
 * This is deliberately a declaration-data layer over the generic LF
 * transfer compiler. It does not extend the frozen intrinsic owner catalog
 * and it does not install TypeScript-only computation. Transparent candidate
 * Lambdapi definitions are imported opaquely for this first bracket slice;
 * the exact supporting `Functor` classifier equation and one product-functor
 * normalization are installed through the generic engines because typed
 * pairing requires them. Remaining bodies and rules stay conformance
 * authority.
 */

import {
    CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE,
    compileCoreDirectedContinuationTransferWithRuntime,
    coreDirectedContinuationTransferSymbol
} from './directed_continuation_transfer';
import {
    compileCoreDirectedContinuationRuntimeTransfer
} from './directed_continuation_runtime_transfer';
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
    CoreLfMixedDeclarationContext
} from './lf_transfer_mixed';
import {
    CoreLfCompiledRuntimeProgram,
    CoreLfComposedRuntimeProgram,
    compileCoreLfRuntimeProgram
} from './lf_transfer_runtime';
import {
    binderMode
} from './kernel';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';

const MODULE_ID = 'emdash.emdash3_2';

export const CORE_CATEGORICAL_STRUCTURAL_TRANSFER_REVISION =
    'USABILITY-1C-CATEGORICAL-STRUCTURAL-SIGNATURES-1' as const;

export const CORE_CATEGORICAL_STRUCTURAL_SOURCE_SHA256 =
    'sha256:33e7e78b6516180507f2e99cff465119effbb84f2981d44b609d751963e24f94';

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

export const CORE_CATEGORICAL_STRUCTURAL_SYMBOLS = Object.freeze({
    functorCategory:
        coreLfQualifiedSymbol(MODULE_ID, 'Functor_cat'),
    identityFunctor:
        coreLfQualifiedSymbol(MODULE_ID, 'id_func'),
    functorComposition:
        coreLfQualifiedSymbol(MODULE_ID, 'comp_cat_fapp0'),
    productCategory:
        coreLfQualifiedSymbol(MODULE_ID, 'Product_cat'),
    productPair:
        coreLfQualifiedSymbol(MODULE_ID, 'Product_pair'),
    productLeftProjection:
        coreLfQualifiedSymbol(MODULE_ID, 'Product_projL_func'),
    productRightProjection:
        coreLfQualifiedSymbol(MODULE_ID, 'Product_projR_func'),
    productMap:
        coreLfQualifiedSymbol(MODULE_ID, 'Product_map_func'),
    evaluationFunctor:
        coreLfQualifiedSymbol(MODULE_ID, 'Eval_func'),
    curryPackage:
        coreLfQualifiedSymbol(MODULE_ID, 'curry_func_func'),
    uncurryPackage:
        coreLfQualifiedSymbol(MODULE_ID, 'uncurry_func_func'),
    constantFunctorAbstraction:
        coreLfQualifiedSymbol(MODULE_ID, 'Const_func_func'),
    exchangeFunctorAbstraction:
        coreLfQualifiedSymbol(MODULE_ID, 'sym_func_func'),
    diagonalFunctorAbstraction:
        coreLfQualifiedSymbol(MODULE_ID, 'diag_func_func')
});

const {
    functorCategory,
    identityFunctor,
    functorComposition,
    productCategory,
    productPair,
    productLeftProjection,
    productRightProjection,
    productMap,
    evaluationFunctor,
    curryPackage,
    uncurryPackage,
    constantFunctorAbstraction,
    exchangeFunctorAbstraction,
    diagonalFunctorAbstraction
} = CORE_CATEGORICAL_STRUCTURAL_SYMBOLS;

export type CoreCategoricalStructuralPrerequisiteId =
    | 'identity-functor'
    | 'constant-functor-abstraction'
    | 'exchange-functor-abstraction'
    | 'diagonal-functor-abstraction'
    | 'product-category'
    | 'product-left-projection'
    | 'product-right-projection'
    | 'product-pair'
    | 'product-map'
    | 'evaluation-functor'
    | 'functor-composition'
    | 'curry-package'
    | 'uncurry-package';

export interface CoreCategoricalStructuralTransferPrerequisite {
    readonly id: CoreCategoricalStructuralPrerequisiteId;
    readonly symbol: CoreLfQualifiedSymbol;
    readonly activeAuthority:
        | 'active-primitive'
        | 'checked-transparent-definition';
}

/**
 * The thirteen prerequisites frozen by USABILITY-1A. `Functor_cat` is a
 * separate classifier dependency needed to state their exact signatures.
 */
const structuralPrerequisites:
readonly CoreCategoricalStructuralTransferPrerequisite[] = [
    {
        id: 'identity-functor',
        symbol: identityFunctor,
        activeAuthority: 'checked-transparent-definition'
    },
    {
        id: 'constant-functor-abstraction',
        symbol: constantFunctorAbstraction,
        activeAuthority: 'active-primitive'
    },
    {
        id: 'exchange-functor-abstraction',
        symbol: exchangeFunctorAbstraction,
        activeAuthority: 'active-primitive'
    },
    {
        id: 'diagonal-functor-abstraction',
        symbol: diagonalFunctorAbstraction,
        activeAuthority: 'active-primitive'
    },
    {
        id: 'product-category',
        symbol: productCategory,
        activeAuthority: 'active-primitive'
    },
    {
        id: 'product-left-projection',
        symbol: productLeftProjection,
        activeAuthority: 'active-primitive'
    },
    {
        id: 'product-right-projection',
        symbol: productRightProjection,
        activeAuthority: 'active-primitive'
    },
    {
        id: 'product-pair',
        symbol: productPair,
        activeAuthority: 'checked-transparent-definition'
    },
    {
        id: 'product-map',
        symbol: productMap,
        activeAuthority: 'active-primitive'
    },
    {
        id: 'evaluation-functor',
        symbol: evaluationFunctor,
        activeAuthority: 'active-primitive'
    },
    {
        id: 'functor-composition',
        symbol: functorComposition,
        activeAuthority: 'checked-transparent-definition'
    },
    {
        id: 'curry-package',
        symbol: curryPackage,
        activeAuthority: 'checked-transparent-definition'
    },
    {
        id: 'uncurry-package',
        symbol: uncurryPackage,
        activeAuthority: 'checked-transparent-definition'
    }
];

export const CORE_CATEGORICAL_STRUCTURAL_PREREQUISITES:
readonly CoreCategoricalStructuralTransferPrerequisite[] = Object.freeze(
    structuralPrerequisites.map(entry => Object.freeze(entry))
);

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
    decode(
        builder,
        globalCall(builder, objectClassifier, [{
            plicity: 'explicit',
            value: base
        }])
    );

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

const functorCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorCategory, [
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]);

const productCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, productCategory, [
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
    ]);

const functorCategoryType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        _A => builder.pi(
            'B',
            builder.global(category),
            _B => builder.global(category),
            explicitMode
        ),
        explicitMode
    ));
};

const functorClassifierType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        _A => builder.pi(
            'B',
            builder.global(category),
            _B => builder.global(groupoid),
            explicitMode
        ),
        explicitMode
    ));
};

const functorClassifierBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'A',
        builder.global(category),
        A => builder.lam(
            'B',
            builder.global(category),
            B => globalCall(builder, objectClassifier, [{
                plicity: 'explicit',
                value: functorCategoryAt(builder, A, B)
            }]),
            explicitMode
        ),
        explicitMode
    ));
};

const identityFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => functorType(builder, A, A),
        implicitMode
    ));
};

const functorCompositionType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'C',
                builder.global(category),
                C => builder.pi(
                    'F',
                    functorType(builder, B, C),
                    _F => builder.pi(
                        'G',
                        functorType(builder, A, B),
                        _G => functorType(builder, A, C),
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

const productCategoryType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        _A => builder.pi(
            'B',
            builder.global(category),
            _B => builder.global(category),
            explicitMode
        ),
        explicitMode
    ));
};

const productPairType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'x',
                objectType(builder, A),
                _x => builder.pi(
                    'y',
                    objectType(builder, B),
                    _y => objectType(
                        builder,
                        productCategoryAt(builder, A, B)
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

const productProjectionType = (
    side: 'left' | 'right'
): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => functorType(
                builder,
                productCategoryAt(builder, A, B),
                side === 'left' ? A : B
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const productMapType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'A_prime',
            builder.global(category),
            Aprime => builder.pi(
                'B',
                builder.global(category),
                B => builder.pi(
                    'B_prime',
                    builder.global(category),
                    Bprime => builder.pi(
                        'F',
                        functorType(builder, A, Aprime),
                        _F => builder.pi(
                            'G',
                            functorType(builder, B, Bprime),
                            _G => functorType(
                                builder,
                                productCategoryAt(builder, A, B),
                                productCategoryAt(
                                    builder,
                                    Aprime,
                                    Bprime
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
    ));
};

const evaluationFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => functorType(
                builder,
                productCategoryAt(
                    builder,
                    functorCategoryAt(builder, A, B),
                    A
                ),
                B
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const curryPackageType = (
    direction: 'curry' | 'uncurry'
): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'C',
                builder.global(category),
                C => {
                    const uncurried = functorCategoryAt(
                        builder,
                        productCategoryAt(builder, A, B),
                        C
                    );
                    const curried = functorCategoryAt(
                        builder,
                        A,
                        functorCategoryAt(builder, B, C)
                    );
                    return direction === 'curry'
                        ? functorType(builder, uncurried, curried)
                        : functorType(builder, curried, uncurried);
                },
                implicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const constantFunctorAbstractionType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => functorType(
                builder,
                B,
                functorCategoryAt(builder, A, B)
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const exchangeFunctorAbstractionType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'C',
                builder.global(category),
                C => functorType(
                    builder,
                    functorCategoryAt(
                        builder,
                        A,
                        functorCategoryAt(builder, B, C)
                    ),
                    functorCategoryAt(
                        builder,
                        B,
                        functorCategoryAt(builder, A, C)
                    )
                ),
                implicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const diagonalFunctorAbstractionType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'C',
            builder.global(category),
            C => functorType(
                builder,
                functorCategoryAt(
                    builder,
                    A,
                    functorCategoryAt(builder, A, C)
                ),
                functorCategoryAt(builder, A, C)
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const publicModifiers = (
    rigidity: 'ordinary' | 'injective',
    sourceOpacity: 'transparent' | 'opaque'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity
});

const declarations: readonly CoreLfTransferDeclaration[] = [
    {
        order: 0,
        symbol: functorCategory,
        type: functorCategoryType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Functor_cat : Π (A B : Cat), Cat;'
        )
    },
    {
        order: 1,
        symbol: functorClassifier,
        type: functorClassifierType(),
        body: coreLfTransferExplicitBody(
            functorClassifierBody()
        ),
        modifiers: publicModifiers('injective', 'transparent'),
        provenance: source(
            'injective symbol Functor (A B : Cat) : Grpd'
        )
    },
    {
        order: 2,
        symbol: identityFunctor,
        type: identityFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol id_func [A: Cat] : τ (Functor A A)'
        )
    },
    {
        order: 3,
        symbol: functorComposition,
        type: functorCompositionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol comp_cat_fapp0 [A B : Cat] [C : Cat]'
        )
    },
    {
        order: 4,
        symbol: productCategory,
        type: productCategoryType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Product_cat : Π (A B : Cat), Cat;'
        )
    },
    {
        order: 5,
        symbol: productPair,
        type: productPairType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'transparent'),
        provenance: source(
            'injective symbol Product_pair [A B : Cat]'
        )
    },
    {
        order: 6,
        symbol: productLeftProjection,
        type: productProjectionType('left'),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Product_projL_func [A B : Cat]'
        )
    },
    {
        order: 7,
        symbol: productRightProjection,
        type: productProjectionType('right'),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Product_projR_func [A B : Cat]'
        )
    },
    {
        order: 8,
        symbol: productMap,
        type: productMapType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            "injective symbol Product_map_func [A A' B B' : Cat]"
        )
    },
    {
        order: 9,
        symbol: evaluationFunctor,
        type: evaluationFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol Eval_func [A B : Cat]'
        )
    },
    {
        order: 10,
        symbol: curryPackage,
        type: curryPackageType('curry'),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol curry_func_func [A B C : Cat]'
        )
    },
    {
        order: 11,
        symbol: uncurryPackage,
        type: curryPackageType('uncurry'),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol uncurry_func_func [A B C : Cat]'
        )
    },
    {
        order: 12,
        symbol: constantFunctorAbstraction,
        type: constantFunctorAbstractionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Const_func_func [A B : Cat]'
        )
    },
    {
        order: 13,
        symbol: exchangeFunctorAbstraction,
        type: exchangeFunctorAbstractionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol sym_func_func [A B C : Cat]'
        )
    },
    {
        order: 14,
        symbol: diagonalFunctorAbstraction,
        type: diagonalFunctorAbstractionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol diag_func_func [A C : Cat]'
        )
    }
];

export const CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_CATEGORICAL_STRUCTURAL_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'usability-1c-categorical-structural-signatures',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_STRUCTURAL_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        groupoid,
        decodeOwner,
        objectClassifier
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

const productFunctorNormalizationRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const X = builder.capture('X');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const variables = [X, A, B].map((capture, order) => ({
        name: ['X', 'A', 'B'][order],
        type: builder.template(builder.global(category)),
        capture
    })).map(({ name, type }) => ({ name, type }));
    return {
        order: 0,
        id: 'categorical.product-functor.normalize',
        groupId: 'categorical.product-functor',
        clauseOrder: 0,
        sourceOwner: functorCategory,
        variables,
        left: builder.pattern(globalCall(
            builder,
            functorCategory,
            [
                { plicity: 'explicit', value: X },
                {
                    plicity: 'explicit',
                    value: globalCall(
                        builder,
                        productCategory,
                        [
                            { plicity: 'explicit', value: A },
                            { plicity: 'explicit', value: B }
                        ]
                    )
                }
            ]
        )),
        right: builder.template(globalCall(
            builder,
            productCategory,
            [
                {
                    plicity: 'explicit',
                    value: globalCall(
                        builder,
                        functorCategory,
                        [
                            { plicity: 'explicit', value: X },
                            { plicity: 'explicit', value: A }
                        ]
                    )
                },
                {
                    plicity: 'explicit',
                    value: globalCall(
                        builder,
                        functorCategory,
                        [
                            { plicity: 'explicit', value: X },
                            { plicity: 'explicit', value: B }
                        ]
                    )
                }
            ]
        )),
        provenance: source(
            'rule Functor_cat $X (Product_cat $A $B)'
        )
    };
};

const structuralRuntimeRules = Object.freeze([
    productFunctorNormalizationRule()
]);

export const CORE_CATEGORICAL_STRUCTURAL_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        'USABILITY-1C-CATEGORICAL-STRUCTURAL-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'usability-1c-categorical-structural-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256: CORE_CATEGORICAL_STRUCTURAL_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        functorCategory,
        productCategory
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules: structuralRuntimeRules,
    proofRules: []
});

export const CORE_CATEGORICAL_STRUCTURAL_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_STRUCTURAL_RUNTIME_MODULE,
    {
        revision:
            'USABILITY-1C-CATEGORICAL-STRUCTURAL-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_STRUCTURAL_RUNTIME_MODULE.revision,
        entries: structuralRuntimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact active v3.2 product-valued functor normalization ' +
                'required by typed Product_pair bracket lowering'
        }))
    }
);

export const CORE_CATEGORICAL_STRUCTURAL_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE,
    {
        revision:
            'USABILITY-1C-CATEGORICAL-STRUCTURAL-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE.revision,
        entries: declarations.map((declaration, order) => ({
            order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy:
                declaration.symbol === functorClassifier
                    ? 'checked-transparent-definition' as const
                    : 'opaque-signature' as const,
            evidence:
                'Exact active v3.2 signature imported for ordinary bracket ' +
                'lowering; active bodies and rules remain conformance authority'
        }))
    }
);

const externalLink = (
    symbol: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const link =
        CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries.find(
            candidate =>
                candidate.symbol.moduleId === symbol.moduleId &&
                candidate.symbol.name === symbol.name
        );
    if (link === undefined) {
        throw new Error(
            `Reviewed continuation has no link for ` +
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
    CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE.externalSymbols.map(
        external => external.symbol
    );

export const CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE,
        {
            revision:
                'USABILITY-1C-CATEGORICAL-STRUCTURAL-SIGNATURE-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE.revision,
            entries: [
                ...externalSymbols.map(externalLink),
                ...declarations.map(
                    (
                        declaration,
                        index
                    ): CoreLfTransferDeclarationLink => {
                        if (
                            declaration.symbol === functorClassifier
                        ) {
                            return externalLink(
                                declaration.symbol,
                                externalSymbols.length + index
                            );
                        }
                        return {
                            order: externalSymbols.length + index,
                            symbol: declaration.symbol,
                            kind: 'free-declaration' as const,
                            coreName:
                                `emdash_v3_2_usability_1c_` +
                                declaration.symbol.name,
                            backendName: declaration.symbol.name
                        };
                    }
                )
            ]
        }
    );

export const CORE_CATEGORICAL_STRUCTURAL_TRANSFER_BOUNDARY =
Object.freeze({
    status: 'root-only-signature-transfer',
    prerequisiteCount:
        CORE_CATEGORICAL_STRUCTURAL_PREREQUISITES.length,
    supportDeclarationCount: 2,
    supportDeclarations: Object.freeze([
        functorCategory,
        functorClassifier
    ]),
    allCandidateDeclarationsUseGenericCompiler: true,
    supportTransparentBodiesInstalled: true,
    candidateTransparentBodiesInstalled: false,
    runtimeRulesInstalled: true,
    runtimeRuleIds: Object.freeze(
        structuralRuntimeRules.map(rule => rule.id)
    ),
    proofRulesInstalled: false,
    doesNotProvide: Object.freeze([
        'new-intrinsic-core-owner',
        'owner-specific-checker-case',
        'owner-specific-evaluator-case',
        'typescript-only-categorical-computation',
        'lambdapi-string-parser',
        'displayed-structural-owner',
        'browser-api',
        'semantic-profile-expansion',
        'frontend-graduation',
        'bulk-library-transfer-qualification'
    ])
});

export interface CoreCategoricalStructuralCompilation {
    readonly initialDeclarations:
        ReturnType<
            typeof compileCoreDirectedContinuationTransferWithRuntime
        >;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
    readonly declarationContext: CoreLfMixedDeclarationContext;
}

export function compileCoreCategoricalStructuralTransfer():
CoreCategoricalStructuralCompilation {
    validateCoreLfScaleEngineReview();
    const directed =
        compileCoreDirectedContinuationRuntimeTransfer();
    const initialDeclarations = directed.declarations;
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE,
        CORE_CATEGORICAL_STRUCTURAL_TRANSFER_POLICY,
        CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE,
        {
            initialEnvironment: initialDeclarations.environment,
            runtimeProgram: directed.runtime
        }
    );
    const initialContext = new CoreLfMixedDeclarationContext(
        initialDeclarations,
        [initialCompiled]
    );
    const runtime = compileCoreLfRuntimeProgram(
        CORE_CATEGORICAL_STRUCTURAL_RUNTIME_MODULE,
        CORE_CATEGORICAL_STRUCTURAL_RUNTIME_POLICY,
        initialContext
    );
    const composedRuntime = new CoreLfComposedRuntimeProgram([
        directed.runtime,
        runtime
    ]);
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_STRUCTURAL_TRANSFER_MODULE,
        CORE_CATEGORICAL_STRUCTURAL_TRANSFER_POLICY,
        CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE,
        {
            initialEnvironment: initialDeclarations.environment,
            runtimeProgram: composedRuntime
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        initialDeclarations,
        [compiled]
    );
    return Object.freeze({
        initialDeclarations,
        compiled,
        runtime,
        composedRuntime,
        declarationContext
    });
}

export function coreCategoricalStructuralCoreName(
    prerequisite: CoreCategoricalStructuralPrerequisiteId
): string {
    const entry = CORE_CATEGORICAL_STRUCTURAL_PREREQUISITES.find(
        candidate => candidate.id === prerequisite
    );
    if (entry === undefined) {
        throw new Error(
            `Unknown categorical structural prerequisite '${prerequisite}'`
        );
    }
    return coreCategoricalStructuralSymbolCoreName(entry.symbol);
}

export function coreCategoricalStructuralSymbolCoreName(
    symbol: CoreLfQualifiedSymbol
): string {
    const link = CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries.find(
        candidate =>
            candidate.symbol.moduleId === symbol.moduleId &&
            candidate.symbol.name === symbol.name
    );
    if (link === undefined || link.kind !== 'free-declaration') {
        throw new Error(
            `Categorical structural symbol ` +
                `'${symbol.moduleId}.${symbol.name}' ` +
                'has no free Core declaration'
        );
    }
    return link.coreName;
}
