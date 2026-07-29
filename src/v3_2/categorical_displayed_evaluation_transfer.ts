/**
 * DISPLAYED-EVAL-1A transfer closure.
 *
 * The semantic delta is exactly the two D-DTTLF-USABILITY-011 owners and
 * their two point-component rules. The prerequisite fragment makes four
 * already-active authority items explicit because they were not present in
 * the previous TypeScript declaration environment: `Functor_catd`,
 * `Terminal_func`, `const_section_func`, and the `Functor_catd` fibre
 * projection. None is a new mathematical owner or TypeScript intrinsic.
 */

import {
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS,
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE
} from './categorical_dependent_composition_transfer';
import {
    validateCoreCategoricalDisplayedEvaluationOwnerReview
} from './categorical_displayed_evaluation_owner_review';
import {
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_LINKAGE,
    CoreCategoricalFibredDependentTargetCompilation,
    compileCoreCategoricalFibredDependentTargetTransfer
} from './categorical_fibred_dependent_target_transfer';
import {
    CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS,
    CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE
} from './categorical_fibred_product_transfer';
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

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_REVISION =
    'DISPLAYED-EVAL-1A-GENERIC-TRANSFER-1' as const;

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_SOURCE_SHA256 =
    'sha256:16b5b1adc5ec462012e03555cfe65db91679983ef370e01adb9948a0bacc61cb';

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
const transforComponentCapped =
    coreDirectedContinuationTransferSymbol(
        'transfor-component-capped'
    );

const {
    oppositeCategory,
    displayedFunctorClassifier
} = CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_SYMBOLS;

const {
    functorCategory,
    functorComposition,
    productCategory,
    productPair,
    evaluationFunctor,
    uncurryPackage
} = CORE_CATEGORICAL_STRUCTURAL_SYMBOLS;

const {
    internalProductFunctor
} = CORE_CATEGORICAL_FIBRED_PRODUCT_SYMBOLS;

const {
    terminalCategory
} = CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS;

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_SYMBOLS =
Object.freeze({
    stableFunctorFamily:
        coreLfQualifiedSymbol(MODULE_ID, 'Functor_catd'),
    terminalFunctor:
        coreLfQualifiedSymbol(MODULE_ID, 'Terminal_func'),
    constantSectionFunctor:
        coreLfQualifiedSymbol(MODULE_ID, 'const_section_func')
});

export const CORE_CATEGORICAL_DISPLAYED_EVALUATION_SYMBOLS =
Object.freeze({
    displayedEvaluation:
        coreLfQualifiedSymbol(MODULE_ID, 'Eval_funcd'),
    displayedTerminal:
        coreLfQualifiedSymbol(MODULE_ID, 'Terminal_funcd')
});

const {
    stableFunctorFamily,
    terminalFunctor,
    constantSectionFunctor
} = CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_SYMBOLS;

const {
    displayedEvaluation,
    displayedTerminal
} = CORE_CATEGORICAL_DISPLAYED_EVALUATION_SYMBOLS;

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

const opposite = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, oppositeCategory, [{
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

const functorCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorCategory, [
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

const productCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, productCategory, [
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
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

const pairAt = (
    builder: CoreLfTransferScopedBuilder,
    leftCategory: CoreLfTransferBuilderExpression,
    rightCategory: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, productPair, [
        { plicity: 'implicit', value: leftCategory },
        { plicity: 'implicit', value: rightCategory },
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
    ]);

const composeFunctors = (
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

const uncurryPackageAt = (
    builder: CoreLfTransferScopedBuilder,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, uncurryPackage, [
        { plicity: 'implicit', value: left },
        { plicity: 'implicit', value: right },
        { plicity: 'implicit', value: target }
    ]);

const stableFunctorFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    domain: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, stableFunctorFamily, [
        { plicity: 'implicit', value: base },
        {
            plicity: 'explicit',
            value: constantFamily(
                builder,
                opposite(builder, base),
                domain
            )
        },
        { plicity: 'explicit', value: target }
    ]);

const transparentDisplayedProduct = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression => {
    const cat = builder.global(categoryOfCategories);
    const catProduct = productCategoryAt(builder, cat, cat);
    const catEndofunctors = functorCategoryAt(builder, cat, cat);
    const uncurriedProduct = fapp0(
        builder,
        functorCategoryAt(builder, cat, catEndofunctors),
        functorCategoryAt(builder, catProduct, cat),
        uncurryPackageAt(builder, cat, cat, cat),
        builder.global(internalProductFunctor)
    );
    const familyCategory = functorCategoryAt(builder, base, cat);
    return composeFunctors(
        builder,
        base,
        catProduct,
        cat,
        uncurriedProduct,
        pairAt(builder, familyCategory, familyCategory, left, right)
    );
};

const evaluationSource = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    domain: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    transparentDisplayedProduct(
        builder,
        base,
        stableFunctorFamilyAt(builder, base, domain, target),
        constantFamily(builder, base, domain)
    );

const evaluationAt = (
    builder: CoreLfTransferScopedBuilder,
    domain: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, evaluationFunctor, [
        { plicity: 'implicit', value: domain },
        { plicity: 'implicit', value: target }
    ]);

const displayedEvaluationAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    domain: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedEvaluation, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: domain },
        { plicity: 'explicit', value: target }
    ]);

const displayedTerminalAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedTerminal, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]);

const tapp0At = (
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

const source = (sourceFragment: string) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment
});

const modifiers = (
    rigidity: 'ordinary' | 'injective',
    sourceOpacity: 'opaque' | 'transparent'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity
});

const stableFunctorFamilyType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'A',
            displayedFamilyType(builder, opposite(builder, K)),
            _A => builder.pi(
                'B',
                displayedFamilyType(builder, K),
                _B => displayedFamilyType(builder, K),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const terminalFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => functorType(
            builder,
            A,
            builder.global(terminalCategory)
        ),
        explicitMode
    ));
};

const constantSectionFunctorType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'A',
            builder.global(category),
            A => functorType(
                builder,
                A,
                sectionCategoryAt(
                    builder,
                    K,
                    constantFamily(builder, K, A)
                )
            ),
            explicitMode
        ),
        explicitMode
    ));
};

const displayedEvaluationType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'A',
            builder.global(category),
            A => builder.pi(
                'B',
                displayedFamilyType(builder, K),
                B => displayedFunctorType(
                    builder,
                    K,
                    evaluationSource(builder, K, A, B),
                    B
                ),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const displayedTerminalType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            E => displayedFunctorType(
                builder,
                K,
                E,
                constantFamily(
                    builder,
                    K,
                    builder.global(terminalCategory)
                )
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const prerequisiteDeclarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: stableFunctorFamily,
        type: stableFunctorFamilyType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Functor_catd [K : Cat] ' +
                '(A : τ (Catd (Op_cat K))) (B : τ (Catd K))'
        )
    }),
    Object.freeze({
        order: 1,
        symbol: terminalFunctor,
        type: terminalFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Terminal_func : Π (A : Cat), ' +
                'τ (Functor A Terminal_cat)'
        )
    }),
    Object.freeze({
        order: 2,
        symbol: constantSectionFunctor,
        type: constantSectionFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol const_section_func (K : Cat) (A : Cat) ' +
                ': τ (Functor A (@Pi_cat K (@Const_catd K A)))'
        )
    })
]);

const evaluationDeclarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        order: 0,
        symbol: displayedEvaluation,
        type: displayedEvaluationType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Eval_funcd [K A : Cat] ' +
                '(B : τ (Catd K))'
        )
    }),
    Object.freeze({
        order: 1,
        symbol: displayedTerminal,
        type: displayedTerminalType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Terminal_funcd [K : Cat] ' +
                '(E : τ (Catd K))'
        )
    })
]);

const prerequisiteExternalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    functorClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    constantDisplayedFamily,
    sectionCategory,
    oppositeCategory,
    terminalCategory
]);

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'DISPLAYED-EVAL-1A-EXISTING-PREREQUISITES-1',
    moduleId: MODULE_ID,
    fragmentId: 'displayed-eval-1a-existing-prerequisites',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: prerequisiteExternalSymbols.map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: prerequisiteDeclarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_MODULE,
    {
        revision:
            'DISPLAYED-EVAL-1A-EXISTING-PREREQUISITES-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_MODULE
                .revision,
        entries: prerequisiteDeclarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact pre-existing active v3.2 signature required to ' +
                'state or check the approved displayed-evaluation closure'
        }))
    }
);

const earlierLinks = [
    ...CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_FIBRED_PRODUCT_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_LINKAGE.entries,
    ...CORE_CATEGORICAL_STRUCTURAL_TRANSFER_LINKAGE.entries,
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries
];

const symbolEquals = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId &&
    left.name === right.name;

const dependencyLink = (
    links: readonly CoreLfTransferDeclarationLink[],
    symbol: CoreLfQualifiedSymbol,
    order: number,
    detail: string
): CoreLfTransferDeclarationLink => {
    const link = links.find(candidate =>
        symbolEquals(candidate.symbol, symbol)
    );
    if (link === undefined) {
        throw new Error(
            `${detail} has no dependency link for ` +
                `${symbol.moduleId}.${symbol.name}`
        );
    }
    return Object.freeze({
        ...link,
        order,
        symbol: Object.freeze({ ...link.symbol })
    });
};

const prerequisiteCoreName = (
    symbol: CoreLfQualifiedSymbol
): string =>
    `emdash_v3_2_displayed_eval_1a_prerequisite_${symbol.name}`;

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_MODULE,
        {
            revision:
                'DISPLAYED-EVAL-1A-EXISTING-PREREQUISITES-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_MODULE
                    .revision,
            entries: [
                ...prerequisiteExternalSymbols.map((symbol, order) =>
                    dependencyLink(
                        earlierLinks,
                        symbol,
                        order,
                        'DISPLAYED-EVAL-1A prerequisite'
                    )
                ),
                ...prerequisiteDeclarations.map(
                    (declaration, index) => ({
                        order:
                            prerequisiteExternalSymbols.length + index,
                        symbol: declaration.symbol,
                        kind: 'free-declaration' as const,
                        coreName:
                            prerequisiteCoreName(declaration.symbol),
                        backendName: declaration.symbol.name
                    })
                )
            ]
        }
    );

const stableFunctorFamilyFibreRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const k = builder.capture('k');
    const cat = builder.global(categoryOfCategories);
    return {
        order: 0,
        id:
            'categorical.displayed-evaluation.' +
            'stable-functor-family-fibre',
        groupId:
            'categorical.displayed-evaluation.existing-prerequisite',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'A',
                type: builder.template(
                    displayedFamilyType(builder, opposite(builder, K))
                )
            },
            {
                name: 'B',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'k',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            K,
            cat,
            globalCall(builder, stableFunctorFamily, [
                { plicity: 'implicit', value: K },
                { plicity: 'explicit', value: A },
                { plicity: 'explicit', value: B }
            ]),
            k
        )),
        right: builder.template(functorCategoryAt(
            builder,
            fapp0(builder, opposite(builder, K), cat, A, k),
            fapp0(builder, K, cat, B, k)
        )),
        provenance: source(
            'rule @fapp0 $K Cat_cat (@Functor_catd $K $A $B) $k'
        )
    };
};

const prerequisiteRuntimeRules = Object.freeze([
    stableFunctorFamilyFibreRule()
]);

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        'DISPLAYED-EVAL-1A-EXISTING-PREREQUISITE-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'displayed-eval-1a-existing-prerequisite-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        ...prerequisiteExternalSymbols,
        functorCategory,
        functorObject,
        stableFunctorFamily
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules: prerequisiteRuntimeRules,
    proofRules: []
});

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_RUNTIME_MODULE,
    {
        revision:
            'DISPLAYED-EVAL-1A-EXISTING-PREREQUISITE-' +
            'RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_RUNTIME_MODULE
                .revision,
        entries: [{
            order: 0,
            target: {
                kind: 'runtime-rule' as const,
                id: prerequisiteRuntimeRules[0].id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact active Functor_catd fibre projection required for ' +
                'generic subject reduction of Eval_funcd'
        }]
    }
);

const evaluationExternalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    functorClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    constantDisplayedFamily,
    functorObject,
    transforComponentCapped,
    oppositeCategory,
    displayedFunctorClassifier,
    functorCategory,
    functorComposition,
    productCategory,
    productPair,
    evaluationFunctor,
    uncurryPackage,
    internalProductFunctor,
    terminalCategory,
    stableFunctorFamily,
    terminalFunctor
]);

export const CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'displayed-eval-1a-signatures',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: evaluationExternalSymbols.map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: evaluationDeclarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_MODULE,
    {
        revision: 'DISPLAYED-EVAL-1A-SIGNATURE-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_MODULE
                .revision,
        entries: evaluationDeclarations.map(declaration => ({
            order: declaration.order,
            target: {
                kind: 'declaration' as const,
                symbol: declaration.symbol
            },
            policy: 'opaque-signature' as const,
            evidence:
                'Exact injective mathematical owner approved by ' +
                'D-DTTLF-USABILITY-011'
        }))
    }
);

const prerequisiteLinks = [
    ...CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_LINKAGE
        .entries,
    ...earlierLinks
];

const evaluationCoreName = (
    symbol: CoreLfQualifiedSymbol
): string =>
    `emdash_v3_2_displayed_eval_1a_${symbol.name}`;

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_MODULE,
        {
            revision: 'DISPLAYED-EVAL-1A-SIGNATURE-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_MODULE
                    .revision,
            entries: [
                ...evaluationExternalSymbols.map((symbol, order) =>
                    dependencyLink(
                        prerequisiteLinks,
                        symbol,
                        order,
                        'DISPLAYED-EVAL-1A'
                    )
                ),
                ...evaluationDeclarations.map(
                    (declaration, index) => ({
                        order: evaluationExternalSymbols.length + index,
                        symbol: declaration.symbol,
                        kind: 'free-declaration' as const,
                        coreName: evaluationCoreName(declaration.symbol),
                        backendName: declaration.symbol.name
                    })
                )
            ]
        }
    );

const evaluationComponentRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const A = builder.capture('A');
    const B = builder.capture('B');
    const k = builder.capture('k');
    return {
        order: 0,
        id: 'categorical.displayed-evaluation.component',
        groupId: 'categorical.displayed-evaluation',
        clauseOrder: 0,
        sourceOwner: transforComponentCapped,
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
                name: 'B',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'k',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(tapp0At(
            builder,
            K,
            builder.global(categoryOfCategories),
            evaluationSource(builder, K, A, B),
            B,
            k,
            displayedEvaluationAt(builder, K, A, B)
        )),
        right: builder.template(evaluationAt(
            builder,
            A,
            fapp0(
                builder,
                K,
                builder.global(categoryOfCategories),
                B,
                k
            )
        )),
        provenance: source(
            'rule @tapp0_fapp0 _ Cat_cat _ _ $k ' +
                '(@Eval_funcd _ $A $B)'
        )
    };
};

const terminalComponentRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const k = builder.capture('k');
    const fibre = fapp0(
        builder,
        K,
        builder.global(categoryOfCategories),
        E,
        k
    );
    return {
        order: 1,
        id: 'categorical.displayed-terminal.component',
        groupId: 'categorical.displayed-terminal',
        clauseOrder: 0,
        sourceOwner: transforComponentCapped,
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
                name: 'k',
                type: builder.template(objectType(builder, K))
            }
        ],
        left: builder.pattern(tapp0At(
            builder,
            K,
            builder.global(categoryOfCategories),
            E,
            constantFamily(
                builder,
                K,
                builder.global(terminalCategory)
            ),
            k,
            displayedTerminalAt(builder, K, E)
        )),
        right: builder.template(globalCall(
            builder,
            terminalFunctor,
            [{ plicity: 'explicit', value: fibre }]
        )),
        provenance: source(
            'rule @tapp0_fapp0 _ Cat_cat _ _ $k ' +
                '(@Terminal_funcd _ $E)'
        )
    };
};

const evaluationRuntimeRules = Object.freeze([
    evaluationComponentRule(),
    terminalComponentRule()
]);

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'DISPLAYED-EVAL-1A-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'displayed-eval-1a-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        ...evaluationExternalSymbols,
        ...evaluationDeclarations.map(declaration =>
            declaration.symbol
        )
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules: evaluationRuntimeRules,
    proofRules: []
});

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_MODULE,
    {
        revision: 'DISPLAYED-EVAL-1A-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_MODULE
                .revision,
        entries: evaluationRuntimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact point-component runtime rule approved by ' +
                'D-DTTLF-USABILITY-011'
        }))
    }
);

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_CORE_NAMES =
Object.freeze({
    stableFunctorFamily:
        prerequisiteCoreName(stableFunctorFamily),
    terminalFunctor:
        prerequisiteCoreName(terminalFunctor),
    constantSectionFunctor:
        prerequisiteCoreName(constantSectionFunctor),
    displayedEvaluation:
        evaluationCoreName(displayedEvaluation),
    displayedTerminal:
        evaluationCoreName(displayedTerminal)
});

export type CoreCategoricalDisplayedEvaluationCoreId =
    keyof typeof CORE_CATEGORICAL_DISPLAYED_EVALUATION_CORE_NAMES;

export function coreCategoricalDisplayedEvaluationCoreName(
    id: CoreCategoricalDisplayedEvaluationCoreId
): string {
    return CORE_CATEGORICAL_DISPLAYED_EVALUATION_CORE_NAMES[id];
}

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_BOUNDARY =
Object.freeze({
    status: 'displayed-eval-1a-generic-transfer',
    reviewRevision: 'DISPLAYED-EVAL-OWNER-0C-REVIEWED-1',
    existingPrerequisiteDeclarationNames: Object.freeze(
        prerequisiteDeclarations.map(declaration =>
            declaration.symbol.name
        )
    ),
    existingPrerequisiteRuntimeRuleIds: Object.freeze(
        prerequisiteRuntimeRules.map(rule => rule.id)
    ),
    newOwnerNames: Object.freeze(
        evaluationDeclarations.map(declaration =>
            declaration.symbol.name
        )
    ),
    newRuntimeRuleIds: Object.freeze(
        evaluationRuntimeRules.map(rule => rule.id)
    ),
    existingPrerequisiteDeclarationCount:
        prerequisiteDeclarations.length,
    existingPrerequisiteRuntimeRuleCount:
        prerequisiteRuntimeRules.length,
    newMathematicalOwnerCount: evaluationDeclarations.length,
    newMathematicalRuntimeRuleCount: evaluationRuntimeRules.length,
    newMathematicalProofRuleCount: 0,
    newIntrinsicCoreOwnerCount: 0,
    genericFappTappCoherenceRuleCount: 0,
    allEntriesUseGenericTransferEngines: true
});

export interface CoreCategoricalDisplayedEvaluationCompilation {
    readonly prerequisite:
        CoreCategoricalFibredDependentTargetCompilation;
    readonly prerequisiteCompiled:
        CoreLfCompiledDeclarationModule;
    readonly prerequisiteDeclarationContext:
        CoreLfMixedDeclarationContext;
    readonly prerequisiteRuntimeFragment:
        CoreLfCompiledRuntimeFragment;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation:
    CoreCategoricalDisplayedEvaluationCompilation | undefined;

export function compileCoreCategoricalDisplayedEvaluationTransfer():
CoreCategoricalDisplayedEvaluationCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    validateCoreLfScaleEngineReview();
    validateCoreCategoricalDisplayedEvaluationOwnerReview();
    const prerequisite =
        compileCoreCategoricalFibredDependentTargetTransfer();
    const initialPrerequisiteCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_MODULE,
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_POLICY,
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: prerequisite.composedRuntime
        }
    );
    const initialPrerequisiteContext =
        new CoreLfMixedDeclarationContext(
            prerequisite.declarationContext,
            [initialPrerequisiteCompiled]
        );
    const inheritedRuntimeFragment =
        new CoreLfCompiledRuntimeFragment(
            prerequisite.consumerRuntimeFragment.localProgram,
            [],
            prerequisite.composedRuntime
        );
    const prerequisiteRuntimeFragment =
        compileCoreLfRuntimeFragment(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_RUNTIME_MODULE,
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_RUNTIME_POLICY,
            initialPrerequisiteContext,
            {
                dependencies: [{
                    relation: 'earlier-fragment',
                    fragment: inheritedRuntimeFragment
                }]
            }
        );
    const prerequisiteCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_MODULE,
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_POLICY,
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_PREREQUISITE_LINKAGE,
        {
            initialEnvironment: prerequisite.compiled.environment,
            runtimeProgram: prerequisiteRuntimeFragment.runtime
        }
    );
    const prerequisiteDeclarationContext =
        new CoreLfMixedDeclarationContext(
            prerequisite.declarationContext,
            [prerequisiteCompiled]
        );
    const initialCompiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_MODULE,
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_POLICY,
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisiteCompiled.environment,
            runtimeProgram: prerequisiteRuntimeFragment.runtime
        }
    );
    const initialContext = new CoreLfMixedDeclarationContext(
        prerequisiteDeclarationContext,
        [initialCompiled]
    );
    const runtimeFragment = compileCoreLfRuntimeFragment(
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_MODULE,
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_RUNTIME_POLICY,
        initialContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: prerequisiteRuntimeFragment
            }]
        }
    );
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_MODULE,
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_POLICY,
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_TRANSFER_LINKAGE,
        {
            initialEnvironment: prerequisiteCompiled.environment,
            runtimeProgram: runtimeFragment.runtime
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        prerequisiteDeclarationContext,
        [compiled]
    );
    cachedCompilation = Object.freeze({
        prerequisite,
        prerequisiteCompiled,
        prerequisiteDeclarationContext,
        prerequisiteRuntimeFragment,
        compiled,
        declarationContext,
        runtimeFragment,
        runtime: runtimeFragment.localProgram,
        composedRuntime: runtimeFragment.runtime
    });
    return cachedCompilation;
}
