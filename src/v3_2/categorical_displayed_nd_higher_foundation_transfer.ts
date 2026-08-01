/**
 * DISPLAYED-ND-HIGHER-FOUNDATION-1A generic declaration transfer.
 *
 * This fragment installs exactly the D-019-reviewed thirteen-declaration
 * dependency foundation over the completed displayed-chain-2A environment.
 * D-020 additionally transfers the one existing opposite-involution rule
 * required by those transparent bodies. It contributes no new Lambdapi
 * rule, proof rule, Core owner, checker case, or surface method. Five active
 * transparent bodies are checked by the generic LF compiler and eight active
 * interfaces remain opaque.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_2A_CLOSURE_TRANSFER_LINKAGE,
    CoreCategoricalDisplayedChain2aClosureCompilation,
    compileCoreCategoricalDisplayedChain2aClosureTransfer
} from './categorical_displayed_chain_2a_closure_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
} from './categorical_displayed_nd_higher_audit';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_CORE_NAMES,
    CoreCategoricalDisplayedNdHigherFoundationSymbolId,
    coreCategoricalDisplayedNdHigherFoundationCoreName
} from './categorical_displayed_nd_higher_foundation_contract';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_REVIEW,
    validateCoreCategoricalDisplayedNdHigherReview
} from './categorical_displayed_nd_higher_review';
import {
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
    CoreLfCompiledRuntimeFragment,
    CoreLfCompiledRuntimeProgram,
    CoreLfComposedRuntimeProgram,
    compileCoreLfRuntimeFragment
} from './lf_transfer_runtime';
import {
    binderMode
} from './kernel';
import {
    CoreOwnerId
} from './schema';
import {
    CORE_LF_SCALE_STRESS_3A2A_MODULE
} from './scale_stress_3a2a_representation';

export {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_CORE_NAMES,
    coreCategoricalDisplayedNdHigherFoundationCoreName
};
export type {
    CoreCategoricalDisplayedNdHigherFoundationSymbolId
};

const MODULE_ID = 'emdash.emdash3_2';

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_REVISION =
    'DISPLAYED-ND-HIGHER-FOUNDATION-1A-GENERIC-TRANSFER-1' as const;

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner =
    coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const homClassifier =
    coreDirectedContinuationTransferSymbol('hom-classifier');
const functorClassifier =
    coreDirectedContinuationTransferSymbol('functor-classifier');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-category-category'
    );
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const constantDisplayedFamily =
    coreDirectedContinuationTransferSymbol(
        'constant-displayed-family'
    );

const symbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(MODULE_ID, name);

const displayedFamilyClassifier = symbol('Catd');
const displayedFunctorClassifier = symbol('Functord');
const ordinaryComposition = symbol('comp_fapp0');
const oppositeCategory = symbol('Op_cat');
const functorCategory = symbol('Functor_cat');
const functorEvaluation = symbol('fapp0_func');
const functorComposition = symbol('comp_cat_fapp0');
const sectionCategoryFunctor = symbol('Pi_func');

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS =
Object.freeze({
    identityArrow: symbol('id'),
    displayedComposition: symbol('comp_catd_fapp0'),
    oppositeFunctor: symbol('Op_func'),
    displayedOppositeFunctor: symbol('Op_catd_func'),
    internalHom: symbol('hom_int'),
    displayedOpposite: symbol('Op_catd'),
    displayedOppositeAction: symbol('Op_funcd'),
    mixedFunctorFamily: symbol('Functor_catd_func'),
    edgeFamily: symbol('Edge_catd_func'),
    presheafFamily: symbol('Presheaf_catd_func'),
    homPresheafFamily: symbol('HomPresheaf_catd_func'),
    displayedHomTarget: symbol('Homd_target_catd'),
    displayedInternalHom: symbol('homd_int')
});

const {
    identityArrow,
    displayedComposition,
    oppositeFunctor,
    displayedOppositeFunctor,
    internalHom,
    displayedOpposite,
    displayedOppositeAction,
    mixedFunctorFamily,
    edgeFamily,
    presheafFamily,
    homPresheafFamily,
    displayedHomTarget,
    displayedInternalHom
} = CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS;

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

const functorType = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, functorClassifier, [
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]));

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

const opposite = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, oppositeCategory, [{
        plicity: 'explicit',
        value: base
    }]);

const displayedCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedCategoryCategory, [{
        plicity: 'explicit',
        value: base
    }]);

const functorCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorCategory, [
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]);

const constantFamily = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    fibre: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, constantDisplayedFamily, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: fibre }
    ]);

const identityAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, identityArrow, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: object }
    ]);

const ordinaryComposeAt = (
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

const functorComposeAt = (
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

const displayedComposeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    middle: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    outer: CoreLfTransferBuilderExpression,
    inner: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedComposition, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: middle },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: outer },
        { plicity: 'explicit', value: inner }
    ]);

const oppositeFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, oppositeFunctor, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: functor }
    ]);

const displayedOppositeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedOpposite, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const internalHomAt = (
    builder: CoreLfTransferScopedBuilder,
    target: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, internalHom, [
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: source },
        { plicity: 'explicit', value: functor }
    ]);

const displayedOppositeFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedOppositeFunctor, [{
        plicity: 'explicit',
        value: base
    }]);

const mixedFunctorFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, mixedFunctorFamily, [{
        plicity: 'explicit',
        value: base
    }]);

const edgeFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, edgeFamily, [{
        plicity: 'implicit',
        value: base
    }]);

const presheafFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, presheafFamily, [{
        plicity: 'explicit',
        value: base
    }]);

const homPresheafFamilyAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, homPresheafFamily, [{
        plicity: 'implicit',
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

const functorEvaluationAt = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorEvaluation, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: object }
    ]);

const sectionCategoryFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sectionCategoryFunctor, [{
        plicity: 'explicit',
        value: base
    }]);

const source = (
    sourceFragment: string,
    canonicalCommandOrdinal: number
) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment,
    canonicalCommandOrdinal
});

const modifiers = (
    rigidity: 'ordinary' | 'injective',
    sourceOpacity: 'transparent' | 'opaque'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity
});

const priorIdentityDeclaration =
    CORE_LF_SCALE_STRESS_3A2A_MODULE.declarations.find(declaration =>
        declaration.symbol.moduleId === identityArrow.moduleId &&
        declaration.symbol.name === identityArrow.name
    );

if (priorIdentityDeclaration === undefined) {
    throw new Error(
        'SCALE-STRESS-3A2A no longer exposes the exact id declaration'
    );
}

const displayedCompositionType = (): CoreLfTransferExpression => {
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
                    'C',
                    displayedFamilyType(builder, K),
                    C => builder.pi(
                        'FF',
                        displayedFunctorType(builder, K, D, C),
                        FF => builder.pi(
                            'GG',
                            displayedFunctorType(builder, K, E, D),
                            _GG => displayedFunctorType(
                                builder,
                                K,
                                E,
                                C
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

const displayedCompositionBody = (): CoreLfTransferExpression => {
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
                    'C',
                    displayedFamilyType(builder, K),
                    C => builder.lam(
                        'FF',
                        displayedFunctorType(builder, K, D, C),
                        FF => builder.lam(
                            'GG',
                            displayedFunctorType(builder, K, E, D),
                            GG => ordinaryComposeAt(
                                builder,
                                displayedCategoryAt(builder, K),
                                E,
                                D,
                                C,
                                FF,
                                GG
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

const oppositeFunctorType = (): CoreLfTransferExpression => {
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
                    opposite(builder, A),
                    opposite(builder, B)
                ),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const displayedOppositeFunctorType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => functorType(
            builder,
            displayedCategoryAt(builder, Z),
            displayedCategoryAt(builder, Z)
        ),
        explicitMode
    ));
};

const internalHomType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'F',
                functorType(builder, B, A),
                _F => functorType(
                    builder,
                    opposite(builder, A),
                    displayedCategoryAt(builder, B)
                ),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const displayedOppositeType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'E',
            displayedFamilyType(builder, K),
            _E => displayedFamilyType(builder, K),
            explicitMode
        ),
        implicitMode
    ));
};

const displayedOppositeActionType =
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
                    _FF => displayedFunctorType(
                        builder,
                        K,
                        displayedOppositeAt(builder, K, E),
                        displayedOppositeAt(builder, K, D)
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

const mixedFunctorFamilyType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => functorType(
            builder,
            opposite(
                builder,
                displayedCategoryAt(builder, opposite(builder, K))
            ),
            functorCategoryAt(
                builder,
                displayedCategoryAt(builder, K),
                displayedCategoryAt(builder, K)
            )
        ),
        explicitMode
    ));
};

const edgeFamilyType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => functorType(
            builder,
            opposite(builder, Z),
            displayedCategoryAt(builder, Z)
        ),
        implicitMode
    ));
};

const edgeFamilyBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => functorComposeAt(
            builder,
            opposite(builder, Z),
            displayedCategoryAt(builder, Z),
            displayedCategoryAt(builder, Z),
            displayedOppositeFunctorAt(builder, Z),
            internalHomAt(
                builder,
                Z,
                Z,
                identityAt(
                    builder,
                    builder.global(categoryOfCategories),
                    Z
                )
            )
        ),
        implicitMode
    ));
};

const presheafFamilyType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => functorType(
            builder,
            opposite(
                builder,
                displayedCategoryAt(builder, opposite(builder, K))
            ),
            displayedCategoryAt(builder, K)
        ),
        explicitMode
    ));
};

const presheafFamilyBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'K',
        builder.global(category),
        K => {
            const source = opposite(
                builder,
                displayedCategoryAt(builder, opposite(builder, K))
            );
            const middle = functorCategoryAt(
                builder,
                displayedCategoryAt(builder, K),
                displayedCategoryAt(builder, K)
            );
            const target = displayedCategoryAt(builder, K);
            return functorComposeAt(
                builder,
                source,
                middle,
                target,
                functorEvaluationAt(
                    builder,
                    displayedCategoryAt(builder, K),
                    displayedCategoryAt(builder, K),
                    constantFamily(
                        builder,
                        K,
                        builder.global(categoryOfCategories)
                    )
                ),
                mixedFunctorFamilyAt(builder, K)
            );
        },
        explicitMode
    ));
};

const homPresheafFamilyType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => functorType(
            builder,
            Z,
            displayedCategoryAt(builder, opposite(builder, Z))
        ),
        implicitMode
    ));
};

const homPresheafFamilyBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => functorComposeAt(
            builder,
            Z,
            opposite(builder, displayedCategoryAt(builder, Z)),
            displayedCategoryAt(builder, opposite(builder, Z)),
            presheafFamilyAt(builder, opposite(builder, Z)),
            oppositeFunctorAt(
                builder,
                opposite(builder, Z),
                displayedCategoryAt(builder, Z),
                edgeFamilyAt(builder, Z)
            )
        ),
        implicitMode
    ));
};

const displayedHomTargetType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'E',
            displayedFamilyType(builder, Z),
            _E => displayedFamilyType(builder, Z),
            explicitMode
        ),
        implicitMode
    ));
};

const displayedHomTargetBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'Z',
        builder.global(category),
        Z => builder.lam(
            'E',
            displayedFamilyType(builder, Z),
            E => {
                const oppositeZ = opposite(builder, Z);
                const oppositeCatdZ = opposite(
                    builder,
                    displayedCategoryAt(builder, Z)
                );
                const catdOppositeZ =
                    displayedCategoryAt(builder, oppositeZ);
                const inner = functorObjectAt(
                    builder,
                    oppositeCatdZ,
                    functorCategoryAt(
                        builder,
                        catdOppositeZ,
                        catdOppositeZ
                    ),
                    mixedFunctorFamilyAt(builder, oppositeZ),
                    E
                );
                const pi = sectionCategoryFunctorAt(
                    builder,
                    oppositeZ
                );
                return functorComposeAt(
                    builder,
                    Z,
                    catdOppositeZ,
                    builder.global(categoryOfCategories),
                    functorComposeAt(
                        builder,
                        catdOppositeZ,
                        catdOppositeZ,
                        builder.global(categoryOfCategories),
                        pi,
                        inner
                    ),
                    homPresheafFamilyAt(builder, Z)
                );
            },
            explicitMode
        ),
        implicitMode
    ));
};

const displayedInternalHomType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'Z',
        builder.global(category),
        Z => builder.pi(
            'D',
            displayedFamilyType(builder, Z),
            D => builder.pi(
                'E',
                displayedFamilyType(builder, Z),
                E => builder.pi(
                    'FF',
                    displayedFunctorType(builder, Z, D, E),
                    _FF => displayedFunctorType(
                        builder,
                        Z,
                        displayedOppositeAt(builder, Z, E),
                        globalCall(
                            builder,
                            displayedHomTarget,
                            [
                                { plicity: 'implicit', value: Z },
                                { plicity: 'explicit', value: D }
                            ]
                        )
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

const declarations:
readonly CoreLfTransferDeclaration[] = Object.freeze([
    Object.freeze({
        ...priorIdentityDeclaration,
        order: 0
    }),
    Object.freeze({
        order: 1,
        symbol: displayedComposition,
        type: displayedCompositionType(),
        body: coreLfTransferExplicitBody(
            displayedCompositionBody()
        ),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol comp_catd_fapp0 [K : Cat] [E D : τ (Catd K)]',
            398
        )
    }),
    Object.freeze({
        order: 2,
        symbol: oppositeFunctor,
        type: oppositeFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source('injective symbol Op_func', 505)
    }),
    Object.freeze({
        order: 3,
        symbol: displayedOppositeFunctor,
        type: displayedOppositeFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Op_catd_func (Z : Cat)',
            540
        )
    }),
    Object.freeze({
        order: 4,
        symbol: internalHom,
        type: internalHomType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol hom_int [A B : Cat]',
            648
        )
    }),
    Object.freeze({
        order: 5,
        symbol: displayedOpposite,
        type: displayedOppositeType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Op_catd [K : Cat]',
            951
        )
    }),
    Object.freeze({
        order: 6,
        symbol: displayedOppositeAction,
        type: displayedOppositeActionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Op_funcd [K : Cat]',
            958
        )
    }),
    Object.freeze({
        order: 7,
        symbol: mixedFunctorFamily,
        type: mixedFunctorFamilyType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Functor_catd_func (K : Cat)',
            1036
        )
    }),
    Object.freeze({
        order: 8,
        symbol: edgeFamily,
        type: edgeFamilyType(),
        body: coreLfTransferExplicitBody(edgeFamilyBody()),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol Edge_catd_func [Z : Cat]',
            1049
        )
    }),
    Object.freeze({
        order: 9,
        symbol: presheafFamily,
        type: presheafFamilyType(),
        body: coreLfTransferExplicitBody(
            presheafFamilyBody()
        ),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol Presheaf_catd_func (K : Cat)',
            1050
        )
    }),
    Object.freeze({
        order: 10,
        symbol: homPresheafFamily,
        type: homPresheafFamilyType(),
        body: coreLfTransferExplicitBody(
            homPresheafFamilyBody()
        ),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol HomPresheaf_catd_func [Z : Cat]',
            1051
        )
    }),
    Object.freeze({
        order: 11,
        symbol: displayedHomTarget,
        type: displayedHomTargetType(),
        body: coreLfTransferExplicitBody(
            displayedHomTargetBody()
        ),
        modifiers: modifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol Homd_target_catd [Z : Cat]',
            1053
        )
    }),
    Object.freeze({
        order: 12,
        symbol: displayedInternalHom,
        type: displayedInternalHomType(),
        body: coreLfTransferAbsentBody(),
        modifiers: modifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol homd_int',
            1054
        )
    })
]);

const foundationExternalSymbols = Object.freeze([
    category,
    decodeOwner,
    objectClassifier,
    homClassifier,
    functorClassifier,
    categoryOfCategories,
    displayedCategoryCategory,
    functorObject,
    constantDisplayedFamily,
    displayedFamilyClassifier,
    displayedFunctorClassifier,
    ordinaryComposition,
    oppositeCategory,
    functorCategory,
    functorEvaluation,
    functorComposition,
    sectionCategoryFunctor
]);

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_DEPENDENCY_CORRECTION =
Object.freeze({
    revision:
        'DISPLAYED-ND-HIGHER-FOUNDATION-1A-DEPENDENCY-CORRECTION-1',
    triggeredBy:
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
            .recommendedContinuation.mandatoryStop,
    auditCheckpoint:
        '4db1ce8a80725c0030ac8908f416d412591620bd',
    reviewCheckpoint:
        'f674be92ae04eff5642428724053fb4e75274e50',
    decision:
        'D-DTTLF-USABILITY-020-directly-approved-2026-07-29',
    missingExistingCoreOwnerLinks: Object.freeze([
        Object.freeze({
            symbol: 'Obj',
            owner: 'object-classifier' as CoreOwnerId
        }),
        Object.freeze({
            symbol: 'Hom',
            owner: 'hom-classifier' as CoreOwnerId
        })
    ]),
    missingExistingRuntimeRule: Object.freeze({
        id: 'categorical.opposite.involution',
        canonicalCommandOrdinal: 237,
        canonicalCommandText:
            'rule Op_cat (Op_cat $A) ↪ $A;',
        canonicalCommandTextSha256:
            'c9ff2c9e112c82facf9f1a01573c5cbf7aa9fa6cfa5458d1c46e77c94feb24ec',
        activeLambdapiRuleDelta: 0,
        typescriptRuntimeRuleDelta: 1
    }),
    reason:
        'the-reused-id-signature-references-Obj-and-Hom-and-the-' +
        'HomPresheaf-catd-func-transparent-body-needs-opposite-involution;' +
        'all-three-are-existing-authority-omitted-from-the-audit-boundary',
    semanticScopeChanged: false,
    declarationCountChanged: false,
    policyChanged: false,
    typescriptRuntimeRuleDelta: 1,
    activeLambdapiRuntimeRuleDelta: 0,
    proofRuleDelta: 0,
    intrinsicCoreOwnerDelta: 0,
    checkerBranchDelta: 0,
    surfaceMethodDelta: 0,
    disposition:
        'apply-the-directly-approved-D-020-dependency-correction-and-' +
        'continue-the-exact-reviewed-thirteen-declaration-scope'
});

const oppositeInvolutionRule = (): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    return {
        order: 0,
        id:
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_DEPENDENCY_CORRECTION
                .missingExistingRuntimeRule.id,
        groupId: 'categorical.opposite',
        clauseOrder: 0,
        sourceOwner: oppositeCategory,
        variables: [{
            name: 'A',
            type: builder.template(builder.global(category))
        }],
        left: builder.pattern(opposite(builder, opposite(builder, A))),
        right: builder.template(A),
        provenance: source(
            'rule Op_cat (Op_cat $A) ↪ $A;',
            237
        )
    };
};

const foundationRuntimeRules:
readonly CoreLfTransferRuntimeRule[] = Object.freeze([
    oppositeInvolutionRule()
]);

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        'DISPLAYED-ND-HIGHER-FOUNDATION-1A-RUNTIME-D020-1',
    moduleId: MODULE_ID,
    fragmentId: 'displayed-nd-higher-foundation-1a-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        'sha256:' +
        '4d5791fc95c158308b87c970b622da35c2dd0ec64bd32b7f535679a95eba195a',
    dependencies: [],
    externalSymbols: [category, oppositeCategory].map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules: foundationRuntimeRules,
    proofRules: []
});

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_RUNTIME_MODULE,
    {
        revision:
            'DISPLAYED-ND-HIGHER-FOUNDATION-1A-RUNTIME-D020-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_RUNTIME_MODULE
                .revision,
        entries: foundationRuntimeRules.map(rule => ({
            order: rule.order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact active ordinal-237 computation directly approved ' +
                'by D-DTTLF-USABILITY-020'
        }))
    }
);

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_REVISION,
    moduleId: MODULE_ID,
    fragmentId: 'displayed-nd-higher-foundation-1a',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
            .measuredClosure.acquisitionRevision ===
                'DISPLAYED-ND-HIGHER-1B-ACQUISITION-1'
            ? 'sha256:' +
                '4d5791fc95c158308b87c970b622da35c2dd0ec64bd32b7f535679a95eba195a'
            : 'invalid-audit-revision',
    dependencies: [],
    externalSymbols: foundationExternalSymbols.map(symbol_ => ({
        symbol: symbol_,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

const reviewedPolicies =
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_REVIEW
        .authorization.exactPolicies;

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_MODULE,
    {
        revision:
            'DISPLAYED-ND-HIGHER-FOUNDATION-1A-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_MODULE
                .revision,
        entries: declarations.map(declaration => {
            const reviewed = reviewedPolicies.find(entry =>
                entry.name === declaration.symbol.name
            );
            if (reviewed === undefined) {
                throw new Error(
                    `No D-019 policy for ${declaration.symbol.name}`
                );
            }
            return {
                order: declaration.order,
                target: {
                    kind: 'declaration' as const,
                    symbol: declaration.symbol
                },
                policy: reviewed.policy,
                evidence:
                    'Exact existing active declaration approved by ' +
                    'D-DTTLF-USABILITY-019'
            };
        })
    }
);

const auditedCoreOwnerLinks = [
    ...CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
        .dependencyBoundary.alreadyAvailableCoreOwnerLinks,
    ...CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_DEPENDENCY_CORRECTION
        .missingExistingCoreOwnerLinks
];

const auditedFreeDeclarationLinks =
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
        .dependencyBoundary.alreadyAvailableFreeDeclarationLinks;

const externalLink = (
    target: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const core = auditedCoreOwnerLinks.find(entry =>
        entry.symbol === target.name
    );
    if (core !== undefined) {
        return Object.freeze({
            order,
            symbol: target,
            kind: 'core-owner' as const,
            owner: core.owner
        });
    }
    const free = auditedFreeDeclarationLinks.find(entry =>
        entry.symbol === target.name
    );
    if (free !== undefined) {
        return Object.freeze({
            order,
            symbol: target,
            kind: 'free-declaration' as const,
            coreName: free.coreName,
            backendName: free.symbol
        });
    }
    throw new Error(
        `No reviewed foundation dependency link for ${target.name}`
    );
};

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_MODULE,
        {
            revision:
                'DISPLAYED-ND-HIGHER-FOUNDATION-1A-LINKAGE-1',
            moduleRevision:
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_MODULE
                    .revision,
            entries: [
                ...foundationExternalSymbols.map(externalLink),
                ...declarations.map((declaration, index) => ({
                    order: foundationExternalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName: (() => {
                        const entry = Object.entries(
                            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_SYMBOLS
                        ).find(([, symbol_]) =>
                            symbol_.moduleId ===
                                declaration.symbol.moduleId &&
                            symbol_.name === declaration.symbol.name
                        );
                        if (entry === undefined) {
                            throw new Error(
                                'Displayed higher foundation declaration ' +
                                `'${declaration.symbol.name}' has no Core ` +
                                'name contract entry'
                            );
                        }
                        return coreCategoricalDisplayedNdHigherFoundationCoreName(
                            entry[0] as
                                CoreCategoricalDisplayedNdHigherFoundationSymbolId
                        );
                    })(),
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_BOUNDARY =
Object.freeze({
    revision:
        'DISPLAYED-ND-HIGHER-FOUNDATION-1A-BOUNDARY-1',
    declarationNames: Object.freeze(
        declarations.map(declaration => declaration.symbol.name)
    ),
    declarationCount: declarations.length,
    checkedTransparentDefinitionCount:
        reviewedPolicies.filter(entry =>
            entry.policy === 'checked-transparent-definition'
        ).length,
    opaqueSignatureCount:
        reviewedPolicies.filter(entry =>
            entry.policy === 'opaque-signature'
        ).length,
    existingRuntimeRuleIds: Object.freeze(
        foundationRuntimeRules.map(rule => rule.id)
    ),
    runtimeRuleCount: foundationRuntimeRules.length,
    proofRuleCount: 0,
    reusedIdentityCoreName:
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
            .dependencyBoundary.reusablePriorRepresentation.coreName,
    activeLambdapiOwnerDelta: 0,
    activeLambdapiRuleDelta: 0,
    typescriptRuntimeRuleDelta: 1,
    intrinsicCoreOwnerDelta: 0,
    ownerSpecificCheckerOrEvaluatorDelta: 0,
    surfaceMethodDelta: 0,
    browserPromotionDelta: 0,
    targetOwnersIncluded: false,
    targetProjectionRulesIncluded: false,
    allEntriesUseGenericTransferEngines: true
});

export interface CoreCategoricalDisplayedNdHigherFoundationCompilation {
    readonly prerequisite:
        CoreCategoricalDisplayedChain2aClosureCompilation;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

let cachedCompilation:
    CoreCategoricalDisplayedNdHigherFoundationCompilation | undefined;

export function compileCoreCategoricalDisplayedNdHigherFoundationTransfer():
CoreCategoricalDisplayedNdHigherFoundationCompilation {
    if (cachedCompilation !== undefined) return cachedCompilation;
    validateCoreCategoricalDisplayedNdHigherReview();
    const prerequisite =
        compileCoreCategoricalDisplayedChain2aClosureTransfer();
    const runtimeFragment = compileCoreLfRuntimeFragment(
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_RUNTIME_MODULE,
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_RUNTIME_POLICY,
        prerequisite.declarationContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: prerequisite.runtimeFragment
            }],
            comparisonStepLimit: 512
        }
    );
    const compiled = compileCoreLfDeclarations(
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_MODULE,
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_POLICY,
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_TRANSFER_LINKAGE,
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
