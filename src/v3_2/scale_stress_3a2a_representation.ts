/**
 * Representation-only SCALE-STRESS-3A2A transfer of profunctor comparison
 * push/pull.
 *
 * This fragment extends the exact 3A1 declaration context, adds the one
 * source-prior Hom owner definition and identity-functor object rule needed
 * by the transparent bodies, and keeps tensor/product action for
 * SCALE-STRESS-3A2B.
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
    CoreLfTransferDeclaration,
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
    CORE_LF_SCALE_STRESS_3_PROFUNCTOR_COMPARISON_ACQUISITION
} from './scale_stress_3_acquisition';
import {
    CORE_LF_SCALE_STRESS_3A1_LINKAGE,
    CORE_LF_SCALE_STRESS_3A1_SYMBOLS,
    CoreLfScaleStress3a1Compilation,
    compileCoreLfScaleStress3a1Representation
} from './scale_stress_3a1_representation';

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
const homClassifier =
    coreDirectedContinuationTransferSymbol('hom-classifier');
const homCategory =
    coreDirectedContinuationTransferSymbol('hom-category');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol('category-of-categories');
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');

const {
    definitionalIsomorphism,
    profunctorCategory,
    profunctorClassifier,
    profunctorComparison
} = CORE_LF_SCALE_STRESS_3A1_SYMBOLS;

export const CORE_LF_SCALE_STRESS_3A2A_SYMBOLS = Object.freeze({
    homClassifier,
    identityArrow:
        coreLfQualifiedSymbol(moduleId, 'id'),
    identityFunctor:
        coreLfQualifiedSymbol(moduleId, 'id_func'),
    postcompositionAction:
        coreLfQualifiedSymbol(moduleId, 'hom_postcomp_fapp0'),
    definitionalIsomorphismTo:
        coreLfQualifiedSymbol(moduleId, 'defiso_to'),
    definitionalIsomorphismFrom:
        coreLfQualifiedSymbol(moduleId, 'defiso_from'),
    profunctorMap:
        coreLfQualifiedSymbol(moduleId, 'ProfMap'),
    comparisonPush:
        coreLfQualifiedSymbol(moduleId, 'prof_comparison_push'),
    comparisonPull:
        coreLfQualifiedSymbol(moduleId, 'prof_comparison_pull')
});

const {
    identityArrow,
    identityFunctor,
    postcompositionAction,
    definitionalIsomorphismTo,
    definitionalIsomorphismFrom,
    profunctorMap,
    comparisonPush,
    comparisonPull
} = CORE_LF_SCALE_STRESS_3A2A_SYMBOLS;

/**
 * The source declaration keeps the existing backend-neutral
 * `hom-classifier` owner and contributes only its checked transparent body.
 * It is installed before every selected consumer, without a shadowing free
 * declaration or an owner-specific runtime rule.
 */
export const CORE_LF_SCALE_STRESS_3A2A_INTRINSIC_DEFINITIONS =
    Object.freeze([
        Object.freeze({
            acquisitionId:
                'profunctor-comparison.hom-classifier',
            sourceSymbol: homClassifier,
            targetOwner: 'hom-classifier' as const,
            sourceBody:
                'Obj (Hom_cat A X_A Y_A)',
            sourceDependencies: Object.freeze([
                objectClassifier,
                homCategory
            ]),
            consumer: profunctorMap
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
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, functorClassifier, [
        { plicity: 'explicit', value: sourceCategory },
        { plicity: 'explicit', value: targetCategory }
    ]));

const homClassifierAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, homClassifier, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: sourceObject },
        { plicity: 'explicit', value: targetObject }
    ]);

const homCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, homCategory, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: sourceObject },
        { plicity: 'explicit', value: targetObject }
    ]);

const homType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(
        builder,
        homClassifierAt(
            builder,
            base,
            sourceObject,
            targetObject
        )
    );

const fapp0 = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorObject, [
        { plicity: 'implicit', value: sourceCategory },
        { plicity: 'implicit', value: targetCategory },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: object }
    ]);

const identityArrowAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, identityArrow, [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: object }
    ]);

const identityFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, identityFunctor, [{
        plicity: 'implicit',
        value: base
    }]);

const profunctorCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, profunctorCategory, [
        { plicity: 'explicit', value: sourceCategory },
        { plicity: 'explicit', value: targetCategory }
    ]);

const profunctorClassifierAt = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, profunctorClassifier, [
        { plicity: 'explicit', value: sourceCategory },
        { plicity: 'explicit', value: targetCategory }
    ]);

const profunctorType = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(
        builder,
        profunctorClassifierAt(
            builder,
            sourceCategory,
            targetCategory
        )
    );

const profunctorComparisonType = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, profunctorComparison, [
        { plicity: 'implicit', value: sourceCategory },
        { plicity: 'implicit', value: targetCategory },
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
    ]));

const profunctorMapClassifierAt = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression,
    sourceProfunctor: CoreLfTransferBuilderExpression,
    targetProfunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, profunctorMap, [
        { plicity: 'implicit', value: sourceCategory },
        { plicity: 'implicit', value: targetCategory },
        { plicity: 'explicit', value: sourceProfunctor },
        { plicity: 'explicit', value: targetProfunctor }
    ]);

const profunctorMapType = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression,
    sourceProfunctor: CoreLfTransferBuilderExpression,
    targetProfunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, profunctorMapClassifierAt(
        builder,
        sourceCategory,
        targetCategory,
        sourceProfunctor,
        targetProfunctor
    ));

const definitionalIsomorphismType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, definitionalIsomorphism, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
    ]));

const definitionalIsomorphismProjection = (
    builder: CoreLfTransferScopedBuilder,
    projection: CoreLfQualifiedSymbol,
    base: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression,
    witness: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, projection, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: left },
        { plicity: 'implicit', value: right },
        { plicity: 'explicit', value: witness }
    ]);

const postcomposition = (
    builder: CoreLfTransferScopedBuilder,
    targetCategory: CoreLfTransferBuilderExpression,
    sourceCategory: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    fixedSource: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression,
    incoming: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, postcompositionAction, [
        { plicity: 'implicit', value: targetCategory },
        { plicity: 'implicit', value: sourceCategory },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: fixedSource },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: arrow },
        { plicity: 'explicit', value: incoming }
    ]);

const identityArrowType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'X',
            objectType(builder, A),
            X => homType(builder, A, X, X),
            explicitMode
        ),
        explicitMode
    ));
};

const homClassifierDefinitionType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'X_A',
            objectType(builder, A),
            _X => builder.pi(
                'Y_A',
                objectType(builder, A),
                _Y => builder.global(groupoid),
                explicitMode
            ),
            explicitMode
        ),
        explicitMode
    ));
};

const homClassifierDefinitionBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'A',
        builder.global(category),
        A => builder.lam(
            'X_A',
            objectType(builder, A),
            X => builder.lam(
                'Y_A',
                objectType(builder, A),
                Y => objectClassifierAt(
                    builder,
                    homCategoryAt(builder, A, X, Y)
                ),
                explicitMode
            ),
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

const identityFunctorBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'A',
        builder.global(category),
        A => identityArrowAt(
            builder,
            builder.global(categoryOfCategories),
            A
        ),
        implicitMode
    ));
};

const postcompositionActionType =
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
                functorType(builder, B, A),
                F => builder.pi(
                    'W',
                    objectType(builder, A),
                    W => builder.pi(
                        'X',
                        objectType(builder, B),
                        X => builder.pi(
                            'Y',
                            objectType(builder, B),
                            Y => builder.pi(
                                'f',
                                homType(builder, B, X, Y),
                                _f => builder.pi(
                                    'g',
                                    homType(
                                        builder,
                                        A,
                                        W,
                                        fapp0(
                                            builder,
                                            B,
                                            A,
                                            F,
                                            X
                                        )
                                    ),
                                    _g => homType(
                                        builder,
                                        A,
                                        W,
                                        fapp0(
                                            builder,
                                            B,
                                            A,
                                            F,
                                            Y
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
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const definitionalIsomorphismProjectionType = (
    direction: 'to' | 'from'
): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'C',
        builder.global(category),
        C => builder.pi(
            'x',
            objectType(builder, C),
            x => builder.pi(
                'y',
                objectType(builder, C),
                y => builder.pi(
                    'i',
                    definitionalIsomorphismType(builder, C, x, y),
                    _i => homType(
                        builder,
                        C,
                        direction === 'to' ? x : y,
                        direction === 'to' ? y : x
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

const profunctorMapTypeDeclaration =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'P',
                profunctorType(builder, A, B),
                P => builder.pi(
                    'Q',
                    profunctorType(builder, A, B),
                    _Q => builder.global(groupoid),
                    explicitMode
                ),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const profunctorMapBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'A',
        builder.global(category),
        A => builder.lam(
            'B',
            builder.global(category),
            B => builder.lam(
                'P',
                profunctorType(builder, A, B),
                P => builder.lam(
                    'Q',
                    profunctorType(builder, A, B),
                    Q => homClassifierAt(
                        builder,
                        profunctorCategoryAt(builder, A, B),
                        P,
                        Q
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

const comparisonTransportType = (
    direction: 'push' | 'pull'
): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'P',
                profunctorType(builder, A, B),
                P => builder.pi(
                    'Q',
                    profunctorType(builder, A, B),
                    Q => builder.pi(
                        'i',
                        profunctorComparisonType(
                            builder,
                            A,
                            B,
                            P,
                            Q
                        ),
                        _i => builder.pi(
                            'R',
                            profunctorType(builder, A, B),
                            R => builder.pi(
                                direction === 'push' ? 'r' : 's',
                                profunctorMapType(
                                    builder,
                                    A,
                                    B,
                                    R,
                                    direction === 'push' ? P : Q
                                ),
                                _incoming => profunctorMapType(
                                    builder,
                                    A,
                                    B,
                                    R,
                                    direction === 'push' ? Q : P
                                ),
                                explicitMode
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
    ));
};

const comparisonTransportBody = (
    direction: 'push' | 'pull'
): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'A',
        builder.global(category),
        A => builder.lam(
            'B',
            builder.global(category),
            B => builder.lam(
                'P',
                profunctorType(builder, A, B),
                P => builder.lam(
                    'Q',
                    profunctorType(builder, A, B),
                    Q => builder.lam(
                        'i',
                        profunctorComparisonType(
                            builder,
                            A,
                            B,
                            P,
                            Q
                        ),
                        i => builder.lam(
                            'R',
                            profunctorType(builder, A, B),
                            R => builder.lam(
                                direction === 'push' ? 'r' : 's',
                                profunctorMapType(
                                    builder,
                                    A,
                                    B,
                                    R,
                                    direction === 'push' ? P : Q
                                ),
                                incoming => {
                                    const base =
                                        profunctorCategoryAt(
                                            builder,
                                            A,
                                            B
                                        );
                                    return postcomposition(
                                        builder,
                                        base,
                                        base,
                                        identityFunctorAt(
                                            builder,
                                            base
                                        ),
                                        R,
                                        direction === 'push' ? P : Q,
                                        direction === 'push' ? Q : P,
                                        definitionalIsomorphismProjection(
                                            builder,
                                            direction === 'push'
                                                ? definitionalIsomorphismTo
                                                : definitionalIsomorphismFrom,
                                            base,
                                            P,
                                            Q,
                                            i
                                        ),
                                        incoming
                                    );
                                },
                                explicitMode
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
    ));
};

const identityObjectRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const x = builder.capture('x');
    return {
        order: 3,
        id: 'stress.profunctor-comparison.identity-object',
        groupId: 'stress.profunctor-comparison.identity-object',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, A))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            A,
            A,
            identityArrowAt(
                builder,
                builder.global(categoryOfCategories),
                A
            ),
            x
        )),
        right: builder.template(x),
        provenance: source(
            'rule @fapp0 $A $A (@id Cat_cat $A) $xA ↪ $xA;',
            407
        )
    };
};

const source = (
    sourceFragment: string,
    canonicalCommandOrdinal: number
) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment,
    canonicalCommandOrdinal
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
        symbol: homClassifier,
        type: homClassifierDefinitionType(),
        body: coreLfTransferExplicitBody(
            homClassifierDefinitionBody()
        ),
        modifiers: publicModifiers('injective', 'transparent'),
        provenance: source(
            'injective symbol Hom (A : Cat)',
            230
        )
    },
    {
        order: 1,
        symbol: identityArrow,
        type: identityArrowType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol id : Π (A : Cat)',
            232
        )
    },
    {
        order: 2,
        symbol: identityFunctor,
        type: identityFunctorType(),
        body: coreLfTransferExplicitBody(identityFunctorBody()),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol id_func [A: Cat]',
            406
        )
    },
    {
        order: 4,
        symbol: postcompositionAction,
        type: postcompositionActionType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol hom_postcomp_fapp0 [A B : Cat]',
            547
        )
    },
    {
        order: 5,
        symbol: definitionalIsomorphismTo,
        type: definitionalIsomorphismProjectionType('to'),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol defiso_to',
            578
        )
    },
    {
        order: 6,
        symbol: definitionalIsomorphismFrom,
        type: definitionalIsomorphismProjectionType('from'),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol defiso_from',
            579
        )
    },
    {
        order: 7,
        symbol: profunctorMap,
        type: profunctorMapTypeDeclaration(),
        body: coreLfTransferExplicitBody(profunctorMapBody()),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol ProfMap',
            1204
        )
    },
    {
        order: 8,
        symbol: comparisonPush,
        type: comparisonTransportType('push'),
        body: coreLfTransferExplicitBody(
            comparisonTransportBody('push')
        ),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol prof_comparison_push',
            1233
        )
    },
    {
        order: 9,
        symbol: comparisonPull,
        type: comparisonTransportType('pull'),
        body: coreLfTransferExplicitBody(
            comparisonTransportBody('pull')
        ),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol prof_comparison_pull',
            1234
        )
    }
];

const runtimeRules = [identityObjectRule()] as const;

export const CORE_LF_SCALE_STRESS_3A2A_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'SCALE-STRESS-3A2A-PROFUNCTOR-COMPARISON-1',
    moduleId,
    fragmentId: 'scale-stress-3a2a-profunctor-comparison',
    authorityPath:
        CORE_LF_SCALE_STRESS_3_PROFUNCTOR_COMPARISON_ACQUISITION
            .authorityPath,
    sourceSha256:
        CORE_LF_SCALE_STRESS_3_PROFUNCTOR_COMPARISON_ACQUISITION
            .sourceSha256,
    canonicalExport: {
        exporterVersion:
            CORE_LF_SCALE_STRESS_3_PROFUNCTOR_COMPARISON_ACQUISITION
                .canonicalExport.exporterVersion,
        sha256:
            CORE_LF_SCALE_STRESS_3_PROFUNCTOR_COMPARISON_ACQUISITION
                .canonicalExport.sha256
    },
    dependencies: [],
    externalSymbols: [
        category,
        groupoid,
        decodeOwner,
        objectClassifier,
        functorClassifier,
        homCategory,
        categoryOfCategories,
        functorObject,
        definitionalIsomorphism,
        profunctorCategory,
        profunctorClassifier,
        profunctorComparison
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const CORE_LF_SCALE_STRESS_3A2A_POLICY:
CoreLfTransferPolicyOverlay =
    createCoreLfTransferPolicyOverlay(
        CORE_LF_SCALE_STRESS_3A2A_MODULE,
        {
            revision:
                'SCALE-STRESS-3A2A-PROFUNCTOR-COMPARISON-POLICY-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_3A2A_MODULE.revision,
            entries: [
                {
                    order: 0,
                    target: {
                        kind: 'declaration',
                        symbol: homClassifier
                    },
                    policy: 'checked-transparent-definition',
                    evidence:
                        'Exact active transparent Hom owner definition'
                },
                {
                    order: 1,
                    target: {
                        kind: 'declaration',
                        symbol: identityArrow
                    },
                    policy: 'opaque-signature',
                    evidence:
                        'Exact active identity-arrow signature'
                },
                {
                    order: 2,
                    target: {
                        kind: 'declaration',
                        symbol: identityFunctor
                    },
                    policy: 'checked-transparent-definition',
                    evidence:
                        'Exact active transparent identity functor'
                },
                {
                    order: 3,
                    target: {
                        kind: 'runtime-rule',
                        id:
                            'stress.profunctor-comparison.' +
                            'identity-object'
                    },
                    policy: 'runtime-rewrite',
                    evidence:
                        'Exact active identity-functor object rule'
                },
                ...declarations.slice(3).map(
                    (declaration, index) => ({
                        order: index + 4,
                        target: {
                            kind: 'declaration' as const,
                            symbol: declaration.symbol
                        },
                        policy:
                            declaration.symbol === profunctorMap ||
                            declaration.symbol === comparisonPush ||
                            declaration.symbol === comparisonPull
                                ? 'checked-transparent-definition' as const
                                : 'opaque-signature' as const,
                        evidence:
                            'Exact active comparison-action declaration'
                    })
                )
            ]
        }
    );

export const CORE_LF_SCALE_STRESS_3A2A_PLAN:
CoreLfMixedPhasePlan = planCoreLfMixedPhases(
    CORE_LF_SCALE_STRESS_3A2A_MODULE,
    CORE_LF_SCALE_STRESS_3A2A_POLICY
);

const prerequisiteLinks = [
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries,
    ...CORE_LF_SCALE_STRESS_3A1_LINKAGE.entries
];

const externalLink = (
    symbol: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const link = prerequisiteLinks.find(candidate =>
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
    CORE_LF_SCALE_STRESS_3A2A_MODULE.externalSymbols.map(
        external => external.symbol
    );

export const CORE_LF_SCALE_STRESS_3A2A_LINKAGE:
CoreLfMixedDeclarationLinkage =
    createCoreLfMixedDeclarationLinkage(
        CORE_LF_SCALE_STRESS_3A2A_PLAN,
        {
            revision:
                'SCALE-STRESS-3A2A-PROFUNCTOR-COMPARISON-LINKAGE-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_3A2A_MODULE.revision,
            entries: [
                ...externalSymbols.map(externalLink),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    ...(declaration.symbol === homClassifier
                        ? {
                            kind: 'core-owner' as const,
                            owner: 'hom-classifier' as const
                        }
                        : {
                            kind: 'free-declaration' as const,
                            coreName:
                                `emdash_v3_2_scale_stress_3a2a_` +
                                declaration.symbol.name,
                            backendName: declaration.symbol.name
                        })
                }))
            ]
        }
    );

export const CORE_LF_SCALE_STRESS_3A2A_BOUNDARY = Object.freeze({
    semanticStatus: 'isolated-representation-only',
    intrinsicTransparentDefinitions:
        CORE_LF_SCALE_STRESS_3A2A_INTRINSIC_DEFINITIONS,
    selectedRuntimeRuleIds: Object.freeze([
        'stress.profunctor-comparison.identity-object'
    ]),
    selectedTransparentBodies: Object.freeze([
        homClassifier,
        identityFunctor,
        profunctorMap,
        comparisonPush,
        comparisonPull
    ]),
    selectedOpaquePrimitives: Object.freeze([
        identityArrow,
        postcompositionAction,
        definitionalIsomorphismTo,
        definitionalIsomorphismFrom
    ]),
    doesNotProvide: Object.freeze([
        'active-policy-selection',
        'DefIso-cancellation-runtime',
        'profunctor-comparison-beta-eta',
        'profunctor-tensor-map-or-functor',
        'profunctor-tensor-action-runtime',
        'protected-module-visibility',
        'proof-heavy-extension',
        'WalkingEnd-HIT',
        'browser-api',
        'mechanical-transfer-qualification'
    ])
});

export interface CoreLfScaleStress3a2aCompilation {
    readonly prerequisite: CoreLfScaleStress3a1Compilation;
    readonly continuationRuntime: CoreLfCompiledRuntimeFragment;
    readonly compiled: CoreLfCompiledMixedModule;
}

export function compileCoreLfScaleStress3a2aRepresentation():
CoreLfScaleStress3a2aCompilation {
    validateCoreLfScaleEngineReview();
    const prerequisite =
        compileCoreLfScaleStress3a1Representation();
    const continuationRuntime = compileCoreLfRuntimeFragment(
        CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE,
        CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_POLICY,
        prerequisite.initialDeclarations,
        {
            dependencies: [],
            subjectReductionOracle:
                CORE_DIRECTED_CONTINUATION_RUNTIME_SUBJECT_ORACLE
        }
    );
    const compiled = compileCoreLfMixedPhases(
        CORE_LF_SCALE_STRESS_3A2A_PLAN,
        CORE_LF_SCALE_STRESS_3A2A_LINKAGE,
        {
            initialDeclarations: prerequisite.declarationContext,
            runtimeDependencies: [{
                relation: 'earlier-fragment',
                fragment: continuationRuntime
            }]
        }
    );
    return Object.freeze({
        prerequisite,
        continuationRuntime,
        compiled
    });
}
