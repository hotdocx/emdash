/**
 * Representation-only SCALE-STRESS-3A2B transfer of product closure and the
 * fixed-endpoint profunctor tensor bifunctor action.
 *
 * The fragment is deliberately narrow: four product/projection primitives,
 * two tensor-action primitives, and the five exact runtime clauses required
 * to type and execute object/capped-arrow action. It extends the checked Hom
 * intrinsic definition from 3A2A and adds no owner-specific engine branch.
 */

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
    CORE_LF_SCALE_STRESS_3_PROFUNCTOR_TENSOR_ACTION_ACQUISITION
} from './scale_stress_3_acquisition';
import {
    CORE_LF_SCALE_STRESS_3A1_LINKAGE,
    CORE_LF_SCALE_STRESS_3A1_SYMBOLS
} from './scale_stress_3a1_representation';
import {
    CORE_LF_SCALE_STRESS_3A2A_LINKAGE,
    CORE_LF_SCALE_STRESS_3A2A_SYMBOLS,
    CoreLfScaleStress3a2aCompilation,
    compileCoreLfScaleStress3a2aRepresentation
} from './scale_stress_3a2a_representation';

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
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const functorHomCapped =
    coreDirectedContinuationTransferSymbol('functor-hom-capped');
const decodedDependentPair =
    coreDirectedContinuationTransferSymbol('decoded-dependent-pair');

const {
    profunctorCategory,
    profunctorClassifier,
    profunctorTensor
} = CORE_LF_SCALE_STRESS_3A1_SYMBOLS;
const {
    profunctorMap
} = CORE_LF_SCALE_STRESS_3A2A_SYMBOLS;

export const CORE_LF_SCALE_STRESS_3A2B_SYMBOLS = Object.freeze({
    sigmaFirst:
        coreLfQualifiedSymbol(moduleId, 'sigma_Fst'),
    sigmaSecond:
        coreLfQualifiedSymbol(moduleId, 'sigma_Snd'),
    productGroupoid:
        coreLfQualifiedSymbol(moduleId, 'Product_grpd'),
    productCategory:
        coreLfQualifiedSymbol(moduleId, 'Product_cat'),
    profunctorTensorMap:
        coreLfQualifiedSymbol(moduleId, 'Prof_tensor_map'),
    profunctorTensorFunctor:
        coreLfQualifiedSymbol(moduleId, 'Prof_tensor_func')
});

const {
    sigmaFirst,
    sigmaSecond,
    productGroupoid,
    productCategory,
    profunctorTensorMap,
    profunctorTensorFunctor
} = CORE_LF_SCALE_STRESS_3A2B_SYMBOLS;

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
    decode(builder, homClassifierAt(
        builder,
        base,
        sourceObject,
        targetObject
    ));

const groupoidFamilyType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    builder.pi(
        'x',
        decode(builder, base),
        _x => builder.global(groupoid),
        explicitMode
    );

const applyFamily = (
    builder: CoreLfTransferScopedBuilder,
    family: CoreLfTransferBuilderExpression,
    value: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    call(builder, family, [{
        plicity: 'explicit',
        value
    }]);

const decodedPairAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, decodedDependentPair, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]);

const constantGroupoidFamily = (
    builder: CoreLfTransferScopedBuilder,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    builder.lam(
        'ignored',
        decode(builder, left),
        _x => right,
        explicitMode
    );

const sigmaFirstAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    pair: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaFirst, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: family },
        { plicity: 'explicit', value: pair }
    ]);

const sigmaSecondAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    family: CoreLfTransferBuilderExpression,
    pair: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, sigmaSecond, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: family },
        { plicity: 'explicit', value: pair }
    ]);

const productGroupoidAt = (
    builder: CoreLfTransferScopedBuilder,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, productGroupoid, [
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
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

const productObjectComponents = (
    builder: CoreLfTransferScopedBuilder,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression,
    pair: CoreLfTransferBuilderExpression
) => {
    const leftClassifier = objectClassifierAt(builder, left);
    const rightClassifier = objectClassifierAt(builder, right);
    const family = constantGroupoidFamily(
        builder,
        leftClassifier,
        rightClassifier
    );
    return {
        first: sigmaFirstAt(
            builder,
            leftClassifier,
            family,
            pair
        ),
        second: sigmaSecondAt(
            builder,
            leftClassifier,
            family,
            pair
        )
    };
};

const profunctorCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, profunctorCategory, [
        { plicity: 'explicit', value: sourceCategory },
        { plicity: 'explicit', value: targetCategory }
    ]);

const profunctorType = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, profunctorClassifier, [
        { plicity: 'explicit', value: sourceCategory },
        { plicity: 'explicit', value: targetCategory }
    ]));

const profunctorMapType = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression,
    sourceProfunctor: CoreLfTransferBuilderExpression,
    targetProfunctor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, profunctorMap, [
        { plicity: 'implicit', value: sourceCategory },
        { plicity: 'implicit', value: targetCategory },
        { plicity: 'explicit', value: sourceProfunctor },
        { plicity: 'explicit', value: targetProfunctor }
    ]));

const profunctorTensorAt = (
    builder: CoreLfTransferScopedBuilder,
    A: CoreLfTransferBuilderExpression,
    B: CoreLfTransferBuilderExpression,
    X: CoreLfTransferBuilderExpression,
    P: CoreLfTransferBuilderExpression,
    Q: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, profunctorTensor, [
        { plicity: 'implicit', value: A },
        { plicity: 'implicit', value: B },
        { plicity: 'implicit', value: X },
        { plicity: 'explicit', value: P },
        { plicity: 'explicit', value: Q }
    ]);

const profunctorTensorMapAt = (
    builder: CoreLfTransferScopedBuilder,
    A: CoreLfTransferBuilderExpression,
    B: CoreLfTransferBuilderExpression,
    X: CoreLfTransferBuilderExpression,
    P: CoreLfTransferBuilderExpression,
    nextP: CoreLfTransferBuilderExpression,
    Q: CoreLfTransferBuilderExpression,
    nextQ: CoreLfTransferBuilderExpression,
    r: CoreLfTransferBuilderExpression,
    s: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, profunctorTensorMap, [
        { plicity: 'implicit', value: A },
        { plicity: 'implicit', value: B },
        { plicity: 'implicit', value: X },
        { plicity: 'implicit', value: P },
        { plicity: 'implicit', value: nextP },
        { plicity: 'implicit', value: Q },
        { plicity: 'implicit', value: nextQ },
        { plicity: 'explicit', value: r },
        { plicity: 'explicit', value: s }
    ]);

const profunctorTensorFunctorAt = (
    builder: CoreLfTransferScopedBuilder,
    A: CoreLfTransferBuilderExpression,
    B: CoreLfTransferBuilderExpression,
    X: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, profunctorTensorFunctor, [
        { plicity: 'implicit', value: A },
        { plicity: 'implicit', value: B },
        { plicity: 'implicit', value: X }
    ]);

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

const fapp1 = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    sourceObject: CoreLfTransferBuilderExpression,
    targetObject: CoreLfTransferBuilderExpression,
    arrow: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorHomCapped, [
        { plicity: 'implicit', value: sourceCategory },
        { plicity: 'implicit', value: targetCategory },
        { plicity: 'explicit', value: functor },
        { plicity: 'implicit', value: sourceObject },
        { plicity: 'implicit', value: targetObject },
        { plicity: 'explicit', value: arrow }
    ]);

const sigmaFirstType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'a',
        builder.global(groupoid),
        a => builder.pi(
            'P',
            groupoidFamilyType(builder, a),
            P => builder.pi(
                's',
                decodedPairAt(builder, a, P),
                _s => decode(builder, a),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const sigmaSecondType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'a',
        builder.global(groupoid),
        a => builder.pi(
            'P',
            groupoidFamilyType(builder, a),
            P => builder.pi(
                's',
                decodedPairAt(builder, a, P),
                s => decode(builder, applyFamily(
                    builder,
                    P,
                    sigmaFirstAt(builder, a, P, s)
                )),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const productGroupoidType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(groupoid),
        _A => builder.pi(
            'B',
            builder.global(groupoid),
            _B => builder.global(groupoid),
            explicitMode
        ),
        explicitMode
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

const profunctorTensorMapType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'X',
                builder.global(category),
                X => builder.pi(
                    'P',
                    profunctorType(builder, A, B),
                    P => builder.pi(
                        'P_next',
                        profunctorType(builder, A, B),
                        nextP => builder.pi(
                            'Q',
                            profunctorType(builder, B, X),
                            Q => builder.pi(
                                'Q_next',
                                profunctorType(builder, B, X),
                                nextQ => builder.pi(
                                    'r',
                                    profunctorMapType(
                                        builder,
                                        A,
                                        B,
                                        P,
                                        nextP
                                    ),
                                    r => builder.pi(
                                        's',
                                        profunctorMapType(
                                            builder,
                                            B,
                                            X,
                                            Q,
                                            nextQ
                                        ),
                                        _s => profunctorMapType(
                                            builder,
                                            A,
                                            X,
                                            profunctorTensorAt(
                                                builder,
                                                A,
                                                B,
                                                X,
                                                P,
                                                Q
                                            ),
                                            profunctorTensorAt(
                                                builder,
                                                A,
                                                B,
                                                X,
                                                nextP,
                                                nextQ
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
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const profunctorTensorFunctorType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'X',
                builder.global(category),
                X => functorType(
                    builder,
                    productCategoryAt(
                        builder,
                        profunctorCategoryAt(builder, A, B),
                        profunctorCategoryAt(builder, B, X)
                    ),
                    profunctorCategoryAt(builder, A, X)
                ),
                implicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const productGroupoidDecodeRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    return {
        order: 3,
        id: 'stress.profunctor-tensor.product-groupoid-decode',
        groupId: 'stress.profunctor-tensor.product-groupoid-decode',
        clauseOrder: 0,
        sourceOwner: decodeOwner,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(groupoid))
            },
            {
                name: 'B',
                type: builder.template(builder.global(groupoid))
            }
        ],
        left: builder.pattern(decode(
            builder,
            productGroupoidAt(builder, A, B)
        )),
        right: builder.template(decodedPairAt(
            builder,
            A,
            constantGroupoidFamily(builder, A, B)
        )),
        provenance: source(
            'rule τ (Product_grpd $A $B)',
            185
        )
    };
};

const productObjectRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    return {
        order: 5,
        id: 'stress.profunctor-tensor.product-object',
        groupId: 'stress.profunctor-tensor.product-object',
        clauseOrder: 0,
        sourceOwner: objectClassifier,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'B',
                type: builder.template(builder.global(category))
            }
        ],
        left: builder.pattern(objectClassifierAt(
            builder,
            productCategoryAt(builder, A, B)
        )),
        right: builder.template(productGroupoidAt(
            builder,
            objectClassifierAt(builder, A),
            objectClassifierAt(builder, B)
        )),
        provenance: source(
            'rule Obj (Product_cat $A $B)',
            663
        )
    };
};

const productHomCategoryRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const product = productCategoryAt(builder, A, B);
    const p = builder.capture('p');
    const q = builder.capture('q');
    const pComponents = productObjectComponents(builder, A, B, p);
    const qComponents = productObjectComponents(builder, A, B, q);
    return {
        order: 6,
        id: 'stress.profunctor-tensor.product-hom-category',
        groupId: 'stress.profunctor-tensor.product-hom-category',
        clauseOrder: 0,
        sourceOwner: homCategory,
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
                name: 'p',
                type: builder.template(objectType(builder, product))
            },
            {
                name: 'q',
                type: builder.template(objectType(builder, product))
            }
        ],
        left: builder.pattern(homCategoryAt(
            builder,
            product,
            p,
            q
        )),
        right: builder.template(productCategoryAt(
            builder,
            homCategoryAt(
                builder,
                A,
                pComponents.first,
                qComponents.first
            ),
            homCategoryAt(
                builder,
                B,
                pComponents.second,
                qComponents.second
            )
        )),
        provenance: source(
            'rule Hom_cat (Product_cat $A $B) $p $q',
            680
        )
    };
};

const tensorObjectActionRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const X = builder.capture('X');
    const leftCategory = profunctorCategoryAt(builder, A, B);
    const rightCategory = profunctorCategoryAt(builder, B, X);
    const sourceCategory = productCategoryAt(
        builder,
        leftCategory,
        rightCategory
    );
    const targetCategory = profunctorCategoryAt(builder, A, X);
    const PQ = builder.capture('PQ');
    const components = productObjectComponents(
        builder,
        leftCategory,
        rightCategory,
        PQ
    );
    return {
        order: 9,
        id: 'stress.profunctor-tensor.object-action',
        groupId: 'stress.profunctor-tensor.object-action',
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
                name: 'X',
                type: builder.template(builder.global(category))
            },
            {
                name: 'PQ',
                type: builder.template(objectType(
                    builder,
                    sourceCategory
                ))
            }
        ],
        left: builder.pattern(fapp0(
            builder,
            sourceCategory,
            targetCategory,
            profunctorTensorFunctorAt(builder, A, B, X),
            PQ
        )),
        right: builder.template(profunctorTensorAt(
            builder,
            A,
            B,
            X,
            components.first,
            components.second
        )),
        provenance: source(
            'rule @fapp0 _ _ (@Prof_tensor_func $A $B $X) $PQ',
            1266
        )
    };
};

const tensorArrowActionRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const X = builder.capture('X');
    const leftCategory = profunctorCategoryAt(builder, A, B);
    const rightCategory = profunctorCategoryAt(builder, B, X);
    const sourceCategory = productCategoryAt(
        builder,
        leftCategory,
        rightCategory
    );
    const targetCategory = profunctorCategoryAt(builder, A, X);
    const PQ = builder.capture('PQ');
    const nextPQ = builder.capture('PQ_next');
    const rs = builder.capture('rs');
    const sourceComponents = productObjectComponents(
        builder,
        leftCategory,
        rightCategory,
        PQ
    );
    const targetComponents = productObjectComponents(
        builder,
        leftCategory,
        rightCategory,
        nextPQ
    );
    const leftHomClassifier = objectClassifierAt(
        builder,
        homCategoryAt(
            builder,
            leftCategory,
            sourceComponents.first,
            targetComponents.first
        )
    );
    const rightHomClassifier = objectClassifierAt(
        builder,
        homCategoryAt(
            builder,
            rightCategory,
            sourceComponents.second,
            targetComponents.second
        )
    );
    const arrowFamily = constantGroupoidFamily(
        builder,
        leftHomClassifier,
        rightHomClassifier
    );
    const r = sigmaFirstAt(
        builder,
        leftHomClassifier,
        arrowFamily,
        rs
    );
    const s = sigmaSecondAt(
        builder,
        leftHomClassifier,
        arrowFamily,
        rs
    );
    return {
        order: 10,
        id: 'stress.profunctor-tensor.arrow-action',
        groupId: 'stress.profunctor-tensor.arrow-action',
        clauseOrder: 0,
        sourceOwner: functorHomCapped,
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
                name: 'X',
                type: builder.template(builder.global(category))
            },
            {
                name: 'PQ',
                type: builder.template(objectType(
                    builder,
                    sourceCategory
                ))
            },
            {
                name: 'PQ_next',
                type: builder.template(objectType(
                    builder,
                    sourceCategory
                ))
            },
            {
                name: 'rs',
                type: builder.template(homType(
                    builder,
                    sourceCategory,
                    PQ,
                    nextPQ
                ))
            }
        ],
        left: builder.pattern(fapp1(
            builder,
            sourceCategory,
            targetCategory,
            profunctorTensorFunctorAt(builder, A, B, X),
            PQ,
            nextPQ,
            rs
        )),
        right: builder.template(profunctorTensorMapAt(
            builder,
            A,
            B,
            X,
            sourceComponents.first,
            targetComponents.first,
            sourceComponents.second,
            targetComponents.second,
            r,
            s
        )),
        provenance: source(
            'rule @fapp1_fapp0 _ _ ' +
                '(@Prof_tensor_func $A $B $X) $PQ $PQ\' $rs',
            1267
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
    rigidity: 'ordinary' | 'injective'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity: 'opaque' as const
});

const declarations: readonly CoreLfTransferDeclaration[] = [
    {
        order: 0,
        symbol: sigmaFirst,
        type: sigmaFirstType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective'),
        provenance: source(
            'injective symbol sigma_Fst [a P]',
            59
        )
    },
    {
        order: 1,
        symbol: sigmaSecond,
        type: sigmaSecondType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective'),
        provenance: source(
            'injective symbol sigma_Snd [a P]',
            61
        )
    },
    {
        order: 2,
        symbol: productGroupoid,
        type: productGroupoidType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective'),
        provenance: source(
            'injective symbol Product_grpd',
            184
        )
    },
    {
        order: 4,
        symbol: productCategory,
        type: productCategoryType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective'),
        provenance: source(
            'injective symbol Product_cat',
            661
        )
    },
    {
        order: 7,
        symbol: profunctorTensorMap,
        type: profunctorTensorMapType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary'),
        provenance: source(
            'symbol Prof_tensor_map',
            1264
        )
    },
    {
        order: 8,
        symbol: profunctorTensorFunctor,
        type: profunctorTensorFunctorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary'),
        provenance: source(
            'symbol Prof_tensor_func [A B X : Cat]',
            1265
        )
    }
];

const runtimeRules = [
    productGroupoidDecodeRule(),
    productObjectRule(),
    productHomCategoryRule(),
    tensorObjectActionRule(),
    tensorArrowActionRule()
] as const;

export const CORE_LF_SCALE_STRESS_3A2B_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'SCALE-STRESS-3A2B-PROFUNCTOR-TENSOR-ACTION-1',
    moduleId,
    fragmentId: 'scale-stress-3a2b-profunctor-tensor-action',
    authorityPath:
        CORE_LF_SCALE_STRESS_3_PROFUNCTOR_TENSOR_ACTION_ACQUISITION
            .authorityPath,
    sourceSha256:
        CORE_LF_SCALE_STRESS_3_PROFUNCTOR_TENSOR_ACTION_ACQUISITION
            .sourceSha256,
    canonicalExport: {
        exporterVersion:
            CORE_LF_SCALE_STRESS_3_PROFUNCTOR_TENSOR_ACTION_ACQUISITION
                .canonicalExport.exporterVersion,
        sha256:
            CORE_LF_SCALE_STRESS_3_PROFUNCTOR_TENSOR_ACTION_ACQUISITION
                .canonicalExport.sha256
    },
    dependencies: [],
    externalSymbols: [
        category,
        groupoid,
        decodeOwner,
        objectClassifier,
        functorClassifier,
        homClassifier,
        homCategory,
        functorObject,
        functorHomCapped,
        decodedDependentPair,
        profunctorCategory,
        profunctorClassifier,
        profunctorMap,
        profunctorTensor
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules,
    proofRules: []
});

export const CORE_LF_SCALE_STRESS_3A2B_POLICY:
CoreLfTransferPolicyOverlay =
    createCoreLfTransferPolicyOverlay(
        CORE_LF_SCALE_STRESS_3A2B_MODULE,
        {
            revision:
                'SCALE-STRESS-3A2B-PROFUNCTOR-TENSOR-ACTION-POLICY-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_3A2B_MODULE.revision,
            entries: [
                ...declarations.map(declaration => ({
                    order: declaration.order,
                    target: {
                        kind: 'declaration' as const,
                        symbol: declaration.symbol
                    },
                    policy: 'opaque-signature' as const,
                    evidence:
                        'Exact active product/tensor-action signature'
                })),
                ...runtimeRules.map(rule => ({
                    order: rule.order,
                    target: {
                        kind: 'runtime-rule' as const,
                        id: rule.id
                    },
                    policy: 'runtime-rewrite' as const,
                    evidence:
                        'Exact active product/tensor-action computation'
                }))
            ].sort((left, right) => left.order - right.order)
        }
    );

export const CORE_LF_SCALE_STRESS_3A2B_PLAN:
CoreLfMixedPhasePlan = planCoreLfMixedPhases(
    CORE_LF_SCALE_STRESS_3A2B_MODULE,
    CORE_LF_SCALE_STRESS_3A2B_POLICY
);

const prerequisiteLinks = [
    ...CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries,
    ...CORE_LF_SCALE_STRESS_3A1_LINKAGE.entries,
    ...CORE_LF_SCALE_STRESS_3A2A_LINKAGE.entries
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
    CORE_LF_SCALE_STRESS_3A2B_MODULE.externalSymbols.map(
        external => external.symbol
    );

export const CORE_LF_SCALE_STRESS_3A2B_LINKAGE:
CoreLfMixedDeclarationLinkage =
    createCoreLfMixedDeclarationLinkage(
        CORE_LF_SCALE_STRESS_3A2B_PLAN,
        {
            revision:
                'SCALE-STRESS-3A2B-PROFUNCTOR-TENSOR-ACTION-LINKAGE-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_3A2B_MODULE.revision,
            entries: [
                ...externalSymbols.map(externalLink),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `emdash_v3_2_scale_stress_3a2b_` +
                        declaration.symbol.name,
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

export const CORE_LF_SCALE_STRESS_3A2B_BOUNDARY = Object.freeze({
    semanticStatus: 'isolated-representation-only',
    selectedRuntimeRuleIds: Object.freeze(
        runtimeRules.map(rule => rule.id)
    ),
    selectedOpaquePrimitives: Object.freeze(
        declarations.map(declaration => declaration.symbol)
    ),
    dependsOnIntrinsicDefinitions: Object.freeze([
        homClassifier
    ]),
    doesNotProvide: Object.freeze([
        'active-policy-selection',
        'product-functor-or-transfor-closure',
        'profunctor-tensor-associativity-or-units',
        'endpoint-changing-tensor-cells',
        'protected-module-visibility',
        'proof-heavy-extension',
        'WalkingEnd-HIT',
        'browser-api',
        'mechanical-transfer-qualification'
    ])
});

export interface CoreLfScaleStress3a2bCompilation {
    readonly prerequisite: CoreLfScaleStress3a2aCompilation;
    readonly compiled: CoreLfCompiledMixedModule;
}

export function compileCoreLfScaleStress3a2bRepresentation():
CoreLfScaleStress3a2bCompilation {
    validateCoreLfScaleEngineReview();
    const prerequisite =
        compileCoreLfScaleStress3a2aRepresentation();
    const previousRuntime = prerequisite.compiled.latestRuntime;
    if (previousRuntime === undefined) {
        throw new Error(
            'SCALE-STRESS-3A2B requires the source-prior 3A2A runtime'
        );
    }
    const compiled = compileCoreLfMixedPhases(
        CORE_LF_SCALE_STRESS_3A2B_PLAN,
        CORE_LF_SCALE_STRESS_3A2B_LINKAGE,
        {
            initialDeclarations: prerequisite.compiled.declarations,
            runtimeDependencies: [{
                relation: 'earlier-fragment',
                fragment: previousRuntime
            }]
        }
    );
    return Object.freeze({
        prerequisite,
        compiled
    });
}
