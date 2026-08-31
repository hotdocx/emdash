/** Explicit-Core realizations of presentation-morphism matrix equations. */

import {
    algebraFormalMatrixTerm
} from './algebra_formal_finite_module';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialModuleMap
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialChainMapSquare,
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement,
    algebraPolynomialPresentationRelationMap
} from './algebra_polynomial_presentation_morphism';
import {
    serializeAlgebraPolynomialChainMapSquare,
    serializeAlgebraPolynomialPresentationAgreement,
    serializeAlgebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism_reference_operations';
import {
    KernelExpression,
    kernelCall,
    kernelFree,
    provenance
} from './kernel';

export const ALGEBRA_FORMAL_PRESENTATION_MORPHISM_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-presentation-morphism-v1' as const,
    morphismRevision:
        'emdash-formal-presentation-morphism-realization-v1' as const,
    agreementRevision:
        'emdash-formal-presentation-agreement-realization-v1' as const,
    chainSquareRevision:
        'emdash-formal-chain-map-square-realization-v1' as const,
    equationPolicy: 'selected-data-plus-exact-law' as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

export const AFFINE_FORMAL_PRESENTATION_MORPHISM_BINDINGS = Object.freeze({
    bridge_comm_ring_matrix_sub: 'comm_ring_matrix_sub'
});

const p = provenance('derived', 'formal presentation morphism');
const call = (
    name: string,
    values: readonly { plicity: 'explicit' | 'implicit'; value: KernelExpression }[]
): KernelExpression => kernelCall(kernelFree(name, p), values, p);
const nat = (value: number): KernelExpression => {
    let result: KernelExpression = kernelFree('bridge_nat_zero', p);
    for (let index = 0; index < value; index++) {
        result = call('bridge_nat_succ', [{ plicity: 'explicit', value: result }]);
    }
    return result;
};
const tau = (value: KernelExpression): KernelExpression => call('bridge_tau', [
    { plicity: 'explicit', value }
]);
const vectorClassifier = (
    ring: KernelExpression,
    rank: number
): KernelExpression => call('bridge_FiniteFamily', [
    {
        plicity: 'explicit',
        value: call('bridge_comm_ring_carrier', [
            { plicity: 'explicit', value: ring }
        ])
    },
    { plicity: 'explicit', value: nat(rank) }
]);
const matrixClassifier = (
    ring: KernelExpression,
    rows: number,
    columns: number
): KernelExpression => call('bridge_FiniteFamily', [
    { plicity: 'explicit', value: vectorClassifier(ring, rows) },
    { plicity: 'explicit', value: nat(columns) }
]);
const matrixTerm = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    reifier: AffineFormalPolynomialReifier<P, C, I>,
    map: AlgebraPolynomialModuleMap<P, C, I>
): KernelExpression => algebraFormalMatrixTerm(
    reifier,
    map.columns,
    map.target.rank
);
const matrixComp = (
    ring: KernelExpression,
    rows: number,
    middle: number,
    columns: number,
    after: KernelExpression,
    before: KernelExpression
): KernelExpression => call('bridge_comm_ring_matrix_comp', [
    { plicity: 'explicit', value: ring },
    { plicity: 'explicit', value: nat(rows) },
    { plicity: 'explicit', value: nat(middle) },
    { plicity: 'explicit', value: nat(columns) },
    { plicity: 'explicit', value: after },
    { plicity: 'explicit', value: before }
]);
const equation = (
    classifier: KernelExpression,
    left: KernelExpression,
    right: KernelExpression
): KernelExpression => tau(call('bridge_eq', [
    { plicity: 'implicit', value: classifier },
    { plicity: 'explicit', value: left },
    { plicity: 'explicit', value: right }
]));

const assertReifierRing = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    reifier: AffineFormalPolynomialReifier<P, C, I>,
    ring: AlgebraParent,
    path: string
): void => {
    if (!sameAlgebraParent(
        reifier.algebra.quotient.polynomialRing,
        ring
    )) throw new Error(`Formal reifier has a foreign polynomial ring at ${path}`);
};

export interface AlgebraFormalPresentationMorphismRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_PRESENTATION_MORPHISM_PROFILE.morphismRevision;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly selectedOutputData: string;
    readonly formalTargetRelations: KernelExpression;
    readonly formalRelationWitness: KernelExpression;
    readonly formalMap: KernelExpression;
    readonly formalSourceRelations: KernelExpression;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
    readonly claimType: KernelExpression;
}

export function defineAlgebraFormalPresentationMorphismRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialPresentationMorphism<P, C, I>;
}): AlgebraFormalPresentationMorphismRealization<P, C, I> {
    const value = input.selected;
    assertReifierRing(input.reifier, value.source.ambient.ring, 'morphism.source');
    assertReifierRing(input.reifier, value.target.ambient.ring, 'morphism.target');
    const formalTargetRelations = matrixTerm(
        input.reifier,
        algebraPolynomialPresentationRelationMap(value.target)
    );
    const formalRelationWitness = matrixTerm(input.reifier, value.relationWitness);
    const formalMap = matrixTerm(input.reifier, value.map);
    const formalSourceRelations = matrixTerm(
        input.reifier,
        algebraPolynomialPresentationRelationMap(value.source)
    );
    const gQ = value.target.ambient.rank;
    const gP = value.source.ambient.rank;
    const rQ = value.target.relations.generators.length;
    const rP = value.source.relations.generators.length;
    const left = matrixComp(
        input.reifier.formalRing,
        gQ,
        rQ,
        rP,
        formalTargetRelations,
        formalRelationWitness
    );
    const right = matrixComp(
        input.reifier.formalRing,
        gQ,
        gP,
        rP,
        formalMap,
        formalSourceRelations
    );
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_PRESENTATION_MORPHISM_PROFILE.morphismRevision,
        reifier: input.reifier,
        selected: value,
        selectedOutputData: serializeAlgebraPolynomialPresentationMorphism(value),
        formalTargetRelations,
        formalRelationWitness,
        formalMap,
        formalSourceRelations,
        left,
        right,
        claimType: equation(
            matrixClassifier(input.reifier.formalRing, gQ, rP),
            left,
            right
        )
    });
}

export interface AlgebraFormalPresentationAgreementRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_PRESENTATION_MORPHISM_PROFILE.agreementRevision;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly selectedOutputData: string;
    readonly formalTargetRelations: KernelExpression;
    readonly formalAgreementWitness: KernelExpression;
    readonly formalLeftMap: KernelExpression;
    readonly formalRightMap: KernelExpression;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
    readonly claimType: KernelExpression;
}

export function defineAlgebraFormalPresentationAgreementRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
}): AlgebraFormalPresentationAgreementRealization<P, C, I> {
    const value = input.selected;
    assertReifierRing(input.reifier, value.source.ambient.ring, 'agreement.source');
    assertReifierRing(input.reifier, value.target.ambient.ring, 'agreement.target');
    const formalTargetRelations = matrixTerm(
        input.reifier,
        algebraPolynomialPresentationRelationMap(value.target)
    );
    const formalAgreementWitness = matrixTerm(
        input.reifier,
        value.agreementWitness
    );
    const formalLeftMap = matrixTerm(input.reifier, value.left);
    const formalRightMap = matrixTerm(input.reifier, value.right);
    const gQ = value.target.ambient.rank;
    const gP = value.source.ambient.rank;
    const rQ = value.target.relations.generators.length;
    const left = matrixComp(
        input.reifier.formalRing,
        gQ,
        rQ,
        gP,
        formalTargetRelations,
        formalAgreementWitness
    );
    const right = call('bridge_comm_ring_matrix_sub', [
        { plicity: 'explicit', value: input.reifier.formalRing },
        { plicity: 'explicit', value: nat(gQ) },
        { plicity: 'explicit', value: nat(gP) },
        { plicity: 'explicit', value: formalLeftMap },
        { plicity: 'explicit', value: formalRightMap }
    ]);
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_PRESENTATION_MORPHISM_PROFILE.agreementRevision,
        reifier: input.reifier,
        selected: value,
        selectedOutputData: serializeAlgebraPolynomialPresentationAgreement(value),
        formalTargetRelations,
        formalAgreementWitness,
        formalLeftMap,
        formalRightMap,
        left,
        right,
        claimType: equation(
            matrixClassifier(input.reifier.formalRing, gQ, gP),
            left,
            right
        )
    });
}

export interface AlgebraFormalChainMapSquareRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_PRESENTATION_MORPHISM_PROFILE.chainSquareRevision;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialChainMapSquare<P, C, I>;
    readonly selectedOutputData: string;
    readonly formalDifferentialSource: KernelExpression;
    readonly formalDifferentialTarget: KernelExpression;
    readonly formalComponentPrevious: KernelExpression;
    readonly formalComponentNow: KernelExpression;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
    readonly claimType: KernelExpression;
}

export function defineAlgebraFormalChainMapSquareRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialChainMapSquare<P, C, I>;
}): AlgebraFormalChainMapSquareRealization<P, C, I> {
    const value = input.selected;
    assertReifierRing(
        input.reifier,
        value.differentialSource.source.ring,
        'chainSquare'
    );
    const formalDifferentialSource = matrixTerm(
        input.reifier,
        value.differentialSource
    );
    const formalDifferentialTarget = matrixTerm(
        input.reifier,
        value.differentialTarget
    );
    const formalComponentPrevious = matrixTerm(
        input.reifier,
        value.componentPrevious
    );
    const formalComponentNow = matrixTerm(input.reifier, value.componentNow);
    const sourcePrev = value.differentialSource.target.rank;
    const sourceNow = value.differentialSource.source.rank;
    const targetPrev = value.differentialTarget.target.rank;
    const targetNow = value.differentialTarget.source.rank;
    const left = matrixComp(
        input.reifier.formalRing,
        targetPrev,
        targetNow,
        sourceNow,
        formalDifferentialTarget,
        formalComponentNow
    );
    const right = matrixComp(
        input.reifier.formalRing,
        targetPrev,
        sourcePrev,
        sourceNow,
        formalComponentPrevious,
        formalDifferentialSource
    );
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_PRESENTATION_MORPHISM_PROFILE.chainSquareRevision,
        reifier: input.reifier,
        selected: value,
        selectedOutputData: serializeAlgebraPolynomialChainMapSquare(value),
        formalDifferentialSource,
        formalDifferentialTarget,
        formalComponentPrevious,
        formalComponentNow,
        left,
        right,
        claimType: equation(
            matrixClassifier(input.reifier.formalRing, targetPrev, sourceNow),
            left,
            right
        )
    });
}
