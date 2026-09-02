/** Witness-retaining normality algorithms in the polynomial Freyd category. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialModuleGroebnerOptions,
    AlgebraPolynomialModuleVector,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleEquals,
    algebraPolynomialModuleVector
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialModuleMap,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapCompose,
    algebraPolynomialModuleMapIdentity
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialPresentationMorphism,
    AlgebraPolynomialPresentationMorphismAgreement,
    algebraPolynomialModuleMapEquals,
    algebraPolynomialModuleMapSubtract,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialPresentationRelationMap
} from './algebra_polynomial_presentation_morphism';
import {
    algebraPresentedPolynomialModuleEquals,
    algebraPolynomialPresentationMorphismCompose,
    algebraPolynomialPresentationMorphismCongruence,
    algebraPolynomialPresentationMorphismZero
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydKernel,
    algebraPolynomialFreydKernel
} from './algebra_polynomial_freyd_kernel';
import {
    AlgebraPolynomialFreydCokernel,
    algebraPolynomialFreydCokernel
} from './algebra_polynomial_freyd_cokernel';
import {
    AlgebraPolynomialWeakPullbackFactorization,
    algebraPolynomialWeakPullbackFactor
} from './algebra_polynomial_weak_pullback';
import {
    AlgebraPolynomialWeakKernelFactorOptions
} from './algebra_polynomial_weak_kernel';

export const ALGEBRA_POLYNOMIAL_FREYD_NORMALITY_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-normality-v1' as const,
    monomorphismWitness: 'kernel-embedding-agrees-with-zero' as const,
    epimorphismWitness: 'cokernel-projection-agrees-with-zero' as const,
    liftConstruction: 'posur-construction-3.14' as const,
    coliftConstruction: 'posur-construction-3.15' as const,
    retainsAgreements: true as const,
    usesFieldInverse: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydNormalityErrorCode =
    | 'INVALID_ROW_SPLIT'
    | 'NOT_MONOMORPHISM'
    | 'NOT_EPIMORPHISM'
    | 'INVALID_NORMAL_TEST'
    | 'NON_ANNIHILATED_NORMAL_TEST'
    | 'INVALID_NORMAL_FACTOR'
    | 'INVALID_COMPETING_NORMAL_FACTOR';

export class AlgebraPolynomialFreydNormalityError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydNormalityErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydNormalityError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydNormalityErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraPolynomialFreydNormalityError(code, path, message);
};

export interface AlgebraPolynomialModuleMapRowSplit<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-module-map-row-split';
    readonly map: AlgebraPolynomialModuleMap<P, C, I>;
    readonly topRows: number;
    readonly bottomRows: number;
    readonly top: AlgebraPolynomialModuleMap<P, C, I>;
    readonly bottom: AlgebraPolynomialModuleMap<P, C, I>;
    readonly reconstructs: true;
}

/** Split every column into top and bottom row blocks. */
export function algebraPolynomialModuleMapSplitRows<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    map: AlgebraPolynomialModuleMap<P, C, I>,
    topRows: number
): AlgebraPolynomialModuleMapRowSplit<P, C, I> {
    if (
        !Number.isSafeInteger(topRows) ||
        topRows < 0 ||
        topRows > map.target.rank
    ) {
        return fail(
            'INVALID_ROW_SPLIT',
            'polynomialModuleMapSplitRows.topRows',
            'Row split must lie within the target rank'
        );
    }
    const bottomRows = map.target.rank - topRows;
    const topTarget = algebraPolynomialFreeModule(map.target.ring, topRows);
    const bottomTarget = algebraPolynomialFreeModule(
        map.target.ring,
        bottomRows
    );
    const topColumns: AlgebraPolynomialModuleVector<P, C, I>[] = [];
    const bottomColumns: AlgebraPolynomialModuleVector<P, C, I>[] = [];
    map.columns.forEach(column => {
        topColumns.push(algebraPolynomialModuleVector(
            topTarget,
            column.components.slice(0, topRows)
        ));
        bottomColumns.push(algebraPolynomialModuleVector(
            bottomTarget,
            column.components.slice(topRows)
        ));
    });
    const top = algebraPolynomialModuleMap(map.source, topTarget, topColumns);
    const bottom = algebraPolynomialModuleMap(
        map.source,
        bottomTarget,
        bottomColumns
    );
    const reconstructs = map.columns.every((column, index) =>
        algebraPolynomialModuleEquals(
            column,
            algebraPolynomialModuleVector(map.target, [
                ...top.columns[index].components,
                ...bottom.columns[index].components
            ])
        )
    );
    if (!reconstructs) {
        return fail(
            'INVALID_ROW_SPLIT',
            'polynomialModuleMapSplitRows.reconstruction',
            'Row blocks failed to reconstruct their source columns'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-module-map-row-split',
        map,
        topRows,
        bottomRows,
        top,
        bottom,
        reconstructs: true
    });
}

export interface AlgebraPolynomialFreydMonomorphismWitness<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-monomorphism-witness';
    readonly morphism: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly kernel: AlgebraPolynomialFreydKernel<P, C, I>;
    readonly zeroEmbedding: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly kernelZeroAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly kernelZeroWitness: AlgebraPolynomialModuleMap<P, C, I>;
    readonly monic: true;
}

/** Classify monicity by the selected kernel embedding agreeing with zero. */
export function algebraPolynomialFreydMonomorphismWitness<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    morphism: AlgebraPolynomialPresentationMorphism<P, C, I>,
    options: AlgebraPolynomialModuleGroebnerOptions = {}
): AlgebraPolynomialFreydMonomorphismWitness<P, C, I> {
    const kernel = algebraPolynomialFreydKernel(morphism, options);
    const zeroEmbedding = algebraPolynomialPresentationMorphismZero(
        kernel.object,
        morphism.source
    );
    const kernelZeroAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            kernel.embedding,
            zeroEmbedding
        );
    if (!kernelZeroAgreement.agrees) {
        return fail(
            'NOT_MONOMORPHISM',
            'freydMonomorphism.kernelEmbedding',
            'Selected kernel embedding does not agree with zero'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-monomorphism-witness',
        morphism,
        kernel,
        zeroEmbedding,
        kernelZeroAgreement,
        kernelZeroWitness: kernelZeroAgreement.agreementWitness,
        monic: true
    });
}

export interface AlgebraPolynomialFreydLiftAlongMonomorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-lift-along-monomorphism';
    readonly monomorphism: AlgebraPolynomialFreydMonomorphismWitness<P, C, I>;
    readonly test: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly cokernel: AlgebraPolynomialFreydCokernel<P, C, I>;
    readonly testCokernelComposite:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testCokernelZero:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testCokernelZeroAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly agreementBlocks: AlgebraPolynomialModuleMapRowSplit<P, C, I>;
    readonly targetRelationComponent: AlgebraPolynomialModuleMap<P, C, I>;
    readonly liftMap: AlgebraPolynomialModuleMap<P, C, I>;
    readonly liftAfterSourceRelations: AlgebraPolynomialModuleMap<P, C, I>;
    readonly targetComponentAfterSourceRelations:
        AlgebraPolynomialModuleMap<P, C, I>;
    readonly weakPullbackRightComponent:
        AlgebraPolynomialModuleMap<P, C, I>;
    readonly relationFactorization:
        AlgebraPolynomialWeakPullbackFactorization<P, C, I>;
    readonly expectedRelationWitness: AlgebraPolynomialModuleMap<P, C, I>;
    readonly expectedRelationWitnessEquation: true;
    readonly lift: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly reconstruction: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly reconstructionAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly reconstructs: true;
}

/** Posur Construction 3.14 in the active column convention. */
export function algebraPolynomialFreydLiftAlongMonomorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    monomorphism: AlgebraPolynomialFreydMonomorphismWitness<P, C, I>,
    test: AlgebraPolynomialPresentationMorphism<P, C, I>,
    options: AlgebraPolynomialWeakKernelFactorOptions = {}
): AlgebraPolynomialFreydLiftAlongMonomorphism<P, C, I> {
    const morphism = monomorphism.morphism;
    if (!algebraPresentedPolynomialModuleEquals(test.target, morphism.target)) {
        return fail(
            'INVALID_NORMAL_TEST',
            'freydLiftAlongMonomorphism.test',
            'Normal-monomorphism test must target the monomorphism codomain'
        );
    }
    const cokernel = algebraPolynomialFreydCokernel(morphism);
    const testCokernelComposite =
        algebraPolynomialPresentationMorphismCompose(
            cokernel.projection,
            test
        );
    const testCokernelZero = algebraPolynomialPresentationMorphismZero(
        test.source,
        cokernel.object
    );
    const testCokernelZeroAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            testCokernelComposite,
            testCokernelZero
        );
    if (!testCokernelZeroAgreement.agrees) {
        return fail(
            'NON_ANNIHILATED_NORMAL_TEST',
            'freydLiftAlongMonomorphism.test',
            'Test does not vanish after the selected cokernel projection'
        );
    }
    const targetRelationRows = morphism.target.relations.generators.length;
    const agreementBlocks = algebraPolynomialModuleMapSplitRows(
        testCokernelZeroAgreement.agreementWitness,
        targetRelationRows
    );
    if (
        agreementBlocks.bottom.target.rank !== morphism.source.ambient.rank ||
        !sameAlgebraParent(
            agreementBlocks.bottom.source,
            test.source.ambient
        )
    ) {
        return fail(
            'INVALID_NORMAL_FACTOR',
            'freydLiftAlongMonomorphism.agreementBlocks',
            'Cokernel-zero witness does not have the expected lower block'
        );
    }
    const targetRelationComponent = agreementBlocks.top;
    const liftMap = agreementBlocks.bottom;
    const sourceRelations = algebraPolynomialPresentationRelationMap(
        test.source
    );
    const liftAfterSourceRelations = algebraPolynomialModuleMapCompose(
        liftMap,
        sourceRelations
    );
    const targetComponentAfterSourceRelations =
        algebraPolynomialModuleMapCompose(
            targetRelationComponent,
            sourceRelations
        );
    const weakPullbackRightComponent = algebraPolynomialModuleMapSubtract(
        test.relationWitness,
        targetComponentAfterSourceRelations
    );
    const relationFactorization = algebraPolynomialWeakPullbackFactor(
        monomorphism.kernel.firstWeakPullback,
        liftAfterSourceRelations,
        weakPullbackRightComponent,
        options
    );
    const expectedRelationWitness = algebraPolynomialModuleMapCompose(
        monomorphism.kernelZeroWitness,
        relationFactorization.lift
    );
    const expectedRelationTarget = algebraPolynomialModuleMapCompose(
        algebraPolynomialPresentationRelationMap(morphism.source),
        expectedRelationWitness
    );
    if (!algebraPolynomialModuleMapEquals(
        expectedRelationTarget,
        liftAfterSourceRelations
    )) {
        return fail(
            'INVALID_NORMAL_FACTOR',
            'freydLiftAlongMonomorphism.relationWitness',
            'Constructed monic lift relation witness does not reconstruct'
        );
    }
    const lift = algebraPolynomialPresentationMorphism({
        source: test.source,
        target: morphism.source,
        map: liftMap
    });
    if (!lift.preservesRelations) {
        return fail(
            'INVALID_NORMAL_FACTOR',
            'freydLiftAlongMonomorphism.lift',
            'Constructed monic lift is not relation-preserving'
        );
    }
    const reconstruction = algebraPolynomialPresentationMorphismCompose(
        morphism,
        lift
    );
    const reconstructionAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            reconstruction,
            test
        );
    if (!reconstructionAgreement.agrees) {
        return fail(
            'INVALID_NORMAL_FACTOR',
            'freydLiftAlongMonomorphism.reconstruction',
            'Constructed monic lift does not reconstruct the test in the quotient'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-lift-along-monomorphism',
        monomorphism,
        test,
        cokernel,
        testCokernelComposite,
        testCokernelZero,
        testCokernelZeroAgreement,
        agreementBlocks,
        targetRelationComponent,
        liftMap,
        liftAfterSourceRelations,
        targetComponentAfterSourceRelations,
        weakPullbackRightComponent,
        relationFactorization,
        expectedRelationWitness,
        expectedRelationWitnessEquation: true,
        lift,
        reconstruction,
        reconstructionAgreement,
        reconstructs: true
    });
}

export interface AlgebraPolynomialFreydNormalMonoUniqueness<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-normal-mono-uniqueness';
    readonly selected: AlgebraPolynomialFreydLiftAlongMonomorphism<P, C, I>;
    readonly candidate: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly candidateReconstruction:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly candidateReconstructionAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly uniquenessAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly uniqueInQuotient: true;
}

export function algebraPolynomialFreydLiftAlongMonomorphismUnique<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    selected: AlgebraPolynomialFreydLiftAlongMonomorphism<P, C, I>,
    candidate: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialFreydNormalMonoUniqueness<P, C, I> {
    if (
        !algebraPresentedPolynomialModuleEquals(
            candidate.source,
            selected.test.source
        ) ||
        !algebraPresentedPolynomialModuleEquals(
            candidate.target,
            selected.monomorphism.morphism.source
        )
    ) {
        return fail(
            'INVALID_COMPETING_NORMAL_FACTOR',
            'freydLiftAlongMonomorphismUnique.candidate',
            'Competing monic lift has incorrect endpoints'
        );
    }
    const candidateReconstruction =
        algebraPolynomialPresentationMorphismCompose(
            selected.monomorphism.morphism,
            candidate
        );
    const candidateReconstructionAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            candidateReconstruction,
            selected.test
        );
    if (!candidateReconstructionAgreement.agrees) {
        return fail(
            'INVALID_COMPETING_NORMAL_FACTOR',
            'freydLiftAlongMonomorphismUnique.reconstruction',
            'Competing monic lift does not reconstruct the test'
        );
    }
    const uniquenessAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            candidate,
            selected.lift
        );
    if (!uniquenessAgreement.agrees) {
        return fail(
            'INVALID_NORMAL_FACTOR',
            'freydLiftAlongMonomorphismUnique.uniqueness',
            'Monomorphism failed quotient cancellation'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-normal-mono-uniqueness',
        selected,
        candidate,
        candidateReconstruction,
        candidateReconstructionAgreement,
        uniquenessAgreement,
        uniqueInQuotient: true
    });
}

export interface AlgebraPolynomialFreydEpimorphismWitness<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-epimorphism-witness';
    readonly morphism: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly cokernel: AlgebraPolynomialFreydCokernel<P, C, I>;
    readonly zeroProjection: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly cokernelZeroAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly identityBlocks: AlgebraPolynomialModuleMapRowSplit<P, C, I>;
    readonly targetRelationComponent: AlgebraPolynomialModuleMap<P, C, I>;
    readonly sourceGeneratorComponent: AlgebraPolynomialModuleMap<P, C, I>;
    readonly epic: true;
}

/** Classify epicity by the selected cokernel projection agreeing with zero. */
export function algebraPolynomialFreydEpimorphismWitness<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(morphism: AlgebraPolynomialPresentationMorphism<P, C, I>):
    AlgebraPolynomialFreydEpimorphismWitness<P, C, I> {
    const cokernel = algebraPolynomialFreydCokernel(morphism);
    const zeroProjection = algebraPolynomialPresentationMorphismZero(
        morphism.target,
        cokernel.object
    );
    const cokernelZeroAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            cokernel.projection,
            zeroProjection
        );
    if (!cokernelZeroAgreement.agrees) {
        return fail(
            'NOT_EPIMORPHISM',
            'freydEpimorphism.cokernelProjection',
            'Selected cokernel projection does not agree with zero'
        );
    }
    const identityBlocks = algebraPolynomialModuleMapSplitRows(
        cokernelZeroAgreement.agreementWitness,
        morphism.target.relations.generators.length
    );
    if (identityBlocks.bottom.target.rank !== morphism.source.ambient.rank) {
        return fail(
            'INVALID_NORMAL_FACTOR',
            'freydEpimorphism.identityBlocks',
            'Cokernel-zero witness does not have the expected lower block'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-epimorphism-witness',
        morphism,
        cokernel,
        zeroProjection,
        cokernelZeroAgreement,
        identityBlocks,
        targetRelationComponent: identityBlocks.top,
        sourceGeneratorComponent: identityBlocks.bottom,
        epic: true
    });
}

export interface AlgebraPolynomialFreydColiftAlongEpimorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-colift-along-epimorphism';
    readonly epimorphism: AlgebraPolynomialFreydEpimorphismWitness<P, C, I>;
    readonly test: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly kernel: AlgebraPolynomialFreydKernel<P, C, I>;
    readonly testKernelComposite:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testKernelZero: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testKernelZeroAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly sourceComponentAfterTargetRelations:
        AlgebraPolynomialModuleMap<P, C, I>;
    readonly targetComponentAfterTargetRelations:
        AlgebraPolynomialModuleMap<P, C, I>;
    readonly weakPullbackRightComponent:
        AlgebraPolynomialModuleMap<P, C, I>;
    readonly relationFactorization:
        AlgebraPolynomialWeakPullbackFactorization<P, C, I>;
    readonly coliftMap: AlgebraPolynomialModuleMap<P, C, I>;
    readonly expectedRelationWitness: AlgebraPolynomialModuleMap<P, C, I>;
    readonly expectedRelationWitnessEquation: true;
    readonly colift: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly reconstruction: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly reconstructionAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly reconstructs: true;
}

/** Posur Construction 3.15 in the active column convention. */
export function algebraPolynomialFreydColiftAlongEpimorphism<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    epimorphism: AlgebraPolynomialFreydEpimorphismWitness<P, C, I>,
    test: AlgebraPolynomialPresentationMorphism<P, C, I>,
    options: AlgebraPolynomialWeakKernelFactorOptions = {}
): AlgebraPolynomialFreydColiftAlongEpimorphism<P, C, I> {
    const morphism = epimorphism.morphism;
    if (!algebraPresentedPolynomialModuleEquals(test.source, morphism.source)) {
        return fail(
            'INVALID_NORMAL_TEST',
            'freydColiftAlongEpimorphism.test',
            'Normal-epimorphism test must start at the epimorphism domain'
        );
    }
    const kernel = algebraPolynomialFreydKernel(morphism);
    const testKernelComposite =
        algebraPolynomialPresentationMorphismCompose(test, kernel.embedding);
    const testKernelZero = algebraPolynomialPresentationMorphismZero(
        kernel.object,
        test.target
    );
    const testKernelZeroAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            testKernelComposite,
            testKernelZero
        );
    if (!testKernelZeroAgreement.agrees) {
        return fail(
            'NON_ANNIHILATED_NORMAL_TEST',
            'freydColiftAlongEpimorphism.test',
            'Test does not annihilate the selected kernel embedding'
        );
    }
    const targetRelations = algebraPolynomialPresentationRelationMap(
        morphism.target
    );
    const sourceComponentAfterTargetRelations =
        algebraPolynomialModuleMapCompose(
            epimorphism.sourceGeneratorComponent,
            targetRelations
        );
    const targetComponentAfterTargetRelations =
        algebraPolynomialModuleMapCompose(
            epimorphism.targetRelationComponent,
            targetRelations
        );
    const weakPullbackRightComponent = algebraPolynomialModuleMapSubtract(
        algebraPolynomialModuleMapIdentity(targetRelations.source),
        targetComponentAfterTargetRelations
    );
    const relationFactorization = algebraPolynomialWeakPullbackFactor(
        kernel.firstWeakPullback,
        sourceComponentAfterTargetRelations,
        weakPullbackRightComponent,
        options
    );
    const coliftMap = algebraPolynomialModuleMapCompose(
        test.map,
        epimorphism.sourceGeneratorComponent
    );
    const expectedRelationWitness = algebraPolynomialModuleMapCompose(
        testKernelZeroAgreement.agreementWitness,
        relationFactorization.lift
    );
    const expectedRelationTarget = algebraPolynomialModuleMapCompose(
        algebraPolynomialPresentationRelationMap(test.target),
        expectedRelationWitness
    );
    const expectedRelationSource = algebraPolynomialModuleMapCompose(
        coliftMap,
        targetRelations
    );
    if (!algebraPolynomialModuleMapEquals(
        expectedRelationTarget,
        expectedRelationSource
    )) {
        return fail(
            'INVALID_NORMAL_FACTOR',
            'freydColiftAlongEpimorphism.relationWitness',
            'Constructed epic colift relation witness does not reconstruct'
        );
    }
    const colift = algebraPolynomialPresentationMorphism({
        source: morphism.target,
        target: test.target,
        map: coliftMap
    });
    if (!colift.preservesRelations) {
        return fail(
            'INVALID_NORMAL_FACTOR',
            'freydColiftAlongEpimorphism.colift',
            'Constructed epic colift is not relation-preserving'
        );
    }
    const reconstruction = algebraPolynomialPresentationMorphismCompose(
        colift,
        morphism
    );
    const reconstructionAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            reconstruction,
            test
        );
    if (!reconstructionAgreement.agrees) {
        return fail(
            'INVALID_NORMAL_FACTOR',
            'freydColiftAlongEpimorphism.reconstruction',
            'Constructed epic colift does not reconstruct the test in the quotient'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-colift-along-epimorphism',
        epimorphism,
        test,
        kernel,
        testKernelComposite,
        testKernelZero,
        testKernelZeroAgreement,
        sourceComponentAfterTargetRelations,
        targetComponentAfterTargetRelations,
        weakPullbackRightComponent,
        relationFactorization,
        coliftMap,
        expectedRelationWitness,
        expectedRelationWitnessEquation: true,
        colift,
        reconstruction,
        reconstructionAgreement,
        reconstructs: true
    });
}

export interface AlgebraPolynomialFreydNormalEpiUniqueness<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-normal-epi-uniqueness';
    readonly selected: AlgebraPolynomialFreydColiftAlongEpimorphism<P, C, I>;
    readonly candidate: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly candidateReconstruction:
        AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly candidateReconstructionAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly uniquenessAgreement:
        AlgebraPolynomialPresentationMorphismAgreement<P, C, I>;
    readonly uniqueInQuotient: true;
}

export function algebraPolynomialFreydColiftAlongEpimorphismUnique<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    selected: AlgebraPolynomialFreydColiftAlongEpimorphism<P, C, I>,
    candidate: AlgebraPolynomialPresentationMorphism<P, C, I>
): AlgebraPolynomialFreydNormalEpiUniqueness<P, C, I> {
    if (
        !algebraPresentedPolynomialModuleEquals(
            candidate.source,
            selected.epimorphism.morphism.target
        ) ||
        !algebraPresentedPolynomialModuleEquals(
            candidate.target,
            selected.test.target
        )
    ) {
        return fail(
            'INVALID_COMPETING_NORMAL_FACTOR',
            'freydColiftAlongEpimorphismUnique.candidate',
            'Competing epic colift has incorrect endpoints'
        );
    }
    const candidateReconstruction =
        algebraPolynomialPresentationMorphismCompose(
            candidate,
            selected.epimorphism.morphism
        );
    const candidateReconstructionAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            candidateReconstruction,
            selected.test
        );
    if (!candidateReconstructionAgreement.agrees) {
        return fail(
            'INVALID_COMPETING_NORMAL_FACTOR',
            'freydColiftAlongEpimorphismUnique.reconstruction',
            'Competing epic colift does not reconstruct the test'
        );
    }
    const uniquenessAgreement =
        algebraPolynomialPresentationMorphismCongruence(
            candidate,
            selected.colift
        );
    if (!uniquenessAgreement.agrees) {
        return fail(
            'INVALID_NORMAL_FACTOR',
            'freydColiftAlongEpimorphismUnique.uniqueness',
            'Epimorphism failed quotient cancellation'
        );
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-normal-epi-uniqueness',
        selected,
        candidate,
        candidateReconstruction,
        candidateReconstructionAgreement,
        uniquenessAgreement,
        uniqueInQuotient: true
    });
}
