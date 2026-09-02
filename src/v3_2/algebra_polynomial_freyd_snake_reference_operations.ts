/** Native operations and canonical data for the polynomial Freyd snake map. */

import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraPolynomialRing,
    algebraPolynomialText
} from './algebra_polynomial';
import {
    AlgebraPresentedPolynomialModule
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism';
import {
    AlgebraPolynomialFreydAbelianCategoryModel
} from './algebra_polynomial_freyd_abelian_category';
import {
    AlgebraPolynomialFreydFiberProduct,
    AlgebraPolynomialFreydFiberProductFactor,
    algebraPolynomialFreydFiberProduct,
    algebraPolynomialFreydFiberProductFactor
} from './algebra_polynomial_freyd_fiber_product';
import {
    AlgebraPolynomialFreydPushout,
    AlgebraPolynomialFreydPushoutCofactor,
    algebraPolynomialFreydPushout,
    algebraPolynomialFreydPushoutCofactor
} from './algebra_polynomial_freyd_pushout';
import {
    AlgebraPolynomialFreydFiberProductEpicProjection,
    AlgebraPolynomialFreydPushoutMonicInjection
} from './algebra_polynomial_freyd_stability';
import {
    AlgebraPolynomialFreydSnakeConnecting,
    AlgebraPolynomialFreydSnakeTriple,
    algebraPolynomialFreydSnakeConnecting,
    algebraPolynomialFreydSnakeTriple
} from './algebra_polynomial_freyd_snake';
import {
    AlgebraPolynomialFreydShortExactTriple,
    algebraPolynomialFreydShortExactTriple
} from './algebra_polynomial_freyd_short_exact';
import {
    serializeAlgebraPolynomialFreydCokernel,
    serializeAlgebraPolynomialFreydCokernelColift,
    serializeAlgebraPolynomialFreydKernel,
    serializeAlgebraPolynomialFreydKernelLift
} from './algebra_formal_freyd_preabelian';
import {
    serializeAlgebraPolynomialFreydEpimorphismWitness,
    serializeAlgebraPolynomialFreydMonomorphismWitness,
    serializeAlgebraPolynomialFreydNormalEpiColift,
    serializeAlgebraPolynomialFreydNormalMonoLift
} from './algebra_formal_freyd_abelian';
import {
    serializeAlgebraPolynomialFreydExactnessAt,
    serializeAlgebraPolynomialFreydHomologyAt
} from './algebra_polynomial_freyd_homology_reference_operations';
import {
    serializeAlgebraPolynomialPresentationAgreement,
    serializeAlgebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism_reference_operations';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_POLYNOMIAL_FREYD_SNAKE_REFERENCE_PROFILE = Object.freeze({
    revision: 'emdash-polynomial-freyd-snake-reference-v1' as const,
    algorithmRevision: 'typescript-polynomial-freyd-snake-v1' as const,
    wholeResults: true as const,
    assumesSplitEpimorphisms: false as const,
    performsIo: false as const
});

export interface AlgebraPolynomialFreydSnakeTripleInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly delta: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly beta: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly lambda: AlgebraPolynomialPresentationMorphism<P, C, I>;
}

export interface AlgebraPolynomialFreydMorphismPairInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly left: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly right: AlgebraPolynomialPresentationMorphism<P, C, I>;
}

export interface AlgebraPolynomialFreydFiberProductLiftInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly fiberProduct: AlgebraPolynomialFreydFiberProduct<P, C, I>;
    readonly testLeft: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testRight: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly maximumReductionSteps?: number;
}

export interface AlgebraPolynomialFreydPushoutColiftInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly pushout: AlgebraPolynomialFreydPushout<P, C, I>;
    readonly testLeft: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly testRight: AlgebraPolynomialPresentationMorphism<P, C, I>;
}

export interface AlgebraPolynomialFreydShortExactTripleInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly incoming: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly outgoing: AlgebraPolynomialPresentationMorphism<P, C, I>;
    readonly maximumReductionSteps?: number;
}

export interface AlgebraPolynomialFreydSnakeReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly morphismPairSchema:
        AlgebraRuntimeSchema<AlgebraPolynomialFreydMorphismPairInput<P, C, I>>;
    readonly fiberProduct: AlgebraOperation<
        AlgebraPolynomialFreydMorphismPairInput<P, C, I>,
        AlgebraPolynomialFreydFiberProduct<P, C, I>
    >;
    readonly fiberProductProjectionLeft: AlgebraOperation<
        AlgebraPolynomialFreydFiberProduct<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly fiberProductProjectionRight: AlgebraOperation<
        AlgebraPolynomialFreydFiberProduct<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly fiberProductLiftInputSchema:
        AlgebraRuntimeSchema<AlgebraPolynomialFreydFiberProductLiftInput<P, C, I>>;
    readonly fiberProductLift: AlgebraOperation<
        AlgebraPolynomialFreydFiberProductLiftInput<P, C, I>,
        AlgebraPolynomialFreydFiberProductFactor<P, C, I>
    >;
    readonly pushout: AlgebraOperation<
        AlgebraPolynomialFreydMorphismPairInput<P, C, I>,
        AlgebraPolynomialFreydPushout<P, C, I>
    >;
    readonly pushoutInjectionLeft: AlgebraOperation<
        AlgebraPolynomialFreydPushout<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly pushoutInjectionRight: AlgebraOperation<
        AlgebraPolynomialFreydPushout<P, C, I>,
        AlgebraPolynomialPresentationMorphism<P, C, I>
    >;
    readonly pushoutColiftInputSchema:
        AlgebraRuntimeSchema<AlgebraPolynomialFreydPushoutColiftInput<P, C, I>>;
    readonly pushoutColift: AlgebraOperation<
        AlgebraPolynomialFreydPushoutColiftInput<P, C, I>,
        AlgebraPolynomialFreydPushoutCofactor<P, C, I>
    >;
    readonly shortExactTripleInputSchema:
        AlgebraRuntimeSchema<AlgebraPolynomialFreydShortExactTripleInput<P, C, I>>;
    readonly shortExactTriple: AlgebraOperation<
        AlgebraPolynomialFreydShortExactTripleInput<P, C, I>,
        AlgebraPolynomialFreydShortExactTriple<P, C, I>
    >;
    readonly tripleInputSchema:
        AlgebraRuntimeSchema<AlgebraPolynomialFreydSnakeTripleInput<P, C, I>>;
    readonly triple: AlgebraOperation<
        AlgebraPolynomialFreydSnakeTripleInput<P, C, I>,
        AlgebraPolynomialFreydSnakeTriple<P, C, I>
    >;
    readonly connecting: AlgebraOperation<
        AlgebraPolynomialFreydSnakeTriple<P, C, I>,
        AlgebraPolynomialFreydSnakeConnecting<P, C, I>
    >;
    readonly implementations: readonly AlgebraReferenceImplementation[];
}

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const presentationData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPresentedPolynomialModule<P, C, I>) => Object.freeze({
    ambientRank: value.ambient.rank,
    relations: value.relations.generators.map(relation =>
        relation.components.map(algebraPolynomialText)
    )
});

const biproductData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydFiberProduct<P, C, I>['biproduct']) =>
    Object.freeze({
        kind: value.kind,
        left: presentationData(value.left),
        right: presentationData(value.right),
        object: presentationData(value.object),
        injectionLeft:
            serializeAlgebraPolynomialPresentationMorphism(value.injectionLeft),
        injectionRight:
            serializeAlgebraPolynomialPresentationMorphism(value.injectionRight),
        projectionLeft:
            serializeAlgebraPolynomialPresentationMorphism(value.projectionLeft),
        projectionRight:
            serializeAlgebraPolynomialPresentationMorphism(value.projectionRight)
    });

const fiberProductData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydFiberProduct<P, C, I>) => Object.freeze({
    kind: value.kind,
    left: serializeAlgebraPolynomialPresentationMorphism(value.left),
    right: serializeAlgebraPolynomialPresentationMorphism(value.right),
    biproduct: biproductData(value.biproduct),
    leftFromBiproduct:
        serializeAlgebraPolynomialPresentationMorphism(value.leftFromBiproduct),
    negatedRightFromBiproduct:
        serializeAlgebraPolynomialPresentationMorphism(
            value.negatedRightFromBiproduct
        ),
    difference:
        serializeAlgebraPolynomialPresentationMorphism(value.difference),
    kernel: serializeAlgebraPolynomialFreydKernel(value.kernel),
    object: presentationData(value.object),
    combinedMorphism:
        serializeAlgebraPolynomialPresentationMorphism(value.combinedMorphism),
    projectionLeft:
        serializeAlgebraPolynomialPresentationMorphism(value.projectionLeft),
    projectionRight:
        serializeAlgebraPolynomialPresentationMorphism(value.projectionRight),
    compatibilityLeft:
        serializeAlgebraPolynomialPresentationMorphism(value.compatibilityLeft),
    compatibilityRight:
        serializeAlgebraPolynomialPresentationMorphism(value.compatibilityRight),
    compatibilityAgreement:
        serializeAlgebraPolynomialPresentationAgreement(
            value.compatibilityAgreement
        ),
    compatible: value.compatible,
    claimsContractibleFactors: value.claimsContractibleFactors
});

const pushoutData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydPushout<P, C, I>) => Object.freeze({
    kind: value.kind,
    left: serializeAlgebraPolynomialPresentationMorphism(value.left),
    right: serializeAlgebraPolynomialPresentationMorphism(value.right),
    biproduct: biproductData(value.biproduct),
    leftIntoBiproduct:
        serializeAlgebraPolynomialPresentationMorphism(value.leftIntoBiproduct),
    negatedRightIntoBiproduct:
        serializeAlgebraPolynomialPresentationMorphism(
            value.negatedRightIntoBiproduct
        ),
    difference:
        serializeAlgebraPolynomialPresentationMorphism(value.difference),
    cokernel: serializeAlgebraPolynomialFreydCokernel(value.cokernel),
    object: presentationData(value.object),
    combinedMorphism:
        serializeAlgebraPolynomialPresentationMorphism(value.combinedMorphism),
    injectionLeft:
        serializeAlgebraPolynomialPresentationMorphism(value.injectionLeft),
    injectionRight:
        serializeAlgebraPolynomialPresentationMorphism(value.injectionRight),
    compatibilityLeft:
        serializeAlgebraPolynomialPresentationMorphism(value.compatibilityLeft),
    compatibilityRight:
        serializeAlgebraPolynomialPresentationMorphism(value.compatibilityRight),
    compatibilityAgreement:
        serializeAlgebraPolynomialPresentationAgreement(
            value.compatibilityAgreement
        ),
    compatible: value.compatible,
    claimsContractibleCofactors: value.claimsContractibleCofactors
});

const fiberProductFactorData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydFiberProductFactor<P, C, I>) => Object.freeze({
    kind: value.kind,
    fiberProduct: fiberProductData(value.fiberProduct),
    testLeft:
        serializeAlgebraPolynomialPresentationMorphism(value.testLeft),
    testRight:
        serializeAlgebraPolynomialPresentationMorphism(value.testRight),
    testCompatibilityLeft:
        serializeAlgebraPolynomialPresentationMorphism(
            value.testCompatibilityLeft
        ),
    testCompatibilityRight:
        serializeAlgebraPolynomialPresentationMorphism(
            value.testCompatibilityRight
        ),
    testCompatibilityAgreement:
        serializeAlgebraPolynomialPresentationAgreement(
            value.testCompatibilityAgreement
        ),
    pairedTest:
        serializeAlgebraPolynomialPresentationMorphism(value.pairedTest),
    kernelLift: serializeAlgebraPolynomialFreydKernelLift(value.kernelLift),
    lift: serializeAlgebraPolynomialPresentationMorphism(value.lift),
    reconstructionCombined:
        serializeAlgebraPolynomialPresentationMorphism(
            value.reconstructionCombined
        ),
    reconstructionCombinedAgreement:
        serializeAlgebraPolynomialPresentationAgreement(
            value.reconstructionCombinedAgreement
        ),
    reconstructionLeft:
        serializeAlgebraPolynomialPresentationMorphism(value.reconstructionLeft),
    reconstructionRight:
        serializeAlgebraPolynomialPresentationMorphism(value.reconstructionRight),
    reconstructionLeftAgreement:
        serializeAlgebraPolynomialPresentationAgreement(
            value.reconstructionLeftAgreement
        ),
    reconstructionRightAgreement:
        serializeAlgebraPolynomialPresentationAgreement(
            value.reconstructionRightAgreement
        ),
    reconstructs: value.reconstructs,
    claimsUniqueFactor: value.claimsUniqueFactor
});

const pushoutCofactorData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydPushoutCofactor<P, C, I>) => Object.freeze({
    kind: value.kind,
    pushout: pushoutData(value.pushout),
    testLeft:
        serializeAlgebraPolynomialPresentationMorphism(value.testLeft),
    testRight:
        serializeAlgebraPolynomialPresentationMorphism(value.testRight),
    testCompatibilityLeft:
        serializeAlgebraPolynomialPresentationMorphism(
            value.testCompatibilityLeft
        ),
    testCompatibilityRight:
        serializeAlgebraPolynomialPresentationMorphism(
            value.testCompatibilityRight
        ),
    testCompatibilityAgreement:
        serializeAlgebraPolynomialPresentationAgreement(
            value.testCompatibilityAgreement
        ),
    copairTest:
        serializeAlgebraPolynomialPresentationMorphism(value.copairTest),
    cokernelColift:
        serializeAlgebraPolynomialFreydCokernelColift(value.cokernelColift),
    cofactor: serializeAlgebraPolynomialPresentationMorphism(value.cofactor),
    reconstructionCombined:
        serializeAlgebraPolynomialPresentationMorphism(
            value.reconstructionCombined
        ),
    reconstructionCombinedAgreement:
        serializeAlgebraPolynomialPresentationAgreement(
            value.reconstructionCombinedAgreement
        ),
    reconstructionLeft:
        serializeAlgebraPolynomialPresentationMorphism(value.reconstructionLeft),
    reconstructionRight:
        serializeAlgebraPolynomialPresentationMorphism(value.reconstructionRight),
    reconstructionLeftAgreement:
        serializeAlgebraPolynomialPresentationAgreement(
            value.reconstructionLeftAgreement
        ),
    reconstructionRightAgreement:
        serializeAlgebraPolynomialPresentationAgreement(
            value.reconstructionRightAgreement
        ),
    reconstructs: value.reconstructs,
    claimsUniqueCofactor: value.claimsUniqueCofactor
});

export const serializeAlgebraPolynomialFreydFiberProduct = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydFiberProduct<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson(
        fiberProductData(value),
        'polynomialFreydFiberProduct'
    );

export const serializeAlgebraPolynomialFreydFiberProductFactor = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydFiberProductFactor<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson(
        fiberProductFactorData(value),
        'polynomialFreydFiberProductFactor'
    );

export const serializeAlgebraPolynomialFreydPushout = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydPushout<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson(
        pushoutData(value),
        'polynomialFreydPushout'
    );

export const serializeAlgebraPolynomialFreydPushoutCofactor = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydPushoutCofactor<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson(
        pushoutCofactorData(value),
        'polynomialFreydPushoutCofactor'
    );

export const serializeAlgebraPolynomialFreydShortExactTriple = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydShortExactTriple<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        incoming:
            serializeAlgebraPolynomialPresentationMorphism(value.incoming),
        outgoing:
            serializeAlgebraPolynomialPresentationMorphism(value.outgoing),
        homology: serializeAlgebraPolynomialFreydHomologyAt(value.homology),
        exactness: serializeAlgebraPolynomialFreydExactnessAt(value.exactness),
        incomingMonomorphism:
            serializeAlgebraPolynomialFreydMonomorphismWitness(
                value.incomingMonomorphism
            ),
        outgoingEpimorphism:
            serializeAlgebraPolynomialFreydEpimorphismWitness(
                value.outgoingEpimorphism
            ),
        shortExact: value.shortExact
    }, 'polynomialFreydShortExactTriple');

const fiberProductStabilityData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydFiberProductEpicProjection<P, C, I>) =>
    Object.freeze({
        kind: value.kind,
        fiberProduct: fiberProductData(value.fiberProduct),
        pulledBackEpimorphism:
            serializeAlgebraPolynomialFreydEpimorphismWitness(
                value.pulledBackEpimorphism
            ),
        selectedArrowAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.selectedArrowAgreement
            ),
        projectionEpimorphism:
            serializeAlgebraPolynomialFreydEpimorphismWitness(
                value.projectionEpimorphism
            ),
        epic: value.epic
    });

const pushoutStabilityData = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydPushoutMonicInjection<P, C, I>) =>
    Object.freeze({
        kind: value.kind,
        pushout: pushoutData(value.pushout),
        pushedOutMonomorphism:
            serializeAlgebraPolynomialFreydMonomorphismWitness(
                value.pushedOutMonomorphism
            ),
        selectedArrowAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.selectedArrowAgreement
            ),
        injectionMonomorphism:
            serializeAlgebraPolynomialFreydMonomorphismWitness(
                value.injectionMonomorphism
            ),
        monic: value.monic
    });

export const serializeAlgebraPolynomialFreydSnakeTriple = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydSnakeTriple<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        delta: serializeAlgebraPolynomialPresentationMorphism(value.delta),
        beta: serializeAlgebraPolynomialPresentationMorphism(value.beta),
        lambda: serializeAlgebraPolynomialPresentationMorphism(value.lambda),
        betaAfterDelta:
            serializeAlgebraPolynomialPresentationMorphism(value.betaAfterDelta),
        tripleComposite:
            serializeAlgebraPolynomialPresentationMorphism(value.tripleComposite),
        tripleZero:
            serializeAlgebraPolynomialPresentationMorphism(value.tripleZero),
        tripleZeroAgreement:
            serializeAlgebraPolynomialPresentationAgreement(
                value.tripleZeroAgreement
            ),
        isSnakeTriple: value.isSnakeTriple
    }, 'polynomialFreydSnakeTriple');

export const serializeAlgebraPolynomialFreydSnakeConnecting = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialFreydSnakeConnecting<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        triple: serializeAlgebraPolynomialFreydSnakeTriple(value.triple),
        deltaCokernel:
            serializeAlgebraPolynomialFreydCokernel(value.deltaCokernel),
        epsilon:
            serializeAlgebraPolynomialPresentationMorphism(value.epsilon),
        lambdaAfterBeta:
            serializeAlgebraPolynomialPresentationMorphism(value.lambdaAfterBeta),
        gammaColift:
            serializeAlgebraPolynomialFreydCokernelColift(value.gammaColift),
        gamma: serializeAlgebraPolynomialPresentationMorphism(value.gamma),
        gammaKernel: serializeAlgebraPolynomialFreydKernel(value.gammaKernel),
        iota: serializeAlgebraPolynomialPresentationMorphism(value.iota),
        lambdaKernel: serializeAlgebraPolynomialFreydKernel(value.lambdaKernel),
        mu: serializeAlgebraPolynomialPresentationMorphism(value.mu),
        alphaLift: serializeAlgebraPolynomialFreydKernelLift(value.alphaLift),
        alpha: serializeAlgebraPolynomialPresentationMorphism(value.alpha),
        alphaCokernel:
            serializeAlgebraPolynomialFreydCokernel(value.alphaCokernel),
        pi: serializeAlgebraPolynomialPresentationMorphism(value.pi),
        epsilonEpimorphism:
            serializeAlgebraPolynomialFreydEpimorphismWitness(
                value.epsilonEpimorphism
            ),
        fiberProduct: fiberProductData(value.fiberProduct),
        fiberProductIdentityFactor:
            fiberProductFactorData(value.fiberProductIdentityFactor),
        fiberProductStability:
            fiberProductStabilityData(value.fiberProductStability),
        p1Epimorphism:
            serializeAlgebraPolynomialFreydEpimorphismWitness(
                value.p1Epimorphism
            ),
        muMonomorphism:
            serializeAlgebraPolynomialFreydMonomorphismWitness(
                value.muMonomorphism
            ),
        pushout: pushoutData(value.pushout),
        pushoutIdentityCofactor:
            pushoutCofactorData(value.pushoutIdentityCofactor),
        pushoutStability: pushoutStabilityData(value.pushoutStability),
        q2Monomorphism:
            serializeAlgebraPolynomialFreydMonomorphismWitness(
                value.q2Monomorphism
            ),
        betaAfterP2:
            serializeAlgebraPolynomialPresentationMorphism(value.betaAfterP2),
        normalEpiTest:
            serializeAlgebraPolynomialPresentationMorphism(value.normalEpiTest),
        uColift: serializeAlgebraPolynomialFreydNormalEpiColift(value.uColift),
        u: serializeAlgebraPolynomialPresentationMorphism(value.u),
        connectingLift:
            serializeAlgebraPolynomialFreydNormalMonoLift(value.connectingLift),
        connecting:
            serializeAlgebraPolynomialPresentationMorphism(value.connecting),
        source: presentationData(value.source),
        target: presentationData(value.target),
        assumesSplitEpimorphisms: value.assumesSplitEpimorphisms
    }, 'polynomialFreydSnakeConnecting');

const wholeSchema = <T extends { readonly kind: string }>(input: {
    readonly id: string;
    readonly kind: T['kind'];
    readonly ringOf: (value: T) => AlgebraParent;
    readonly ring: AlgebraParent;
}): AlgebraRuntimeSchema<T> => defineAlgebraRuntimeSchema({
    id: input.id,
    revision: ALGEBRA_POLYNOMIAL_FREYD_SNAKE_REFERENCE_PROFILE.revision,
    normalize(value: unknown, path: string) {
        if (
            !record(value) ||
            value.kind !== input.kind ||
            !sameAlgebraParent(input.ringOf(value as T), input.ring)
        ) throw new Error(`${input.kind} for the selected ring expected at ${path}`);
        return value as T;
    }
});

export function algebraPolynomialFreydSnakeReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    base: AlgebraPolynomialFreydAbelianCategoryModel<P, C, I>,
    selectedRing: AlgebraPolynomialRing<P, C, I>
): AlgebraPolynomialFreydSnakeReferenceOperations<P, C, I> {
    const revision = ALGEBRA_POLYNOMIAL_FREYD_SNAKE_REFERENCE_PROFILE.revision;
    const morphismSchema = base.category.morphismSchema;
    const maximumReductionSteps = (value: unknown, path: string):
        number | undefined => {
        if (value === undefined) return undefined;
        if (!Number.isSafeInteger(value) || (value as number) <= 0) {
            throw new Error(`positive reduction bound expected at ${path}`);
        }
        return value as number;
    };
    const morphismPairSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydMorphismPairInput<P, C, I>
    >({
        id: `algebra.polynomial-freyd-morphism-pair-input/` +
            selectedRing.identity.id,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) {
                throw new Error(`Freyd morphism pair expected at ${path}`);
            }
            return Object.freeze({
                left: morphismSchema.normalize(value.left, `${path}.left`),
                right: morphismSchema.normalize(value.right, `${path}.right`)
            });
        }
    });
    const fiberProductSchema = wholeSchema<
        AlgebraPolynomialFreydFiberProduct<P, C, I>
    >({
        id: `algebra.polynomial-freyd-fiber-product-result/` +
            selectedRing.identity.id,
        kind: 'algebra-polynomial-freyd-fiber-product',
        ring: selectedRing,
        ringOf: value => value.left.source.ambient.ring
    });
    const fiberProductFactorSchema = wholeSchema<
        AlgebraPolynomialFreydFiberProductFactor<P, C, I>
    >({
        id: `algebra.polynomial-freyd-fiber-product-factor-result/` +
            selectedRing.identity.id,
        kind: 'algebra-polynomial-freyd-fiber-product-factor',
        ring: selectedRing,
        ringOf: value => value.fiberProduct.left.source.ambient.ring
    });
    const fiberProductLiftInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydFiberProductLiftInput<P, C, I>
    >({
        id: `algebra.polynomial-freyd-fiber-product-lift-input/` +
            selectedRing.identity.id,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) {
                throw new Error(`Freyd fiber-product lift input expected at ${path}`);
            }
            const bound = maximumReductionSteps(
                value.maximumReductionSteps,
                `${path}.maximumReductionSteps`
            );
            return Object.freeze({
                fiberProduct: fiberProductSchema.normalize(
                    value.fiberProduct,
                    `${path}.fiberProduct`
                ),
                testLeft: morphismSchema.normalize(
                    value.testLeft,
                    `${path}.testLeft`
                ),
                testRight: morphismSchema.normalize(
                    value.testRight,
                    `${path}.testRight`
                ),
                ...(bound === undefined ? {} : { maximumReductionSteps: bound })
            });
        }
    });
    const pushoutSchema = wholeSchema<AlgebraPolynomialFreydPushout<P, C, I>>({
        id: `algebra.polynomial-freyd-pushout-result/` +
            selectedRing.identity.id,
        kind: 'algebra-polynomial-freyd-pushout',
        ring: selectedRing,
        ringOf: value => value.left.source.ambient.ring
    });
    const pushoutCofactorSchema = wholeSchema<
        AlgebraPolynomialFreydPushoutCofactor<P, C, I>
    >({
        id: `algebra.polynomial-freyd-pushout-cofactor-result/` +
            selectedRing.identity.id,
        kind: 'algebra-polynomial-freyd-pushout-cofactor',
        ring: selectedRing,
        ringOf: value => value.pushout.left.source.ambient.ring
    });
    const pushoutColiftInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydPushoutColiftInput<P, C, I>
    >({
        id: `algebra.polynomial-freyd-pushout-colift-input/` +
            selectedRing.identity.id,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) {
                throw new Error(`Freyd pushout colift input expected at ${path}`);
            }
            return Object.freeze({
                pushout: pushoutSchema.normalize(value.pushout, `${path}.pushout`),
                testLeft: morphismSchema.normalize(
                    value.testLeft,
                    `${path}.testLeft`
                ),
                testRight: morphismSchema.normalize(
                    value.testRight,
                    `${path}.testRight`
                )
            });
        }
    });
    const shortExactTripleInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydShortExactTripleInput<P, C, I>
    >({
        id: `algebra.polynomial-freyd-short-exact-triple-input/` +
            selectedRing.identity.id,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) {
                throw new Error(`Freyd short-exact input expected at ${path}`);
            }
            const bound = maximumReductionSteps(
                value.maximumReductionSteps,
                `${path}.maximumReductionSteps`
            );
            return Object.freeze({
                incoming: morphismSchema.normalize(
                    value.incoming,
                    `${path}.incoming`
                ),
                outgoing: morphismSchema.normalize(
                    value.outgoing,
                    `${path}.outgoing`
                ),
                ...(bound === undefined ? {} : { maximumReductionSteps: bound })
            });
        }
    });
    const shortExactTripleSchema = wholeSchema<
        AlgebraPolynomialFreydShortExactTriple<P, C, I>
    >({
        id: `algebra.polynomial-freyd-short-exact-triple-result/` +
            selectedRing.identity.id,
        kind: 'algebra-polynomial-freyd-short-exact-triple',
        ring: selectedRing,
        ringOf: value => value.incoming.source.ambient.ring
    });
    const tripleInputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialFreydSnakeTripleInput<P, C, I>
    >({
        id: `algebra.polynomial-freyd-snake-triple-input/` +
            selectedRing.identity.id,
        revision,
        normalize(value: unknown, path: string) {
            if (!record(value)) {
                throw new Error(`Freyd snake triple input expected at ${path}`);
            }
            return Object.freeze({
                delta: morphismSchema.normalize(value.delta, `${path}.delta`),
                beta: morphismSchema.normalize(value.beta, `${path}.beta`),
                lambda: morphismSchema.normalize(value.lambda, `${path}.lambda`)
            });
        }
    });
    const tripleSchema = wholeSchema<
        AlgebraPolynomialFreydSnakeTriple<P, C, I>
    >({
        id: `algebra.polynomial-freyd-snake-triple-result/` +
            selectedRing.identity.id,
        kind: 'algebra-polynomial-freyd-snake-triple',
        ring: selectedRing,
        ringOf: value => value.delta.source.ambient.ring
    });
    const connectingSchema = wholeSchema<
        AlgebraPolynomialFreydSnakeConnecting<P, C, I>
    >({
        id: `algebra.polynomial-freyd-snake-connecting-result/` +
            selectedRing.identity.id,
        kind: 'algebra-polynomial-freyd-snake-connecting',
        ring: selectedRing,
        ringOf: value => value.triple.delta.source.ambient.ring
    });
    const prefix = `algebra.polynomial-freyd-snake/` + selectedRing.identity.id;
    const fiberProduct = defineAlgebraOperation({
        id: `${prefix}/fiber-product`,
        revision,
        input: morphismPairSchema,
        output: fiberProductSchema
    });
    const fiberProductProjectionLeft = defineAlgebraOperation({
        id: `${prefix}/fiber-product-projection-left`,
        revision,
        input: fiberProductSchema,
        output: morphismSchema
    });
    const fiberProductProjectionRight = defineAlgebraOperation({
        id: `${prefix}/fiber-product-projection-right`,
        revision,
        input: fiberProductSchema,
        output: morphismSchema
    });
    const fiberProductLift = defineAlgebraOperation({
        id: `${prefix}/fiber-product-lift`,
        revision,
        input: fiberProductLiftInputSchema,
        output: fiberProductFactorSchema
    });
    const pushout = defineAlgebraOperation({
        id: `${prefix}/pushout`,
        revision,
        input: morphismPairSchema,
        output: pushoutSchema
    });
    const pushoutInjectionLeft = defineAlgebraOperation({
        id: `${prefix}/pushout-injection-left`,
        revision,
        input: pushoutSchema,
        output: morphismSchema
    });
    const pushoutInjectionRight = defineAlgebraOperation({
        id: `${prefix}/pushout-injection-right`,
        revision,
        input: pushoutSchema,
        output: morphismSchema
    });
    const pushoutColift = defineAlgebraOperation({
        id: `${prefix}/pushout-colift`,
        revision,
        input: pushoutColiftInputSchema,
        output: pushoutCofactorSchema
    });
    const shortExactTriple = defineAlgebraOperation({
        id: `${prefix}/short-exact-triple`,
        revision,
        input: shortExactTripleInputSchema,
        output: shortExactTripleSchema
    });
    const triple = defineAlgebraOperation({
        id: `${prefix}/triple`,
        revision,
        input: tripleInputSchema,
        output: tripleSchema
    });
    const connecting = defineAlgebraOperation({
        id: `${prefix}/connecting`,
        revision,
        input: tripleSchema,
        output: connectingSchema
    });
    const algorithm = (operation: AlgebraOperation<unknown, unknown>) =>
        algebraAlgorithmIdentity(
            `algebra.typescript-reference/${operation.identity.id}`,
            ALGEBRA_POLYNOMIAL_FREYD_SNAKE_REFERENCE_PROFILE.algorithmRevision
        );
    const implementation = <Input, Output>(
        operation: AlgebraOperation<Input, Output>,
        execute: (input: Input) => Output
    ): AlgebraReferenceImplementation => defineAlgebraReferenceImplementation({
        operation,
        algorithm: algorithm(operation as AlgebraOperation<unknown, unknown>),
        execute
    });
    return Object.freeze({
        morphismPairSchema,
        fiberProduct,
        fiberProductProjectionLeft,
        fiberProductProjectionRight,
        fiberProductLiftInputSchema,
        fiberProductLift,
        pushout,
        pushoutInjectionLeft,
        pushoutInjectionRight,
        pushoutColiftInputSchema,
        pushoutColift,
        shortExactTripleInputSchema,
        shortExactTriple,
        tripleInputSchema,
        triple,
        connecting,
        implementations: Object.freeze([
            implementation(fiberProduct, input =>
                algebraPolynomialFreydFiberProduct(input.left, input.right)),
            implementation(fiberProductProjectionLeft,
                value => value.projectionLeft),
            implementation(fiberProductProjectionRight,
                value => value.projectionRight),
            implementation(fiberProductLift, input =>
                algebraPolynomialFreydFiberProductFactor(
                    input.fiberProduct,
                    input.testLeft,
                    input.testRight,
                    input.maximumReductionSteps === undefined
                        ? {}
                        : { maximumReductionSteps: input.maximumReductionSteps }
                )),
            implementation(pushout, input =>
                algebraPolynomialFreydPushout(input.left, input.right)),
            implementation(pushoutInjectionLeft,
                value => value.injectionLeft),
            implementation(pushoutInjectionRight,
                value => value.injectionRight),
            implementation(pushoutColift, input =>
                algebraPolynomialFreydPushoutCofactor(
                    input.pushout,
                    input.testLeft,
                    input.testRight
                )),
            implementation(shortExactTriple, input =>
                algebraPolynomialFreydShortExactTriple(
                    input.incoming,
                    input.outgoing,
                    input.maximumReductionSteps === undefined
                        ? {}
                        : { maximumReductionSteps: input.maximumReductionSteps }
                )),
            implementation(triple, input => algebraPolynomialFreydSnakeTriple(
                input.delta,
                input.beta,
                input.lambda
            )),
            implementation(connecting, algebraPolynomialFreydSnakeConnecting)
        ])
    });
}
