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
    AlgebraPolynomialFreydFiberProduct
} from './algebra_polynomial_freyd_fiber_product';
import {
    AlgebraPolynomialFreydPushout
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

export interface AlgebraPolynomialFreydSnakeReferenceOperations<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
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
        tripleInputSchema,
        triple,
        connecting,
        implementations: Object.freeze([
            implementation(triple, input => algebraPolynomialFreydSnakeTriple(
                input.delta,
                input.beta,
                input.lambda
            )),
            implementation(connecting, algebraPolynomialFreydSnakeConnecting)
        ])
    });
}
