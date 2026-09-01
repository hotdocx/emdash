/** Explicit-Core realizations and proof-CAS adapters for weak-kernel equations. */

import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    algebraFormalCompositeZeroClaimType,
    algebraFormalMatrixTerm
} from './algebra_formal_finite_module';
import {
    AlgebraFormalComputationInterpretationInput,
    AlgebraFormalDelegationError,
    defineAlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraOperation
} from './algebra_engine';
import {
    algebraPolynomialText
} from './algebra_polynomial';
import {
    AlgebraPolynomialModuleMap
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialWeakKernel,
    AlgebraPolynomialWeakKernelFactorization
} from './algebra_polynomial_weak_kernel';
import {
    AlgebraPolynomialWeakKernelCategoryModel,
    AlgebraPolynomialWeakKernelLiftInput,
    algebraPolynomialWeakKernelCategoryModel
} from './algebra_polynomial_weak_kernel_category';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    KernelExpression,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from './kernel';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_FORMAL_WEAK_KERNEL_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-weak-kernel-v1' as const,
    annihilationRevision: 'emdash-formal-weak-kernel-annihilation-v1' as const,
    factorizationRevision: 'emdash-formal-weak-kernel-factorization-v1' as const,
    equationPolicy: 'selected-data-plus-exact-law' as const,
    universalFactorOperationSupplied: false as const,
    claimsRingWideWeakKernels: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

const p = provenance('derived', 'formal computational weak kernel');
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
    { plicity: 'explicit', value: call('bridge_comm_ring_carrier', [
        { plicity: 'explicit', value: ring }
    ]) },
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

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const assertReifierRing = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    reifier: AffineFormalPolynomialReifier<P, C, I>,
    ring: AlgebraParent,
    path: string
): void => {
    if (!sameAlgebraParent(
        reifier.algebra.quotient.polynomialRing,
        ring
    )) throw new Error(`Formal weak-kernel reifier has a foreign ring at ${path}`);
};

const serializeMap = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    map: AlgebraPolynomialModuleMap<P, C, I>
) => ({
    sourceRank: map.source.rank,
    targetRank: map.target.rank,
    columns: map.columns.map(column => column.components.map(algebraPolynomialText))
});

export const serializeAlgebraPolynomialWeakKernel = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialWeakKernel<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        map: serializeMap(value.map),
        objectRank: value.object.rank,
        morphism: serializeMap(value.morphism),
        annihilates: value.annihilates,
        claimsUniqueLifts: value.claimsUniqueLifts
    }, 'algebraPolynomialWeakKernel');

export const serializeAlgebraPolynomialWeakKernelFactorization = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(value: AlgebraPolynomialWeakKernelFactorization<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        weakKernel: serializeAlgebraPolynomialWeakKernel(value.weakKernel),
        test: serializeMap(value.test),
        lift: serializeMap(value.lift),
        reconstruction: serializeMap(value.reconstruction),
        reconstructs: value.reconstructs,
        reductionSteps: value.reductionSteps
    }, 'algebraPolynomialWeakKernelFactorization');

export interface AlgebraFormalWeakKernelRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_WEAK_KERNEL_PROFILE.annihilationRevision;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialWeakKernel<P, C, I>;
    readonly selectedOutputData: string;
    readonly formalMap: KernelExpression;
    readonly formalObjectRank: KernelExpression;
    readonly formalMorphism: KernelExpression;
    readonly claimType: KernelExpression;
}

export function defineAlgebraFormalWeakKernelRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialWeakKernel<P, C, I>;
}): AlgebraFormalWeakKernelRealization<P, C, I> {
    assertReifierRing(input.reifier, input.selected.map.source.ring, 'map');
    if (!input.selected.annihilates) {
        throw new Error('Selected computational weak kernel does not annihilate');
    }
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_WEAK_KERNEL_PROFILE.annihilationRevision,
        reifier: input.reifier,
        selected: input.selected,
        selectedOutputData: serializeAlgebraPolynomialWeakKernel(input.selected),
        formalMap: algebraFormalMatrixTerm(
            input.reifier,
            input.selected.map.columns,
            input.selected.map.target.rank
        ),
        formalObjectRank: nat(input.selected.object.rank),
        formalMorphism: algebraFormalMatrixTerm(
            input.reifier,
            input.selected.morphism.columns,
            input.selected.morphism.target.rank
        ),
        claimType: algebraFormalCompositeZeroClaimType({
            reifier: input.reifier,
            left: input.selected.map,
            right: input.selected.morphism
        })
    });
}

export interface AlgebraFormalWeakKernelFactorizationRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_WEAK_KERNEL_PROFILE.factorizationRevision;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialWeakKernelFactorization<P, C, I>;
    readonly selectedOutputData: string;
    readonly formalWeakKernelMorphism: KernelExpression;
    readonly formalLift: KernelExpression;
    readonly formalTest: KernelExpression;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
    readonly claimType: KernelExpression;
}

export function defineAlgebraFormalWeakKernelFactorizationRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialWeakKernelFactorization<P, C, I>;
}): AlgebraFormalWeakKernelFactorizationRealization<P, C, I> {
    const value = input.selected;
    assertReifierRing(input.reifier, value.test.source.ring, 'factorization');
    if (!value.reconstructs) {
        throw new Error('Selected weak-kernel factorization does not reconstruct');
    }
    const formalWeakKernelMorphism = algebraFormalMatrixTerm(
        input.reifier,
        value.weakKernel.morphism.columns,
        value.weakKernel.morphism.target.rank
    );
    const formalLift = algebraFormalMatrixTerm(
        input.reifier,
        value.lift.columns,
        value.lift.target.rank
    );
    const formalTest = algebraFormalMatrixTerm(
        input.reifier,
        value.test.columns,
        value.test.target.rank
    );
    const left = matrixComp(
        input.reifier.formalRing,
        value.test.target.rank,
        value.weakKernel.object.rank,
        value.test.source.rank,
        formalWeakKernelMorphism,
        formalLift
    );
    return Object.freeze({
        profileRevision:
            ALGEBRA_FORMAL_WEAK_KERNEL_PROFILE.factorizationRevision,
        reifier: input.reifier,
        selected: value,
        selectedOutputData:
            serializeAlgebraPolynomialWeakKernelFactorization(value),
        formalWeakKernelMorphism,
        formalLift,
        formalTest,
        left,
        right: formalTest,
        claimType: equation(
            matrixClassifier(
                input.reifier.formalRing,
                value.test.target.rank,
                value.test.source.rank
            ),
            left,
            formalTest
        )
    });
}

const exactTarget = (
    goal: { readonly target: KernelExpression },
    target: KernelExpression,
    path: string
): void => {
    if (!kernelExpressionEquals(goal.target, target)) {
        throw new AlgebraFormalDelegationError(
            'CLAIM_TARGET_MISMATCH',
            path,
            'Goal differs from the selected weak-kernel equation'
        );
    }
};

export function algebraFormalWeakKernelDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialWeakKernel<P, C, I>;
}) {
    const model = algebraPolynomialWeakKernelCategoryModel(
        input.selected.map.source.ring
    );
    const realization = defineAlgebraFormalWeakKernelRealization(input);
    const operation = model.native.operations.weakKernel as AlgebraOperation<
        AlgebraPolynomialModuleMap<P, C, I>,
        AlgebraPolynomialWeakKernel<P, C, I>
    >;
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.polynomial-weak-kernel/${input.selected.map.source.ring.identity.id}`,
        revision: ALGEBRA_FORMAL_WEAK_KERNEL_PROFILE.revision,
        operation,
        normalizeRealization(value, path) {
            if (!record(value) || value.profileRevision !==
                ALGEBRA_FORMAL_WEAK_KERNEL_PROFILE.annihilationRevision) {
                throw new Error(`formal weak-kernel realization expected at ${path}`);
            }
            const candidate = value as unknown as typeof realization;
            if (candidate.selectedOutputData !== realization.selectedOutputData ||
                !kernelExpressionEquals(candidate.claimType, realization.claimType)) {
                throw new Error(`formal weak-kernel realization drift at ${path}`);
            }
            return candidate;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            selected: value.selectedOutputData,
            claim: serializeCoreExpression(value.claimType)
        }, 'formalWeakKernelRealization'),
        acquire: (goal, value) => {
            exactTarget(goal, value.claimType, 'formalWeakKernel.goal');
            return value.selected.map;
        },
        serializeInput: serializeMapInput,
        serializeOutput: serializeAlgebraPolynomialWeakKernel,
        interpret: ({ goal, realization: value, computed }):
            AlgebraFormalComputationInterpretationInput =>
            serializeAlgebraPolynomialWeakKernel(computed.value) ===
                value.selectedOutputData
                ? { kind: 'claim', summary: 'selected F o K is zero',
                    claimType: goal.target }
                : { kind: 'observation',
                    summary: 'computed weak kernel differs from selected data' }
    });
    return Object.freeze({ model, realization, adapter });
}

const serializeMapInput = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    map: AlgebraPolynomialModuleMap<P, C, I>
): string => serializeCoreLfWorkspaceCanonicalJson(
    serializeMap(map),
    'formalWeakKernelMapInput'
);

export function algebraFormalWeakKernelFactorizationDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialWeakKernelFactorization<P, C, I>;
}) {
    const model = algebraPolynomialWeakKernelCategoryModel(
        input.selected.weakKernel.map.source.ring
    );
    const realization =
        defineAlgebraFormalWeakKernelFactorizationRealization(input);
    const operation = model.native.operations.weakKernelLift as AlgebraOperation<
        AlgebraPolynomialWeakKernelLiftInput<P, C, I>,
        AlgebraPolynomialWeakKernelFactorization<P, C, I>
    >;
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.polynomial-weak-kernel-lift/` +
            input.selected.weakKernel.map.source.ring.identity.id,
        revision: ALGEBRA_FORMAL_WEAK_KERNEL_PROFILE.revision,
        operation,
        normalizeRealization(value, path) {
            if (!record(value) || value.profileRevision !==
                ALGEBRA_FORMAL_WEAK_KERNEL_PROFILE.factorizationRevision) {
                throw new Error(`formal weak-kernel lift expected at ${path}`);
            }
            const candidate = value as unknown as typeof realization;
            if (candidate.selectedOutputData !== realization.selectedOutputData ||
                !kernelExpressionEquals(candidate.claimType, realization.claimType)) {
                throw new Error(`formal weak-kernel lift drift at ${path}`);
            }
            return candidate;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            selected: value.selectedOutputData,
            claim: serializeCoreExpression(value.claimType)
        }, 'formalWeakKernelFactorizationRealization'),
        acquire: (goal, value) => {
            exactTarget(goal, value.claimType, 'formalWeakKernelLift.goal');
            return Object.freeze({
                map: value.selected.weakKernel.map,
                test: value.selected.test
            });
        },
        serializeInput: value => serializeCoreLfWorkspaceCanonicalJson({
            map: serializeMap(value.map),
            test: serializeMap(value.test),
            maximumReductionSteps: value.maximumReductionSteps ?? null
        }, 'formalWeakKernelLiftInput'),
        serializeOutput: serializeAlgebraPolynomialWeakKernelFactorization,
        interpret: ({ goal, realization: value, computed }):
            AlgebraFormalComputationInterpretationInput =>
            serializeAlgebraPolynomialWeakKernelFactorization(computed.value) ===
                value.selectedOutputData
                ? { kind: 'claim', summary: 'selected K o U reconstructs H',
                    claimType: goal.target }
                : { kind: 'observation',
                    summary: 'computed weak-kernel lift differs from selected data' }
    });
    return Object.freeze({ model, realization, adapter });
}
