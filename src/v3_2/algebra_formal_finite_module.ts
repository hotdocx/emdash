/** Explicit-Core reification and membership delegation for finite modules. */

import {
    AlgebraFormalComputationInterpretationInput,
    AlgebraFormalDelegationError,
    defineAlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import {
    AffineFormalPolynomialReifier
} from './algebra_formal_reifier';
import {
    buildAffineFormalFamily
} from './algebra_formal_cover';
import {
    AlgebraAlgorithmIdentity,
    AlgebraOperation,
    AlgebraRuntimeSchema,
    algebraAlgorithmIdentity,
    defineAlgebraOperation,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraReferenceImplementation,
    defineAlgebraReferenceImplementation
} from './algebra_reference_engine';
import {
    AlgebraElement,
    AlgebraParent,
    sameAlgebraParent
} from './algebra_parent';
import {
    AlgebraPolynomialModuleGroebnerBasis,
    AlgebraPolynomialModuleMembership,
    AlgebraPolynomialModuleSchreyerSyzygies,
    AlgebraPolynomialModuleVector,
    algebraPolynomialModuleMembership,
    algebraPolynomialModuleVectorSchema
} from './algebra_polynomial_module';
import {
    AlgebraPolynomialModuleMap,
    AlgebraPolynomialSchreyerResolution
} from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialModuleReferenceOperations,
    algebraPolynomialModuleReferenceOperations
} from './algebra_polynomial_module_reference_operations';
import {
    algebraPolynomialText
} from './algebra_polynomial';
import {
    KernelExpression,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from './kernel';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const ALGEBRA_FORMAL_FINITE_MODULE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-finite-module-v1' as const,
    orientation: 'formal-columns-cas-component-arrays' as const,
    membershipRevision: 'emdash-formal-module-membership-v1' as const,
    syzygyRevision: 'emdash-formal-module-syzygy-v1' as const,
    resolutionRevision: 'emdash-formal-module-resolution-v1' as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

export const AFFINE_FORMAL_FINITE_MODULE_BINDINGS = Object.freeze({
    bridge_CommRingVector: 'CommRingVector',
    bridge_CommRingMatrix: 'CommRingMatrix',
    bridge_comm_ring_matrix_apply: 'comm_ring_matrix_apply',
    bridge_comm_ring_vector_zero: 'comm_ring_vector_zero',
    bridge_comm_ring_matrix_zero: 'comm_ring_matrix_zero',
    bridge_comm_ring_matrix_comp: 'comm_ring_matrix_comp',
    bridge_CommRingPresentationAgreement: 'CommRingPresentationAgreement',
    bridge_CommRingMatrixSyzygy: 'CommRingMatrixSyzygy',
    bridge_CommRingMatrixCompositeZero: 'CommRingMatrixCompositeZero'
});

const nodeProvenance = provenance('derived', 'formal finite module');
const call = (
    name: string,
    values: readonly { plicity: 'explicit' | 'implicit'; value: KernelExpression }[]
): KernelExpression => kernelCall(
    kernelFree(name, nodeProvenance),
    values,
    nodeProvenance
);
const nat = (value: number): KernelExpression => {
    let result: KernelExpression = kernelFree(
        'bridge_nat_zero',
        nodeProvenance
    );
    for (let index = 0; index < value; index++) {
        result = call('bridge_nat_succ', [{ plicity: 'explicit', value: result }]);
    }
    return result;
};
const tau = (value: KernelExpression): KernelExpression => call(
    'bridge_tau',
    [{ plicity: 'explicit', value }]
);

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const invalidRealization = (path: string, message: string): never => {
    throw new AlgebraFormalDelegationError(
        'INVALID_REALIZATION',
        path,
        message
    );
};

export interface AlgebraFormalModuleMembershipInput<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly vector: AlgebraPolynomialModuleVector<P, C, I>;
    readonly basis: AlgebraPolynomialModuleGroebnerBasis<P, C, I>;
}

export interface AlgebraFormalModuleMembershipRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision: typeof ALGEBRA_FORMAL_FINITE_MODULE_PROFILE.revision;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly input: AlgebraFormalModuleMembershipInput<P, C, I>;
    readonly selected: AlgebraPolynomialModuleMembership<P, C, I>;
    readonly selectedOutputData: string;
    readonly formalGenerators: KernelExpression;
    readonly formalCoefficients: KernelExpression;
    readonly formalVector: KernelExpression;
    readonly claimType: KernelExpression;
}

const vectorTerm = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    reifier: AffineFormalPolynomialReifier<P, C, I>,
    vector: AlgebraPolynomialModuleVector<P, C, I>
): KernelExpression => buildAffineFormalFamily(
    call('bridge_comm_ring_carrier', [{
        plicity: 'explicit', value: reifier.formalRing
    }]),
    vector.components.map(reifier.reifyPolynomial)
).family;

export const algebraFormalMatrixTerm = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    reifier: AffineFormalPolynomialReifier<P, C, I>,
    columns: readonly AlgebraPolynomialModuleVector<P, C, I>[],
    rows: number
): KernelExpression => {
    if (!Number.isSafeInteger(rows) || rows < 0) {
        return invalidRealization(
            'formalMatrix.rows',
            'Formal matrix row count must be a nonnegative safe integer'
        );
    }
    columns.forEach((column, index) => {
        if (column.parent.rank !== rows) {
            return invalidRealization(
                `formalMatrix.columns[${index}]`,
                `Expected a column of rank ${rows}`
            );
        }
    });
    return buildAffineFormalFamily(
        call('bridge_FiniteFamily', [
            {
                plicity: 'explicit',
                value: call('bridge_comm_ring_carrier', [{
                    plicity: 'explicit', value: reifier.formalRing
                }])
            },
            { plicity: 'explicit', value: nat(rows) }
        ]),
        columns.map(column => vectorTerm(reifier, column))
    ).family;
};

export const algebraFormalSyzygyClaimType = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly generators: readonly AlgebraPolynomialModuleVector<P, C, I>[];
    readonly syzygy: AlgebraPolynomialModuleVector<P, C, I>;
}): KernelExpression => {
    const first = input.generators[0];
    if (first === undefined) {
        return invalidRealization(
            'formalSyzygy.generators',
            'A selected Schreyer syzygy requires a nonempty basis'
        );
    }
    input.generators.forEach((generator, index) => {
        if (!sameAlgebraParent(generator.parent, first.parent)) {
            return invalidRealization(
                `formalSyzygy.generators[${index}]`,
                'Syzygy matrix columns belong to different free modules'
            );
        }
    });
    if (input.syzygy.parent.rank !== input.generators.length) {
        return invalidRealization(
            'formalSyzygy.syzygy',
            `Expected a coefficient vector of rank ${input.generators.length}`
        );
    }
    return tau(call('bridge_CommRingMatrixSyzygy', [
        { plicity: 'explicit', value: input.reifier.formalRing },
        { plicity: 'explicit', value: nat(first.parent.rank) },
        { plicity: 'explicit', value: nat(input.generators.length) },
        {
            plicity: 'explicit',
            value: algebraFormalMatrixTerm(
                input.reifier,
                input.generators,
                first.parent.rank
            )
        },
        { plicity: 'explicit', value: vectorTerm(input.reifier, input.syzygy) }
    ]));
};

export const algebraFormalCompositeZeroClaimType = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly left: AlgebraPolynomialModuleMap<P, C, I>;
    readonly right: AlgebraPolynomialModuleMap<P, C, I>;
}): KernelExpression => {
    if (!sameAlgebraParent(input.left.source, input.right.target)) {
        return invalidRealization(
            'formalCompositeZero.maps',
            'Adjacent formal matrices are not composable'
        );
    }
    return tau(call('bridge_CommRingMatrixCompositeZero', [
        { plicity: 'explicit', value: input.reifier.formalRing },
        { plicity: 'explicit', value: nat(input.left.target.rank) },
        { plicity: 'explicit', value: nat(input.left.source.rank) },
        { plicity: 'explicit', value: nat(input.right.source.rank) },
        {
            plicity: 'explicit',
            value: algebraFormalMatrixTerm(
                input.reifier,
                input.left.columns,
                input.left.target.rank
            )
        },
        {
            plicity: 'explicit',
            value: algebraFormalMatrixTerm(
                input.reifier,
                input.right.columns,
                input.right.target.rank
            )
        }
    ]));
};

export function defineAlgebraFormalModuleMembershipRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly vector: AlgebraPolynomialModuleVector<P, C, I>;
    readonly basis: AlgebraPolynomialModuleGroebnerBasis<P, C, I>;
    readonly selected: AlgebraPolynomialModuleMembership<P, C, I>;
}): AlgebraFormalModuleMembershipRealization<P, C, I> {
    if (!sameAlgebraParent(input.vector.parent, input.basis.submodule.module)) {
        return invalidRealization(
            'formalMembership.vector',
            'Membership vector and basis belong to different free modules'
        );
    }
    const rank = input.vector.parent.rank;
    const columns = input.basis.submodule.generators.length;
    if (
        input.selected.kind !== 'algebra-polynomial-module-membership' ||
        !sameAlgebraParent(input.selected.vector.parent, input.vector.parent) ||
        input.selected.coefficients.length !== columns ||
        input.selected.vector.components.map(algebraPolynomialText).join('\n') !==
            input.vector.components.map(algebraPolynomialText).join('\n')
    ) {
        return invalidRealization(
            'formalMembership.selected',
            'Selected membership result does not match the vector and presentation'
        );
    }
    const vectorClassifier = call('bridge_FiniteFamily', [
        { plicity: 'explicit', value: call('bridge_comm_ring_carrier', [{
            plicity: 'explicit', value: input.reifier.formalRing
        }]) },
        { plicity: 'explicit', value: nat(rank) }
    ]);
    const formalGenerators = algebraFormalMatrixTerm(
        input.reifier,
        input.basis.submodule.generators,
        rank
    );
    const formalCoefficients = buildAffineFormalFamily(
        call('bridge_comm_ring_carrier', [{
            plicity: 'explicit', value: input.reifier.formalRing
        }]),
        input.selected.coefficients.map(input.reifier.reifyPolynomial)
    ).family;
    const formalVector = vectorTerm(input.reifier, input.vector);
    const applied = call('bridge_comm_ring_matrix_apply', [
        { plicity: 'explicit', value: input.reifier.formalRing },
        { plicity: 'explicit', value: nat(rank) },
        { plicity: 'explicit', value: nat(columns) },
        { plicity: 'explicit', value: formalGenerators },
        { plicity: 'explicit', value: formalCoefficients }
    ]);
    const claimType = tau(call('bridge_eq', [
        { plicity: 'implicit', value: vectorClassifier },
        { plicity: 'explicit', value: applied },
        { plicity: 'explicit', value: formalVector }
    ]));
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_FINITE_MODULE_PROFILE.revision,
        reifier: input.reifier,
        input: Object.freeze({ vector: input.vector, basis: input.basis }),
        selected: input.selected,
        selectedOutputData: serializeMembership(input.selected),
        formalGenerators,
        formalCoefficients,
        formalVector,
        claimType
    });
}

const serializeMembership = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPolynomialModuleMembership<P, C, I>
): string => serializeCoreLfWorkspaceCanonicalJson({
    member: value.member,
    vector: value.vector.components.map(algebraPolynomialText),
    coefficients: value.coefficients.map(algebraPolynomialText),
    remainder: value.remainder.components.map(algebraPolynomialText),
    steps: value.reductionSteps
}, 'formalModuleMembership');

export function algebraFormalModuleMembershipBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(sample: AlgebraPolynomialModuleVector<P, C, I>) {
    const vectorSchema = algebraPolynomialModuleVectorSchema(sample.parent);
    const inputSchema: AlgebraRuntimeSchema<AlgebraFormalModuleMembershipInput<P, C, I>> =
        defineAlgebraRuntimeSchema({
            id: `algebra.formal-module-membership-input/${sample.parent.identity.id}`,
            revision: sample.parent.identity.revision,
            normalize(value, path) {
                if (value === null || typeof value !== 'object') {
                    throw new Error(`module membership input expected at ${path}`);
                }
                const input = value as AlgebraFormalModuleMembershipInput<P, C, I>;
                if (
                    !record(input.basis) ||
                    input.basis.kind !== 'algebra-polynomial-module-groebner-basis' ||
                    !sameAlgebraParent(
                        input.basis.submodule.module,
                        sample.parent
                    )
                ) {
                    throw new Error(`module membership basis expected at ${path}.basis`);
                }
                return Object.freeze({
                    vector: vectorSchema.normalize(input.vector, `${path}.vector`),
                    basis: input.basis
                });
            }
        });
    const outputSchema = defineAlgebraRuntimeSchema<
        AlgebraPolynomialModuleMembership<P, C, I>
    >({
        id: `algebra.formal-module-membership/${sample.parent.identity.id}`,
        revision: sample.parent.identity.revision,
        normalize(value, path) {
            if (
                !record(value) ||
                value.kind !== 'algebra-polynomial-module-membership'
            ) {
                throw new Error(`module membership result expected at ${path}`);
            }
            const membership = value as unknown as
                AlgebraPolynomialModuleMembership<P, C, I>;
            if (!sameAlgebraParent(membership.vector.parent, sample.parent)) {
                throw new Error(`foreign membership result at ${path}`);
            }
            return membership;
        }
    });
    const operation: AlgebraOperation<
        AlgebraFormalModuleMembershipInput<P, C, I>,
        AlgebraPolynomialModuleMembership<P, C, I>
    > = defineAlgebraOperation({
        id: `algebra.module.membership/${sample.parent.identity.id}`,
        revision: sample.parent.identity.revision,
        input: inputSchema,
        output: outputSchema
    });
    const algorithm: AlgebraAlgorithmIdentity = algebraAlgorithmIdentity(
        `algebra.typescript-reference/${operation.identity.id}`,
        'module-membership-v1'
    );
    const implementations: readonly AlgebraReferenceImplementation[] = Object.freeze([
        defineAlgebraReferenceImplementation({
            operation,
            algorithm,
            execute: input => algebraPolynomialModuleMembership(
                input.vector,
                input.basis
            )
        })
    ]);
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.module-membership/${sample.parent.identity.id}`,
        revision: sample.parent.identity.revision,
        operation,
        normalizeRealization(value, path) {
            if (
                !record(value) ||
                value.profileRevision !==
                    ALGEBRA_FORMAL_FINITE_MODULE_PROFILE.revision
            ) {
                return invalidRealization(
                    path,
                    'Expected one current formal module-membership realization'
                );
            }
            const realization = value as unknown as
                AlgebraFormalModuleMembershipRealization<P, C, I>;
            if (!sameAlgebraParent(realization.input.vector.parent, sample.parent)) {
                return invalidRealization(
                    path,
                    'Formal membership realization belongs to a foreign module'
                );
            }
            const expected = defineAlgebraFormalModuleMembershipRealization({
                reifier: realization.reifier,
                vector: realization.input.vector,
                basis: realization.input.basis,
                selected: realization.selected
            });
            if (
                realization.selectedOutputData !== expected.selectedOutputData ||
                !kernelExpressionEquals(realization.claimType, expected.claimType)
            ) {
                return invalidRealization(
                    path,
                    'Formal membership realization differs from its selected equation'
                );
            }
            return realization;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            selected: value.selectedOutputData,
            claim: serializeCoreExpression(value.claimType)
        }, 'formalModuleMembershipRealization'),
        acquire: (goal, value) => {
            if (!kernelExpressionEquals(goal.target, value.claimType)) {
                throw new AlgebraFormalDelegationError(
                    'CLAIM_TARGET_MISMATCH',
                    'formalMembership.goal',
                    'Goal differs from the selected module-membership equation'
                );
            }
            return value.input;
        },
        serializeInput: value => serializeCoreLfWorkspaceCanonicalJson({
            vector: value.vector.components.map(algebraPolynomialText)
        }, 'formalModuleMembershipInput'),
        serializeOutput: serializeMembership,
        interpret: ({ goal, realization, computed }):
            AlgebraFormalComputationInterpretationInput =>
            serializeMembership(computed.value) ===
                realization.selectedOutputData && computed.value.member
                ? {
                    kind: 'claim',
                    summary: 'selected module linear combination equals vector',
                    claimType: goal.target
                }
                : {
                    kind: 'observation',
                    summary: 'module vector has a nonzero or changed remainder'
                }
    });
    return Object.freeze({ inputSchema, outputSchema, operation, implementations, adapter });
}

const serializeSyzygies = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPolynomialModuleSchreyerSyzygies<P, C, I>
): string => serializeCoreLfWorkspaceCanonicalJson({
    basis: value.basis.basis.map(vector =>
        vector.components.map(algebraPolynomialText)
    ),
    generators: value.generators.map(vector =>
        vector.components.map(algebraPolynomialText)
    ),
    pairs: value.sourcePairs
}, 'formalModuleSyzygies');

export interface AlgebraFormalModuleSyzygyRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_FINITE_MODULE_PROFILE.syzygyRevision;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly basis: AlgebraPolynomialModuleGroebnerBasis<P, C, I>;
    readonly selected: AlgebraPolynomialModuleSchreyerSyzygies<P, C, I>;
    readonly selectedOutputData: string;
    readonly index: number;
    readonly claimType: KernelExpression;
}

export function algebraFormalSyzygyDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly basis: AlgebraPolynomialModuleGroebnerBasis<P, C, I>;
    readonly selected: AlgebraPolynomialModuleSchreyerSyzygies<P, C, I>;
    readonly index: number;
}) {
    if (
        !Number.isSafeInteger(input.index) ||
        input.index < 0 ||
        input.index >= input.selected.generators.length
    ) {
        return invalidRealization(
            'formalSyzygy.index',
            'Selected syzygy index is outside the computed generator family'
        );
    }
    const operations: AlgebraPolynomialModuleReferenceOperations<P, C, I> =
        algebraPolynomialModuleReferenceOperations(input.basis.submodule.module);
    const claimType = algebraFormalSyzygyClaimType({
        reifier: input.reifier,
        generators: input.basis.basis,
        syzygy: input.selected.generators[input.index]
    });
    const selectedOutputData = serializeSyzygies(input.selected);
    const realization: AlgebraFormalModuleSyzygyRealization<P, C, I> =
        Object.freeze({
            profileRevision: ALGEBRA_FORMAL_FINITE_MODULE_PROFILE.syzygyRevision,
            ...input,
            selectedOutputData,
            claimType
        });
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.module-syzygy/${input.basis.submodule.module.identity.id}`,
        revision: input.basis.submodule.module.identity.revision,
        operation: operations.syzygies,
        normalizeRealization(value, path) {
            if (
                !record(value) ||
                value.profileRevision !==
                    ALGEBRA_FORMAL_FINITE_MODULE_PROFILE.syzygyRevision
            ) {
                return invalidRealization(
                    path,
                    'Expected one current formal syzygy realization'
                );
            }
            const candidate = value as unknown as typeof realization;
            if (
                candidate.index !== input.index ||
                candidate.selectedOutputData !== selectedOutputData ||
                !kernelExpressionEquals(candidate.claimType, claimType)
            ) {
                return invalidRealization(
                    path,
                    'Formal syzygy realization differs from the selected equation'
                );
            }
            return candidate;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            selected: serializeSyzygies(value.selected),
            index: value.index,
            claim: serializeCoreExpression(value.claimType)
        }, 'formalSyzygyRealization'),
        acquire: (goal, value) => {
            if (!kernelExpressionEquals(goal.target, value.claimType)) {
                throw new AlgebraFormalDelegationError(
                    'CLAIM_TARGET_MISMATCH',
                    'formalSyzygy.goal',
                    'Goal differs from the selected formal syzygy equation'
                );
            }
            return value.basis;
        },
        serializeInput: basis => serializeCoreLfWorkspaceCanonicalJson({
            basis: basis.basis.map(vector =>
                vector.components.map(algebraPolynomialText)
            )
        }, 'formalSyzygyInput'),
        serializeOutput: serializeSyzygies,
        interpret: ({ goal, computed }): AlgebraFormalComputationInterpretationInput =>
            serializeSyzygies(computed.value) === realization.selectedOutputData
                ? {
                    kind: 'claim',
                    summary: 'selected Schreyer generator is a syzygy',
                    claimType: goal.target
                }
                : {
                    kind: 'observation',
                    summary: 'Schreyer output differs from selected syzygy'
                }
    });
    return Object.freeze({ operations, realization, adapter });
}

const serializeResolution = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPolynomialSchreyerResolution<P, C, I>
): string => serializeCoreLfWorkspaceCanonicalJson({
    ranks: value.freeModules.map(module => module.rank),
    differentials: value.differentials.map(map => map.columns.map(column =>
        column.components.map(algebraPolynomialText)
    )),
    length: value.length,
    complete: value.complete
}, 'formalModuleResolution');

export interface AlgebraFormalModuleResolutionRealization<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_FINITE_MODULE_PROFILE.resolutionRevision;
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly relations:
        import('./algebra_polynomial_module').AlgebraPolynomialSubmodule<P, C, I>;
    readonly maximumLength: number;
    readonly selected: AlgebraPolynomialSchreyerResolution<P, C, I>;
    readonly selectedOutputData: string;
    readonly adjacentIndex: number;
    readonly claimType: KernelExpression;
}

export function algebraFormalResolutionDelegationBundle<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly relations:
        import('./algebra_polynomial_module').AlgebraPolynomialSubmodule<P, C, I>;
    readonly maximumLength: number;
    readonly selected: AlgebraPolynomialSchreyerResolution<P, C, I>;
    readonly adjacentIndex: number;
}) {
    if (
        !Number.isSafeInteger(input.adjacentIndex) ||
        input.adjacentIndex < 0 ||
        input.adjacentIndex + 1 >= input.selected.differentials.length
    ) {
        return invalidRealization(
            'formalResolution.adjacentIndex',
            'Selected adjacent differential pair is outside the resolution'
        );
    }
    const operations = algebraPolynomialModuleReferenceOperations(
        input.relations.module
    );
    const claimType = algebraFormalCompositeZeroClaimType({
        reifier: input.reifier,
        left: input.selected.differentials[input.adjacentIndex],
        right: input.selected.differentials[input.adjacentIndex + 1]
    });
    const selectedOutputData = serializeResolution(input.selected);
    const realization: AlgebraFormalModuleResolutionRealization<P, C, I> =
        Object.freeze({
            profileRevision:
                ALGEBRA_FORMAL_FINITE_MODULE_PROFILE.resolutionRevision,
            ...input,
            selectedOutputData,
            claimType
        });
    const adapter = defineAlgebraFormalComputationAdapter({
        id: `proof-cas.module-resolution/${input.relations.module.identity.id}`,
        revision: input.relations.module.identity.revision,
        operation: operations.resolution,
        normalizeRealization(value, path) {
            if (
                !record(value) ||
                value.profileRevision !==
                    ALGEBRA_FORMAL_FINITE_MODULE_PROFILE.resolutionRevision
            ) {
                return invalidRealization(
                    path,
                    'Expected one current formal resolution realization'
                );
            }
            const candidate = value as unknown as typeof realization;
            if (
                candidate.adjacentIndex !== input.adjacentIndex ||
                candidate.selectedOutputData !== selectedOutputData ||
                !kernelExpressionEquals(candidate.claimType, claimType)
            ) {
                return invalidRealization(
                    path,
                    'Formal resolution realization differs from the selected equation'
                );
            }
            return candidate;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            selected: serializeResolution(value.selected),
            adjacentIndex: value.adjacentIndex,
            claim: serializeCoreExpression(value.claimType)
        }, 'formalResolutionRealization'),
        acquire: (goal, value) => {
            if (!kernelExpressionEquals(goal.target, value.claimType)) {
                throw new AlgebraFormalDelegationError(
                    'CLAIM_TARGET_MISMATCH',
                    'formalResolution.goal',
                    'Goal differs from the selected adjacent-zero equation'
                );
            }
            return Object.freeze({
                relations: value.relations,
                maximumLength: value.maximumLength
            });
        },
        serializeInput: value => serializeCoreLfWorkspaceCanonicalJson({
            generators: value.relations.generators.map(vector =>
                vector.components.map(algebraPolynomialText)
            ),
            maximumLength: value.maximumLength
        }, 'formalResolutionInput'),
        serializeOutput: serializeResolution,
        interpret: ({ goal, computed }): AlgebraFormalComputationInterpretationInput =>
            serializeResolution(computed.value) === realization.selectedOutputData
                ? {
                    kind: 'claim',
                    summary: 'selected adjacent resolution maps compose to zero',
                    claimType: goal.target
                }
                : {
                    kind: 'observation',
                    summary: 'resolution output differs from selected complex'
                }
    });
    return Object.freeze({ operations, realization, adapter });
}
