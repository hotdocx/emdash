/**
 * Frozen FIBRED-WEAKEN-REINDEX-1 contract.
 *
 * This is an existing-authority frontend/transfer slice. It adds no
 * Lambdapi declaration, runtime rule, proof rule, or new Core binder mode.
 */

export const CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT_REVISION =
    'FIBRED-WEAKEN-REINDEX-1-CONTRACT-1' as const;

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        Object.freeze(value);
    }
    return value;
};

export const CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT =
deepFreeze({
    revision:
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT_REVISION,
    row: 'FIBRED-WEAKEN-REINDEX-1',
    status: 'frozen-existing-authority-contract',
    qualificationCases: Object.freeze([2, 3]),
    transfer: {
        declarations: [
            'Pullback_catd_func',
            'Obj_func',
            'section_pullback_func',
            'section_pullback_sec'
        ],
        prerequisiteRuntimeRules: [
            'constant-displayed-family-object',
            'sigma-projection-pullback-fold'
        ],
        consumerRuntimeRules: [
            'pullback-functor-object',
            'pullback-functor-hom-component',
            'section-pullback-object',
            'section-pullback-component'
        ],
        runtimeRuleCount: 6,
        proofRules: Object.freeze([]),
        genericEnginesOnly: true
    },
    surface: {
        profile: 'fibred-weaken-reindex-1',
        contextualIndexMethod: 'indexOf',
        weakeningMethod: 'displayedFunctorLambda',
        reindexMethod: 'pullbackDisplayedFunctor',
        callbackEvaluationCount: 1,
        callbackStoredAfterConstruction: false,
        primitiveCoreBinderModeAdded: false
    },
    weakening: {
        surface:
            'λ k :^n K. λ a :^f E[k]. s[k]',
        directSurface:
            'λ a :^fd E. s[indexOf(a)]',
        lowering:
            'section_pullback_func(Sigma_proj1_func(E),D)[s]',
        fibreUses: 0,
        hiddenBaseUses: 1,
        closedSectionRequired: true,
        closedPointProjection:
            'Const_func(E[k],D[k],s[k])'
    },
    reindexing: {
        surface:
            'σ^*FF : Functord(σ^*E,σ^*D)',
        lowering:
            'fapp1_fapp0(Pullback_catd_func(σ),E,D,FF)',
        abstractionBeforeAfter:
            'structurally-equal-explicit-core',
        pointComputation:
            '(σ^*FF)[a](u) = FF[σ(a)](u)'
    },
    semanticDelta: {
        newLambdapiOwners: 0,
        newLambdapiRuntimeRules: 0,
        newLambdapiProofRules: 0,
        newIntrinsicCoreOwners: 0,
        browserProfilePromotion: false
    },
    failClosed: [
        'contextual index requested outside its active hidden base',
        'weakening section over the wrong base or target family',
        'unused displayed input without the exact closed-section body',
        'reindexing substitution with the wrong codomain',
        'reindexing a non-displayed-functor term',
        'arbitrary callback coherence'
    ],
    doesNotProvide: [
        'new kernel owner or rule',
        'primitive weakd',
        'general dependent displayed bracket',
        'arbitrary pointwise coherence synthesis',
        'section-arrow computation',
        'new global reindexing equality',
        'genuinely fibre-dependent target B[k,a]',
        'string parsing',
        'browser or deployed profile',
        'bulk transfer',
        'total-category comparison'
    ]
} as const);

export function
validateCoreCategoricalFibredWeakenReindexContract(): void {
    const contract =
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT;
    if (
        contract.revision !==
            CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT_REVISION ||
        contract.row !== 'FIBRED-WEAKEN-REINDEX-1' ||
        contract.status !== 'frozen-existing-authority-contract' ||
        contract.qualificationCases.join(',') !== '2,3' ||
        contract.transfer.declarations.join(',') !==
            'Pullback_catd_func,Obj_func,section_pullback_func,' +
            'section_pullback_sec' ||
        contract.transfer.prerequisiteRuntimeRules.join(',') !==
            'constant-displayed-family-object,' +
            'sigma-projection-pullback-fold' ||
        contract.transfer.consumerRuntimeRules.length !== 4 ||
        contract.transfer.runtimeRuleCount !== 6 ||
        contract.transfer.proofRules.length !== 0 ||
        !contract.transfer.genericEnginesOnly ||
        contract.weakening.fibreUses !== 0 ||
        contract.weakening.hiddenBaseUses !== 1 ||
        contract.reindexing.abstractionBeforeAfter !==
            'structurally-equal-explicit-core' ||
        Object.values(contract.semanticDelta).some(Boolean)
    ) {
        throw new Error(
            'FIBRED-WEAKEN-REINDEX-1 contract drifted'
        );
    }
}
