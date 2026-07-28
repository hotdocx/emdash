/**
 * Frozen FIBRED-DEPENDENT-TARGET-1 contract.
 *
 * This is an existing-authority TypeScript transfer and end-user consumer.
 * It adds no Lambdapi declaration, runtime rule, proof rule, or Core binder
 * mode. Two runtime subjects require the exact active proof-time category
 * presentation rule; that rule is never installed in runtime conversion.
 */

export const
CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CONTRACT_REVISION =
    'FIBRED-DEPENDENT-TARGET-1-CONTRACT-1' as const;

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

export const CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CONTRACT =
deepFreeze({
    revision:
        CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CONTRACT_REVISION,
    row: 'FIBRED-DEPENDENT-TARGET-1',
    decisions: Object.freeze([
        'D-DTTLF-USABILITY-007',
        'D-DTTLF-USABILITY-007A',
        'D-DTTLF-USABILITY-007B'
    ]),
    status: 'frozen-existing-authority-contract',
    transfer: {
        declarations: [
            'Hom',
            'Op_cat',
            'Functord',
            'fapp0_func',
            'Functor_cat_func',
            'Functor_cat_fapp0_func',
            'Catd_cat_func',
            'Pi_func',
            'Pi_int_funcd',
            'Pi_pullback_funcd'
        ],
        prerequisiteRuntimeRules: [
            'categorical.dependent-target.opposite-object',
            'categorical.dependent-target.fixed-evaluation-object',
            'categorical.dependent-target.functor-category-first-object',
            'categorical.dependent-target.functor-category-second-object',
            'categorical.dependent-target.constant-pullback',
            'categorical.dependent-target.section-functor-object',
            'categorical.dependent-target.displayed-hom-category'
        ],
        consumerRuntimeRules: [
            'categorical.dependent-target.package-component',
            'categorical.dependent-target.pullback-fold',
            'categorical.dependent-target.pullback-component'
        ],
        proofRules: [
            'categorical.dependent-target.category-presentation'
        ],
        directlyCheckedRuntimeRules: [
            'categorical.dependent-target.opposite-object',
            'categorical.dependent-target.fixed-evaluation-object',
            'categorical.dependent-target.functor-category-first-object',
            'categorical.dependent-target.functor-category-second-object',
            'categorical.dependent-target.constant-pullback',
            'categorical.dependent-target.section-functor-object',
            'categorical.dependent-target.displayed-hom-category',
            'categorical.dependent-target.pullback-fold'
        ],
        proofCheckedRuntimeRules: [
            'categorical.dependent-target.package-component',
            'categorical.dependent-target.pullback-component'
        ],
        declarationCount: 10,
        runtimeRuleCount: 10,
        proofRuleCount: 1,
        typedPatternWildcardRules: [
            'categorical.dependent-target.section-functor-object'
        ],
        genericEnginesOnly: true,
        externalSubjectOracleUsed: false
    },
    surface: {
        profile: 'fibred-dependent-target-1',
        contravariantFamilyMethod: 'contravariantCategoryFamily',
        motiveFamilyMethod: 'dependentSectionMotive',
        targetFamilyMethod: 'dependentSectionTarget',
        callbackEvaluationCount: 1,
        callbackStoredAfterConstruction: false,
        primitiveCoreBinderModeAdded: false
    },
    consumer: {
        inputFamily: 'G : Functor(K,Op(Cat_cat))',
        motive: 'Pullback_catd(Catd_cat_func,G)',
        displayedSectionPackage: 'Pi_pullback_funcd(G)',
        target:
            'Sigma_catd_functord_catd(Pi_pullback_funcd(G))',
        targetBase: 'Sigma_cat(Pullback_catd(Catd_cat_func,G))',
        computedFibre: 'Pi_cat(G[k],M)',
        eta: 'λ z :^n Sigma(motive). s[z]'
    },
    semanticDelta: {
        newLambdapiOwners: 0,
        newLambdapiRuntimeRules: 0,
        newLambdapiProofRules: 0,
        newIntrinsicCoreOwners: 0,
        runtimeCategoryPresentationCollapse: false,
        browserProfilePromotion: false
    },
    failClosed: [
        'contravariant family with the wrong source or target category',
        'target-family request outside the explicit profile',
        'fibre point from the wrong total context',
        'dependent eta section over the wrong target family',
        'stale or unnecessary proof-subject exception',
        'arbitrary pointwise data presented as a coherent section'
    ],
    doesNotProvide: [
        'new kernel owner or rule',
        'runtime Functor_cat(K,Cat_cat)-to-Catd_cat(K) collapse',
        'external subject-reduction oracle',
        'arbitrary coherent-section synthesis',
        'general dependent displayed bracket',
        'complete :^fd or :^nd syntax',
        'new internal-Pi arrow action',
        'groupoidal closure',
        'string parsing',
        'browser or deployed profile',
        'bulk transfer',
        'general total-category theorem'
    ]
} as const);

export function
validateCoreCategoricalFibredDependentTargetContract(): void {
    const contract =
        CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CONTRACT;
    const transfer = contract.transfer;
    if (
        contract.revision !==
            CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CONTRACT_REVISION ||
        contract.row !== 'FIBRED-DEPENDENT-TARGET-1' ||
        contract.status !== 'frozen-existing-authority-contract' ||
        transfer.declarations.length !== transfer.declarationCount ||
        transfer.prerequisiteRuntimeRules.length !== 7 ||
        transfer.consumerRuntimeRules.length !== 3 ||
        transfer.prerequisiteRuntimeRules.length +
            transfer.consumerRuntimeRules.length !==
                transfer.runtimeRuleCount ||
        transfer.proofRules.length !== transfer.proofRuleCount ||
        transfer.typedPatternWildcardRules.join(',') !==
            'categorical.dependent-target.section-functor-object' ||
        transfer.directlyCheckedRuntimeRules.length !== 8 ||
        transfer.proofCheckedRuntimeRules.join(',') !==
            'categorical.dependent-target.package-component,' +
            'categorical.dependent-target.pullback-component' ||
        !transfer.genericEnginesOnly ||
        transfer.externalSubjectOracleUsed ||
        Object.values(contract.semanticDelta).some(Boolean)
    ) {
        throw new Error(
            'FIBRED-DEPENDENT-TARGET-1 contract drifted'
        );
    }
}
