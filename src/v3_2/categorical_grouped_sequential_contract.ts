/**
 * FIBRED-GROUPED-SEQUENTIAL-1 executable contract.
 *
 * This contract connects the completed dependency planner to the existing
 * comprehension, displayed-product, and displayed-structure owners. It adds
 * no Lambdapi declaration or rule and does not claim an equivalence between
 * the sequential and grouped total categories.
 */

export const CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT_REVISION =
    'FIBRED-GROUPED-SEQUENTIAL-1-FINITE-SIBLING-CONTRACT-1' as const;

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

export const CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT = deepFreeze({
    revision:
        CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT_REVISION,
    row: 'FIBRED-GROUPED-SEQUENTIAL-1',
    status: 'frozen-existing-authority-contract',
    input: {
        shape:
            'one base object slot plus a finite ordered block of ' +
            'two-or-more displayed siblings',
        minimumSiblingCount: 2,
        commonBaseRequired: true,
        dependencyAuthority: 'FIBRED-CONTEXT-0B generic dependency graph',
        genuineDependencyEdgeRejected: true
    },
    presentations: {
        sequential: {
            surface: 'k : K; b : B[k]; c : C[k]',
            firstExtension: 'Sigma_cat(B)',
            laterExtension:
                'Sigma_cat(Pullback_catd(C,projection-to-K))',
            finiteAlgorithm:
                'left-to-right Sigma extension with accumulated ' +
                'projection-to-base composition'
        },
        grouped: {
            surface: 'k : K; (b,c) : P(B,C)[k]',
            family:
                'left-associated transparent displayed-product fold',
            total: 'Sigma_cat(P(B,C))',
            finiteAlgorithm:
                'left-associated displayedProduct fold'
        }
    },
    objectConformance: {
        sequentialObject: '((k,b),c)',
        groupedObject: '(k,(b,c))',
        check:
            'each later sequential fibre and the grouped product fibre ' +
            'are related only by active runtime conversion',
        componentEvidence:
            'existing Sigma first projection and displayed-product ' +
            'component owners',
        totalCategoryEqualityClaimed: false,
        totalCategoryEquivalenceClaimed: false,
        arrowLevelTotalComparisonClaimed: false
    },
    existingAuthority: {
        dependency: [
            'planCoreCategoricalContextDependencies',
            'dependency-sensitive sibling rejection'
        ],
        comprehension: [
            'Sigma_cat',
            'Sigma_proj1_func',
            'Pullback_catd',
            'Struct_sigma'
        ],
        grouped: [
            'transparent P(B,C)',
            'Product_projL_funcd',
            'Product_projR_funcd',
            'Product_pair_funcd'
        ],
        generic: [
            'id_func',
            'comp_cat_fapp0',
            'Product_cat',
            'Product_pair',
            'Struct_sigma'
        ]
    },
    semanticDelta: {
        newLambdapiOwners: 0,
        newLambdapiRuntimeRules: 0,
        newLambdapiProofRules: 0,
        newIntrinsicCoreOwners: 0,
        browserProfilePromotion: false
    },
    failClosed: [
        'fewer than two siblings',
        'duplicate binding names',
        'foreign category or family handles',
        'displayed families over different bases',
        'a requested group containing a genuine dependency edge',
        'a component outside its expected fibre'
    ],
    doesNotProvide: [
        'generic total-category pullback',
        'runtime equality or equivalence of sequential and grouped totals',
        'Sigma first-projection arrow computation',
        'general dependent displayed bracket',
        'grouping across a genuine dependency edge',
        'arbitrary dependent target B[k,a]',
        'string parsing or acquisition',
        'browser or deployed profile',
        'bulk Lambdapi transfer'
    ]
} as const);

export function validateCoreCategoricalGroupedSequentialContract(): void {
    const contract = CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT;
    if (
        contract.revision !==
            CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT_REVISION ||
        contract.row !== 'FIBRED-GROUPED-SEQUENTIAL-1' ||
        contract.status !== 'frozen-existing-authority-contract' ||
        contract.input.minimumSiblingCount !== 2 ||
        !contract.input.genuineDependencyEdgeRejected ||
        contract.objectConformance.totalCategoryEqualityClaimed ||
        contract.objectConformance.totalCategoryEquivalenceClaimed ||
        contract.objectConformance.arrowLevelTotalComparisonClaimed ||
        Object.values(contract.semanticDelta).some(Boolean)
    ) {
        throw new Error(
            'FIBRED-GROUPED-SEQUENTIAL-1 contract drifted'
        );
    }
}
