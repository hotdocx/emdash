/**
 * PATHOUT-TRUST-BOUNDARY-0A authority and dependency audit.
 *
 * This immutable record describes the smallest reviewed PathOut/PathInd
 * product profile over the active Emdash v3.2 authority. It installs no Core
 * declaration, rewrite rule, proof rule, syntax, browser API, or package
 * export. Source-byte and source-position checks live in the focused test so
 * this contributor artifact remains browser-safe and free of filesystem I/O.
 */

export const CORE_PATHOUT_TRUST_BOUNDARY_0A_REVISION =
    'PATHOUT-TRUST-BOUNDARY-0A-AUDIT-1' as const;

export type CorePathoutLibrarySlice =
    | 'foundation'
    | 'fixed-source-induction'
    | 'internalized-induction'
    | 'transitivity';

export type CorePathoutOwnerSourceKind =
    | 'symbol'
    | 'constant-symbol'
    | 'injective-symbol';

export type CorePathoutOwnerDisposition =
    | 'derived-library'
    | 'trusted-profile';

export interface CorePathoutOwnerAuditEntry {
    readonly order: number;
    readonly name: string;
    readonly line: number;
    readonly sourceKind: CorePathoutOwnerSourceKind;
    readonly hasBody: boolean;
    readonly sourceOpacity: 'transparent' | 'opaque';
    readonly slice: CorePathoutLibrarySlice;
    readonly disposition: CorePathoutOwnerDisposition;
}

export interface CorePathoutRuleAuditEntry {
    readonly order: number;
    readonly id: string;
    readonly line: number;
    readonly sourceKind: 'runtime-rule' | 'proof-unification-rule';
    readonly owner: string;
    readonly slice:
        | CorePathoutLibrarySlice
        | 'path-category-conformance';
    readonly disposition:
        | 'trusted-profile'
        | 'deferred-path-category-bridge';
}

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

const owner = (
    order: number,
    name: string,
    line: number,
    sourceKind: CorePathoutOwnerSourceKind,
    hasBody: boolean,
    slice: CorePathoutLibrarySlice
): CorePathoutOwnerAuditEntry => ({
    order,
    name,
    line,
    sourceKind,
    hasBody,
    sourceOpacity: hasBody ? 'transparent' : 'opaque',
    slice,
    disposition: hasBody ? 'derived-library' : 'trusted-profile'
});

const owners: readonly CorePathoutOwnerAuditEntry[] = [
    owner(0, 'Rep_catd_func', 13765, 'symbol', true, 'foundation'),
    owner(1, 'Rep_catd', 13773, 'symbol', true, 'foundation'),
    owner(2, 'Rep_transport_func', 13785, 'symbol', true, 'foundation'),
    owner(3, 'PathOut_cat', 18960, 'symbol', true, 'foundation'),
    owner(4, 'PathOut_cat_func', 18969, 'symbol', true, 'foundation'),
    owner(
        5,
        'PathOut_transport_func',
        18984,
        'symbol',
        true,
        'foundation'
    ),
    owner(
        6,
        'PathOutMotives_catd',
        19002,
        'symbol',
        true,
        'internalized-induction'
    ),
    owner(
        7,
        'PathOutPi_funcd',
        19018,
        'symbol',
        true,
        'internalized-induction'
    ),
    owner(
        8,
        'PathIndTgt_catd',
        19036,
        'symbol',
        true,
        'internalized-induction'
    ),
    owner(9, 'pathout_obj', 19047, 'symbol', true, 'foundation'),
    owner(
        10,
        'pathout_refl_obj',
        19056,
        'symbol',
        true,
        'foundation'
    ),
    owner(
        11,
        'pathout_refl_eval_func',
        19067,
        'symbol',
        true,
        'fixed-source-induction'
    ),
    owner(
        12,
        'PathOutReflEval_funcd',
        19080,
        'constant-symbol',
        false,
        'internalized-induction'
    ),
    owner(
        13,
        'pathout_refl_arrow',
        19100,
        'symbol',
        true,
        'foundation'
    ),
    owner(
        14,
        'pathout_refl_eval_base_func',
        19118,
        'symbol',
        true,
        'fixed-source-induction'
    ),
    owner(
        15,
        'pathout_motive_transport_obj',
        19139,
        'symbol',
        true,
        'internalized-induction'
    ),
    owner(
        16,
        'pathout_motive_transport_arrow',
        19160,
        'symbol',
        true,
        'internalized-induction'
    ),
    owner(
        17,
        'path_ind_sec',
        19181,
        'symbol',
        false,
        'fixed-source-induction'
    ),
    owner(
        18,
        'pathout_refl_arrow_sec',
        19193,
        'symbol',
        true,
        'fixed-source-induction'
    ),
    owner(
        19,
        'PathInd_src_catd',
        19210,
        'symbol',
        true,
        'fixed-source-induction'
    ),
    owner(
        20,
        'PathInd_tgt_catd',
        19218,
        'symbol',
        true,
        'fixed-source-induction'
    ),
    owner(
        21,
        'path_ind_func_fapp0',
        19227,
        'symbol',
        false,
        'fixed-source-induction'
    ),
    owner(
        22,
        'PathInd_func',
        19242,
        'constant-symbol',
        false,
        'fixed-source-induction'
    ),
    owner(
        23,
        'PathInd_transfd',
        19281,
        'constant-symbol',
        false,
        'internalized-induction'
    ),
    owner(
        24,
        'PathIndSrc_catd',
        19296,
        'symbol',
        true,
        'internalized-induction'
    ),
    owner(
        25,
        'PathIndSrc_transport_func',
        19309,
        'symbol',
        true,
        'internalized-induction'
    ),
    owner(
        26,
        'PathInd_funcd',
        19332,
        'symbol',
        true,
        'internalized-induction'
    ),
    owner(
        27,
        'CompTarget_catd',
        19363,
        'injective-symbol',
        true,
        'transitivity'
    ),
    owner(
        28,
        'CompTarget_fapp1_func',
        19381,
        'symbol',
        true,
        'transitivity'
    ),
    owner(
        29,
        'CompMotive_catd',
        19401,
        'symbol',
        true,
        'transitivity'
    ),
    owner(
        30,
        'path_comp_sec',
        19687,
        'symbol',
        true,
        'transitivity'
    ),
    owner(
        31,
        'path_comp_func',
        19701,
        'symbol',
        true,
        'transitivity'
    ),
    owner(
        32,
        'pathout_pi_transport_func',
        19734,
        'symbol',
        true,
        'internalized-induction'
    ),
    owner(
        33,
        'PathIndTgt_transport_func',
        19751,
        'symbol',
        true,
        'internalized-induction'
    )
];

const rules: readonly CorePathoutRuleAuditEntry[] = [
    {
        order: 0,
        id: 'pathout-refl-eval-component',
        line: 19084,
        sourceKind: 'runtime-rule',
        owner: 'PathOutReflEval_funcd',
        slice: 'internalized-induction',
        disposition: 'trusted-profile'
    },
    {
        order: 1,
        id: 'path-ind-section-object-action',
        line: 19234,
        sourceKind: 'runtime-rule',
        owner: 'path_ind_func_fapp0',
        slice: 'fixed-source-induction',
        disposition: 'trusted-profile'
    },
    {
        order: 2,
        id: 'path-ind-functor-component',
        line: 19248,
        sourceKind: 'runtime-rule',
        owner: 'PathInd_func',
        slice: 'fixed-source-induction',
        disposition: 'trusted-profile'
    },
    {
        order: 3,
        id: 'path-ind-transfd-component',
        line: 19409,
        sourceKind: 'runtime-rule',
        owner: 'PathInd_transfd',
        slice: 'internalized-induction',
        disposition: 'trusted-profile'
    },
    {
        order: 4,
        id: 'path-ind-point-computation',
        line: 19418,
        sourceKind: 'runtime-rule',
        owner: 'path_ind_sec',
        slice: 'fixed-source-induction',
        disposition: 'trusted-profile'
    },
    {
        order: 5,
        id: 'path-ind-sigma-pullback-computation',
        line: 19441,
        sourceKind: 'runtime-rule',
        owner: 'path_ind_sec',
        slice: 'transitivity',
        disposition: 'trusted-profile'
    },
    {
        order: 6,
        id: 'path-category-reflexive-component-join',
        line: 19455,
        sourceKind: 'proof-unification-rule',
        owner: 'fib_cov_transf',
        slice: 'path-category-conformance',
        disposition: 'deferred-path-category-bridge'
    }
];

const rawAudit = {
    revision: CORE_PATHOUT_TRUST_BOUNDARY_0A_REVISION,
    row: 'PATHOUT-TRUST-BOUNDARY-0A',
    status: 'completed-read-only-trust-boundary-audit',
    authority: {
        moduleId: 'emdash.emdash3_2',
        source: {
            path: 'emdash2/emdash3_2.lp',
            sha256:
                'sha256:' +
                '0a117742d326bad82fe72cc73c624a0c174e3b48dd4047ebd8f6ed6ff7837860'
        },
        checks: {
            path: 'emdash2/emdash3_2_checks.lp',
            sha256:
                'sha256:' +
                'fbbe7ed4b7675c46ad79f65e2f6799dfc3c87b9287b593e6f1f0e1bd8e37f26a',
            selectedEvidenceRanges: [
                {
                    firstLine: 6976,
                    lastLine: 6977,
                    purpose: 'representable-precomposition'
                },
                {
                    firstLine: 11339,
                    lastLine: 11696,
                    purpose: 'fixed-internalized-and-transitivity-induction'
                },
                {
                    firstLine: 12456,
                    lastLine: 12542,
                    purpose: 'internalized-source-and-target-transport'
                },
                {
                    firstLine: 14685,
                    lastLine: 15046,
                    purpose: 'pathout-construction-and-arrow-action'
                }
            ]
        },
        method:
            'exact-byte-pin-plus-source-position-owner-rule-and-' +
            'typescript-provider-inventory;no-general-source-parser'
    },
    selectedOwners: owners,
    observedRules: rules,
    currentTransferAnchors: [
        {
            name: 'hom_int',
            provider:
                'categorical_displayed_nd_higher_foundation_transfer.ts'
        },
        {
            name: 'Sigma_cat',
            provider: 'directed_1a.ts'
        },
        {
            name: 'sigma_map_func',
            provider: 'categorical_displayed_chain_transfer.ts'
        },
        {
            name: 'hom_con',
            provider: 'categorical_mixed_action_transfer.ts'
        },
        {
            name: 'fib_cov_tapp0_func',
            provider: 'categorical_mixed_action_transfer.ts'
        },
        {
            name: 'Pi_pullback_funcd',
            provider: 'categorical_fibred_dependent_target_transfer.ts'
        },
        {
            name: 'sigma_transport_arrow',
            provider: 'directed_1b.ts'
        },
        {
            name: 'Sigma_proj1_pullback_catd',
            provider: 'categorical_displayed_chain_transfer.ts'
        },
        {
            name: 'section_pullback_func',
            provider: 'categorical_fibred_weaken_reindex_transfer.ts'
        }
    ],
    prerequisiteClosures: [
        {
            id: 'represented-source-action',
            status: 'missing-selected-profile-transfer',
            requiredBy: ['foundation', 'transitivity'],
            reusedTransferredOwners: ['hom_int'],
            transparentDefinitions: [],
            opaqueOwners: [
                {
                    name: 'hom_int_precomp_tele_func',
                    line: 8427,
                    sourceKind: 'symbol'
                },
                {
                    name: 'hom_int_precomp_func',
                    line: 8438,
                    sourceKind: 'symbol'
                }
            ],
            runtimeRules: [
                { id: 'hom-int-precomp-full-action', line: 8445 },
                { id: 'hom-int-precomp-capped-action', line: 8449 },
                { id: 'hom-int-precomp-tele-application', line: 8453 }
            ],
            proofRules: [
                { id: 'hom-int-precomp-projection-order', line: 8463 }
            ],
            excludedAuxiliaryDefinitions: []
        },
        {
            id: 'sigma-totalization-functor-action',
            status: 'missing-selected-profile-transfer',
            requiredBy: ['foundation'],
            reusedTransferredOwners: ['Sigma_cat', 'sigma_map_func'],
            transparentDefinitions: [],
            opaqueOwners: [
                {
                    name: 'Sigma_func',
                    line: 12801,
                    sourceKind: 'injective-symbol'
                }
            ],
            runtimeRules: [
                { id: 'sigma-func-object', line: 12803 },
                { id: 'sigma-func-capped-action', line: 13148 }
            ],
            proofRules: [],
            excludedAuxiliaryDefinitions: [],
            deferredHigherAction: {
                owner: 'sigma_map_transf',
                ownerLine: 13138,
                ruleLine: 13154,
                reason:
                    'not-required-by-the-smallest-object-and-capped-' +
                    'arrow-foundation;reassess-for-internalized-higher-' +
                    'action'
            }
        },
        {
            id: 'covariant-fibre-transport',
            status: 'missing-selected-profile-transfer',
            requiredBy: ['fixed-source-induction', 'transitivity'],
            reusedTransferredOwners: ['hom_con', 'fib_cov_tapp0_func'],
            transparentDefinitions: [
                {
                    name: 'FibCov_target_catd',
                    line: 13923,
                    sourceKind: 'symbol'
                }
            ],
            opaqueOwners: [
                {
                    name: 'fib_cov_int',
                    line: 13948,
                    sourceKind: 'constant-symbol'
                },
                {
                    name: 'fib_cov_src_func',
                    line: 13952,
                    sourceKind: 'symbol'
                },
                {
                    name: 'fib_cov_transf',
                    line: 13959,
                    sourceKind: 'injective-symbol'
                }
            ],
            runtimeRules: [
                { id: 'fib-cov-package-component', line: 13965 },
                { id: 'fib-cov-component-object', line: 13975 },
                { id: 'fib-cov-section-point', line: 13979 }
            ],
            proofRules: [],
            excludedAuxiliaryDefinitions: [
                {
                    name: 'FibCov_source_catd',
                    line: 13933,
                    reason:
                        'readable-alias-not-in-selected-typed-or-lexical-' +
                        'closure'
                }
            ]
        },
        {
            id: 'sigma-total-transfd-uncurrying',
            status: 'isolated-qualification-not-selected-profile-transfer',
            requiredBy: ['internalized-induction'],
            reusedTransferredOwners: [],
            transparentDefinitions: [],
            opaqueOwners: [
                {
                    name: 'Sigma_transfd_funcd',
                    line: 13360,
                    sourceKind: 'constant-symbol'
                }
            ],
            runtimeRules: [
                { id: 'sigma-transfd-object-component', line: 14516 }
            ],
            proofRules: [],
            excludedAuxiliaryDefinitions: [],
            isolatedEvidence:
                'scale_stress_2b3_representation.ts'
        }
    ],
    smallestProfiles: {
        foundation: {
            owners: [
                'Rep_catd_func',
                'Rep_catd',
                'Rep_transport_func',
                'PathOut_cat',
                'PathOut_cat_func',
                'PathOut_transport_func',
                'pathout_obj',
                'pathout_refl_obj',
                'pathout_refl_arrow'
            ],
            rules: [],
            prerequisiteClosures: [
                'represented-source-action',
                'sigma-totalization-functor-action'
            ]
        },
        fixedSourceInduction: {
            addsOwners: [
                'pathout_refl_eval_func',
                'pathout_refl_eval_base_func',
                'path_ind_sec',
                'pathout_refl_arrow_sec',
                'PathInd_src_catd',
                'PathInd_tgt_catd',
                'path_ind_func_fapp0',
                'PathInd_func'
            ],
            addsRules: [
                'path-ind-section-object-action',
                'path-ind-functor-component',
                'path-ind-point-computation',
                'path-ind-sigma-pullback-computation'
            ],
            addsPrerequisiteClosures: ['covariant-fibre-transport']
        },
        internalizedInduction: {
            addsOwners: [
                'PathOutMotives_catd',
                'PathOutPi_funcd',
                'PathIndTgt_catd',
                'PathOutReflEval_funcd',
                'pathout_motive_transport_obj',
                'pathout_motive_transport_arrow',
                'PathInd_transfd',
                'PathIndSrc_catd',
                'PathIndSrc_transport_func',
                'PathInd_funcd',
                'pathout_pi_transport_func',
                'PathIndTgt_transport_func'
            ],
            addsRules: [
                'pathout-refl-eval-component',
                'path-ind-transfd-component'
            ],
            addsPrerequisiteClosures: [
                'sigma-total-transfd-uncurrying'
            ]
        },
        transitivity: {
            addsOwners: [
                'CompTarget_catd',
                'CompTarget_fapp1_func',
                'CompMotive_catd',
                'path_comp_sec',
                'path_comp_func'
            ],
            addsRules: [],
            addsPrerequisiteClosures: []
        }
    },
    excludedAuthority: [
        {
            firstLine: 19455,
            lastLine: 19475,
            kind: 'proof-rule',
            reason:
                'observed-but-deferred-path-category-reflexive-join'
        },
        {
            firstLine: 19488,
            lastLine: 19673,
            kind: 'transparent-path-category-comparison-library',
            reason:
                'not-required-by-selected-generic-pathout-pathind-or-' +
                'transitivity-profile'
        }
    ],
    trustBoundary: {
        genericKernel:
            'existing-backend-neutral-lf-core-checker-and-rule-engines',
        profile:
            'sealed-provenance-pinned-opaque-owners-and-exact-rules',
        library:
            'transparent-definitions-and-checked-proof-terms-only',
        presentation: 'later-thin-typed-text-and-reviewer-facades',
        ordinaryLibraryCanDeclareTransparentDefinitions: true,
        ordinaryLibraryCanDeclareOpaqueOwners: false,
        ordinaryLibraryCanInstallRuntimeRules: false,
        ordinaryLibraryCanInstallProofRules: false,
        profileRuleCapability: 'sealed-profile-construction-only',
        lambdapiRuntimeRequired: false,
        deterministicLambdapiEmission:
            'optional-backend-and-required-bounded-conformance-oracle'
    },
    continuation: {
        nextRow: 'PATHOUT-LIBRARY-FOUNDATION-1B',
        semanticImplementationAuthorizedByThisAudit: false,
        requiredFirstAction:
            'freeze-a-separate-foundation-proposal-over-represented-' +
            'source-and-sigma-totalization-action-prerequisites'
    },
    productEffects: []
} as const;

export const CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT =
    deepFreeze(rawAudit);

export function validateCorePathoutTrustBoundary0aAudit(): void {
    const audit = CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT;
    const ownerNames = audit.selectedOwners.map(entry => entry.name);
    const ruleIds = audit.observedRules.map(entry => entry.id);
    const ownerLines = audit.selectedOwners.map(entry => entry.line);
    const ruleLines = audit.observedRules.map(entry => entry.line);
    const closures = audit.prerequisiteClosures.map(entry => entry.id);
    const strictlyIncreasing = (values: readonly number[]): boolean =>
        values.every((value, index) =>
            index === 0 || values[index - 1] < value
        );

    if (
        audit.revision !== 'PATHOUT-TRUST-BOUNDARY-0A-AUDIT-1' ||
        audit.selectedOwners.length !== 34 ||
        new Set(ownerNames).size !== ownerNames.length ||
        !strictlyIncreasing(ownerLines) ||
        audit.observedRules.length !== 7 ||
        new Set(ruleIds).size !== ruleIds.length ||
        !strictlyIncreasing(ruleLines) ||
        audit.selectedOwners.some(entry =>
            entry.hasBody !== (entry.disposition === 'derived-library') ||
            entry.hasBody !== (entry.sourceOpacity === 'transparent')
        ) ||
        closures.join(',') !==
            'represented-source-action,sigma-totalization-functor-action,' +
            'covariant-fibre-transport,sigma-total-transfd-uncurrying' ||
        audit.productEffects.length !== 0 ||
        audit.continuation.semanticImplementationAuthorizedByThisAudit ||
        audit.trustBoundary.ordinaryLibraryCanDeclareOpaqueOwners ||
        audit.trustBoundary.ordinaryLibraryCanInstallRuntimeRules ||
        audit.trustBoundary.ordinaryLibraryCanInstallProofRules
    ) {
        throw new Error(
            'PATHOUT-TRUST-BOUNDARY-0A immutable audit drifted'
        );
    }
}
