/**
 * Lightweight executable capability contract for DISPLAYED-BRACKET-1A.
 *
 * The evidence-heavy proposal and delegated review intentionally remain
 * separate immutable artifacts. Runtime code imports this acyclic contract
 * so loading the categorical program cannot recursively initialize the
 * historical proposal/review graph.
 */

export const CORE_CATEGORICAL_DISPLAYED_BRACKET_CONTRACT_REVISION =
    'DISPLAYED-BRACKET-1A-CONTRACT-1' as const;

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

export const CORE_CATEGORICAL_DISPLAYED_BRACKET_CONTRACT = deepFreeze({
    revision:
        CORE_CATEGORICAL_DISPLAYED_BRACKET_CONTRACT_REVISION,
    row: 'DISPLAYED-BRACKET-1A',
    status: 'approved-root-only-existing-authority-contract',
    approval: {
        reviewRevision: 'DISPLAYED-BRACKET-0A-REVIEWED-1',
        decisionId: 'D-DTTLF-USABILITY-009',
        decision: 'approved-as-proposed',
        implementationAuthorized: true,
        humanDecisionSupersedes: true
    },
    surface: {
        profile: 'fibred-displayed-bracket-1',
        abstractionMethod: 'displayedContextLambda',
        pairMethod: 'fibrePair',
        callbackEvaluationCount: 1,
        callbackStoredAfterConstruction: false,
        contextScope:
            'finite-nonempty-independent-sibling-block-over-common-base',
        dependencyFlagsSuppliedByUser: false
    },
    authority: {
        runtimeFoundation: 'fibred-weaken-reindex-1',
        typedPairIsConstructionIrOnly: true,
        existingDisplayedOwnersOnly: true
    },
    semanticDelta: {
        newLambdapiOwners: 0,
        newLambdapiRuntimeRules: 0,
        newLambdapiProofRules: 0,
        newIntrinsicCoreOwners: 0,
        ownerSpecificLfBranches: 0,
        browserProfilePromotion: false
    },
    withheld: [
        'genuine-dependent-chain-lowering',
        'dependent-target-profile-join',
        'general-nd-coherence',
        'sigma-arrow-action',
        'total-category-comparison',
        'parser-or-bulk-transfer',
        'browser-or-deployed-profile'
    ]
} as const);

export function validateCoreCategoricalDisplayedBracketContract(): void {
    const contract =
        CORE_CATEGORICAL_DISPLAYED_BRACKET_CONTRACT;
    if (
        contract.revision !==
            CORE_CATEGORICAL_DISPLAYED_BRACKET_CONTRACT_REVISION ||
        contract.row !== 'DISPLAYED-BRACKET-1A' ||
        contract.status !==
            'approved-root-only-existing-authority-contract' ||
        contract.approval.reviewRevision !==
            'DISPLAYED-BRACKET-0A-REVIEWED-1' ||
        contract.approval.decisionId !== 'D-DTTLF-USABILITY-009' ||
        contract.approval.decision !== 'approved-as-proposed' ||
        !contract.approval.implementationAuthorized ||
        !contract.approval.humanDecisionSupersedes ||
        contract.surface.profile !== 'fibred-displayed-bracket-1' ||
        contract.surface.callbackEvaluationCount !== 1 ||
        contract.surface.callbackStoredAfterConstruction ||
        contract.surface.dependencyFlagsSuppliedByUser ||
        contract.authority.runtimeFoundation !==
            'fibred-weaken-reindex-1' ||
        !contract.authority.typedPairIsConstructionIrOnly ||
        !contract.authority.existingDisplayedOwnersOnly ||
        Object.values(contract.semanticDelta).some(Boolean) ||
        !contract.withheld.includes(
            'genuine-dependent-chain-lowering'
        ) ||
        !contract.withheld.includes(
            'dependent-target-profile-join'
        )
    ) {
        throw new Error(
            'DISPLAYED-BRACKET-1A capability contract drifted'
        );
    }
}

validateCoreCategoricalDisplayedBracketContract();
