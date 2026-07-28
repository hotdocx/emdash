/**
 * FIBRED-BINDER-1 executable contract for the first direct displayed-functor
 * abstraction.
 *
 * This is a frontend/transfer contract over already-active v3.2 authority.
 * It authorizes no new Lambdapi owner, rewrite, or unification rule.
 */

export const CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT_REVISION =
    'FIBRED-BINDER-1-DIRECT-NESTED-CONTRACT-1' as const;

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

export const CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT = deepFreeze({
    revision: CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT_REVISION,
    row: 'FIBRED-BINDER-1',
    status: 'frozen-existing-authority-contract',
    surface: {
        method: 'displayedFunctorLambda',
        provisionalNotation: 'λ a :^fd E. body',
        hiddenTelescope:
            'λ (k :^n K; a :^f E[k]). body[k,a]',
        callbackEvaluationCount: 1,
        callbackStoredAfterConstruction: false,
        primitiveCoreBinderModeAdded: false
    },
    supportedBodies: [
        {
            id: 'identity',
            surface: 'λ a :^fd E. a',
            lowering: 'id_funcd(E)'
        },
        {
            id: 'eta',
            surface: 'λ a :^fd E. FF[a]',
            lowering: 'FF'
        },
        {
            id: 'composition',
            surface: 'λ a :^fd E. GG[FF[a]]',
            lowering: 'comp_fapp0(Catd_cat(K),GG,FF)'
        }
    ],
    classifierPresentations: {
        direct: 'Functord_cat(E,D)',
        nested:
            'Pi_cat(Sigma_cat(E),Sigma_proj1_pullback_catd(E,D))',
        proofTimeRelation: 'active-sigma-pi-uncurrying-unification',
        runtimeRelation: 'intentionally-not-equal',
        preserveElaboratedPresentation: true
    },
    reusedAuthority: {
        declarations: [
            'Catd',
            'Sigma_proj1_pullback_catd',
            'Functord_cat',
            'Pi_cat',
            'Sigma_cat',
            'id_funcd',
            'comp_fapp0'
        ],
        proofRules: [
            'sigma-pi-uncurrying'
        ],
        runtimeRules: [
            'displayed-functor-composition-point-projection',
            'functor-composition-object-projection'
        ],
        genericRepresentation:
            'SCALE-STRESS-2A source-ordered declaration/proof fragment'
    },
    semanticDelta: {
        newLambdapiOwners: 0,
        newLambdapiRuntimeRules: 0,
        newLambdapiProofRules: 0,
        newIntrinsicCoreOwners: 0,
        browserProfilePromotion: false
    },
    failClosed: [
        'wrong displayed base',
        'wrong source or target family',
        'escaped direct fibre slot',
        'foreign callback term',
        'non-chain displayed body',
        'displayed transfor abstraction',
        'genuinely fibre-dependent target B[k,a]'
    ],
    doesNotProvide: [
        ':^nd abstraction',
        'general dependent displayed bracket',
        'displayed weakening or exchange lowering',
        'grouped-versus-sequential context conformance',
        'runtime collapse of Pi_cat to Functord_cat',
        'string parsing',
        'browser or deployed profile',
        'bulk Lambdapi transfer'
    ]
} as const);

export function validateCoreCategoricalFibredBinderContract(): void {
    const contract = CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT;
    if (
        contract.revision !==
            CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT_REVISION ||
        contract.row !== 'FIBRED-BINDER-1' ||
        contract.status !== 'frozen-existing-authority-contract' ||
        contract.surface.method !== 'displayedFunctorLambda' ||
        contract.surface.callbackEvaluationCount !== 1 ||
        contract.surface.callbackStoredAfterConstruction ||
        contract.surface.primitiveCoreBinderModeAdded ||
        contract.classifierPresentations.proofTimeRelation !==
            'active-sigma-pi-uncurrying-unification' ||
        contract.classifierPresentations.runtimeRelation !==
            'intentionally-not-equal' ||
        contract.supportedBodies.map(body => body.id).join(',') !==
            'identity,eta,composition' ||
        Object.values(contract.semanticDelta).some(Boolean)
    ) {
        throw new Error(
            'FIBRED-BINDER-1 direct/nested contract drifted'
        );
    }
}
