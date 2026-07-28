/**
 * FIBRED-TRANSFD-1 executable contract for the first direct displayed-
 * transfor abstraction and its component/higher-cell consumers.
 *
 * This is a frontend/transfer contract over already-active v3.2 authority.
 * It authorizes no new Lambdapi owner, rewrite, or unification rule.
 */

export const CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT_REVISION =
    'FIBRED-TRANSFD-1-DIRECT-NEXT-HOM-CONTRACT-1' as const;

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

export const CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT = deepFreeze({
    revision: CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT_REVISION,
    row: 'FIBRED-TRANSFD-1',
    status: 'frozen-existing-authority-contract',
    surface: {
        method: 'displayedTransforLambda',
        provisionalNotation: 'λ k :^nd K. body',
        semanticResult: 'Transfd_cat(E,D,FF,GG)',
        callbackEvaluationCount: 1,
        callbackStoredAfterConstruction: false,
        primitiveCoreBinderModeAdded: false
    },
    supportedBody: {
        id: 'coherent-component-eta',
        surface: 'λ k :^nd K. eta[k]',
        lowering: 'eta',
        restriction:
            'eta must already be a closed coherent displayed transfor'
    },
    consumers: [
        {
            id: 'fibre-component',
            surface: 'eta[x]',
            lowering: 'tdapp0_fapp0(x,eta)'
        },
        {
            id: 'fibre-point',
            surface: 'eta[x][u]',
            lowering: 'tapp0_fapp0(u,tdapp0_fapp0(x,eta))'
        },
        {
            id: 'higher-naturality-cell',
            surface: 'eta[p][u]',
            lowering: 'tdapp1_int_cell(eta,p,u)'
        }
    ],
    classifierPresentations: {
        direct: 'Transfd_cat(E,D,FF,GG)',
        ordinaryNextHom:
            'Hom_cat(Transf_cat(K,Cat_cat,E,D),FF,GG)',
        sigmaPiNextHom:
            'Hom_cat(Pi_cat(Sigma_cat(E),' +
            'Sigma_proj1_pullback_catd(E,D)),FF,GG)',
        directOrdinaryCategoryRelation:
            'active-direct-second-hom-proof-rule',
        directOrdinaryRuntimeRelation:
            'category-not-equal-object-classifiers-equal',
        sigmaPiRuntimeRelation:
            'active-next-hom-and-sigma-uncurrying-reduction',
        preserveElaboratedPresentation: true
    },
    transferredExistingAuthority: {
        reusedScaleStress2b3Declarations: [
            'Transfd_cat',
            'Transfd',
            'tdapp0_fapp0'
        ],
        additionalSignatures: [
            'functord_transport_lhs_func',
            'functord_transport_rhs_func',
            'tdapp1_int_cell'
        ],
        runtimeRules: [
            'Hom_cat(Functord_cat(E,D),FF,GG) -> Transfd_cat(FF,GG)',
            'Obj(Transfd_cat(FF,GG)) -> ' +
                'Obj(Hom_cat(Transf_cat(K,Cat_cat,E,D),FF,GG))',
            'Hom_cat(Pi_cat(E),s,t) -> ' +
                'Transfd_cat(Const_catd(K,Terminal_cat),E,s,t)',
            'Sigma/Pi object-classifier uncurrying join',
            'Sigma/Pi next-hom uncurrying',
            'displayed component of vertical composition, direct facade',
            'displayed component of vertical composition, ordinary facade'
        ],
        proofRules: [
            'Hom_cat(Transf_cat(K,Cat_cat,E,D),FF,GG) ' +
                '=proof-time Transfd_cat(E,D,FF,GG)'
        ],
        genericRepresentation:
            'SCALE-STRESS-2B3 declaration evidence plus generic ' +
            'declaration/runtime/proof engines'
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
        'wrong displayed-functor endpoints',
        'escaped direct base slot',
        'foreign callback term',
        'arbitrary pointwise family without coherence',
        'whole displayed-functor laxity synthesis'
    ],
    doesNotProvide: [
        'arbitrary pointwise-to-coherent displayed-transfor synthesis',
        'general :^nd bracket compilation',
        'runtime collapse of Transfd_cat to ordinary next hom',
        'Sigma-total arrow action',
        'whole displayed-functor laxity transfor',
        'dependent displayed codomain abstraction',
        'string parsing',
        'browser or deployed profile',
        'bulk Lambdapi transfer'
    ]
} as const);

export function validateCoreCategoricalFibredTransfdContract(): void {
    const contract = CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT;
    if (
        contract.revision !==
            CORE_CATEGORICAL_FIBRED_TRANSFD_CONTRACT_REVISION ||
        contract.row !== 'FIBRED-TRANSFD-1' ||
        contract.status !== 'frozen-existing-authority-contract' ||
        contract.surface.method !== 'displayedTransforLambda' ||
        contract.surface.callbackEvaluationCount !== 1 ||
        contract.surface.callbackStoredAfterConstruction ||
        contract.surface.primitiveCoreBinderModeAdded ||
        contract.supportedBody.id !== 'coherent-component-eta' ||
        contract.consumers.map(consumer => consumer.id).join(',') !==
            'fibre-component,fibre-point,higher-naturality-cell' ||
        contract.classifierPresentations
            .directOrdinaryRuntimeRelation !==
            'category-not-equal-object-classifiers-equal' ||
        Object.values(contract.semanticDelta).some(Boolean)
    ) {
        throw new Error(
            'FIBRED-TRANSFD-1 direct/next-hom contract drifted'
        );
    }
}
