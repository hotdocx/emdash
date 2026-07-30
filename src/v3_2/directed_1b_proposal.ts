/**
 * Machine-readable H-DTTLF-02 proposal for the second directed-DTT slice.
 *
 * This is an authority inventory and review input only. It does not install
 * the proposed primitives, transparent definition, or runtime rules.
 */

import {
    CORE_DIRECTED_1A_REVIEW,
    CORE_LF_CONTINUATION_PROFILE_REVIEW,
    validateCoreDirected1aReview,
    validateCoreLfContinuationProfileReview
} from './continuation_review';
import {
    CORE_DIRECTED_1A_PROPOSAL,
    CoreDirected1aCandidateOwnerId
} from './directed_1a_proposal';
import {
    CORE_MVP_MANIFEST
} from './manifest';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    Plicity
} from './schema';

export type CoreDirected1bCandidateOwnerId =
    | 'decoded-dependent-pair'
    | 'dependent-pair'
    | 'sigma-first-projection'
    | 'sigma-transport-arrow'
    | 'sigma-telescope-transport';

export type CoreDirected1bExpressionOwnerId =
    | CoreOwnerId
    | CoreDirected1aCandidateOwnerId
    | CoreDirected1bCandidateOwnerId;

export type CoreDirected1bExpression =
    | {
        readonly tag: 'variable';
        readonly name: string;
    }
    | {
        readonly tag: 'type';
    }
    | {
        readonly tag: 'owner-application';
        readonly owner: CoreDirected1bExpressionOwnerId;
        readonly arguments: readonly CoreDirected1bExpression[];
    }
    | {
        readonly tag: 'call';
        readonly callee: CoreDirected1bExpression;
        readonly arguments: readonly {
            readonly plicity: Plicity;
            readonly value: CoreDirected1bExpression;
        }[];
    }
    | {
        readonly tag: 'pi' | 'lambda';
        readonly binder: {
            readonly name: string;
            readonly plicity: Plicity;
            readonly variation: 'functorial';
            readonly type: CoreDirected1bExpression;
        };
        readonly body: CoreDirected1bExpression;
    };

export interface CoreDirected1bTypedSlot {
    readonly name: string;
    readonly plicity: Plicity;
    readonly role: string;
    readonly type: CoreDirected1bExpression;
}

export interface CoreDirected1bOwnerProposal {
    readonly order: number;
    readonly owner: CoreDirected1bCandidateOwnerId;
    readonly activeAuthority:
        | 'inductive-type'
        | 'inductive-constructor'
        | 'injective-symbol'
        | 'transparent-definition';
    readonly candidateDisposition:
        | 'opaque-import'
        | 'transparent-checked-definition';
    readonly slots: readonly CoreDirected1bTypedSlot[];
    readonly result: CoreDirected1bExpression;
    readonly body?: CoreDirected1bExpression;
}

export type CoreDirected1bRuntimeRuleId =
    | 'directed.sigma-object.decode'
    | 'directed.sigma-first-projection.evaluate'
    | 'directed.sigma-telescope-fibre.evaluate';

export interface CoreDirected1bRuntimeRuleProposal {
    readonly order: number;
    readonly id: CoreDirected1bRuntimeRuleId;
    readonly authority: 'active-runtime-rule';
    readonly execution: 'catalog-scoped-reviewed-runtime';
    readonly variables: readonly CoreDirected1bTypedSlot[];
    readonly left: CoreDirected1bExpression;
    readonly right: CoreDirected1bExpression;
}

export interface CoreDirected1bProposalInput {
    readonly revision: 'DIRECTED-1B';
    readonly experimentId: 'DTTLF-DIRECTED-1B-E01';
    readonly status: 'proposal-awaiting-h-dttlf-02';
    readonly reviewGate: 'H-DTTLF-02';
    readonly consumer:
        'nested-telescope-pair-fibre-projection-and-total-transport';
    readonly owners: readonly CoreDirected1bOwnerProposal[];
    readonly runtimeRules: readonly CoreDirected1bRuntimeRuleProposal[];
    readonly proofTimeRules: readonly [];
    readonly runtimeExtensionPolicy: {
        readonly scope: 'directed-catalog-local';
        readonly insertionPoint:
            'reviewed-runtime-phase-before-frozen-mvp-program';
        readonly budget: 'shared-outer-lf-global-budget';
        readonly defaultLfProfile: 'unchanged';
        readonly arbitraryUserRules: false;
    };
    readonly backendProjectionPolicy: {
        readonly opaqueImports:
            'signature-checked-external-references';
        readonly transparentDefinitions:
            'checked-local-mirror-mapped-to-active-owner';
        readonly emittedShadowDeclarations: false;
        readonly activeDefinitionBody:
            'proposal-exact-and-lambdapi-oracle-checked';
    };
    readonly prerequisites: {
        readonly lfProfileReview: 'LF-PROFILE-1-REVIEWED';
        readonly directed1aReview: 'DIRECTED-1A-REVIEWED';
        readonly directed1aOwnerIds:
            readonly CoreDirected1aCandidateOwnerId[];
    };
    readonly preservedMvpProfile: {
        readonly revision: 'emdash-v3.2-mvp-1';
        readonly contentHash:
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0';
        readonly ownerIds: readonly string[];
        readonly runtimeRuleIds: readonly string[];
    };
    readonly explicitDeferrals: readonly string[];
    readonly nonEffects: readonly string[];
}

export interface CoreDirected1bLambdapiOwnerBinding {
    readonly order: number;
    readonly owner: CoreDirected1bCandidateOwnerId;
    readonly module: 'emdash.emdash3_2';
    readonly serializedName:
        | 'τΣ_'
        | 'Struct_sigma'
        | 'Sigma_proj1_func'
        | 'sigma_transport_arrow'
        | 'Sigma_catd_transport_func';
    readonly authority:
        | 'inductive-type'
        | 'inductive-constructor'
        | 'injective-symbol'
        | 'transparent-definition';
    readonly provenance: {
        readonly authorityPath: 'emdash2/emdash3_2.lp';
        readonly section: string;
        readonly sourceFragment: string;
        readonly auditedOn: '2026-07-24';
    };
}

export interface CoreDirected1bLambdapiRuleBinding {
    readonly order: number;
    readonly id: CoreDirected1bRuntimeRuleId;
    readonly module: 'emdash.emdash3_2';
    readonly authority: 'runtime-rule';
    readonly provenance: {
        readonly authorityPath: 'emdash2/emdash3_2.lp';
        readonly section: string;
        readonly sourceFragment: string;
        readonly auditedOn: '2026-07-24';
    };
}

export type CoreDirected1bProposalErrorCode =
    | 'INVALID_PROPOSAL_BOUNDARY'
    | 'INVALID_PREREQUISITE'
    | 'INVALID_OWNER_SET'
    | 'INVALID_EXPRESSION'
    | 'INVALID_DEFINITION_SET'
    | 'INVALID_RULE_SET'
    | 'INVALID_RUNTIME_POLICY'
    | 'INVALID_BACKEND_BINDINGS'
    | 'MVP_PROFILE_DRIFT'
    | 'PROPOSAL_DRIFT';

export class CoreDirected1bProposalError extends Error {
    constructor(
        public readonly code: CoreDirected1bProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirected1bProposalError';
    }
}

const variable = (name: string): CoreDirected1bExpression => ({
    tag: 'variable',
    name
});

const ownerApplication = (
    owner: CoreDirected1bExpressionOwnerId,
    ...arguments_: readonly CoreDirected1bExpression[]
): CoreDirected1bExpression => ({
    tag: 'owner-application',
    owner,
    arguments: arguments_
});

const call = (
    callee: CoreDirected1bExpression,
    ...arguments_: readonly {
        readonly plicity: Plicity;
        readonly value: CoreDirected1bExpression;
    }[]
): CoreDirected1bExpression => ({
    tag: 'call',
    callee,
    arguments: arguments_
});

const argument = (
    value: CoreDirected1bExpression,
    plicity: Plicity = 'explicit'
): {
    readonly plicity: Plicity;
    readonly value: CoreDirected1bExpression;
} => ({
    plicity,
    value
});

const binding = (
    tag: 'pi' | 'lambda',
    name: string,
    type: CoreDirected1bExpression,
    body: CoreDirected1bExpression,
    plicity: Plicity = 'explicit'
): CoreDirected1bExpression => ({
    tag,
    binder: {
        name,
        plicity,
        variation: 'functorial',
        type
    },
    body
});

const typedSlot = (
    name: string,
    plicity: Plicity,
    role: string,
    type: CoreDirected1bExpression
): CoreDirected1bTypedSlot => ({
    name,
    plicity,
    role,
    type
});

const TYPE: CoreDirected1bExpression = { tag: 'type' };
const groupoidUniverse = ownerApplication('groupoid-universe');
const categoryUniverse = ownerApplication('category-universe');
const categoryOfCategories =
    ownerApplication('category-of-categories');

const decode = (
    classifier: CoreDirected1bExpression
): CoreDirected1bExpression => ownerApplication('decode', classifier);

const objectClassifier = (
    category: CoreDirected1bExpression
): CoreDirected1bExpression =>
    ownerApplication('object-classifier', category);

const functorClassifier = (
    source: CoreDirected1bExpression,
    target: CoreDirected1bExpression
): CoreDirected1bExpression =>
    ownerApplication('functor-classifier', source, target);

const homClassifier = (
    category: CoreDirected1bExpression,
    source: CoreDirected1bExpression,
    target: CoreDirected1bExpression
): CoreDirected1bExpression =>
    ownerApplication('hom-classifier', category, source, target);

const objectType = (
    category: CoreDirected1bExpression
): CoreDirected1bExpression => decode(objectClassifier(category));

const displayedFamilyType = (
    base: CoreDirected1bExpression
): CoreDirected1bExpression => decode(objectClassifier(
    ownerApplication('displayed-category-category', base)
));

const constantCategoryFamily = (
    base: CoreDirected1bExpression
): CoreDirected1bExpression =>
    ownerApplication(
        'constant-displayed-family',
        base,
        categoryOfCategories
    );

const displayedFunctorType = (
    base: CoreDirected1bExpression,
    source: CoreDirected1bExpression,
    target: CoreDirected1bExpression
): CoreDirected1bExpression => decode(objectClassifier(
    ownerApplication(
        'displayed-functor-category',
        base,
        source,
        target
    )
));

const fibre = (
    base: CoreDirected1bExpression,
    family: CoreDirected1bExpression,
    point: CoreDirected1bExpression
): CoreDirected1bExpression => ownerApplication(
    'functor-object',
    base,
    categoryOfCategories,
    family,
    point
);

const familyObjectType = (
    base: CoreDirected1bExpression,
    family: CoreDirected1bExpression,
    point: CoreDirected1bExpression
): CoreDirected1bExpression => objectType(fibre(base, family, point));

const sigmaCategory = (
    base: CoreDirected1bExpression,
    family: CoreDirected1bExpression
): CoreDirected1bExpression =>
    ownerApplication('sigma-category', base, family);

const sigmaTelescopeFamily = (
    base: CoreDirected1bExpression,
    family: CoreDirected1bExpression,
    telescope: CoreDirected1bExpression
): CoreDirected1bExpression => ownerApplication(
    'sigma-telescope-family',
    base,
    family,
    telescope
);

const encodedPairFamily = (
    base: CoreDirected1bExpression,
    family: CoreDirected1bExpression
): CoreDirected1bExpression => binding(
    'lambda',
    'pairPoint',
    objectType(base),
    objectClassifier(fibre(base, family, variable('pairPoint')))
);

const dependentPair = (
    base: CoreDirected1bExpression,
    family: CoreDirected1bExpression,
    point: CoreDirected1bExpression,
    value: CoreDirected1bExpression
): CoreDirected1bExpression => ownerApplication(
    'dependent-pair',
    objectClassifier(base),
    encodedPairFamily(base, family),
    point,
    value
);

const familyTransportFunctor = (
    base: CoreDirected1bExpression,
    family: CoreDirected1bExpression,
    source: CoreDirected1bExpression,
    target: CoreDirected1bExpression,
    arrow: CoreDirected1bExpression
): CoreDirected1bExpression => ownerApplication(
    'functor-hom-capped',
    base,
    categoryOfCategories,
    family,
    source,
    target,
    arrow
);

const transportedObject = (
    base: CoreDirected1bExpression,
    family: CoreDirected1bExpression,
    source: CoreDirected1bExpression,
    target: CoreDirected1bExpression,
    arrow: CoreDirected1bExpression,
    value: CoreDirected1bExpression
): CoreDirected1bExpression => ownerApplication(
    'functor-object',
    fibre(base, family, source),
    fibre(base, family, target),
    familyTransportFunctor(base, family, source, target, arrow),
    value
);

const telescopePointFunctor = (
    base: CoreDirected1bExpression,
    family: CoreDirected1bExpression,
    telescope: CoreDirected1bExpression,
    point: CoreDirected1bExpression
): CoreDirected1bExpression => ownerApplication(
    'transfor-component-capped',
    base,
    categoryOfCategories,
    family,
    constantCategoryFamily(base),
    point,
    telescope
);

const K = variable('K');
const R = variable('R');
const E = variable('E');
const FF = variable('FF');
const x = variable('x');
const y = variable('y');
const k = variable('k');
const p = variable('p');
const r = variable('r');
const u = variable('u');

const pairFunctionType = (
    classifier: CoreDirected1bExpression
): CoreDirected1bExpression => binding(
    'pi',
    'pairIndex',
    decode(classifier),
    groupoidUniverse
);

const transportedR = transportedObject(K, R, x, y, p, r);
const pairX = dependentPair(K, R, x, r);
const pairY = dependentPair(K, R, y, transportedR);
const sigmaBase = sigmaCategory(K, R);
const telescopeFamily = sigmaTelescopeFamily(K, R, FF);
const telescopeSource = fibre(sigmaBase, telescopeFamily, pairX);
const telescopeTarget = fibre(sigmaBase, telescopeFamily, pairY);
const canonicalTransport = ownerApplication(
    'sigma-transport-arrow',
    K,
    R,
    x,
    y,
    p,
    r
);

const rawOwners: readonly CoreDirected1bOwnerProposal[] = [
    {
        order: 0,
        owner: 'decoded-dependent-pair',
        activeAuthority: 'inductive-type',
        candidateDisposition: 'opaque-import',
        slots: [
            typedSlot(
                'a',
                'implicit',
                'base-groupoid',
                groupoidUniverse
            ),
            typedSlot(
                'P',
                'explicit',
                'dependent-groupoid-family',
                pairFunctionType(variable('a'))
            )
        ],
        result: TYPE
    },
    {
        order: 1,
        owner: 'dependent-pair',
        activeAuthority: 'inductive-constructor',
        candidateDisposition: 'opaque-import',
        slots: [
            typedSlot(
                'a',
                'implicit',
                'base-groupoid',
                groupoidUniverse
            ),
            typedSlot(
                'P',
                'implicit',
                'dependent-groupoid-family',
                pairFunctionType(variable('a'))
            ),
            typedSlot(
                'pairFirst',
                'explicit',
                'first-component',
                decode(variable('a'))
            ),
            typedSlot(
                'pairSecond',
                'explicit',
                'second-component',
                decode(call(
                    variable('P'),
                    argument(variable('pairFirst'))
                ))
            )
        ],
        result: ownerApplication(
            'decoded-dependent-pair',
            variable('a'),
            variable('P')
        )
    },
    {
        order: 2,
        owner: 'sigma-first-projection',
        activeAuthority: 'injective-symbol',
        candidateDisposition: 'opaque-import',
        slots: [
            typedSlot(
                'K',
                'implicit',
                'base-category',
                categoryUniverse
            ),
            typedSlot(
                'E',
                'explicit',
                'displayed-family',
                displayedFamilyType(K)
            )
        ],
        result: decode(functorClassifier(
            sigmaCategory(K, E),
            K
        ))
    },
    {
        order: 3,
        owner: 'sigma-transport-arrow',
        activeAuthority: 'transparent-definition',
        candidateDisposition: 'opaque-import',
        slots: [
            typedSlot(
                'K',
                'implicit',
                'base-category',
                categoryUniverse
            ),
            typedSlot(
                'E',
                'explicit',
                'displayed-family',
                displayedFamilyType(K)
            ),
            typedSlot(
                'x',
                'implicit',
                'source-base-object',
                objectType(K)
            ),
            typedSlot(
                'y',
                'implicit',
                'target-base-object',
                objectType(K)
            ),
            typedSlot(
                'p',
                'explicit',
                'base-arrow',
                decode(homClassifier(K, x, y))
            ),
            typedSlot(
                'u',
                'explicit',
                'source-fibre-object',
                familyObjectType(K, E, x)
            )
        ],
        result: decode(homClassifier(
            sigmaCategory(K, E),
            dependentPair(K, E, x, u),
            dependentPair(
                K,
                E,
                y,
                transportedObject(K, E, x, y, p, u)
            )
        ))
    },
    {
        order: 4,
        owner: 'sigma-telescope-transport',
        activeAuthority: 'transparent-definition',
        candidateDisposition: 'transparent-checked-definition',
        slots: [
            typedSlot(
                'K',
                'implicit',
                'base-category',
                categoryUniverse
            ),
            typedSlot(
                'R',
                'implicit',
                'first-displayed-family',
                displayedFamilyType(K)
            ),
            typedSlot(
                'FF',
                'explicit',
                'dependent-cat-valued-telescope',
                displayedFunctorType(
                    K,
                    R,
                    constantCategoryFamily(K)
                )
            ),
            typedSlot(
                'x',
                'implicit',
                'source-base-object',
                objectType(K)
            ),
            typedSlot(
                'y',
                'implicit',
                'target-base-object',
                objectType(K)
            ),
            typedSlot(
                'p',
                'explicit',
                'base-arrow',
                decode(homClassifier(K, x, y))
            ),
            typedSlot(
                'r',
                'explicit',
                'source-first-fibre-object',
                familyObjectType(K, R, x)
            )
        ],
        result: decode(functorClassifier(
            telescopeSource,
            telescopeTarget
        )),
        body: ownerApplication(
            'functor-hom-capped',
            sigmaBase,
            categoryOfCategories,
            telescopeFamily,
            pairX,
            pairY,
            canonicalTransport
        )
    }
];

const ruleVariable = (
    name: string,
    role: string,
    type: CoreDirected1bExpression
): CoreDirected1bTypedSlot =>
    typedSlot(name, 'explicit', role, type);

const rawRules: readonly CoreDirected1bRuntimeRuleProposal[] = [
    {
        order: 0,
        id: 'directed.sigma-object.decode',
        authority: 'active-runtime-rule',
        execution: 'catalog-scoped-reviewed-runtime',
        variables: [
            ruleVariable('K', 'base-category', categoryUniverse),
            ruleVariable(
                'E',
                'displayed-family',
                displayedFamilyType(K)
            )
        ],
        left: objectType(sigmaCategory(K, E)),
        right: ownerApplication(
            'decoded-dependent-pair',
            objectClassifier(K),
            encodedPairFamily(K, E)
        )
    },
    {
        order: 1,
        id: 'directed.sigma-first-projection.evaluate',
        authority: 'active-runtime-rule',
        execution: 'catalog-scoped-reviewed-runtime',
        variables: [
            ruleVariable('K', 'base-category', categoryUniverse),
            ruleVariable(
                'E',
                'displayed-family',
                displayedFamilyType(K)
            ),
            ruleVariable('k', 'base-object', objectType(K)),
            ruleVariable(
                'u',
                'fibre-object',
                familyObjectType(K, E, k)
            )
        ],
        left: ownerApplication(
            'functor-object',
            sigmaCategory(K, E),
            K,
            ownerApplication('sigma-first-projection', K, E),
            dependentPair(K, E, k, u)
        ),
        right: k
    },
    {
        order: 2,
        id: 'directed.sigma-telescope-fibre.evaluate',
        authority: 'active-runtime-rule',
        execution: 'catalog-scoped-reviewed-runtime',
        variables: [
            ruleVariable('K', 'base-category', categoryUniverse),
            ruleVariable(
                'R',
                'first-displayed-family',
                displayedFamilyType(K)
            ),
            ruleVariable(
                'FF',
                'dependent-cat-valued-telescope',
                displayedFunctorType(
                    K,
                    R,
                    constantCategoryFamily(K)
                )
            ),
            ruleVariable('k', 'base-object', objectType(K)),
            ruleVariable(
                'r',
                'first-fibre-object',
                familyObjectType(K, R, k)
            )
        ],
        left: fibre(
            sigmaCategory(K, R),
            sigmaTelescopeFamily(K, R, FF),
            dependentPair(K, R, k, r)
        ),
        right: ownerApplication(
            'functor-object',
            fibre(K, R, k),
            categoryOfCategories,
            telescopePointFunctor(K, R, FF, k),
            r
        )
    }
];

const rawProposal: CoreDirected1bProposalInput = {
    revision: 'DIRECTED-1B',
    experimentId: 'DTTLF-DIRECTED-1B-E01',
    status: 'proposal-awaiting-h-dttlf-02',
    reviewGate: 'H-DTTLF-02',
    consumer:
        'nested-telescope-pair-fibre-projection-and-total-transport',
    owners: rawOwners,
    runtimeRules: rawRules,
    proofTimeRules: [],
    runtimeExtensionPolicy: {
        scope: 'directed-catalog-local',
        insertionPoint:
            'reviewed-runtime-phase-before-frozen-mvp-program',
        budget: 'shared-outer-lf-global-budget',
        defaultLfProfile: 'unchanged',
        arbitraryUserRules: false
    },
    backendProjectionPolicy: {
        opaqueImports: 'signature-checked-external-references',
        transparentDefinitions:
            'checked-local-mirror-mapped-to-active-owner',
        emittedShadowDeclarations: false,
        activeDefinitionBody:
            'proposal-exact-and-lambdapi-oracle-checked'
    },
    prerequisites: {
        lfProfileReview: 'LF-PROFILE-1-REVIEWED',
        directed1aReview: 'DIRECTED-1A-REVIEWED',
        directed1aOwnerIds: [
            'displayed-functor-category',
            'sigma-category',
            'sigma-telescope-family'
        ]
    },
    preservedMvpProfile: {
        revision: 'emdash-v3.2-mvp-1',
        contentHash:
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0',
        ownerIds: [
            'groupoid-universe',
            'category-universe',
            'decode',
            'object-classifier',
            'functor-classifier',
            'hom-classifier',
            'transfor-classifier',
            'hom-category',
            'transfor-category',
            'functor-object',
            'functor-hom-full',
            'functor-hom-capped',
            'transfor-component-full',
            'transfor-component-capped',
            'transfor-hom-full',
            'transfor-hom-capped'
        ],
        runtimeRuleIds: [
            'projection.functor-hom.evaluate',
            'projection.transfor-component.evaluate',
            'projection.transfor-hom.evaluate'
        ]
    },
    explicitDeferrals: [
        'general Sigma-category Hom normalization',
        'sigma-arrow construction and computation',
        'sigma-transport-arrow unfolding',
        'constant-family Sigma-to-product computation',
        'Sigma projection pullback and proof-time uncurrying',
        'section/internal-Pi and displayed-transfor uncurrying',
        'groupoidal Sigma path elimination and closure'
    ],
    nonEffects: [
        'does not extend CORE_OWNER_SCHEMAS',
        'does not extend LAMBDAPI_V32_OWNER_BINDINGS',
        'does not mutate CORE_MVP_MANIFEST or CORE_MVP_RUNTIME_PROGRAM',
        'does not alter the default LF-PROFILE-1 runtime component',
        'does not add arbitrary user rewrite rules',
        'does not enter src/v3_2/browser.ts',
        'does not authorize a termination, confluence, or subject-reduction claim'
    ]
};

const rawOwnerBindings: readonly CoreDirected1bLambdapiOwnerBinding[] = [
    {
        order: 0,
        owner: 'decoded-dependent-pair',
        module: 'emdash.emdash3_2',
        serializedName: 'τΣ_',
        authority: 'inductive-type',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section:
                '1a. Encoded dependent pairs, projections, and Sigma path views',
            sourceFragment: 'inductive τΣ_ [a : Grpd]',
            auditedOn: '2026-07-24'
        }
    },
    {
        order: 1,
        owner: 'dependent-pair',
        module: 'emdash.emdash3_2',
        serializedName: 'Struct_sigma',
        authority: 'inductive-constructor',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section:
                '1a. Encoded dependent pairs, projections, and Sigma path views',
            sourceFragment: '| Struct_sigma [a P]',
            auditedOn: '2026-07-24'
        }
    },
    {
        order: 2,
        owner: 'sigma-first-projection',
        module: 'emdash.emdash3_2',
        serializedName: 'Sigma_proj1_func',
        authority: 'injective-symbol',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '9a. Sigma totals, Sigma homs, and projection',
            sourceFragment: 'injective symbol Sigma_proj1_func',
            auditedOn: '2026-07-24'
        }
    },
    {
        order: 3,
        owner: 'sigma-transport-arrow',
        module: 'emdash.emdash3_2',
        serializedName: 'sigma_transport_arrow',
        authority: 'transparent-definition',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '9b. Sigma maps and canonical transport arrows',
            sourceFragment: 'symbol sigma_transport_arrow [K : Cat]',
            auditedOn: '2026-07-24'
        }
    },
    {
        order: 4,
        owner: 'sigma-telescope-transport',
        module: 'emdash.emdash3_2',
        serializedName: 'Sigma_catd_transport_func',
        authority: 'transparent-definition',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section:
                '9c. Families over Sigma totals and displayed-transfor ' +
                'uncurrying',
            sourceFragment: 'symbol Sigma_catd_transport_func [K : Cat]',
            auditedOn: '2026-07-24'
        }
    }
];

const rawRuleBindings: readonly CoreDirected1bLambdapiRuleBinding[] = [
    {
        order: 0,
        id: 'directed.sigma-object.decode',
        module: 'emdash.emdash3_2',
        authority: 'runtime-rule',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '9a. Sigma totals, Sigma homs, and projection',
            sourceFragment: 'rule τ (Obj (@Sigma_cat $K $E))',
            auditedOn: '2026-07-24'
        }
    },
    {
        order: 1,
        id: 'directed.sigma-first-projection.evaluate',
        module: 'emdash.emdash3_2',
        authority: 'runtime-rule',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '9a. Sigma totals, Sigma homs, and projection',
            sourceFragment:
                'rule fapp0 (Sigma_proj1_func $E) ' +
                '(Struct_sigma $k $u) ↪ $k;',
            auditedOn: '2026-07-24'
        }
    },
    {
        order: 2,
        id: 'directed.sigma-telescope-fibre.evaluate',
        module: 'emdash.emdash3_2',
        authority: 'runtime-rule',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section:
                '9c. Families over Sigma totals and displayed-transfor ' +
                'uncurrying',
            sourceFragment:
                '(@Sigma_catd_functord_catd $K $R $FF)',
            auditedOn: '2026-07-24'
        }
    }
];

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(item =>
            deepFreeze(item)
        );
        Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const fail = (
    code: CoreDirected1bProposalErrorCode,
    message: string
): never => {
    throw new CoreDirected1bProposalError(code, message);
};

const liveMvpIdentity = (): {
    readonly revision: string;
    readonly contentHash: string;
    readonly ownerIds: readonly string[];
    readonly runtimeRuleIds: readonly string[];
} => ({
    revision: CORE_MVP_MANIFEST.revision,
    contentHash: CORE_MVP_MANIFEST.contentHash,
    ownerIds: CORE_MVP_MANIFEST.owners.map(entry => entry.owner),
    runtimeRuleIds: CORE_MVP_MANIFEST.rules.map(rule => rule.id)
});

const PORTABLE_NAME = /^[A-Za-z][A-Za-z0-9_]*$/;

const validateExpression = (
    expression: CoreDirected1bExpression,
    availableOwners: ReadonlyMap<string, number>,
    availableVariables: ReadonlySet<string>,
    detail: string
): void => {
    if (expression.tag === 'type') return;

    if (expression.tag === 'variable') {
        if (!availableVariables.has(expression.name)) {
            fail(
                'INVALID_EXPRESSION',
                `${detail} refers to unavailable variable ` +
                `'${expression.name}'`
            );
        }
        return;
    }

    if (expression.tag === 'owner-application') {
        const arity = availableOwners.get(expression.owner);
        if (arity === undefined) {
            fail(
                'INVALID_EXPRESSION',
                `${detail} refers to unavailable owner ` +
                `'${expression.owner}'`
            );
        }
        if (expression.arguments.length !== arity) {
            fail(
                'INVALID_EXPRESSION',
                `${detail} applies '${expression.owner}' to ` +
                `${expression.arguments.length} arguments, expected ${arity}`
            );
        }
        expression.arguments.forEach((value, index) =>
            validateExpression(
                value,
                availableOwners,
                availableVariables,
                `${detail}, ${expression.owner} argument ${index}`
            )
        );
        return;
    }

    if (expression.tag === 'call') {
        if (expression.arguments.length === 0) {
            fail(
                'INVALID_EXPRESSION',
                `${detail} contains an empty generic call`
            );
        }
        validateExpression(
            expression.callee,
            availableOwners,
            availableVariables,
            `${detail}, call callee`
        );
        expression.arguments.forEach((entry, index) => {
            if (
                entry.plicity !== 'explicit' &&
                entry.plicity !== 'implicit'
            ) {
                fail(
                    'INVALID_EXPRESSION',
                    `${detail} has invalid call plicity at ${index}`
                );
            }
            validateExpression(
                entry.value,
                availableOwners,
                availableVariables,
                `${detail}, call argument ${index}`
            );
        });
        return;
    }

    if (
        !PORTABLE_NAME.test(expression.binder.name) ||
        availableVariables.has(expression.binder.name) ||
        expression.binder.variation !== 'functorial' ||
        (
            expression.binder.plicity !== 'explicit' &&
            expression.binder.plicity !== 'implicit'
        )
    ) {
        fail(
            'INVALID_EXPRESSION',
            `${detail} has an invalid or shadowing binder`
        );
    }
    validateExpression(
        expression.binder.type,
        availableOwners,
        availableVariables,
        `${detail}, binder type`
    );
    validateExpression(
        expression.body,
        availableOwners,
        new Set([...availableVariables, expression.binder.name]),
        `${detail}, binder body`
    );
};

const validateTypedTelescope = (
    slots: readonly CoreDirected1bTypedSlot[],
    availableOwners: ReadonlyMap<string, number>,
    detail: string
): ReadonlySet<string> => {
    const availableVariables = new Set<string>();
    slots.forEach((slot, index) => {
        if (
            !PORTABLE_NAME.test(slot.name) ||
            availableVariables.has(slot.name) ||
            slot.role.length === 0 ||
            (slot.plicity !== 'explicit' && slot.plicity !== 'implicit')
        ) {
            fail(
                'INVALID_EXPRESSION',
                `${detail} has an invalid slot at ${index}`
            );
        }
        validateExpression(
            slot.type,
            availableOwners,
            availableVariables,
            `${detail} slot ${slot.name} type`
        );
        availableVariables.add(slot.name);
    });
    return availableVariables;
};

export const CORE_DIRECTED_1B_PROPOSAL = deepFreeze(rawProposal);

export const LAMBDAPI_V32_DIRECTED_1B_OWNER_BINDINGS = deepFreeze(
    rawOwnerBindings
);

export const LAMBDAPI_V32_DIRECTED_1B_RULE_BINDINGS = deepFreeze(
    rawRuleBindings
);

/**
 * Validate the exact pre-review proposal without granting semantic authority.
 */
export function validateCoreDirected1bProposal(
    proposal: CoreDirected1bProposalInput = CORE_DIRECTED_1B_PROPOSAL,
    ownerBindings: readonly CoreDirected1bLambdapiOwnerBinding[] =
        LAMBDAPI_V32_DIRECTED_1B_OWNER_BINDINGS,
    ruleBindings: readonly CoreDirected1bLambdapiRuleBinding[] =
        LAMBDAPI_V32_DIRECTED_1B_RULE_BINDINGS
): void {
    if (
        proposal.revision !== 'DIRECTED-1B' ||
        proposal.experimentId !== 'DTTLF-DIRECTED-1B-E01' ||
        proposal.status !== 'proposal-awaiting-h-dttlf-02' ||
        proposal.reviewGate !== 'H-DTTLF-02' ||
        proposal.consumer !==
            'nested-telescope-pair-fibre-projection-and-total-transport'
    ) {
        fail(
            'INVALID_PROPOSAL_BOUNDARY',
            'DIRECTED-1B must remain the exact consumer-led proposal ' +
            'awaiting a new H-DTTLF-02 decision'
        );
    }

    try {
        validateCoreLfContinuationProfileReview(
            CORE_LF_CONTINUATION_PROFILE_REVIEW
        );
        validateCoreDirected1aReview(CORE_DIRECTED_1A_REVIEW);
    } catch (error: unknown) {
        fail(
            'INVALID_PREREQUISITE',
            'DIRECTED-1B requires the reviewed LF and DIRECTED-1A ' +
            `boundaries: ${
                error instanceof Error ? error.message : String(error)
            }`
        );
    }
    if (
        proposal.prerequisites.lfProfileReview !==
            CORE_LF_CONTINUATION_PROFILE_REVIEW.revision ||
        proposal.prerequisites.directed1aReview !==
            CORE_DIRECTED_1A_REVIEW.revision ||
        !sameData(
            proposal.prerequisites.directed1aOwnerIds,
            CORE_DIRECTED_1A_PROPOSAL.owners.map(entry => entry.owner)
        )
    ) {
        fail(
            'INVALID_PREREQUISITE',
            'DIRECTED-1B prerequisite reviews or owner snapshot drifted'
        );
    }

    if (proposal.owners.length !== 5) {
        fail(
            'INVALID_OWNER_SET',
            `DIRECTED-1B must propose exactly five owners, received ` +
            proposal.owners.length
        );
    }

    const availableOwners = new Map<string, number>(
        Object.entries(CORE_OWNER_SCHEMAS).map(([owner, schema]) => [
            owner,
            schema.slots.length
        ])
    );
    for (const owner of CORE_DIRECTED_1A_PROPOSAL.owners) {
        availableOwners.set(owner.owner, owner.slots.length);
    }

    const seenOwners = new Set<string>();
    proposal.owners.forEach((owner, order) => {
        if (
            owner.order !== order ||
            seenOwners.has(owner.owner) ||
            availableOwners.has(owner.owner)
        ) {
            fail(
                'INVALID_OWNER_SET',
                `DIRECTED-1B owner ${order} is duplicated, integrated, or ` +
                'reordered'
            );
        }
        const variables = validateTypedTelescope(
            owner.slots,
            availableOwners,
            `DIRECTED-1B owner ${owner.owner}`
        );
        validateExpression(
            owner.result,
            availableOwners,
            variables,
            `${owner.owner} result`
        );

        const transfersBody =
            owner.candidateDisposition ===
            'transparent-checked-definition';
        if (
            transfersBody !== (owner.body !== undefined) ||
            (
                transfersBody &&
                owner.activeAuthority !== 'transparent-definition'
            )
        ) {
            fail(
                'INVALID_DEFINITION_SET',
                `${owner.owner} has an unauthorized candidate body policy`
            );
        }
        if (owner.body !== undefined) {
            validateExpression(
                owner.body,
                availableOwners,
                variables,
                `${owner.owner} transparent body`
            );
        }

        seenOwners.add(owner.owner);
        availableOwners.set(owner.owner, owner.slots.length);
    });

    if (
        proposal.runtimeRules.length !== 3 ||
        proposal.proofTimeRules.length !== 0
    ) {
        fail(
            'INVALID_RULE_SET',
            'DIRECTED-1B must propose exactly three runtime rules and zero ' +
            'proof-time rules'
        );
    }
    const seenRuleIds = new Set<string>();
    proposal.runtimeRules.forEach((rule, order) => {
        if (
            rule.order !== order ||
            seenRuleIds.has(rule.id) ||
            rule.authority !== 'active-runtime-rule' ||
            rule.execution !== 'catalog-scoped-reviewed-runtime'
        ) {
            fail(
                'INVALID_RULE_SET',
                `DIRECTED-1B rule ${order} is duplicated, reordered, or has ` +
                'an unauthorized authority class'
            );
        }
        const variables = validateTypedTelescope(
            rule.variables,
            availableOwners,
            `DIRECTED-1B rule ${rule.id}`
        );
        validateExpression(
            rule.left,
            availableOwners,
            variables,
            `${rule.id} left side`
        );
        validateExpression(
            rule.right,
            availableOwners,
            variables,
            `${rule.id} right side`
        );
        seenRuleIds.add(rule.id);
    });

    if (
        proposal.runtimeExtensionPolicy.scope !==
            'directed-catalog-local' ||
        proposal.runtimeExtensionPolicy.insertionPoint !==
            'reviewed-runtime-phase-before-frozen-mvp-program' ||
        proposal.runtimeExtensionPolicy.budget !==
            'shared-outer-lf-global-budget' ||
        proposal.runtimeExtensionPolicy.defaultLfProfile !== 'unchanged' ||
        proposal.runtimeExtensionPolicy.arbitraryUserRules !== false ||
        proposal.backendProjectionPolicy.opaqueImports !==
            'signature-checked-external-references' ||
        proposal.backendProjectionPolicy.transparentDefinitions !==
            'checked-local-mirror-mapped-to-active-owner' ||
        proposal.backendProjectionPolicy.emittedShadowDeclarations !==
            false ||
        proposal.backendProjectionPolicy.activeDefinitionBody !==
            'proposal-exact-and-lambdapi-oracle-checked'
    ) {
        fail(
            'INVALID_RUNTIME_POLICY',
            'DIRECTED-1B must preserve the default LF profile and use only ' +
            'a catalog-scoped reviewed runtime extension'
        );
    }

    if (
        ownerBindings.length !== proposal.owners.length ||
        ownerBindings.some((binding_, order) =>
            binding_.order !== order ||
            binding_.owner !== proposal.owners[order].owner ||
            binding_.authority !==
                proposal.owners[order].activeAuthority ||
            binding_.module !== 'emdash.emdash3_2' ||
            binding_.provenance.authorityPath !==
                'emdash2/emdash3_2.lp' ||
            binding_.provenance.auditedOn !== '2026-07-24'
        ) ||
        ruleBindings.length !== proposal.runtimeRules.length ||
        ruleBindings.some((binding_, order) =>
            binding_.order !== order ||
            binding_.id !== proposal.runtimeRules[order].id ||
            binding_.module !== 'emdash.emdash3_2' ||
            binding_.authority !== 'runtime-rule' ||
            binding_.provenance.authorityPath !==
                'emdash2/emdash3_2.lp' ||
            binding_.provenance.auditedOn !== '2026-07-24'
        )
    ) {
        fail(
            'INVALID_BACKEND_BINDINGS',
            'DIRECTED-1B backend evidence must cover the exact ordered ' +
            'owner and runtime-rule proposal'
        );
    }

    if (
        !sameData(
            proposal.preservedMvpProfile,
            rawProposal.preservedMvpProfile
        ) ||
        !sameData(liveMvpIdentity(), rawProposal.preservedMvpProfile)
    ) {
        fail(
            'MVP_PROFILE_DRIFT',
            'DIRECTED-1B must preserve the exact emdash-v3.2-mvp-1 profile'
        );
    }

    if (
        !sameData(proposal, rawProposal) ||
        !sameData(ownerBindings, rawOwnerBindings) ||
        !sameData(ruleBindings, rawRuleBindings)
    ) {
        fail(
            'PROPOSAL_DRIFT',
            'DIRECTED-1B differs from its exact H-DTTLF-02 review input'
        );
    }
}

validateCoreDirected1bProposal();
