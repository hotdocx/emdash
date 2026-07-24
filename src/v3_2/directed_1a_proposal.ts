/**
 * Machine-readable H-DTTLF-02 proposal for the first directed-DTT slice.
 *
 * This module records candidate declaration signatures only. It deliberately
 * does not extend `CORE_OWNER_SCHEMAS`, the Lambdapi backend binding catalog,
 * the frozen MVP manifest, or either runtime program. A distinct reviewed
 * artifact must record approval before integration.
 */

import {
    CORE_MVP_MANIFEST
} from './manifest';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    Plicity
} from './schema';

export type CoreDirected1aCandidateOwnerId =
    | 'displayed-functor-category'
    | 'sigma-category'
    | 'sigma-telescope-family';

export type CoreDirected1aSignatureOwnerId =
    | CoreOwnerId
    | CoreDirected1aCandidateOwnerId;

export type CoreDirected1aSignatureExpression =
    | {
        readonly tag: 'slot';
        readonly name: string;
    }
    | {
        readonly tag: 'owner-application';
        readonly owner: CoreDirected1aSignatureOwnerId;
        readonly arguments: readonly CoreDirected1aSignatureExpression[];
    };

export interface CoreDirected1aTypedSlot {
    readonly name: string;
    readonly plicity: Plicity;
    readonly role: string;
    readonly type: CoreDirected1aSignatureExpression;
}

export interface CoreDirected1aOwnerProposal {
    readonly order: number;
    readonly owner: CoreDirected1aCandidateOwnerId;
    readonly authority: 'active-declaration-signature';
    readonly disposition: 'candidate-awaiting-h-dttlf-02';
    readonly slots: readonly CoreDirected1aTypedSlot[];
    readonly result: CoreDirected1aSignatureExpression;
}

export interface CoreDirected1aProposalInput {
    readonly revision: 'DIRECTED-1A';
    readonly experimentId: 'DTTLF-DIRECTED-1A-E01';
    readonly status: 'proposal-awaiting-h-dttlf-02';
    readonly reviewGate: 'H-DTTLF-02';
    readonly consumer: 'nested-cat-valued-telescope';
    readonly owners: readonly CoreDirected1aOwnerProposal[];
    readonly rules: readonly [];
    readonly preservedMvpProfile: {
        readonly revision: 'emdash-v3.2-mvp-1';
        readonly contentHash:
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0';
        readonly ownerIds: readonly string[];
        readonly runtimeRuleIds: readonly string[];
    };
    readonly nonEffects: readonly string[];
}

export interface CoreDirected1aLambdapiBinding {
    readonly order: number;
    readonly owner: CoreDirected1aCandidateOwnerId;
    readonly module: 'emdash.emdash3_2';
    readonly serializedName:
        | 'Functord_cat'
        | 'Sigma_cat'
        | 'Sigma_catd_functord_catd';
    readonly authority: 'declaration-signature';
    readonly provenance: {
        readonly authorityPath: 'emdash2/emdash3_2.lp';
        readonly section: string;
        readonly declaration: string;
        readonly auditedOn: '2026-07-24';
    };
}

export type CoreDirected1aProposalErrorCode =
    | 'INVALID_PROPOSAL_BOUNDARY'
    | 'INVALID_OWNER_SET'
    | 'INVALID_SIGNATURE'
    | 'INVALID_RULE_SET'
    | 'INVALID_BACKEND_BINDINGS'
    | 'MVP_PROFILE_DRIFT'
    | 'PROPOSAL_DRIFT';

export class CoreDirected1aProposalError extends Error {
    constructor(
        public readonly code: CoreDirected1aProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirected1aProposalError';
    }
}

const slot = (
    name: string
): CoreDirected1aSignatureExpression => ({
    tag: 'slot',
    name
});

const application = (
    owner: CoreDirected1aSignatureOwnerId,
    ...arguments_: readonly CoreDirected1aSignatureExpression[]
): CoreDirected1aSignatureExpression => ({
    tag: 'owner-application',
    owner,
    arguments: arguments_
});

const typedSlot = (
    name: string,
    plicity: Plicity,
    role: string,
    type: CoreDirected1aSignatureExpression
): CoreDirected1aTypedSlot => ({
    name,
    plicity,
    role,
    type
});

const categoryUniverse = application('category-universe');

const displayedFamilyType = (
    base: CoreDirected1aSignatureExpression
): CoreDirected1aSignatureExpression => application(
    'decode',
    application(
        'object-classifier',
        application('displayed-category-category', base)
    )
);

const displayedFunctorType = (
    base: CoreDirected1aSignatureExpression,
    source: CoreDirected1aSignatureExpression,
    target: CoreDirected1aSignatureExpression
): CoreDirected1aSignatureExpression => application(
    'decode',
    application(
        'object-classifier',
        application(
            'displayed-functor-category',
            base,
            source,
            target
        )
    )
);

const K = slot('K');
const R = slot('R');

const rawProposal: CoreDirected1aProposalInput = {
    revision: 'DIRECTED-1A',
    experimentId: 'DTTLF-DIRECTED-1A-E01',
    status: 'proposal-awaiting-h-dttlf-02',
    reviewGate: 'H-DTTLF-02',
    consumer: 'nested-cat-valued-telescope',
    owners: [
        {
            order: 0,
            owner: 'displayed-functor-category',
            authority: 'active-declaration-signature',
            disposition: 'candidate-awaiting-h-dttlf-02',
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
                    'source-displayed-family',
                    displayedFamilyType(K)
                ),
                typedSlot(
                    'D',
                    'explicit',
                    'target-displayed-family',
                    displayedFamilyType(K)
                )
            ],
            result: categoryUniverse
        },
        {
            order: 1,
            owner: 'sigma-category',
            authority: 'active-declaration-signature',
            disposition: 'candidate-awaiting-h-dttlf-02',
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
            result: categoryUniverse
        },
        {
            order: 2,
            owner: 'sigma-telescope-family',
            authority: 'active-declaration-signature',
            disposition: 'candidate-awaiting-h-dttlf-02',
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
                        application(
                            'constant-displayed-family',
                            K,
                            application('category-of-categories')
                        )
                    )
                )
            ],
            result: displayedFamilyType(
                application('sigma-category', K, R)
            )
        }
    ],
    rules: [],
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
    nonEffects: [
        'does not extend CORE_OWNER_SCHEMAS',
        'does not extend LAMBDAPI_V32_OWNER_BINDINGS',
        'does not mutate CORE_MVP_MANIFEST',
        'does not add a runtime or proof-time rule',
        'does not enter src/v3_2/browser.ts'
    ]
};

const rawBindings: readonly CoreDirected1aLambdapiBinding[] = [
    {
        order: 0,
        owner: 'displayed-functor-category',
        module: 'emdash.emdash3_2',
        serializedName: 'Functord_cat',
        authority: 'declaration-signature',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section:
                '3d. Directed-family and displayed-arrow classifiers',
            declaration: 'injective symbol Functord_cat',
            auditedOn: '2026-07-24'
        }
    },
    {
        order: 1,
        owner: 'sigma-category',
        module: 'emdash.emdash3_2',
        serializedName: 'Sigma_cat',
        authority: 'declaration-signature',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section:
                '9a. Sigma totals, Sigma homs, and projection',
            declaration: 'injective symbol Sigma_cat',
            auditedOn: '2026-07-24'
        }
    },
    {
        order: 2,
        owner: 'sigma-telescope-family',
        module: 'emdash.emdash3_2',
        serializedName: 'Sigma_catd_functord_catd',
        authority: 'declaration-signature',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section:
                '9c. Families over Sigma totals and displayed-transfor ' +
                'uncurrying',
            declaration: 'symbol Sigma_catd_functord_catd',
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
    code: CoreDirected1aProposalErrorCode,
    message: string
): never => {
    throw new CoreDirected1aProposalError(code, message);
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

const validateExpression = (
    expression: CoreDirected1aSignatureExpression,
    availableOwners: ReadonlyMap<string, number>,
    availableSlots: ReadonlySet<string>,
    detail: string
): void => {
    if (expression.tag === 'slot') {
        if (!availableSlots.has(expression.name)) {
            fail(
                'INVALID_SIGNATURE',
                `${detail} refers to unavailable slot '${expression.name}'`
            );
        }
        return;
    }

    const arity = availableOwners.get(expression.owner);
    if (arity === undefined) {
        fail(
            'INVALID_SIGNATURE',
            `${detail} refers to unavailable owner '${expression.owner}'`
        );
    }
    if (expression.arguments.length !== arity) {
        fail(
            'INVALID_SIGNATURE',
            `${detail} applies '${expression.owner}' to ` +
            `${expression.arguments.length} arguments, expected ${arity}`
        );
    }
    expression.arguments.forEach((argument, index) =>
        validateExpression(
            argument,
            availableOwners,
            availableSlots,
            `${detail}, ${expression.owner} argument ${index}`
        )
    );
};

export const CORE_DIRECTED_1A_PROPOSAL = deepFreeze(rawProposal);

export const LAMBDAPI_V32_DIRECTED_1A_PROPOSAL_BINDINGS = deepFreeze(
    rawBindings
);

/**
 * Validate the exact pre-review proposal without granting catalog membership.
 */
export function validateCoreDirected1aProposal(
    proposal: CoreDirected1aProposalInput = CORE_DIRECTED_1A_PROPOSAL,
    bindings: readonly CoreDirected1aLambdapiBinding[] =
        LAMBDAPI_V32_DIRECTED_1A_PROPOSAL_BINDINGS
): void {
    if (
        proposal.revision !== 'DIRECTED-1A' ||
        proposal.experimentId !== 'DTTLF-DIRECTED-1A-E01' ||
        proposal.status !== 'proposal-awaiting-h-dttlf-02' ||
        proposal.reviewGate !== 'H-DTTLF-02' ||
        proposal.consumer !== 'nested-cat-valued-telescope'
    ) {
        fail(
            'INVALID_PROPOSAL_BOUNDARY',
            'DIRECTED-1A must remain a nested-telescope proposal awaiting ' +
            'H-DTTLF-02'
        );
    }

    if (proposal.owners.length !== 3) {
        fail(
            'INVALID_OWNER_SET',
            `DIRECTED-1A must propose exactly three owners, received ` +
            proposal.owners.length
        );
    }

    const availableOwners = new Map<string, number>(
        Object.entries(CORE_OWNER_SCHEMAS).map(([owner, schema]) => [
            owner,
            schema.slots.length
        ])
    );
    const seenOwners = new Set<string>();

    proposal.owners.forEach((owner, order) => {
        if (
            owner.order !== order ||
            seenOwners.has(owner.owner) ||
            owner.owner in CORE_OWNER_SCHEMAS ||
            owner.authority !== 'active-declaration-signature' ||
            owner.disposition !== 'candidate-awaiting-h-dttlf-02'
        ) {
            fail(
                'INVALID_OWNER_SET',
                `DIRECTED-1A owner ${order} is duplicated, integrated, ` +
                'reordered, or has an unauthorized disposition'
            );
        }

        const availableSlots = new Set<string>();
        owner.slots.forEach((typed, slotIndex) => {
            if (
                availableSlots.has(typed.name) ||
                (typed.plicity !== 'explicit' &&
                    typed.plicity !== 'implicit') ||
                typed.role.length === 0
            ) {
                fail(
                    'INVALID_SIGNATURE',
                    `DIRECTED-1A owner ${owner.owner} has an invalid slot at ` +
                    `${slotIndex}`
                );
            }
            validateExpression(
                typed.type,
                availableOwners,
                availableSlots,
                `${owner.owner} slot ${typed.name} type`
            );
            availableSlots.add(typed.name);
        });
        validateExpression(
            owner.result,
            availableOwners,
            availableSlots,
            `${owner.owner} result`
        );

        seenOwners.add(owner.owner);
        availableOwners.set(owner.owner, owner.slots.length);
    });

    if (proposal.rules.length !== 0) {
        fail(
            'INVALID_RULE_SET',
            'DIRECTED-1A is an exact zero-rule proposal'
        );
    }

    if (
        bindings.length !== proposal.owners.length ||
        bindings.some((binding, order) =>
            binding.order !== order ||
            binding.owner !== proposal.owners[order].owner ||
            binding.module !== 'emdash.emdash3_2' ||
            binding.authority !== 'declaration-signature' ||
            binding.provenance.authorityPath !==
                'emdash2/emdash3_2.lp' ||
            binding.provenance.auditedOn !== '2026-07-24'
        )
    ) {
        fail(
            'INVALID_BACKEND_BINDINGS',
            'DIRECTED-1A backend bindings must cover the exact ordered ' +
            'proposal at active declaration positions'
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
            'DIRECTED-1A must preserve the exact emdash-v3.2-mvp-1 profile'
        );
    }

    if (
        !sameData(proposal, rawProposal) ||
        !sameData(bindings, rawBindings)
    ) {
        fail(
            'PROPOSAL_DRIFT',
            'DIRECTED-1A differs from its exact H-DTTLF-02 review input'
        );
    }
}

validateCoreDirected1aProposal();
