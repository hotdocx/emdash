/**
 * Machine-readable prerequisite proposal discovered while integrating
 * DIRECTED-1B.
 *
 * This artifact records three earlier active object-level facade reductions.
 * It does not execute them or change the approved DIRECTED-1B proposal.
 */

import {
    CORE_DIRECTED_1A_PROPOSAL,
    CoreDirected1aCandidateOwnerId
} from './directed_1a_proposal';
import {
    CORE_MVP_MANIFEST
} from './manifest';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId
} from './schema';

export type CoreDirectedFoundationRuleId =
    | 'directed.category-object.decode'
    | 'directed.displayed-family.decode'
    | 'directed.displayed-functor.decode';

export type CoreDirectedFoundationExpressionOwnerId =
    | CoreOwnerId
    | CoreDirected1aCandidateOwnerId;

export type CoreDirectedFoundationExpression =
    | {
        readonly tag: 'variable';
        readonly name: string;
    }
    | {
        readonly tag: 'owner-application';
        readonly owner: CoreDirectedFoundationExpressionOwnerId;
        readonly arguments:
            readonly CoreDirectedFoundationExpression[];
    };

export interface CoreDirectedFoundationVariable {
    readonly name: string;
    readonly role: string;
    readonly type: CoreDirectedFoundationExpression;
}

export interface CoreDirectedFoundationRuntimeRuleProposal {
    readonly order: number;
    readonly id: CoreDirectedFoundationRuleId;
    readonly authority: 'active-runtime-rule';
    readonly execution: 'directed-catalog-local-prerequisite';
    readonly variables: readonly CoreDirectedFoundationVariable[];
    readonly left: CoreDirectedFoundationExpression;
    readonly right: CoreDirectedFoundationExpression;
}

export interface CoreDirectedFoundationProposalInput {
    readonly revision: 'DIRECTED-FOUNDATION-1';
    readonly experimentId: 'DTTLF-DIRECTED-1B-E02A';
    readonly status: 'proposal-awaiting-h-dttlf-02';
    readonly reviewGate:
        'H-DTTLF-02/DIRECTED-FOUNDATION-1';
    readonly trigger:
        'directed-1b-signature-checking-prerequisite';
    readonly runtimeRules:
        readonly CoreDirectedFoundationRuntimeRuleProposal[];
    readonly proofTimeRules: readonly [];
    readonly ownerDeclarations: readonly [];
    readonly relationshipToDirected1b: {
        readonly approvedProposalUnchanged: true;
        readonly prerequisiteOnly: true;
        readonly directed1bOwnerCount: 5;
        readonly directed1bOwnRuntimeRuleCount: 3;
    };
    readonly runtimePolicy: {
        readonly scope: 'directed-catalog-local';
        readonly order:
            'foundation-before-directed-1b-before-frozen-mvp';
        readonly budget: 'shared-outer-lf-global-budget';
        readonly defaultLfProfile: 'unchanged';
        readonly arbitraryUserRules: false;
    };
    readonly preservedMvpProfile: {
        readonly revision: 'emdash-v3.2-mvp-1';
        readonly contentHash:
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0';
        readonly ownerIds: readonly string[];
        readonly runtimeRuleIds: readonly string[];
    };
    readonly nonEffects: readonly string[];
}

export interface CoreDirectedFoundationLambdapiRuleBinding {
    readonly order: number;
    readonly id: CoreDirectedFoundationRuleId;
    readonly module: 'emdash.emdash3_2';
    readonly authority: 'runtime-rule';
    readonly provenance: {
        readonly authorityPath: 'emdash2/emdash3_2.lp';
        readonly section: string;
        readonly sourceFragment: string;
        readonly auditedOn: '2026-07-24';
    };
}

export type CoreDirectedFoundationProposalErrorCode =
    | 'INVALID_PROPOSAL_BOUNDARY'
    | 'INVALID_RULE_SET'
    | 'INVALID_EXPRESSION'
    | 'INVALID_RUNTIME_POLICY'
    | 'INVALID_BACKEND_BINDINGS'
    | 'MVP_PROFILE_DRIFT'
    | 'PROPOSAL_DRIFT';

export class CoreDirectedFoundationProposalError extends Error {
    constructor(
        public readonly code: CoreDirectedFoundationProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirectedFoundationProposalError';
    }
}

const variable = (
    name: string
): CoreDirectedFoundationExpression => ({
    tag: 'variable',
    name
});

const ownerApplication = (
    owner: CoreDirectedFoundationExpressionOwnerId,
    ...arguments_: readonly CoreDirectedFoundationExpression[]
): CoreDirectedFoundationExpression => ({
    tag: 'owner-application',
    owner,
    arguments: arguments_
});

const categoryUniverse =
    ownerApplication('category-universe');
const categoryOfCategories =
    ownerApplication('category-of-categories');
const K = variable('K');
const E = variable('E');
const D = variable('D');

const decode = (
    classifier: CoreDirectedFoundationExpression
): CoreDirectedFoundationExpression =>
    ownerApplication('decode', classifier);

const objectClassifier = (
    category: CoreDirectedFoundationExpression
): CoreDirectedFoundationExpression =>
    ownerApplication('object-classifier', category);

const displayedFamilyType = (
    base: CoreDirectedFoundationExpression
): CoreDirectedFoundationExpression => decode(objectClassifier(
    ownerApplication('displayed-category-category', base)
));

const rawRules:
readonly CoreDirectedFoundationRuntimeRuleProposal[] = [
    {
        order: 0,
        id: 'directed.category-object.decode',
        authority: 'active-runtime-rule',
        execution: 'directed-catalog-local-prerequisite',
        variables: [],
        left: decode(objectClassifier(categoryOfCategories)),
        right: categoryUniverse
    },
    {
        order: 1,
        id: 'directed.displayed-family.decode',
        authority: 'active-runtime-rule',
        execution: 'directed-catalog-local-prerequisite',
        variables: [{
            name: 'K',
            role: 'base-category',
            type: categoryUniverse
        }],
        left: displayedFamilyType(K),
        right: decode(ownerApplication(
            'functor-classifier',
            K,
            categoryOfCategories
        ))
    },
    {
        order: 2,
        id: 'directed.displayed-functor.decode',
        authority: 'active-runtime-rule',
        execution: 'directed-catalog-local-prerequisite',
        variables: [{
            name: 'K',
            role: 'base-category',
            type: categoryUniverse
        }, {
            name: 'E',
            role: 'source-displayed-family',
            type: displayedFamilyType(K)
        }, {
            name: 'D',
            role: 'target-displayed-family',
            type: displayedFamilyType(K)
        }],
        left: decode(objectClassifier(ownerApplication(
            'displayed-functor-category',
            K,
            E,
            D
        ))),
        right: decode(ownerApplication(
            'transfor-classifier',
            K,
            categoryOfCategories,
            E,
            D
        ))
    }
];

const rawProposal: CoreDirectedFoundationProposalInput = {
    revision: 'DIRECTED-FOUNDATION-1',
    experimentId: 'DTTLF-DIRECTED-1B-E02A',
    status: 'proposal-awaiting-h-dttlf-02',
    reviewGate: 'H-DTTLF-02/DIRECTED-FOUNDATION-1',
    trigger: 'directed-1b-signature-checking-prerequisite',
    runtimeRules: rawRules,
    proofTimeRules: [],
    ownerDeclarations: [],
    relationshipToDirected1b: {
        approvedProposalUnchanged: true,
        prerequisiteOnly: true,
        directed1bOwnerCount: 5,
        directed1bOwnRuntimeRuleCount: 3
    },
    runtimePolicy: {
        scope: 'directed-catalog-local',
        order:
            'foundation-before-directed-1b-before-frozen-mvp',
        budget: 'shared-outer-lf-global-budget',
        defaultLfProfile: 'unchanged',
        arbitraryUserRules: false
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
    nonEffects: [
        'does not add an owner declaration',
        'does not rewrite Catd_cat to an ordinary functor-category head',
        'does not rewrite Functord_cat to an ordinary transfor-category head',
        'does not add a proof-time rule',
        'does not mutate CORE_MVP_MANIFEST or CORE_MVP_RUNTIME_PROGRAM',
        'does not alter the default LF-PROFILE-1 runtime component',
        'does not change the approved DIRECTED-1B proposal or review',
        'does not enter src/v3_2/browser.ts',
        'does not authorize a metatheory claim'
    ]
};

const rawBindings:
readonly CoreDirectedFoundationLambdapiRuleBinding[] = [
    {
        order: 0,
        id: 'directed.category-object.decode',
        module: 'emdash.emdash3_2',
        authority: 'runtime-rule',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section: '3c. Universe categories',
            sourceFragment: 'rule τ (Obj Cat_cat)  ↪ Cat;',
            auditedOn: '2026-07-24'
        }
    },
    {
        order: 1,
        id: 'directed.displayed-family.decode',
        module: 'emdash.emdash3_2',
        authority: 'runtime-rule',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section:
                '3d. Directed-family and displayed-arrow classifiers',
            sourceFragment: 'rule Obj (@Catd_cat $K)',
            auditedOn: '2026-07-24'
        }
    },
    {
        order: 2,
        id: 'directed.displayed-functor.decode',
        module: 'emdash.emdash3_2',
        authority: 'runtime-rule',
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            section:
                '6a. Transformation classifier, components, and generic ' +
                'projection calculus',
            sourceFragment:
                'rule Obj (@Functord_cat $K $E $D)',
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
    code: CoreDirectedFoundationProposalErrorCode,
    message: string
): never => {
    throw new CoreDirectedFoundationProposalError(code, message);
};

const ownerArities = (): ReadonlyMap<string, number> => new Map([
    ...Object.entries(CORE_OWNER_SCHEMAS).map(([owner, schema]) => [
        owner,
        schema.slots.length
    ] as const),
    ...CORE_DIRECTED_1A_PROPOSAL.owners.map(owner => [
        owner.owner,
        owner.slots.length
    ] as const)
]);

const validateExpression = (
    expression: CoreDirectedFoundationExpression,
    variables: ReadonlySet<string>,
    arities: ReadonlyMap<string, number>,
    detail: string
): void => {
    if (expression.tag === 'variable') {
        if (!variables.has(expression.name)) {
            fail(
                'INVALID_EXPRESSION',
                `${detail} refers to unavailable variable ` +
                `'${expression.name}'`
            );
        }
        return;
    }
    const arity = arities.get(expression.owner);
    if (
        arity === undefined ||
        expression.arguments.length !== arity
    ) {
        fail(
            'INVALID_EXPRESSION',
            `${detail} has unavailable or malformed owner ` +
            `'${expression.owner}'`
        );
    }
    expression.arguments.forEach((argument, index) =>
        validateExpression(
            argument,
            variables,
            arities,
            `${detail}, ${expression.owner} argument ${index}`
        )
    );
};

const liveMvpIdentity = () => ({
    revision: CORE_MVP_MANIFEST.revision,
    contentHash: CORE_MVP_MANIFEST.contentHash,
    ownerIds: CORE_MVP_MANIFEST.owners.map(entry => entry.owner),
    runtimeRuleIds: CORE_MVP_MANIFEST.rules.map(rule => rule.id)
});

export const CORE_DIRECTED_FOUNDATION_PROPOSAL =
    deepFreeze(rawProposal);

export const LAMBDAPI_V32_DIRECTED_FOUNDATION_RULE_BINDINGS =
    deepFreeze(rawBindings);

export function validateCoreDirectedFoundationProposal(
    proposal: CoreDirectedFoundationProposalInput =
        CORE_DIRECTED_FOUNDATION_PROPOSAL,
    bindings:
    readonly CoreDirectedFoundationLambdapiRuleBinding[] =
        LAMBDAPI_V32_DIRECTED_FOUNDATION_RULE_BINDINGS
): void {
    if (
        proposal.revision !== 'DIRECTED-FOUNDATION-1' ||
        proposal.experimentId !== 'DTTLF-DIRECTED-1B-E02A' ||
        proposal.status !== 'proposal-awaiting-h-dttlf-02' ||
        proposal.reviewGate !==
            'H-DTTLF-02/DIRECTED-FOUNDATION-1' ||
        proposal.trigger !==
            'directed-1b-signature-checking-prerequisite'
    ) {
        fail(
            'INVALID_PROPOSAL_BOUNDARY',
            'DIRECTED-FOUNDATION-1 boundary drifted'
        );
    }
    if (
        proposal.runtimeRules.length !== 3 ||
        proposal.proofTimeRules.length !== 0 ||
        proposal.ownerDeclarations.length !== 0 ||
        !sameData(
            proposal.runtimeRules.map(rule => [rule.order, rule.id]),
            rawRules.map(rule => [rule.order, rule.id])
        )
    ) {
        fail(
            'INVALID_RULE_SET',
            'DIRECTED-FOUNDATION-1 must contain exactly its three ' +
            'ordered runtime rules and no owner or proof-time rule'
        );
    }

    const arities = ownerArities();
    proposal.runtimeRules.forEach(rule => {
        const variables = new Set<string>();
        rule.variables.forEach(variable_ => {
            if (
                variables.has(variable_.name) ||
                variable_.role.trim().length === 0
            ) {
                fail(
                    'INVALID_EXPRESSION',
                    `Rule '${rule.id}' has malformed variables`
                );
            }
            validateExpression(
                variable_.type,
                variables,
                arities,
                `Rule '${rule.id}' variable ${variable_.name} type`
            );
            variables.add(variable_.name);
        });
        validateExpression(
            rule.left,
            variables,
            arities,
            `Rule '${rule.id}' left`
        );
        validateExpression(
            rule.right,
            variables,
            arities,
            `Rule '${rule.id}' right`
        );
    });

    if (
        !sameData(proposal.relationshipToDirected1b, {
            approvedProposalUnchanged: true,
            prerequisiteOnly: true,
            directed1bOwnerCount: 5,
            directed1bOwnRuntimeRuleCount: 3
        }) ||
        !sameData(proposal.runtimePolicy, rawProposal.runtimePolicy)
    ) {
        fail(
            'INVALID_RUNTIME_POLICY',
            'DIRECTED-FOUNDATION-1 runtime scope or relationship drifted'
        );
    }
    if (!sameData(proposal.preservedMvpProfile, liveMvpIdentity())) {
        fail(
            'MVP_PROFILE_DRIFT',
            'DIRECTED-FOUNDATION-1 no longer preserves the deployed MVP'
        );
    }
    if (
        bindings.length !== rawBindings.length ||
        !sameData(bindings, rawBindings)
    ) {
        fail(
            'INVALID_BACKEND_BINDINGS',
            'DIRECTED-FOUNDATION-1 active rule bindings drifted'
        );
    }
    if (!sameData(proposal, rawProposal)) {
        fail(
            'PROPOSAL_DRIFT',
            'DIRECTED-FOUNDATION-1 proposal differs from the exact review input'
        );
    }
}

validateCoreDirectedFoundationProposal();
