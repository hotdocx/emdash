/**
 * Machine-readable follow-up prerequisite discovered after the approved
 * DIRECTED-FOUNDATION-1 rules made deeper signature checking executable.
 *
 * This artifact proposes one decoded Cat-hom conversion. It does not execute
 * the rule or alter either approved prerequisite/review artifact.
 */

import {
    CORE_DIRECTED_1B_REVIEW,
    validateCoreDirected1bReview
} from './directed_1b_review';
import {
    CORE_DIRECTED_FOUNDATION_REVIEW,
    validateCoreDirectedFoundationReview
} from './directed_foundation_review';
import {
    CORE_MVP_MANIFEST
} from './manifest';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId
} from './schema';

export type CoreDirectedFoundation2RuleId =
    'directed.category-hom.decode';

export type CoreDirectedFoundation2Expression =
    | {
        readonly tag: 'variable';
        readonly name: string;
    }
    | {
        readonly tag: 'owner-application';
        readonly owner: CoreOwnerId;
        readonly arguments:
            readonly CoreDirectedFoundation2Expression[];
    };

export interface CoreDirectedFoundation2Variable {
    readonly name: string;
    readonly role: string;
    readonly type: CoreDirectedFoundation2Expression;
}

export interface CoreDirectedFoundation2RuntimeRuleProposal {
    readonly order: 0;
    readonly id: CoreDirectedFoundation2RuleId;
    readonly authority:
        'active-runtime-consequence-through-transparent-classifiers';
    readonly execution:
        'directed-catalog-local-prerequisite';
    readonly variables:
        readonly CoreDirectedFoundation2Variable[];
    readonly left: CoreDirectedFoundation2Expression;
    readonly right: CoreDirectedFoundation2Expression;
}

export interface CoreDirectedFoundation2ProposalInput {
    readonly revision: 'DIRECTED-FOUNDATION-2';
    readonly experimentId: 'DTTLF-DIRECTED-1B-E02B';
    readonly status: 'proposal-awaiting-h-dttlf-02';
    readonly reviewGate:
        'H-DTTLF-02/DIRECTED-FOUNDATION-2';
    readonly trigger:
        'directed-1b-transport-functor-classifier-prerequisite';
    readonly runtimeRules:
        readonly CoreDirectedFoundation2RuntimeRuleProposal[];
    readonly proofTimeRules: readonly [];
    readonly ownerDeclarations: readonly [];
    readonly prerequisites: {
        readonly foundation1Revision:
            'DIRECTED-FOUNDATION-1-REVIEWED';
        readonly foundation1RuleIds: readonly string[];
        readonly directed1bRevision: 'DIRECTED-1B-REVIEWED';
        readonly directed1bOwnRuntimeRuleIds: readonly string[];
        readonly approvedArtifactsUnchanged: true;
    };
    readonly runtimePolicy: {
        readonly scope: 'directed-catalog-local';
        readonly order:
            'foundation-1-before-foundation-2-before-directed-1b-before-frozen-mvp';
        readonly budget: 'shared-outer-lf-global-budget';
        readonly redexScope: 'decoded-category-hom-only';
        readonly rawClassifierRewrite: false;
        readonly categoryHeadRewrite: false;
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

export interface CoreDirectedFoundation2LambdapiRuleBinding {
    readonly order: 0;
    readonly id: CoreDirectedFoundation2RuleId;
    readonly module: 'emdash.emdash3_2';
    readonly authority:
        'runtime-rule-plus-transparent-classifier-definitions';
    readonly provenance: {
        readonly authorityPath: 'emdash2/emdash3_2.lp';
        readonly section: '3c. Universe categories';
        readonly sourceFragment:
            'rule Hom_cat Cat_cat $X $Y ↪ Functor_cat $X $Y;';
        readonly auditedOn: '2026-07-24';
    };
}

export type CoreDirectedFoundation2ProposalErrorCode =
    | 'INVALID_PROPOSAL_BOUNDARY'
    | 'INVALID_PREREQUISITE'
    | 'INVALID_RULE_SET'
    | 'INVALID_EXPRESSION'
    | 'INVALID_RUNTIME_POLICY'
    | 'INVALID_BACKEND_BINDING'
    | 'MVP_PROFILE_DRIFT'
    | 'PROPOSAL_DRIFT';

export class CoreDirectedFoundation2ProposalError extends Error {
    constructor(
        public readonly code:
            CoreDirectedFoundation2ProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirectedFoundation2ProposalError';
    }
}

const variable = (
    name: string
): CoreDirectedFoundation2Expression => ({
    tag: 'variable',
    name
});

const ownerApplication = (
    owner: CoreOwnerId,
    ...arguments_: readonly CoreDirectedFoundation2Expression[]
): CoreDirectedFoundation2Expression => ({
    tag: 'owner-application',
    owner,
    arguments: arguments_
});

const categoryUniverse =
    ownerApplication('category-universe');
const categoryOfCategories =
    ownerApplication('category-of-categories');
const A = variable('A');
const B = variable('B');

const rawRule: CoreDirectedFoundation2RuntimeRuleProposal = {
    order: 0,
    id: 'directed.category-hom.decode',
    authority:
        'active-runtime-consequence-through-transparent-classifiers',
    execution: 'directed-catalog-local-prerequisite',
    variables: [
        {
            name: 'A',
            role: 'source-category',
            type: categoryUniverse
        },
        {
            name: 'B',
            role: 'target-category',
            type: categoryUniverse
        }
    ],
    left: ownerApplication(
        'decode',
        ownerApplication(
            'hom-classifier',
            categoryOfCategories,
            A,
            B
        )
    ),
    right: ownerApplication(
        'decode',
        ownerApplication('functor-classifier', A, B)
    )
};

const rawProposal: CoreDirectedFoundation2ProposalInput = {
    revision: 'DIRECTED-FOUNDATION-2',
    experimentId: 'DTTLF-DIRECTED-1B-E02B',
    status: 'proposal-awaiting-h-dttlf-02',
    reviewGate: 'H-DTTLF-02/DIRECTED-FOUNDATION-2',
    trigger:
        'directed-1b-transport-functor-classifier-prerequisite',
    runtimeRules: [rawRule],
    proofTimeRules: [],
    ownerDeclarations: [],
    prerequisites: {
        foundation1Revision:
            CORE_DIRECTED_FOUNDATION_REVIEW.revision,
        foundation1RuleIds: [
            ...CORE_DIRECTED_FOUNDATION_REVIEW.authorization
                .runtimeRuleIds
        ],
        directed1bRevision: CORE_DIRECTED_1B_REVIEW.revision,
        directed1bOwnRuntimeRuleIds: [
            ...CORE_DIRECTED_1B_REVIEW.authorization.runtimeRuleIds
        ],
        approvedArtifactsUnchanged: true
    },
    runtimePolicy: {
        scope: 'directed-catalog-local',
        order:
            'foundation-1-before-foundation-2-before-directed-1b-before-frozen-mvp',
        budget: 'shared-outer-lf-global-budget',
        redexScope: 'decoded-category-hom-only',
        rawClassifierRewrite: false,
        categoryHeadRewrite: false,
        defaultLfProfile: 'unchanged',
        arbitraryUserRules: false
    },
    preservedMvpProfile: {
        revision: 'emdash-v3.2-mvp-1',
        contentHash:
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0',
        ownerIds: CORE_MVP_MANIFEST.owners.map(entry => entry.owner),
        runtimeRuleIds: CORE_MVP_MANIFEST.rules.map(rule => rule.id)
    },
    nonEffects: [
        'does not add an owner declaration',
        'does not rewrite raw Hom classifiers',
        'does not rewrite Hom_cat or any other category head in TypeScript',
        'does not add a proof-time rule',
        'does not change either approved foundation or DIRECTED-1B artifact',
        'does not mutate CORE_MVP_MANIFEST or CORE_MVP_RUNTIME_PROGRAM',
        'does not alter the default LF-PROFILE-1 runtime component',
        'does not enter src/v3_2/browser.ts',
        'does not authorize a metatheory claim or DIRECTED-1C'
    ]
};

const rawBinding:
CoreDirectedFoundation2LambdapiRuleBinding = {
    order: 0,
    id: 'directed.category-hom.decode',
    module: 'emdash.emdash3_2',
    authority:
        'runtime-rule-plus-transparent-classifier-definitions',
    provenance: {
        authorityPath: 'emdash2/emdash3_2.lp',
        section: '3c. Universe categories',
        sourceFragment:
            'rule Hom_cat Cat_cat $X $Y ↪ Functor_cat $X $Y;',
        auditedOn: '2026-07-24'
    }
};

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
    code: CoreDirectedFoundation2ProposalErrorCode,
    message: string
): never => {
    throw new CoreDirectedFoundation2ProposalError(code, message);
};

const validateExpression = (
    expression: CoreDirectedFoundation2Expression,
    variables: ReadonlySet<string>,
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

    const schema = CORE_OWNER_SCHEMAS[expression.owner];
    if (expression.arguments.length !== schema.slots.length) {
        fail(
            'INVALID_EXPRESSION',
            `${detail} applies '${expression.owner}' to ` +
            `${expression.arguments.length} arguments, expected ` +
            schema.slots.length
        );
    }
    expression.arguments.forEach((argument, index) =>
        validateExpression(
            argument,
            variables,
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

export const CORE_DIRECTED_FOUNDATION_2_PROPOSAL =
    deepFreeze(rawProposal);

export const LAMBDAPI_V32_DIRECTED_FOUNDATION_2_RULE_BINDING =
    deepFreeze(rawBinding);

export function validateCoreDirectedFoundation2Proposal(
    proposal: CoreDirectedFoundation2ProposalInput =
        CORE_DIRECTED_FOUNDATION_2_PROPOSAL,
    binding: CoreDirectedFoundation2LambdapiRuleBinding =
        LAMBDAPI_V32_DIRECTED_FOUNDATION_2_RULE_BINDING
): void {
    if (
        proposal.revision !== 'DIRECTED-FOUNDATION-2' ||
        proposal.experimentId !== 'DTTLF-DIRECTED-1B-E02B' ||
        proposal.status !== 'proposal-awaiting-h-dttlf-02' ||
        proposal.reviewGate !==
            'H-DTTLF-02/DIRECTED-FOUNDATION-2' ||
        proposal.trigger !==
            'directed-1b-transport-functor-classifier-prerequisite'
    ) {
        fail(
            'INVALID_PROPOSAL_BOUNDARY',
            'DIRECTED-FOUNDATION-2 boundary drifted'
        );
    }

    try {
        validateCoreDirectedFoundationReview(
            CORE_DIRECTED_FOUNDATION_REVIEW
        );
        validateCoreDirected1bReview(CORE_DIRECTED_1B_REVIEW);
    } catch (error: unknown) {
        fail(
            'INVALID_PREREQUISITE',
            'DIRECTED-FOUNDATION-2 approved prerequisite drifted: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
    if (!sameData(
        proposal.prerequisites,
        rawProposal.prerequisites
    )) {
        fail(
            'INVALID_PREREQUISITE',
            'DIRECTED-FOUNDATION-2 prerequisite snapshot drifted'
        );
    }

    if (
        proposal.runtimeRules.length !== 1 ||
        proposal.proofTimeRules.length !== 0 ||
        proposal.ownerDeclarations.length !== 0 ||
        !sameData(proposal.runtimeRules[0], rawRule)
    ) {
        fail(
            'INVALID_RULE_SET',
            'DIRECTED-FOUNDATION-2 must contain exactly the one ' +
            'decoded Cat-hom rule and no owner or proof-time rule'
        );
    }

    const variables = new Set<string>();
    for (const variable_ of proposal.runtimeRules[0].variables) {
        if (
            variables.has(variable_.name) ||
            variable_.role.trim().length === 0
        ) {
            fail(
                'INVALID_EXPRESSION',
                'DIRECTED-FOUNDATION-2 has malformed variables'
            );
        }
        validateExpression(
            variable_.type,
            variables,
            `Variable ${variable_.name} type`
        );
        variables.add(variable_.name);
    }
    validateExpression(
        proposal.runtimeRules[0].left,
        variables,
        'Rule left'
    );
    validateExpression(
        proposal.runtimeRules[0].right,
        variables,
        'Rule right'
    );

    if (!sameData(
        proposal.runtimePolicy,
        rawProposal.runtimePolicy
    )) {
        fail(
            'INVALID_RUNTIME_POLICY',
            'DIRECTED-FOUNDATION-2 runtime policy drifted'
        );
    }
    if (!sameData(
        proposal.preservedMvpProfile,
        liveMvpIdentity()
    )) {
        fail(
            'MVP_PROFILE_DRIFT',
            'DIRECTED-FOUNDATION-2 no longer preserves the deployed MVP'
        );
    }
    if (!sameData(binding, rawBinding)) {
        fail(
            'INVALID_BACKEND_BINDING',
            'DIRECTED-FOUNDATION-2 active rule binding drifted'
        );
    }
    if (!sameData(proposal, rawProposal)) {
        fail(
            'PROPOSAL_DRIFT',
            'DIRECTED-FOUNDATION-2 differs from its exact review input'
        );
    }
}

validateCoreDirectedFoundation2Proposal();
