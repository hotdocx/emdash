/**
 * Machine-readable H-DTTLF-02 proposal for the section-evaluation slice.
 *
 * The active `piapp0` owner is transparent in Lambdapi, but the concrete
 * graduation consumer needs only its exact dependent signature. This review
 * input therefore proposes one opaque candidate import and no new rule. It
 * does not install the owner or alter any completed directed artifact.
 */

import {
    CORE_DIRECTED_1A_PROPOSAL,
    CoreDirected1aCandidateOwnerId
} from './directed_1a_proposal';
import {
    CORE_DIRECTED_1B_PROPOSAL,
    CoreDirected1bCandidateOwnerId
} from './directed_1b_proposal';
import {
    CORE_DIRECTED_1B_REVIEW,
    validateCoreDirected1bReview
} from './directed_1b_review';
import {
    CORE_DIRECTED_FOUNDATION_2_PROPOSAL,
    CoreDirectedFoundation2RuleId
} from './directed_foundation_2_proposal';
import {
    CORE_DIRECTED_FOUNDATION_2_REVIEW,
    validateCoreDirectedFoundation2Review
} from './directed_foundation_2_review';
import {
    CORE_DIRECTED_FOUNDATION_PROPOSAL,
    CoreDirectedFoundationRuleId
} from './directed_foundation_proposal';
import {
    CORE_DIRECTED_FOUNDATION_REVIEW,
    validateCoreDirectedFoundationReview
} from './directed_foundation_review';
import {
    CORE_LF_CONTINUATION_PROFILE_REVIEW,
    validateCoreLfContinuationProfileReview
} from './continuation_review';
import {
    CORE_MVP_MANIFEST
} from './manifest';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    Plicity
} from './schema';

export type CoreDirected1cCandidateOwnerId =
    'section-object-evaluation';

export type CoreDirected1cExpressionOwnerId =
    | CoreOwnerId
    | CoreDirected1cCandidateOwnerId;

export type CoreDirected1cExpression =
    | {
        readonly tag: 'variable';
        readonly name: string;
    }
    | {
        readonly tag: 'owner-application';
        readonly owner: CoreDirected1cExpressionOwnerId;
        readonly arguments: readonly CoreDirected1cExpression[];
    };

export interface CoreDirected1cTypedSlot {
    readonly name: string;
    readonly plicity: Plicity;
    readonly role: string;
    readonly type: CoreDirected1cExpression;
}

export interface CoreDirected1cOwnerProposal {
    readonly order: 0;
    readonly owner: CoreDirected1cCandidateOwnerId;
    readonly activeAuthority: 'transparent-definition';
    readonly candidateDisposition: 'opaque-import';
    readonly slots: readonly CoreDirected1cTypedSlot[];
    readonly result: CoreDirected1cExpression;
    readonly body?: never;
}

export interface CoreDirected1cProposalInput {
    readonly revision: 'DIRECTED-1C';
    readonly experimentId: 'DTTLF-DIRECTED-1C-E01';
    readonly status: 'proposal-awaiting-h-dttlf-02';
    readonly reviewGate: 'H-DTTLF-02/DIRECTED-1C';
    readonly consumer:
        'section-evaluation-over-reviewed-sigma-telescope-family';
    readonly owners: readonly [CoreDirected1cOwnerProposal];
    readonly runtimeRules: readonly [];
    readonly proofTimeRules: readonly [];
    readonly closurePolicy: {
        readonly sectionCategory:
            'reuse-existing-base-owner';
        readonly telescopeFamily:
            'reuse-reviewed-directed-1a-owner';
        readonly telescopeFibreComputation:
            'reuse-reviewed-directed-1b-runtime-rule';
        readonly dependentPair:
            'reuse-reviewed-directed-1b-owner';
        readonly outerApplication:
            'reuse-generic-outer-lf-beta';
        readonly activeTransparentDefinition:
            'import-signature-opaquely';
        readonly emittedShadowDeclarations: false;
        readonly defaultLfProfile: 'unchanged';
    };
    readonly prerequisites: {
        readonly lfProfileReview: 'LF-PROFILE-1-REVIEWED';
        readonly directed1aOwnerIds:
            readonly CoreDirected1aCandidateOwnerId[];
        readonly foundation1RuleIds:
            readonly CoreDirectedFoundationRuleId[];
        readonly foundation2RuleIds:
            readonly CoreDirectedFoundation2RuleId[];
        readonly directed1bReview: 'DIRECTED-1B-REVIEWED';
        readonly directed1bOwnerIds:
            readonly CoreDirected1bCandidateOwnerId[];
        readonly directed1bRuntimeRuleIds: readonly string[];
        readonly baseSectionOwner: 'section-category';
        readonly exactCompletedArtifactsUnchanged: true;
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

export interface CoreDirected1cLambdapiOwnerBinding {
    readonly order: 0;
    readonly owner: CoreDirected1cCandidateOwnerId;
    readonly module: 'emdash.emdash3_2';
    readonly serializedName: 'piapp0';
    readonly activeAuthority: 'transparent-definition';
    readonly candidateDisposition: 'opaque-import';
    readonly provenance: {
        readonly authorityPath: 'emdash2/emdash3_2.lp';
        readonly section: '8c. Section categories and Pi action';
        readonly sourceFragment:
            'symbol piapp0 : Π [K : Cat], Π [E : τ (Catd K)],';
        readonly auditedOn: '2026-07-24';
    };
}

export type CoreDirected1cProposalErrorCode =
    | 'INVALID_PROPOSAL_BOUNDARY'
    | 'INVALID_PREREQUISITE'
    | 'INVALID_OWNER_SET'
    | 'INVALID_EXPRESSION'
    | 'INVALID_CLOSURE_POLICY'
    | 'INVALID_BACKEND_BINDING'
    | 'MVP_PROFILE_DRIFT'
    | 'PROPOSAL_DRIFT';

export class CoreDirected1cProposalError extends Error {
    constructor(
        public readonly code: CoreDirected1cProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirected1cProposalError';
    }
}

const variable = (name: string): CoreDirected1cExpression => ({
    tag: 'variable',
    name
});

const ownerApplication = (
    owner: CoreDirected1cExpressionOwnerId,
    ...arguments_: readonly CoreDirected1cExpression[]
): CoreDirected1cExpression => ({
    tag: 'owner-application',
    owner,
    arguments: arguments_
});

const typedSlot = (
    name: string,
    plicity: Plicity,
    role: string,
    type: CoreDirected1cExpression
): CoreDirected1cTypedSlot => ({
    name,
    plicity,
    role,
    type
});

const categoryUniverse =
    ownerApplication('category-universe');
const categoryOfCategories =
    ownerApplication('category-of-categories');
const K = variable('K');
const E = variable('E');

const objectType = (
    category: CoreDirected1cExpression
): CoreDirected1cExpression => ownerApplication(
    'decode',
    ownerApplication('object-classifier', category)
);

const displayedFamilyType = (
    base: CoreDirected1cExpression
): CoreDirected1cExpression => objectType(
    ownerApplication('displayed-category-category', base)
);

const sectionCategory = (
    base: CoreDirected1cExpression,
    family: CoreDirected1cExpression
): CoreDirected1cExpression => ownerApplication(
    'section-category',
    base,
    family
);

const fibre = (
    base: CoreDirected1cExpression,
    family: CoreDirected1cExpression,
    point: CoreDirected1cExpression
): CoreDirected1cExpression => ownerApplication(
    'functor-object',
    base,
    categoryOfCategories,
    family,
    point
);

const rawOwner: CoreDirected1cOwnerProposal = {
    order: 0,
    owner: 'section-object-evaluation',
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
            'implicit',
            'displayed-family',
            displayedFamilyType(K)
        ),
        typedSlot(
            's',
            'explicit',
            'section-object',
            objectType(sectionCategory(K, E))
        ),
        typedSlot(
            'k',
            'explicit',
            'base-object',
            objectType(K)
        )
    ],
    result: objectType(fibre(K, E, variable('k')))
};

const rawProposal: CoreDirected1cProposalInput = {
    revision: 'DIRECTED-1C',
    experimentId: 'DTTLF-DIRECTED-1C-E01',
    status: 'proposal-awaiting-h-dttlf-02',
    reviewGate: 'H-DTTLF-02/DIRECTED-1C',
    consumer:
        'section-evaluation-over-reviewed-sigma-telescope-family',
    owners: [rawOwner],
    runtimeRules: [],
    proofTimeRules: [],
    closurePolicy: {
        sectionCategory: 'reuse-existing-base-owner',
        telescopeFamily: 'reuse-reviewed-directed-1a-owner',
        telescopeFibreComputation:
            'reuse-reviewed-directed-1b-runtime-rule',
        dependentPair: 'reuse-reviewed-directed-1b-owner',
        outerApplication: 'reuse-generic-outer-lf-beta',
        activeTransparentDefinition: 'import-signature-opaquely',
        emittedShadowDeclarations: false,
        defaultLfProfile: 'unchanged'
    },
    prerequisites: {
        lfProfileReview:
            CORE_LF_CONTINUATION_PROFILE_REVIEW.revision,
        directed1aOwnerIds:
            CORE_DIRECTED_1A_PROPOSAL.owners.map(entry => entry.owner),
        foundation1RuleIds:
            CORE_DIRECTED_FOUNDATION_PROPOSAL.runtimeRules.map(
                entry => entry.id
            ),
        foundation2RuleIds:
            CORE_DIRECTED_FOUNDATION_2_PROPOSAL.runtimeRules.map(
                entry => entry.id
            ),
        directed1bReview: CORE_DIRECTED_1B_REVIEW.revision,
        directed1bOwnerIds:
            CORE_DIRECTED_1B_PROPOSAL.owners.map(entry => entry.owner),
        directed1bRuntimeRuleIds:
            CORE_DIRECTED_1B_PROPOSAL.runtimeRules.map(entry => entry.id),
        baseSectionOwner: 'section-category',
        exactCompletedArtifactsUnchanged: true
    },
    preservedMvpProfile: {
        revision: 'emdash-v3.2-mvp-1',
        contentHash:
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0',
        ownerIds: CORE_MVP_MANIFEST.owners.map(entry => entry.owner),
        runtimeRuleIds: CORE_MVP_MANIFEST.rules.map(rule => rule.id)
    },
    explicitDeferrals: [
        'section evaluator transparent body and evaluation functor',
        'fixed-base internal section functor and its action rules',
        'contravariant displayed-family functor and global internal sections',
        'pullback internal-section family and its fold and pointwise rules',
        'section hom action and section-arrow evaluation',
        'total-category projection-pullback section uncurrying',
        'displayed-transfor telescope uncurrying',
        'groupoidal product and section specialization and closure'
    ],
    nonEffects: [
        'does not redeclare or alter the base section-category owner',
        'does not add a runtime or proof-time rule',
        'does not transfer or check the active evaluator transparent body',
        'does not alter any completed directed proposal, review, or runtime',
        'does not mutate CORE_OWNER_SCHEMAS or integrated directed catalogs',
        'does not mutate CORE_MVP_MANIFEST or CORE_MVP_RUNTIME_PROGRAM',
        'does not alter the default LF-PROFILE-1 runtime component',
        'does not enter src/v3_2/browser.ts',
        'does not authorize product graduation or a metatheory claim',
        'does not mutate the active Lambdapi kernel'
    ]
};

const rawBinding: CoreDirected1cLambdapiOwnerBinding = {
    order: 0,
    owner: 'section-object-evaluation',
    module: 'emdash.emdash3_2',
    serializedName: 'piapp0',
    activeAuthority: 'transparent-definition',
    candidateDisposition: 'opaque-import',
    provenance: {
        authorityPath: 'emdash2/emdash3_2.lp',
        section: '8c. Section categories and Pi action',
        sourceFragment:
            'symbol piapp0 : Π [K : Cat], Π [E : τ (Catd K)],',
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
    code: CoreDirected1cProposalErrorCode,
    message: string
): never => {
    throw new CoreDirected1cProposalError(code, message);
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
    expression: CoreDirected1cExpression,
    availableOwners: ReadonlyMap<string, number>,
    availableVariables: ReadonlySet<string>,
    detail: string
): void => {
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

    const arity = availableOwners.get(expression.owner);
    if (arity === undefined) {
        fail(
            'INVALID_EXPRESSION',
            `${detail} refers to unavailable owner '${expression.owner}'`
        );
    }
    if (expression.arguments.length !== arity) {
        fail(
            'INVALID_EXPRESSION',
            `${detail} applies '${expression.owner}' to ` +
            `${expression.arguments.length} arguments, expected ${arity}`
        );
    }
    expression.arguments.forEach((argument, index) =>
        validateExpression(
            argument,
            availableOwners,
            availableVariables,
            `${detail}, ${expression.owner} argument ${index}`
        )
    );
};

const validateTypedTelescope = (
    slots: readonly CoreDirected1cTypedSlot[],
    availableOwners: ReadonlyMap<string, number>
): ReadonlySet<string> => {
    const availableVariables = new Set<string>();
    slots.forEach((slot, index) => {
        if (
            !PORTABLE_NAME.test(slot.name) ||
            availableVariables.has(slot.name) ||
            slot.role.length === 0 ||
            (
                slot.plicity !== 'explicit' &&
                slot.plicity !== 'implicit'
            )
        ) {
            fail(
                'INVALID_EXPRESSION',
                `DIRECTED-1C owner has an invalid slot at ${index}`
            );
        }
        validateExpression(
            slot.type,
            availableOwners,
            availableVariables,
            `DIRECTED-1C slot ${slot.name} type`
        );
        availableVariables.add(slot.name);
    });
    return availableVariables;
};

export const CORE_DIRECTED_1C_PROPOSAL =
    deepFreeze(rawProposal);

export const LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING =
    deepFreeze(rawBinding);

/**
 * Validate the exact proposal without granting authority to integrate it.
 */
export function validateCoreDirected1cProposal(
    proposal: CoreDirected1cProposalInput =
        CORE_DIRECTED_1C_PROPOSAL,
    binding: CoreDirected1cLambdapiOwnerBinding =
        LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING
): void {
    if (
        proposal.revision !== 'DIRECTED-1C' ||
        proposal.experimentId !== 'DTTLF-DIRECTED-1C-E01' ||
        proposal.status !== 'proposal-awaiting-h-dttlf-02' ||
        proposal.reviewGate !== 'H-DTTLF-02/DIRECTED-1C' ||
        proposal.consumer !==
            'section-evaluation-over-reviewed-sigma-telescope-family'
    ) {
        fail(
            'INVALID_PROPOSAL_BOUNDARY',
            'DIRECTED-1C must remain the exact section consumer proposal ' +
            'awaiting its own H-DTTLF-02 decision'
        );
    }

    try {
        validateCoreLfContinuationProfileReview(
            CORE_LF_CONTINUATION_PROFILE_REVIEW
        );
        validateCoreDirectedFoundationReview(
            CORE_DIRECTED_FOUNDATION_REVIEW
        );
        validateCoreDirectedFoundation2Review(
            CORE_DIRECTED_FOUNDATION_2_REVIEW
        );
        validateCoreDirected1bReview(CORE_DIRECTED_1B_REVIEW);
    } catch (error: unknown) {
        fail(
            'INVALID_PREREQUISITE',
            'DIRECTED-1C requires the exact reviewed LF and directed ' +
            'boundaries: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }

    const expectedPrerequisites = rawProposal.prerequisites;
    if (
        !sameData(proposal.prerequisites, expectedPrerequisites) ||
        !Object.prototype.hasOwnProperty.call(
            CORE_OWNER_SCHEMAS,
            proposal.prerequisites.baseSectionOwner
        )
    ) {
        fail(
            'INVALID_PREREQUISITE',
            'DIRECTED-1C prerequisite reviews, owners, or rules drifted'
        );
    }

    if (
        proposal.owners.length !== 1 ||
        proposal.owners[0].order !== 0 ||
        proposal.owners[0].owner !== 'section-object-evaluation' ||
        proposal.owners[0].activeAuthority !==
            'transparent-definition' ||
        proposal.owners[0].candidateDisposition !== 'opaque-import' ||
        proposal.owners[0].body !== undefined ||
        proposal.runtimeRules.length !== 0 ||
        proposal.proofTimeRules.length !== 0 ||
        Object.prototype.hasOwnProperty.call(
            CORE_OWNER_SCHEMAS,
            proposal.owners[0].owner
        )
    ) {
        fail(
            'INVALID_OWNER_SET',
            'DIRECTED-1C must propose exactly one opaque import of active ' +
            'piapp0 and zero runtime or proof-time rules'
        );
    }

    const availableOwners = new Map<string, number>(
        Object.entries(CORE_OWNER_SCHEMAS).map(([owner, schema]) => [
            owner,
            schema.slots.length
        ])
    );
    const variables = validateTypedTelescope(
        proposal.owners[0].slots,
        availableOwners
    );
    validateExpression(
        proposal.owners[0].result,
        availableOwners,
        variables,
        'DIRECTED-1C owner result'
    );

    if (
        proposal.closurePolicy.sectionCategory !==
            'reuse-existing-base-owner' ||
        proposal.closurePolicy.telescopeFamily !==
            'reuse-reviewed-directed-1a-owner' ||
        proposal.closurePolicy.telescopeFibreComputation !==
            'reuse-reviewed-directed-1b-runtime-rule' ||
        proposal.closurePolicy.dependentPair !==
            'reuse-reviewed-directed-1b-owner' ||
        proposal.closurePolicy.outerApplication !==
            'reuse-generic-outer-lf-beta' ||
        proposal.closurePolicy.activeTransparentDefinition !==
            'import-signature-opaquely' ||
        proposal.closurePolicy.emittedShadowDeclarations !== false ||
        proposal.closurePolicy.defaultLfProfile !== 'unchanged'
    ) {
        fail(
            'INVALID_CLOSURE_POLICY',
            'DIRECTED-1C must reuse the existing section, telescope, pair, ' +
            'runtime, and outer-LF owners without importing a body'
        );
    }

    if (
        binding.order !== 0 ||
        binding.owner !== proposal.owners[0].owner ||
        binding.module !== 'emdash.emdash3_2' ||
        binding.serializedName !== 'piapp0' ||
        binding.activeAuthority !==
            proposal.owners[0].activeAuthority ||
        binding.candidateDisposition !==
            proposal.owners[0].candidateDisposition ||
        binding.provenance.authorityPath !==
            'emdash2/emdash3_2.lp' ||
        binding.provenance.section !==
            '8c. Section categories and Pi action' ||
        binding.provenance.auditedOn !== '2026-07-24'
    ) {
        fail(
            'INVALID_BACKEND_BINDING',
            'DIRECTED-1C backend evidence must bind the exact active piapp0 ' +
            'owner and authority class'
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
            'DIRECTED-1C must preserve the exact emdash-v3.2-mvp-1 profile'
        );
    }

    if (
        !sameData(proposal, rawProposal) ||
        !sameData(binding, rawBinding)
    ) {
        fail(
            'PROPOSAL_DRIFT',
            'DIRECTED-1C differs from its exact H-DTTLF-02 review input'
        );
    }
}

validateCoreDirected1cProposal();
