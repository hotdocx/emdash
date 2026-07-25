/**
 * Fresh DIRECTED-GRADUATE-1 proposal for H-DTTLF-03.
 *
 * This artifact closes the exact combined outer-LF/directed-DTT profile over
 * its full signature and runtime dependencies. It recommends authority only
 * for the opt-in continuation API. It does not authorize itself, alter the
 * frozen MVP, enter the browser graph, or make a metatheory claim.
 */

import {
    CORE_DIRECTED_1A_PRIMITIVE_NAMES
} from './directed_1a';
import {
    CORE_DIRECTED_1A_PROPOSAL,
    CoreDirected1aOwnerProposal
} from './directed_1a_proposal';
import {
    CORE_DIRECTED_1B_PRIMITIVE_NAMES
} from './directed_1b';
import {
    CORE_DIRECTED_1B_PROPOSAL,
    CoreDirected1bOwnerProposal,
    CoreDirected1bRuntimeRuleProposal
} from './directed_1b_proposal';
import {
    CORE_DIRECTED_1B_REVIEW,
    validateCoreDirected1bReview
} from './directed_1b_review';
import {
    CORE_DIRECTED_1C_PRIMITIVE_NAMES,
    CoreDirected1cCatalog
} from './directed_1c';
import {
    CORE_DIRECTED_1C_PROPOSAL,
    CoreDirected1cOwnerProposal
} from './directed_1c_proposal';
import {
    CORE_DIRECTED_1C_REVIEW,
    validateCoreDirected1cReview
} from './directed_1c_review';
import {
    CORE_DIRECTED_FOUNDATION_2_PROPOSAL,
    CoreDirectedFoundation2RuntimeRuleProposal
} from './directed_foundation_2_proposal';
import {
    CORE_DIRECTED_FOUNDATION_2_REVIEW,
    validateCoreDirectedFoundation2Review
} from './directed_foundation_2_review';
import {
    CORE_DIRECTED_FOUNDATION_PROPOSAL,
    CoreDirectedFoundationRuntimeRuleProposal
} from './directed_foundation_proposal';
import {
    CORE_DIRECTED_FOUNDATION_REVIEW,
    validateCoreDirectedFoundationReview
} from './directed_foundation_review';
import {
    CORE_DIRECTED_1A_REVIEW,
    CORE_LF_CONTINUATION_PROFILE_REVIEW,
    validateCoreDirected1aReview,
    validateCoreLfContinuationProfileReview
} from './continuation_review';
import {
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
} from './lf_checker';
import {
    CoreLfProfileProposalInput
} from './lf_profile_proposal';
import {
    CORE_MVP_MANIFEST,
    CoreManifestRuleInput,
    validateCoreMvpManifest
} from './manifest';
import {
    CORE_OWNER_TYPE_SCHEMAS,
    CoreOwnerTypeSchema
} from './signature';

export type CoreDirectedGraduationBaseOwnerSource =
    | 'frozen-mvp-signature'
    | 'continuation-base-signature';

export interface CoreDirectedGraduationBaseOwnerEntry {
    readonly order: number;
    readonly owner: string;
    readonly source: CoreDirectedGraduationBaseOwnerSource;
    readonly signature: CoreOwnerTypeSchema;
}

export type CoreDirectedGraduationDeclarationSnapshot =
    | CoreDirected1aOwnerProposal
    | CoreDirected1bOwnerProposal
    | CoreDirected1cOwnerProposal;

export interface CoreDirectedGraduationDeclarationEntry {
    readonly order: number;
    readonly extensionOrder: number;
    readonly sourceSlice:
        | 'DIRECTED-1A'
        | 'DIRECTED-1B'
        | 'DIRECTED-1C';
    readonly sourceReview:
        | 'DIRECTED-1A-REVIEWED'
        | 'DIRECTED-1B-REVIEWED'
        | 'DIRECTED-1C-REVIEWED';
    readonly owner: string;
    readonly coreName: string;
    readonly activeAuthority: string;
    readonly candidateDisposition:
        | 'opaque-import'
        | 'transparent-checked-definition';
    readonly bodyPolicy:
        | 'body-free'
        | 'exact-checked-transparent-mirror';
    readonly signatureSnapshot:
        CoreDirectedGraduationDeclarationSnapshot;
}

export type CoreDirectedGraduationRuntimeSnapshot =
    | CoreDirectedFoundationRuntimeRuleProposal
    | CoreDirectedFoundation2RuntimeRuleProposal
    | CoreDirected1bRuntimeRuleProposal
    | CoreManifestRuleInput;

export interface CoreDirectedGraduationRuntimeEntry {
    readonly order: number;
    readonly source:
        | 'DIRECTED-FOUNDATION-1'
        | 'DIRECTED-FOUNDATION-2'
        | 'DIRECTED-1B'
        | 'emdash-v3.2-mvp-1';
    readonly sourceReview:
        | 'DIRECTED-FOUNDATION-1-REVIEWED'
        | 'DIRECTED-FOUNDATION-2-REVIEWED'
        | 'DIRECTED-1B-REVIEWED'
        | 'H-03/D-023';
    readonly id: string;
    readonly authority: 'runtime-reduction';
    readonly executionPhase:
        | 'catalog-runtime'
        | 'frozen-mvp-runtime';
    readonly ruleSnapshot: CoreDirectedGraduationRuntimeSnapshot;
}

export interface CoreDirectedGraduationManifestInput {
    readonly status: 'proposal-awaiting-h-dttlf-03';
    readonly revision: 'emdash-v3.2-dttlf-directed-1';
    readonly ruleSelection: 'closed-world-combined-candidate';
    readonly outerLf: {
        readonly reviewRevision: 'LF-PROFILE-1-REVIEWED';
        readonly proposalSnapshot: CoreLfProfileProposalInput;
        readonly transitionOrder:
            readonly ['zonk', 'beta', 'delta', 'reviewed-runtime'];
        readonly comparisonStepLimit: 256;
        readonly eta: 'disabled';
        readonly arbitraryUserRules: 'excluded';
    };
    readonly baseOwnerSignatures:
        readonly CoreDirectedGraduationBaseOwnerEntry[];
    readonly candidateDeclarations:
        readonly CoreDirectedGraduationDeclarationEntry[];
    readonly runtimeRules:
        readonly CoreDirectedGraduationRuntimeEntry[];
    readonly proofTimeRules: readonly [];
    readonly composition: {
        readonly baseOwnerSignatureCount: 20;
        readonly candidateDeclarationCount: 9;
        readonly totalOwnerSignatureCount: 29;
        readonly opaqueCandidateDeclarationCount: 8;
        readonly transparentCandidateDeclarationCount: 1;
        readonly directedRuntimeRuleCount: 7;
        readonly inheritedMvpRuntimeRuleCount: 3;
        readonly totalRuntimeRuleCount: 10;
        readonly proofTimeRuleCount: 0;
        readonly runtimeOrder:
            'catalog-seven-before-frozen-mvp-three';
        readonly oneSharedOuterLfBudget: true;
    };
    readonly preservedMvp: {
        readonly revision: 'emdash-v3.2-mvp-1';
        readonly contentHash:
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0';
        readonly ownerIds: readonly string[];
        readonly runtimeRuleIds: readonly string[];
        readonly mutation: false;
    };
    readonly contentHash: string;
}

export interface CoreDirectedGraduationRecommendationInput {
    readonly revision: 'DIRECTED-GRADUATE-1';
    readonly status: 'proposal-awaiting-h-dttlf-03';
    readonly reviewGate: 'H-DTTLF-03';
    readonly decisionId: 'D-DTTLF-001';
    readonly candidateManifest: CoreDirectedGraduationManifestInput;
    readonly productBoundary: {
        readonly recommendation:
            'approve-authoritative-opt-in-continuation-kernel';
        readonly scope: 'exact-combined-profile-only';
        readonly entryPoint: 'src/v3_2/index.ts';
        readonly browserEntryPoint: 'excluded';
        readonly deployedMvpProfile: 'unchanged';
        readonly releaseReady: false;
        readonly lambdapiProductionRuntimeDependency: false;
    };
    readonly lambdapiPolicy: {
        readonly mathematicalSpecification: 'active';
        readonly fixedGraduationCorpus: 'required';
        readonly positiveAndNegativeOracle: 'required';
        readonly subjectReductionOracle: 'required';
        readonly selectedChangeAcceptanceAuthority: 'retained';
        readonly perTermRuntimeCheck: 'not-required';
        readonly acceptanceTriggers: readonly string[];
    };
    readonly claimBoundary: {
        readonly deterministicBoundedChecking:
            'implemented-exact-profile';
        readonly boundedStopping: 'implemented';
        readonly inheritedMvpThreeRuleTermination:
            'preserved-for-subprogram-only';
        readonly combinedTermination: 'withheld';
        readonly unrestrictedNormalization: 'withheld';
        readonly confluence: 'withheld';
        readonly typescriptSubjectReduction: 'withheld';
        readonly performanceSla: 'withheld';
        readonly additionalOwnerOrRuleAuthority: false;
    };
    readonly evidence: {
        readonly consumer:
            'outer-beta-section-evaluation-over-sigma-telescope';
        readonly typescriptPositiveConsumerCount: 1;
        readonly typescriptNegativeFamilyOrPairCount: 2;
        readonly generatedLambdapiPositiveCount: 1;
        readonly generatedLambdapiNegativeCount: 1;
        readonly scopedBuilderParity: 'passed';
        readonly combinedTrace:
            readonly [
                'beta',
                'directed.sigma-telescope-fibre.evaluate'
            ];
        readonly validationGates: readonly string[];
    };
    readonly residualRisks: readonly string[];
    readonly explicitDeferrals: readonly string[];
    readonly nonEffects: readonly string[];
    readonly decisionQuestion: string;
    readonly authorityAuthorized: false;
}

export type CoreDirectedGraduationProposalErrorCode =
    | 'GRADUATION_PREREQUISITE_DRIFT'
    | 'GRADUATION_MANIFEST_DRIFT'
    | 'GRADUATION_IMPLEMENTATION_DRIFT'
    | 'GRADUATION_HASH_DRIFT'
    | 'GRADUATION_RECOMMENDATION_DRIFT';

export class CoreDirectedGraduationProposalError extends Error {
    constructor(
        public readonly code: CoreDirectedGraduationProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirectedGraduationProposalError';
    }
}

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

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
    code: CoreDirectedGraduationProposalErrorCode,
    message: string
): never => {
    throw new CoreDirectedGraduationProposalError(code, message);
};

const combinedBaseOwnerIds = [
    'groupoid-universe',
    'category-universe',
    'decode',
    'object-classifier',
    'functor-classifier',
    'hom-classifier',
    'transfor-classifier',
    'category-of-categories',
    'hom-category',
    'transfor-category',
    'displayed-category-category',
    'constant-displayed-family',
    'section-category',
    'functor-object',
    'functor-hom-full',
    'functor-hom-capped',
    'transfor-component-full',
    'transfor-component-capped',
    'transfor-hom-full',
    'transfor-hom-capped'
] as const;

const mvpOwnerIds = new Set(
    CORE_MVP_MANIFEST.owners.map(entry => entry.owner)
);

const baseOwnerSignatures: CoreDirectedGraduationBaseOwnerEntry[] =
    combinedBaseOwnerIds.map((owner, order) => {
        const mvpEntry = CORE_MVP_MANIFEST.owners.find(
            entry => entry.owner === owner
        );
        return {
            order,
            owner,
            source: mvpOwnerIds.has(owner)
                ? 'frozen-mvp-signature'
                : 'continuation-base-signature',
            signature: cloneData(
                mvpEntry?.signature ??
                CORE_OWNER_TYPE_SCHEMAS[owner]
            )
        };
    });

const direct1aDeclarations: CoreDirectedGraduationDeclarationEntry[] =
    CORE_DIRECTED_1A_PROPOSAL.owners.map((owner, extensionOrder) => ({
        order: combinedBaseOwnerIds.length + extensionOrder,
        extensionOrder,
        sourceSlice: 'DIRECTED-1A',
        sourceReview: 'DIRECTED-1A-REVIEWED',
        owner: owner.owner,
        coreName: CORE_DIRECTED_1A_PRIMITIVE_NAMES[owner.owner],
        activeAuthority: owner.authority,
        candidateDisposition: 'opaque-import',
        bodyPolicy: 'body-free',
        signatureSnapshot: cloneData(owner)
    }));

const direct1bDeclarations: CoreDirectedGraduationDeclarationEntry[] =
    CORE_DIRECTED_1B_PROPOSAL.owners.map((owner, localOrder) => {
        const extensionOrder =
            direct1aDeclarations.length + localOrder;
        return {
            order: combinedBaseOwnerIds.length + extensionOrder,
            extensionOrder,
            sourceSlice: 'DIRECTED-1B',
            sourceReview: 'DIRECTED-1B-REVIEWED',
            owner: owner.owner,
            coreName: CORE_DIRECTED_1B_PRIMITIVE_NAMES[owner.owner],
            activeAuthority: owner.activeAuthority,
            candidateDisposition: owner.candidateDisposition,
            bodyPolicy:
                owner.candidateDisposition ===
                    'transparent-checked-definition'
                    ? 'exact-checked-transparent-mirror'
                    : 'body-free',
            signatureSnapshot: cloneData(owner)
        };
    });

const direct1cDeclarations: CoreDirectedGraduationDeclarationEntry[] =
    CORE_DIRECTED_1C_PROPOSAL.owners.map((owner, localOrder) => {
        const extensionOrder =
            direct1aDeclarations.length +
            direct1bDeclarations.length +
            localOrder;
        return {
            order: combinedBaseOwnerIds.length + extensionOrder,
            extensionOrder,
            sourceSlice: 'DIRECTED-1C',
            sourceReview: 'DIRECTED-1C-REVIEWED',
            owner: owner.owner,
            coreName: CORE_DIRECTED_1C_PRIMITIVE_NAMES[owner.owner],
            activeAuthority: owner.activeAuthority,
            candidateDisposition: owner.candidateDisposition,
            bodyPolicy: 'body-free',
            signatureSnapshot: cloneData(owner)
        };
    });

const candidateDeclarations = [
    ...direct1aDeclarations,
    ...direct1bDeclarations,
    ...direct1cDeclarations
];

const foundation1Runtime: CoreDirectedGraduationRuntimeEntry[] =
    CORE_DIRECTED_FOUNDATION_PROPOSAL.runtimeRules.map(
        (rule, order) => ({
            order,
            source: 'DIRECTED-FOUNDATION-1',
            sourceReview: 'DIRECTED-FOUNDATION-1-REVIEWED',
            id: rule.id,
            authority: 'runtime-reduction',
            executionPhase: 'catalog-runtime',
            ruleSnapshot: cloneData(rule)
        })
    );

const foundation2Runtime: CoreDirectedGraduationRuntimeEntry[] =
    CORE_DIRECTED_FOUNDATION_2_PROPOSAL.runtimeRules.map(
        (rule, localOrder) => ({
            order: foundation1Runtime.length + localOrder,
            source: 'DIRECTED-FOUNDATION-2',
            sourceReview: 'DIRECTED-FOUNDATION-2-REVIEWED',
            id: rule.id,
            authority: 'runtime-reduction',
            executionPhase: 'catalog-runtime',
            ruleSnapshot: cloneData(rule)
        })
    );

const direct1bRuntime: CoreDirectedGraduationRuntimeEntry[] =
    CORE_DIRECTED_1B_PROPOSAL.runtimeRules.map(
        (rule, localOrder) => ({
            order:
                foundation1Runtime.length +
                foundation2Runtime.length +
                localOrder,
            source: 'DIRECTED-1B',
            sourceReview: 'DIRECTED-1B-REVIEWED',
            id: rule.id,
            authority: 'runtime-reduction',
            executionPhase: 'catalog-runtime',
            ruleSnapshot: cloneData(rule)
        })
    );

const directedRuntimeCount =
    foundation1Runtime.length +
    foundation2Runtime.length +
    direct1bRuntime.length;

const inheritedMvpRuntime: CoreDirectedGraduationRuntimeEntry[] =
    CORE_MVP_MANIFEST.rules.map((rule, localOrder) => ({
        order: directedRuntimeCount + localOrder,
        source: 'emdash-v3.2-mvp-1',
        sourceReview: 'H-03/D-023',
        id: rule.id,
        authority: 'runtime-reduction',
        executionPhase: 'frozen-mvp-runtime',
        ruleSnapshot: cloneData(rule)
    }));

const runtimeRules = [
    ...foundation1Runtime,
    ...foundation2Runtime,
    ...direct1bRuntime,
    ...inheritedMvpRuntime
];

const rawManifestContent: Omit<
    CoreDirectedGraduationManifestInput,
    'contentHash'
> = {
    status: 'proposal-awaiting-h-dttlf-03',
    revision: 'emdash-v3.2-dttlf-directed-1',
    ruleSelection: 'closed-world-combined-candidate',
    outerLf: {
        reviewRevision: 'LF-PROFILE-1-REVIEWED',
        proposalSnapshot: cloneData(
            CORE_LF_CONTINUATION_PROFILE_REVIEW.proposal
        ),
        transitionOrder: [
            'zonk',
            'beta',
            'delta',
            'reviewed-runtime'
        ],
        comparisonStepLimit: 256,
        eta: 'disabled',
        arbitraryUserRules: 'excluded'
    },
    baseOwnerSignatures,
    candidateDeclarations,
    runtimeRules,
    proofTimeRules: [],
    composition: {
        baseOwnerSignatureCount: 20,
        candidateDeclarationCount: 9,
        totalOwnerSignatureCount: 29,
        opaqueCandidateDeclarationCount: 8,
        transparentCandidateDeclarationCount: 1,
        directedRuntimeRuleCount: 7,
        inheritedMvpRuntimeRuleCount: 3,
        totalRuntimeRuleCount: 10,
        proofTimeRuleCount: 0,
        runtimeOrder: 'catalog-seven-before-frozen-mvp-three',
        oneSharedOuterLfBudget: true
    },
    preservedMvp: {
        revision: 'emdash-v3.2-mvp-1',
        contentHash:
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0',
        ownerIds: CORE_MVP_MANIFEST.owners.map(entry => entry.owner),
        runtimeRuleIds: CORE_MVP_MANIFEST.rules.map(rule => rule.id),
        mutation: false
    }
};

const reviewedCandidateContentHash =
    'sha256:5fbf855e044e3d24e1078289eebad4a3391d67747efcee3c5463c2bfb110a8c7';

const rawManifest: CoreDirectedGraduationManifestInput = {
    ...rawManifestContent,
    contentHash: reviewedCandidateContentHash
};

const acceptanceTriggers = [
    'combined-base-or-candidate-owner-signature-change',
    'combined-runtime-rule-shape-order-or-authority-change',
    'outer-lf-transition-transparency-or-budget-change',
    'browser-release-or-deployed-profile-promotion',
    'termination-confluence-subject-reduction-or-performance-claim-change',
    'graduation-corpus-or-lambdapi-binding-change'
] as const;

const validationGates = [
    'focused-graduation-manifest-tests',
    'combined-typescript-positive-and-negative-consumers',
    'generated-lambdapi-positive-and-negative-oracle',
    'root-check-ts',
    'bounded-active-lambdapi-check',
    'full-repository-check-all'
] as const;

const residualRisks = [
    'the combined evaluator guarantees bounded stopping, not normalization',
    'general termination and confluence of beta-delta plus ten rules are unproved',
    'standalone TypeScript subject reduction remains unproved',
    'the directed transfer covers one representative nested telescope, not the full active tower',
    'the continuation profile has no browser packaging or release completion',
    'no representative-workload performance measurement or SLA exists'
] as const;

const explicitDeferrals = [
    'active piapp0 transparent body and evaluation-functor closure',
    'internal and pullback Pi owners and action rules',
    'section-arrow evaluation and section uncurrying',
    'general Sigma hom normalization and sigma_arrow closure',
    'projection-pullback and displayed-transfor uncurrying',
    'systematic groupoidal specialization and closure',
    'textual parsing and browser or release packaging'
] as const;

const nonEffects = [
    'does not authorize H-DTTLF-03 by construction',
    'does not mutate emdash-v3.2-mvp-1 or its browser entry point',
    'does not add an owner, runtime rule, or proof-time rule',
    'does not transfer another active definition body',
    'does not make Lambdapi a production runtime dependency',
    'does not authorize unrestricted normalization or combined termination',
    'does not authorize confluence or TypeScript subject reduction',
    'does not authorize a performance SLA or release readiness',
    'does not open the groupoidal closure programme'
] as const;

const decisionQuestion =
    'Approve H-DTTLF-03/D-DTTLF-001 as proposed: graduate exactly ' +
    'emdash-v3.2-dttlf-directed-1 as the authoritative opt-in TypeScript ' +
    'continuation checker/evaluator, with 20 base signatures plus 9 reviewed ' +
    'candidate declarations (29 total), 7 directed plus 3 inherited MVP ' +
    'runtime rules (10 total), zero proof-time rules, one bounded outer-LF ' +
    'budget, no browser or deployed-MVP change, and no Lambdapi production ' +
    'dependency; retain Lambdapi as the active mathematical specification, ' +
    'required fixed positive/negative and subject-reduction oracle, and ' +
    'selected-change acceptance authority; and withhold unrestricted ' +
    'normalization, combined termination, confluence, standalone TypeScript ' +
    'subject reduction, performance, release, internal-Pi/uncurrying, and ' +
    'groupoidal-closure claims?';

const rawRecommendation: CoreDirectedGraduationRecommendationInput = {
    revision: 'DIRECTED-GRADUATE-1',
    status: 'proposal-awaiting-h-dttlf-03',
    reviewGate: 'H-DTTLF-03',
    decisionId: 'D-DTTLF-001',
    candidateManifest: rawManifest,
    productBoundary: {
        recommendation:
            'approve-authoritative-opt-in-continuation-kernel',
        scope: 'exact-combined-profile-only',
        entryPoint: 'src/v3_2/index.ts',
        browserEntryPoint: 'excluded',
        deployedMvpProfile: 'unchanged',
        releaseReady: false,
        lambdapiProductionRuntimeDependency: false
    },
    lambdapiPolicy: {
        mathematicalSpecification: 'active',
        fixedGraduationCorpus: 'required',
        positiveAndNegativeOracle: 'required',
        subjectReductionOracle: 'required',
        selectedChangeAcceptanceAuthority: 'retained',
        perTermRuntimeCheck: 'not-required',
        acceptanceTriggers
    },
    claimBoundary: {
        deterministicBoundedChecking: 'implemented-exact-profile',
        boundedStopping: 'implemented',
        inheritedMvpThreeRuleTermination:
            'preserved-for-subprogram-only',
        combinedTermination: 'withheld',
        unrestrictedNormalization: 'withheld',
        confluence: 'withheld',
        typescriptSubjectReduction: 'withheld',
        performanceSla: 'withheld',
        additionalOwnerOrRuleAuthority: false
    },
    evidence: {
        consumer:
            'outer-beta-section-evaluation-over-sigma-telescope',
        typescriptPositiveConsumerCount: 1,
        typescriptNegativeFamilyOrPairCount: 2,
        generatedLambdapiPositiveCount: 1,
        generatedLambdapiNegativeCount: 1,
        scopedBuilderParity: 'passed',
        combinedTrace: [
            'beta',
            'directed.sigma-telescope-fibre.evaluate'
        ],
        validationGates
    },
    residualRisks,
    explicitDeferrals,
    nonEffects,
    decisionQuestion,
    authorityAuthorized: false
};

export const CORE_DIRECTED_GRADUATION_MANIFEST =
    deepFreeze(rawManifest);

export const CORE_DIRECTED_GRADUATION_RECOMMENDATION =
    deepFreeze(rawRecommendation);

const actualMvpIdentity = () => ({
    revision: CORE_MVP_MANIFEST.revision,
    contentHash: CORE_MVP_MANIFEST.contentHash,
    ownerIds: CORE_MVP_MANIFEST.owners.map(entry => entry.owner),
    runtimeRuleIds: CORE_MVP_MANIFEST.rules.map(rule => rule.id),
    mutation: false
});

const actualCatalogIdentity = () => {
    const catalog = CoreDirected1cCatalog.create();
    catalog.createChecker().validateEnvironment();
    return {
        declarations: catalog.environment.declarations.map(
            declaration => ({
                name: declaration.name,
                transparency: declaration.transparency,
                body:
                    declaration.body === undefined
                        ? 'body-free'
                        : 'checked-body'
            })
        ),
        runtimeRuleIds: [
            ...catalog.runtimeProgram.ruleIds,
            ...CORE_MVP_MANIFEST.rules.map(rule => rule.id)
        ]
    };
};

const expectedCatalogIdentity = {
    declarations: candidateDeclarations.map(entry => ({
        name: entry.coreName,
        transparency:
            entry.candidateDisposition ===
                'transparent-checked-definition'
                ? 'transparent'
                : 'opaque',
        body:
            entry.bodyPolicy === 'exact-checked-transparent-mirror'
                ? 'checked-body'
                : 'body-free'
    })),
    runtimeRuleIds: runtimeRules.map(entry => entry.id)
};

const collectOwnerApplications = (
    value: unknown,
    result: Set<string>
): void => {
    if (value === null || typeof value !== 'object') return;
    const record = value as Record<string, unknown>;
    if (
        record.tag === 'owner-application' &&
        typeof record.owner === 'string'
    ) {
        result.add(record.owner);
    }
    Object.values(record).forEach(child => {
        if (Array.isArray(child)) {
            child.forEach(item =>
                collectOwnerApplications(item, result)
            );
        } else {
            collectOwnerApplications(child, result);
        }
    });
};

const validateManifestOwnerClosure = (
    manifest: CoreDirectedGraduationManifestInput
): void => {
    const allowed = new Set([
        ...manifest.baseOwnerSignatures.map(entry => entry.owner),
        ...manifest.candidateDeclarations.map(entry => entry.owner)
    ]);
    const references = new Set<string>();
    manifest.baseOwnerSignatures.forEach(entry =>
        collectOwnerApplications(entry.signature, references)
    );
    manifest.candidateDeclarations.forEach(entry =>
        collectOwnerApplications(
            entry.signatureSnapshot,
            references
        )
    );
    manifest.runtimeRules.forEach(entry =>
        collectOwnerApplications(entry.ruleSnapshot, references)
    );
    const missing = [...references].filter(owner => !allowed.has(owner));
    if (missing.length > 0) {
        fail(
            'GRADUATION_MANIFEST_DRIFT',
            'The combined graduation owner closure is missing: ' +
            missing.join(', ')
        );
    }
};

const validatePrerequisites = (): void => {
    try {
        validateCoreMvpManifest(CORE_MVP_MANIFEST);
        validateCoreLfContinuationProfileReview(
            CORE_LF_CONTINUATION_PROFILE_REVIEW
        );
        validateCoreDirected1aReview(CORE_DIRECTED_1A_REVIEW);
        validateCoreDirectedFoundationReview(
            CORE_DIRECTED_FOUNDATION_REVIEW
        );
        validateCoreDirectedFoundation2Review(
            CORE_DIRECTED_FOUNDATION_2_REVIEW
        );
        validateCoreDirected1bReview(CORE_DIRECTED_1B_REVIEW);
        validateCoreDirected1cReview(CORE_DIRECTED_1C_REVIEW);
    } catch (error: unknown) {
        fail(
            'GRADUATION_PREREQUISITE_DRIFT',
            'DIRECTED-GRADUATE-1 reviewed prerequisite drift: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
};

export function validateCoreDirectedGraduationManifest(
    manifest: CoreDirectedGraduationManifestInput =
        CORE_DIRECTED_GRADUATION_MANIFEST
): void {
    validatePrerequisites();
    validateManifestOwnerClosure(manifest);

    if (
        manifest.status !== 'proposal-awaiting-h-dttlf-03' ||
        manifest.revision !== 'emdash-v3.2-dttlf-directed-1' ||
        manifest.ruleSelection !== 'closed-world-combined-candidate' ||
        manifest.outerLf.reviewRevision !== 'LF-PROFILE-1-REVIEWED' ||
        manifest.outerLf.comparisonStepLimit !==
            CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT ||
        !sameData(
            manifest.outerLf.proposalSnapshot,
            CORE_LF_CONTINUATION_PROFILE_REVIEW.proposal
        ) ||
        !sameData(
            manifest.baseOwnerSignatures,
            rawManifestContent.baseOwnerSignatures
        ) ||
        !sameData(
            manifest.candidateDeclarations,
            rawManifestContent.candidateDeclarations
        ) ||
        !sameData(
            manifest.runtimeRules,
            rawManifestContent.runtimeRules
        ) ||
        manifest.proofTimeRules.length !== 0 ||
        !sameData(
            manifest.composition,
            rawManifestContent.composition
        ) ||
        !sameData(manifest.preservedMvp, actualMvpIdentity())
    ) {
        fail(
            'GRADUATION_MANIFEST_DRIFT',
            'The combined DIRECTED-GRADUATE-1 manifest boundary drifted'
        );
    }

    try {
        if (!sameData(actualCatalogIdentity(), expectedCatalogIdentity)) {
            fail(
                'GRADUATION_IMPLEMENTATION_DRIFT',
                'The live DIRECTED-1C catalog differs from the combined ' +
                'graduation manifest'
            );
        }
    } catch (error: unknown) {
        if (error instanceof CoreDirectedGraduationProposalError) {
            throw error;
        }
        fail(
            'GRADUATION_IMPLEMENTATION_DRIFT',
            'The live directed catalog failed graduation validation: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }

    const { contentHash: _contentHash, ...content } = manifest;
    if (
        manifest.contentHash !== reviewedCandidateContentHash ||
        !sameData(content, rawManifestContent)
    ) {
        fail(
            'GRADUATION_HASH_DRIFT',
            'The fresh combined candidate content or hash drifted'
        );
    }
}

export function validateCoreDirectedGraduationRecommendation(
    recommendation: CoreDirectedGraduationRecommendationInput =
        CORE_DIRECTED_GRADUATION_RECOMMENDATION
): void {
    validateCoreDirectedGraduationManifest(
        recommendation.candidateManifest
    );
    if (
        recommendation.revision !== 'DIRECTED-GRADUATE-1' ||
        recommendation.status !==
            'proposal-awaiting-h-dttlf-03' ||
        recommendation.reviewGate !== 'H-DTTLF-03' ||
        recommendation.decisionId !== 'D-DTTLF-001' ||
        recommendation.authorityAuthorized !== false ||
        !sameData(recommendation, rawRecommendation)
    ) {
        fail(
            'GRADUATION_RECOMMENDATION_DRIFT',
            'DIRECTED-GRADUATE-1 differs from its exact H-DTTLF-03 input'
        );
    }
}

validateCoreDirectedGraduationRecommendation();
