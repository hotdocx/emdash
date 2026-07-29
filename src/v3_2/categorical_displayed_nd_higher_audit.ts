/**
 * Executable DISPLAYED-ND-HIGHER-1B authority/dependency audit.
 *
 * This artifact freezes the measured source-command closure and one concrete
 * next-hom consumer. It deliberately installs no transfer declaration,
 * runtime rule, surface method, Core owner, or checker branch.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_ND_AUDIT
} from './categorical_displayed_nd_audit';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_REVIEW,
    validateCoreCategoricalDisplayedNdReview
} from './categorical_displayed_nd_review';
import {
    compileCoreCategoricalDisplayedChain2aClosureTransfer
} from './categorical_displayed_chain_2a_closure_transfer';
import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_SOURCE_SHA256,
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
} from './categorical_fibred_transfd_transfer';
import {
    CoreLfCanonicalSelectionContract,
    createCoreLfCanonicalSelectionContract
} from './lf_transfer_acquisition';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId
} from './schema';
import {
    CORE_LF_SCALE_STRESS_3A2A_LINKAGE,
    CORE_LF_SCALE_STRESS_3A2A_POLICY,
    CORE_LF_SCALE_STRESS_3A2A_SYMBOLS
} from './scale_stress_3a2a_representation';

export const
CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_ACQUISITION:
CoreLfCanonicalSelectionContract =
    createCoreLfCanonicalSelectionContract({
        revision: 'DISPLAYED-ND-HIGHER-1B-ACQUISITION-1',
        moduleId: 'emdash.emdash3_2',
        authorityPath: 'emdash2/emdash3_2.lp',
        sourceSha256:
            CORE_CATEGORICAL_FIBRED_TRANSFD_SOURCE_SHA256,
        canonicalExport: {
            exporterVersion: '3.0.0-90-gdb4f780',
            sha256:
                'sha256:91f0deb710b93acc55aa3a6f947505de973b9deaa94d68e1a213037dfcc9c3d3',
            imports: []
        },
        commands: [
            {
                id: 'higher-foundation.identity-arrow',
                ordinal: 232,
                kind: 'symbol',
                textSha256:
                    'sha256:76b996552e41e51e42d5c48415a920c092b1f28eca2adad2410c37a68c8e0091',
                name: 'id',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'higher-foundation.displayed-composition',
                ordinal: 398,
                kind: 'symbol',
                textSha256:
                    'sha256:927b801444c819dd3987e462b74ecbd4e2493c203c2c1746bd9343aabc0546b9',
                name: 'comp_catd_fapp0',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'higher-foundation.opposite-functor',
                ordinal: 505,
                kind: 'symbol',
                textSha256:
                    'sha256:239195b97b5ce2811e40a3024b0af50eb629f65f51f06e664b4163723fb5af3d',
                name: 'Op_func',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'higher-foundation.displayed-opposite-functor-owner',
                ordinal: 540,
                kind: 'symbol',
                textSha256:
                    'sha256:d7164cf2bc96a0750db89f5656d6b746e1e0457d235745bf87e84fb6669e9f19',
                name: 'Op_catd_func',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'higher-foundation.ordinary-internal-hom',
                ordinal: 648,
                kind: 'symbol',
                textSha256:
                    'sha256:257855a6283f267a2aebe4acc2a51c37dc53c65f098680c85021b967f60336ea',
                name: 'hom_int',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'higher-foundation.displayed-opposite',
                ordinal: 951,
                kind: 'symbol',
                textSha256:
                    'sha256:e52e9e71ece11fada758191d0ed5e5362ca9de40358a8d82ed7bd98b1b9acff8',
                name: 'Op_catd',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'higher-foundation.displayed-opposite-action',
                ordinal: 958,
                kind: 'symbol',
                textSha256:
                    'sha256:12ca623cfa3d86ac006eae9508a484de237e356675f121f14b97518f51e70385',
                name: 'Op_funcd',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'higher-foundation.mixed-functor-family-owner',
                ordinal: 1036,
                kind: 'symbol',
                textSha256:
                    'sha256:0907a4af9d06dff2b358b2e95637651892cbd466b6f346fa0fccc73a619b3f35',
                name: 'Functor_catd_func',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'higher-foundation.edge-family',
                ordinal: 1049,
                kind: 'symbol',
                textSha256:
                    'sha256:9febc6c848a9ae650fb0769eeef348e9b96e0d93f9cd68c1a2f8d89635fa77d3',
                name: 'Edge_catd_func',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'higher-foundation.presheaf-family',
                ordinal: 1050,
                kind: 'symbol',
                textSha256:
                    'sha256:4d0883c45a5c4d89d195092012d0c9a8a8fc34bc4ff3af0fa90f4cbcd81e65fc',
                name: 'Presheaf_catd_func',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'higher-foundation.hom-presheaf-family',
                ordinal: 1051,
                kind: 'symbol',
                textSha256:
                    'sha256:086d5ba63cf9fa898d47193019d44cbf8f45056ba2e41a86bd734fa605802edb',
                name: 'HomPresheaf_catd_func',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'higher-foundation.displayed-hom-target',
                ordinal: 1053,
                kind: 'symbol',
                textSha256:
                    'sha256:bc764c8b2c1dce013d2ab99060a34c496f3ec8ec3120681d0693bf5b4036a23c',
                name: 'Homd_target_catd',
                modifiers: [],
                hasBody: true
            },
            {
                id: 'higher-foundation.displayed-internal-hom',
                ordinal: 1054,
                kind: 'symbol',
                textSha256:
                    'sha256:a02629baea19025f05a63806291386ef22ed29adcbf814ed34fd7d0f2e20e34f',
                name: 'homd_int',
                modifiers: ['injective'],
                hasBody: false
            },
            {
                id: 'higher-action.full-object-action',
                ordinal: 1073,
                kind: 'symbol',
                textSha256:
                    'sha256:7d30d4f679316291a9cc962e04af3f10177438320c4b260d16795d25b336a0d9',
                name: 'tdapp1_int_func_transfd',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'higher-action.capped-object-action',
                ordinal: 1074,
                kind: 'symbol',
                textSha256:
                    'sha256:0e091f3f5a10689e6b85fc09e53c77fa8aaf142559441ddef47f08d07ad9e3d9',
                name: 'tdapp1_int_fapp0_transfd',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'higher-action.object-projection',
                ordinal: 1075,
                kind: 'rule',
                textSha256:
                    'sha256:a56a0ce8741c72dc54989c2597c2ec4475cb1fa9e4efffe1063da8aa14dded57',
                clauseCount: 1
            },
            {
                id: 'higher-action.full-next-hom-action',
                ordinal: 1076,
                kind: 'symbol',
                textSha256:
                    'sha256:6d4755675603c1fa8ac95161f00232f818d97eba1eb2fe1613e033eb79bb97cc',
                name: 'tdapp1_int_fapp1_func_transfd',
                modifiers: [],
                hasBody: false
            },
            {
                id: 'higher-action.next-hom-projection',
                ordinal: 1077,
                kind: 'rule',
                textSha256:
                    'sha256:b40ff3bd15e12348652fc5199d2ec0a2c647110b7987bba807651264cb7dffe1',
                clauseCount: 1
            }
        ]
    });

const foundationDeclarations = [
    'id',
    'comp_catd_fapp0',
    'Op_func',
    'Op_catd_func',
    'hom_int',
    'Op_catd',
    'Op_funcd',
    'Functor_catd_func',
    'Edge_catd_func',
    'Presheaf_catd_func',
    'HomPresheaf_catd_func',
    'Homd_target_catd',
    'homd_int'
] as const;

const targetDeclarations = [
    'tdapp1_int_func_transfd',
    'tdapp1_int_fapp0_transfd',
    'tdapp1_int_fapp1_func_transfd'
] as const;

const targetRuntimeRules = [
    'fapp0-tdapp1-int-func-transfd',
    'fapp1-func-tdapp1-int-func-transfd'
] as const;

const checkedTransparentFoundationDeclarations = [
    'comp_catd_fapp0',
    'Edge_catd_func',
    'Presheaf_catd_func',
    'HomPresheaf_catd_func',
    'Homd_target_catd'
] as const;

const opaqueFoundationDeclarations = [
    'id',
    'Op_func',
    'Op_catd_func',
    'hom_int',
    'Op_catd',
    'Op_funcd',
    'Functor_catd_func',
    'homd_int'
] as const;

const prerequisiteCoreOwnerLinks = [
    { symbol: 'Cat', owner: 'category-universe' },
    { symbol: 'τ', owner: 'decode' },
    { symbol: 'Functor', owner: 'functor-classifier' },
    { symbol: 'Hom_cat', owner: 'hom-category' },
    {
        symbol: 'Catd_cat',
        owner: 'displayed-category-category'
    },
    { symbol: 'fapp0', owner: 'functor-object' },
    { symbol: 'fapp1_func', owner: 'functor-hom-full' },
    {
        symbol: 'Const_catd',
        owner: 'constant-displayed-family'
    },
    { symbol: 'Cat_cat', owner: 'category-of-categories' }
] as const satisfies readonly {
    readonly symbol: string;
    readonly owner: CoreOwnerId;
}[];

const prerequisiteFreeDeclarationLinks = [
    {
        symbol: 'Catd',
        coreName: 'emdash_v3_2_scale_stress_2_Catd'
    },
    {
        symbol: 'Functord',
        coreName: 'emdash_v3_2_scale_stress_2b1_Functord'
    },
    {
        symbol: 'Functord_cat',
        coreName: 'dttlf_Functord_cat'
    },
    {
        symbol: 'Transfd',
        coreName: 'emdash_v3_2_scale_stress_2b3_Transfd'
    },
    {
        symbol: 'Transfd_cat',
        coreName: 'emdash_v3_2_scale_stress_2b3_Transfd_cat'
    },
    {
        symbol: 'id_funcd',
        coreName: 'emdash_v3_2_fibred_structure_1a_id_funcd'
    },
    {
        symbol: 'fapp0_func',
        coreName:
            'emdash_v3_2_fibred_dependent_target_1_fapp0_func'
    },
    {
        symbol: 'comp_fapp0',
        coreName: 'emdash_v3_2_usability_dependent_1a_comp_fapp0'
    },
    {
        symbol: 'comp_cat_fapp0',
        coreName: 'emdash_v3_2_usability_1c_comp_cat_fapp0'
    },
    {
        symbol: 'Op_cat',
        coreName: 'emdash_v3_2_scale_stress_2b1_Op_cat'
    },
    {
        symbol: 'Pi_func',
        coreName: 'emdash_v3_2_scale_stress_2b1_Pi_func'
    },
    {
        symbol: 'Functor_cat',
        coreName: 'emdash_v3_2_usability_1c_Functor_cat'
    }
] as const;

const reusableIdentityRepresentation = {
    sourceRow: 'SCALE-STRESS-3A2A',
    symbol: 'id',
    coreName: 'emdash_v3_2_scale_stress_3a2a_id',
    policy: 'opaque-signature',
    presentInInitialEnvironment: false,
    importWholeProfileRequired: false,
    interpretation:
        'reuse-or-extract-the-existing-exact-id-representation;' +
        'do-not-import-the-unrelated-profunctor-profile'
} as const;

const foundationPolicies = foundationDeclarations.map(name => ({
    name,
    policy: (
        (checkedTransparentFoundationDeclarations as readonly string[])
            .includes(name)
            ? 'checked-transparent-definition'
            : 'opaque-signature'
    ) as 'checked-transparent-definition' | 'opaque-signature'
}));

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

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const rawAudit = {
    revision: 'DISPLAYED-ND-HIGHER-1B-AUDIT-1',
    row: 'DISPLAYED-ND-HIGHER-1B',
    status:
        'completed-read-only-audit-with-non-self-authorizing-' +
        'dependency-first-proposal',
    prerequisite: {
        displayedNdAuditRevision:
            CORE_CATEGORICAL_DISPLAYED_ND_AUDIT.revision,
        displayedNdReviewRevision:
            CORE_CATEGORICAL_DISPLAYED_ND_REVIEW.revision,
        displayedNd1aImplementationCheckpoint:
            'd8b450222273167ab326701c76fff03f0f539b18',
        currentTransfdDeclarationCount:
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
                .declarationCount,
        currentTransfdRuntimeRuleCount:
            CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_BOUNDARY
                .runtimeRuleCount,
        semanticImplementationAuthorized: false
    },
    measuredClosure: {
        acquisitionRevision:
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_ACQUISITION.revision,
        canonicalCommandCount:
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_ACQUISITION
                .commands.length,
        canonicalExportEvidence: {
            observedSha256:
                CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_ACQUISITION
                    .canonicalExport.sha256,
            historicalScaleContractSha256:
                'sha256:18500d46d4ff3583fef1f25a3c28eff7b849a61d528a6f9e20e89b32db13f1b2',
            reportedExporterVersionUnchanged: true,
            disposition:
                'pin-the-deterministic-current-export-and-retain-the-' +
                'historical-digest-as-non-semantic-drift-evidence'
        },
        foundationDeclarations,
        targetDeclarations,
        targetRuntimeRules,
        totalDeclarationCount:
            foundationDeclarations.length + targetDeclarations.length,
        totalRuntimeRuleCount: targetRuntimeRules.length,
        targetOnlyTransferIsClosed: false,
        reason:
            'the-target-types-reference-an-untransferred-internalized-' +
            'hom-opposite-and-presheaf-family-foundation-and-the-' +
            'transparent-edge-body-needs-the-untransferred-id-signature',
        allCommandsActiveExistingAuthority: true,
        activeKernelOwnerDelta: 0,
        activeKernelRuleDelta: 0
    },
    dependencyBoundary: {
        initialEnvironment:
            'completed-displayed-chain-2a-closure-environment',
        alreadyAvailableCoreOwnerLinks:
            prerequisiteCoreOwnerLinks,
        alreadyAvailableFreeDeclarationLinks:
            prerequisiteFreeDeclarationLinks,
        reusablePriorRepresentation:
            reusableIdentityRepresentation,
        newlyRequiredFoundation: foundationDeclarations,
        transparentDefinitionsMustRemainChecked:
            checkedTransparentFoundationDeclarations,
        opaqueOrInjectiveInterfaces:
            opaqueFoundationDeclarations,
        arbitraryRulesForFoundationIncluded: false,
        interpretation:
            'transfer-the-exact-type-and-transparent-body-closure-before-' +
            'the-three-next-hom-owners;-do-not-install-opaque-mirrors-for-' +
            'source-transparent-definitions'
    },
    concreteConsumer: {
        source:
            'm : Hom(Transfd_cat(FF,GG), epsilon, epsilon-prime)',
        wholeAction:
            'fapp1_func(tdapp1_int_func_transfd(FF,GG),epsilon,' +
            'epsilon-prime)',
        cappedAction:
            'fapp0(tdapp1_int_fapp1_func_transfd(epsilon,' +
            'epsilon-prime),m)',
        result:
            'a-higher-cell-between-the-internal-hom-actions-of-epsilon-' +
            'and-epsilon-prime',
        objectObservation:
            'tdapp1_int_fapp0_transfd(epsilon)',
        liveLambdapiStatus: 'bounded-type-and-projection-conversion-pass',
        fixture:
            'tests/fixtures/v3_2_categorical_displayed_nd_higher_probe.lp',
        requiresNewKernelSemantics: false
    },
    surfaceAssessment: {
        existingGenericMechanisms: [
            'hom-assumption',
            'whole-hom-boundary',
            'ordinary-functor-object-action',
            'ordinary-functor-whole-hom-action',
            'ordinary-functor-capped-arrow-action'
        ],
        exactGap: [
            'rich-construction-of-Transfd-cat-as-a-surface-category',
            'rich-object-result-for-tdapp1-int-fapp0-transfd',
            'stable-recognition-of-a-higher-cell-in-Transfd-cat'
        ],
        preferredConsumerShape: [
            'displayedTransforCell(name,epsilon,epsilonPrime)',
            'displayedTransforInternalHom(epsilon)',
            'displayedTransforNextHom(m)'
        ],
        secondCheckerRequired: false,
        rawExprOrParserRequired: false,
        contextualIrNodeRequired: false,
        newBinderModeRequired: false,
        ownerSpecificLfCheckerBranchRequired: false,
        conclusion:
            'the-generic-action-ladder-is-already-sufficient;the-later-' +
            'surface-slice-needs-rich-classifier-preservation-not-another-' +
            'elaborator'
    },
    alternatives: [
        {
            id: 'transfer-only-the-three-advertised-owners',
            disposition: 'reject',
            reason: 'their-types-are-not-closed-in-the-current-environment'
        },
        {
            id: 'declare-transparent-prerequisites-opaque',
            disposition: 'reject',
            reason:
                'would-turn-a-dependency-convenience-into-a-source-' +
                'transparency-mismatch'
        },
        {
            id: 'add-a-special-next-hom-checker',
            disposition: 'reject',
            reason:
                'generic-functor-and-iterated-hom-checking-already-exists'
        },
        {
            id: 'dependency-first-generic-transfer',
            disposition: 'recommend',
            reason:
                'preserves-exact-source-opacity-and-reuses-only-reviewed-' +
                'generic-declaration-runtime-and-surface-machinery'
        }
    ],
    recommendedContinuation: {
        row: 'DISPLAYED-ND-HIGHER-FOUNDATION-1A',
        gate: 'H-DTTLF-USABILITY-DISPLAYED-ND-HIGHER-01',
        decision: 'D-DTTLF-USABILITY-019',
        kind: 'non-self-authorizing-dependency-first-transfer-proposal',
        exactDeclarations: foundationDeclarations,
        exactPolicies: foundationPolicies,
        exactRuntimeRules: [] as const,
        exactProofRules: [] as const,
        allEntriesUseGenericTransferEngines: true,
        checkedTransparentDefinitionCount:
            foundationPolicies.filter(entry =>
                entry.policy === 'checked-transparent-definition'
            ).length,
        opaqueSignatureCount:
            foundationPolicies.filter(entry =>
                entry.policy === 'opaque-signature'
            ).length,
        newMathematicalOwnerCount: 0,
        newMathematicalRuntimeRuleCount: 0,
        newMathematicalProofRuleCount: 0,
        intrinsicCoreOwnerDelta: 0,
        ownerSpecificCheckerBranchDelta: 0,
        surfaceMethodDelta: 0,
        browserPromotionDelta: 0,
        mandatoryStop:
            'halt-and-revise-if-any-exact-transparent-body-or-type-needs-' +
            'an-unlisted-owner-rule-intrinsic-or-checker-path',
        followingSeparateDecision:
            'transfer-the-three-target-owners-two-projection-rules-and-' +
            'the-concrete-rich-surface-consumer-only-after-the-foundation-' +
            'is-green'
    },
    semanticDelta: {
        activeLambdapiOwners: 0,
        activeLambdapiRuntimeRules: 0,
        activeLambdapiProofRules: 0,
        transferredDeclarations: 0,
        transferredRuntimeRules: 0,
        transferredProofRules: 0,
        frontendMethods: 0,
        contextualIrNodes: 0,
        checkerBranches: 0,
        evaluatorBranches: 0,
        parserLayers: 0,
        browserPromotions: 0
    },
    nonEffects: [
        'does-not-authorize-DISPLAYED-ND-HIGHER-FOUNDATION-1A',
        'does-not-transfer-the-three-target-next-hom-owners',
        'does-not-transfer-the-two-target-projection-rules',
        'does-not-add-the-three-proposed-surface-methods',
        'does-not-add-opposite-or-internal-hom-computation-rules',
        'does-not-add-an-intrinsic-owner-or-owner-specific-checker-branch',
        'does-not-add-a-contextual-node-binder-mode-parser-or-RawExpr-layer',
        'does-not-add-new-Lambdapi-semantics',
        'does-not-promote-browser-or-deployed-profiles',
        'does-not-resume-bulk-transfer',
        'does-not-broaden-Git-authority'
    ],
    decisionQuestion:
        'Approve H-DTTLF-USABILITY-DISPLAYED-ND-HIGHER-01/' +
        'D-DTTLF-USABILITY-019 as proposed: accept the measured 13-' +
        'declaration dependency foundation and authorize only ' +
        'DISPLAYED-ND-HIGHER-FOUNDATION-1A through the generic transfer ' +
        'engines with five checked-transparent definitions, eight opaque ' +
        'signatures, zero rules, zero new mathematical owners, and the ' +
        'mandatory drift stop; retain the three tdapp1_int target owners, ' +
        'their two projection rules, rich surface consumer, unrelated ' +
        'computation rules, parsing, deployment, bulk transfer, and broader ' +
        'Git authority for a later separate decision?'
} as const;

export type CoreCategoricalDisplayedNdHigherAuditInput =
    typeof rawAudit;

export type CoreCategoricalDisplayedNdHigherAuditErrorCode =
    | 'DISPLAYED_ND_HIGHER_PREREQUISITE_DRIFT'
    | 'DISPLAYED_ND_HIGHER_AUTHORITY_DRIFT'
    | 'DISPLAYED_ND_HIGHER_BOUNDARY_DRIFT'
    | 'DISPLAYED_ND_HIGHER_PROPOSAL_DRIFT';

export class CoreCategoricalDisplayedNdHigherAuditError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedNdHigherAuditErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDisplayedNdHigherAuditError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT =
    deepFreeze(rawAudit);

let reviewedPrerequisiteValidated = false;

const validateReviewedPrerequisite = (): void => {
    if (reviewedPrerequisiteValidated) return;
    validateCoreCategoricalDisplayedNdReview();
    const environment =
        compileCoreCategoricalDisplayedChain2aClosureTransfer()
            .compiled.environment;
    prerequisiteCoreOwnerLinks.forEach(link => {
        if (!Object.prototype.hasOwnProperty.call(
            CORE_OWNER_SCHEMAS,
            link.owner
        )) {
            throw new Error(
                `The Core owner catalog lacks '${link.owner}' for ` +
                    `'${link.symbol}'`
            );
        }
    });
    prerequisiteFreeDeclarationLinks.forEach(link => {
        if (environment.lookup(link.coreName) === undefined) {
            throw new Error(
                'The completed chain-2A environment lacks ' +
                    `'${link.coreName}' for '${link.symbol}'`
            );
        }
    });
    const identitySymbol =
        CORE_LF_SCALE_STRESS_3A2A_SYMBOLS.identityArrow;
    const identityLink =
        CORE_LF_SCALE_STRESS_3A2A_LINKAGE.entries.find(link =>
            link.symbol.moduleId === identitySymbol.moduleId &&
            link.symbol.name === identitySymbol.name
        );
    const identityPolicy =
        CORE_LF_SCALE_STRESS_3A2A_POLICY.entries.find(entry =>
            (
                entry.target.kind === 'declaration' ||
                entry.target.kind === 'inductive'
            ) &&
            entry.target.symbol.moduleId === identitySymbol.moduleId &&
            entry.target.symbol.name === identitySymbol.name
        );
    if (
        identityLink === undefined ||
        identityLink.kind !== 'free-declaration' ||
        identityLink.coreName !== reusableIdentityRepresentation.coreName ||
        identityPolicy?.policy !== reusableIdentityRepresentation.policy
    ) {
        throw new Error(
            'The exact prior SCALE-STRESS-3A2A identity representation ' +
                'is unavailable for extraction or reuse'
        );
    }
    reviewedPrerequisiteValidated = true;
};

export function validateCoreCategoricalDisplayedNdHigherAudit(
    audit: CoreCategoricalDisplayedNdHigherAuditInput =
        CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_AUDIT
): void {
    try {
        validateReviewedPrerequisite();
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedNdHigherAuditError(
            'DISPLAYED_ND_HIGHER_PREREQUISITE_DRIFT',
            'The reviewed displayed-ND prerequisite drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        audit.revision !== 'DISPLAYED-ND-HIGHER-1B-AUDIT-1' ||
        audit.row !== 'DISPLAYED-ND-HIGHER-1B' ||
        audit.prerequisite.displayedNdAuditRevision !==
            CORE_CATEGORICAL_DISPLAYED_ND_AUDIT.revision ||
        audit.prerequisite.displayedNdReviewRevision !==
            CORE_CATEGORICAL_DISPLAYED_ND_REVIEW.revision ||
        audit.prerequisite.displayedNd1aImplementationCheckpoint !==
            'd8b450222273167ab326701c76fff03f0f539b18' ||
        audit.prerequisite.semanticImplementationAuthorized
    ) {
        throw new CoreCategoricalDisplayedNdHigherAuditError(
            'DISPLAYED_ND_HIGHER_PREREQUISITE_DRIFT',
            'The audit must preserve completed ND-1A and remain ' +
                'non-self-authorizing'
        );
    }

    if (
        audit.measuredClosure.acquisitionRevision !==
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_ACQUISITION.revision ||
        audit.measuredClosure.canonicalCommandCount !== 18 ||
        audit.measuredClosure.canonicalExportEvidence.observedSha256 !==
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_ACQUISITION
                .canonicalExport.sha256 ||
        audit.measuredClosure.canonicalExportEvidence
            .historicalScaleContractSha256 !==
                'sha256:' +
                '18500d46d4ff3583fef1f25a3c28eff7b849a61d528a6f9e20e89b32db13f1b2' ||
        audit.measuredClosure.canonicalExportEvidence.observedSha256 ===
            audit.measuredClosure.canonicalExportEvidence
                .historicalScaleContractSha256 ||
        !audit.measuredClosure.canonicalExportEvidence
            .reportedExporterVersionUnchanged ||
        !sameData(
            audit.measuredClosure.foundationDeclarations,
            foundationDeclarations
        ) ||
        !sameData(
            audit.measuredClosure.targetDeclarations,
            targetDeclarations
        ) ||
        !sameData(
            audit.measuredClosure.targetRuntimeRules,
            targetRuntimeRules
        ) ||
        audit.measuredClosure.totalDeclarationCount !== 16 ||
        audit.measuredClosure.totalRuntimeRuleCount !== 2 ||
        audit.measuredClosure.targetOnlyTransferIsClosed ||
        !audit.measuredClosure.allCommandsActiveExistingAuthority ||
        audit.measuredClosure.activeKernelOwnerDelta !== 0 ||
        audit.measuredClosure.activeKernelRuleDelta !== 0
    ) {
        throw new CoreCategoricalDisplayedNdHigherAuditError(
            'DISPLAYED_ND_HIGHER_AUTHORITY_DRIFT',
            'The exact active source-command/dependency closure drifted'
        );
    }

    if (
        audit.prerequisite.currentTransfdDeclarationCount !== 6 ||
        audit.prerequisite.currentTransfdRuntimeRuleCount !== 7 ||
        audit.dependencyBoundary.initialEnvironment !==
            'completed-displayed-chain-2a-closure-environment' ||
        !sameData(
            audit.dependencyBoundary.alreadyAvailableCoreOwnerLinks,
            prerequisiteCoreOwnerLinks
        ) ||
        !sameData(
            audit.dependencyBoundary
                .alreadyAvailableFreeDeclarationLinks,
            prerequisiteFreeDeclarationLinks
        ) ||
        !sameData(
            audit.dependencyBoundary.reusablePriorRepresentation,
            reusableIdentityRepresentation
        ) ||
        !sameData(
            audit.dependencyBoundary.newlyRequiredFoundation,
            foundationDeclarations
        ) ||
        !sameData(
            audit.dependencyBoundary
                .transparentDefinitionsMustRemainChecked,
            checkedTransparentFoundationDeclarations
        ) ||
        !sameData(
            audit.dependencyBoundary.opaqueOrInjectiveInterfaces,
            opaqueFoundationDeclarations
        ) ||
        audit.dependencyBoundary.arbitraryRulesForFoundationIncluded ||
        audit.concreteConsumer.requiresNewKernelSemantics ||
        audit.surfaceAssessment.secondCheckerRequired ||
        audit.surfaceAssessment.rawExprOrParserRequired ||
        audit.surfaceAssessment.contextualIrNodeRequired ||
        audit.surfaceAssessment.newBinderModeRequired ||
        audit.surfaceAssessment.ownerSpecificLfCheckerBranchRequired
    ) {
        throw new CoreCategoricalDisplayedNdHigherAuditError(
            'DISPLAYED_ND_HIGHER_BOUNDARY_DRIFT',
            'The current transfer, consumer, or surface boundary drifted'
        );
    }

    const continuation = audit.recommendedContinuation;
    if (
        continuation.row !==
            'DISPLAYED-ND-HIGHER-FOUNDATION-1A' ||
        continuation.gate !==
            'H-DTTLF-USABILITY-DISPLAYED-ND-HIGHER-01' ||
        continuation.decision !== 'D-DTTLF-USABILITY-019' ||
        !sameData(
            continuation.exactDeclarations,
            foundationDeclarations
        ) ||
        !sameData(continuation.exactPolicies, foundationPolicies) ||
        continuation.exactRuntimeRules.length !== 0 ||
        continuation.exactProofRules.length !== 0 ||
        !continuation.allEntriesUseGenericTransferEngines ||
        continuation.checkedTransparentDefinitionCount !== 5 ||
        continuation.opaqueSignatureCount !== 8 ||
        continuation.newMathematicalOwnerCount !== 0 ||
        continuation.newMathematicalRuntimeRuleCount !== 0 ||
        continuation.newMathematicalProofRuleCount !== 0 ||
        continuation.intrinsicCoreOwnerDelta !== 0 ||
        continuation.ownerSpecificCheckerBranchDelta !== 0 ||
        continuation.surfaceMethodDelta !== 0 ||
        continuation.browserPromotionDelta !== 0 ||
        Object.values(audit.semanticDelta).some(value =>
            value !== 0
        ) ||
        !audit.nonEffects.includes(
            'does-not-authorize-DISPLAYED-ND-HIGHER-FOUNDATION-1A'
        ) ||
        !audit.decisionQuestion.includes(
            'D-DTTLF-USABILITY-019'
        )
    ) {
        throw new CoreCategoricalDisplayedNdHigherAuditError(
            'DISPLAYED_ND_HIGHER_PROPOSAL_DRIFT',
            'The dependency-first proposal or its non-effects drifted'
        );
    }
}
