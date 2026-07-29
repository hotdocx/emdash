/**
 * Executable DISPLAYED-CHAIN-TRANSFER-CORRECTION-0A proposal.
 *
 * D-012 correctly freezes the mathematical delta and its three
 * chain-specific transfer prerequisites. During generic rule compilation we
 * discovered one additional ambient constant used literally by two of the
 * six approved rules: `Terminal_obj`. No prior TypeScript fragment declares
 * it. This proposal freezes the smallest faithful correction and authorizes
 * nothing by itself.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL,
    validateCoreCategoricalDisplayedChainProposal
} from './categorical_displayed_chain_proposal';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_REVIEW,
    validateCoreCategoricalDisplayedChainReview
} from './categorical_displayed_chain_review';

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

const rawProposal = {
    revision:
        'DISPLAYED-CHAIN-TRANSFER-CORRECTION-0A-PROPOSAL-1',
    status:
        'proposal-awaiting-h-dttlf-usability-displayed-chain-02',
    reviewGate: 'H-DTTLF-USABILITY-DISPLAYED-CHAIN-02',
    decisionId: 'D-DTTLF-USABILITY-013',
    prerequisite: {
        approvedDecisionId: 'D-DTTLF-USABILITY-012',
        approvedReviewRevision: 'DISPLAYED-CHAIN-0A-REVIEWED-1',
        approvedImplementationRow: 'DISPLAYED-CHAIN-1A',
        chainSpecificDeclarationPrerequisites:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL.transferClosure
                .existingDeclarationPrerequisites,
        chainSpecificDeclarationPrerequisiteCount: 3,
        existingRuntimeRulePrerequisites:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL.transferClosure
                .existingRuntimeRulePrerequisites,
        existingRuntimeRulePrerequisiteCount: 2,
        mathematicalOwnerCount:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL.selectedClosure
                .newMathematicalOwnerCount,
        mathematicalRuntimeRuleCount:
            CORE_CATEGORICAL_DISPLAYED_CHAIN_PROPOSAL.selectedClosure
                .newMathematicalRuntimeRuleCount
    },
    discoveredGap: {
        symbol: 'Terminal_obj',
        activeAuthority:
            'constant symbol Terminal_obj : τ (Obj Terminal_cat);',
        authorityStatus: 'pre-existing-active-opaque-constant',
        approvedRuleOccurrences: [
            'sigma-functord-section-arrow-component-lhs',
            'section-pullback-direct-arrow-component-rhs'
        ],
        occurrenceCount: 2,
        presentInEarlierTypeScriptEnvironment: false,
        genericCompilerRequirement:
            'every-global-in-pattern-or-template-has-a-typed-declaration',
        newMathematicsRequired: false,
        lambdapiEditRequired: false
    },
    alternatives: [
        {
            id: 'typed-wildcard-in-terminal-slot',
            disposition: 'reject',
            reason:
                'It broadens the literal active rule and cannot provide the ' +
                'fixed Terminal_obj used by the second rule template'
        },
        {
            id: 'reuse-arbitrary-source-term-on-rhs',
            disposition: 'reject',
            reason:
                'It changes the selected runtime normal form and ceases to ' +
                'be an exact transfer of the active rule'
        },
        {
            id: 'replace-terminal-object-with-native-tt',
            disposition: 'reject',
            reason:
                'Terminal_obj is opaque and is not definitionally equal to ' +
                'the native unit constructor tt'
        },
        {
            id: 'intrinsic-core-terminal-object',
            disposition: 'reject',
            reason:
                'It would add an owner-specific escape hatch instead of ' +
                'using the generic declaration compiler'
        },
        {
            id: 'transfer-exact-ambient-signature',
            disposition: 'recommend',
            reason:
                'It faithfully types both approved rules without changing ' +
                'the kernel, runtime clauses, or generic engines'
        }
    ],
    proposedCorrection: {
        ambientDeclarationPrerequisites: ['Terminal_obj'],
        ambientDeclarationPrerequisiteCount: 1,
        chainSpecificDeclarationPrerequisiteCountRemains: 3,
        totalExistingDeclarationsCompiledForSlice: 4,
        existingRuntimeRulePrerequisiteCountRemains: 2,
        mathematicalOwnerCountRemains: 1,
        mathematicalRuntimeRuleCountRemains: 6,
        mathematicalProofRuleCountRemains: 0,
        intrinsicCoreOwnerCountRemains: 0,
        activeLambdapiEditCount: 0,
        compiler: 'generic-lf-declaration-compiler'
    },
    validationPlan: {
        exactDeclarationPartition: 'three-chain-specific-plus-one-ambient',
        exactRuntimePartition: 'two-existing-plus-six-semantic',
        allDeclarationsSubjectChecked: true,
        allRuntimeRulesSubjectChecked: true,
        objectAndInternalizedArrowEvidenceRequired: true,
        activeSourceHashRequired: true,
        rootTypecheckLintAndTestsRequired: true,
        browserExclusionRequired: true
    },
    nonEffects: [
        'does-not-change-the-d-012-mathematical-closure',
        'does-not-add-or-edit-a-lambdapi-owner-or-rule',
        'does-not-add-a-runtime-rule',
        'does-not-reinterpret-terminal-objects-as-native-tt',
        'does-not-add-a-wildcard-or-broaden-a-rule-pattern',
        'does-not-add-an-intrinsic-core-owner',
        'does-not-add-a-parser-rawexpr-or-second-checker',
        'does-not-authorize-general-nd-or-arbitrary-telescope-depth',
        'does-not-authorize-browser-promotion-or-bulk-transfer',
        'does-not-broaden-git-authority'
    ],
    decisionEffects: {
        authorityAuthorized: false,
        implementationAuthorized: false,
        nextIfApproved:
            'displayed-chain-1a-generic-transfer-with-exact-ambient-dependency',
        nextIfRejected:
            'displayed-chain-1a-typescript-transfer-blocked-on-terminal-object'
    }
} as const;

export type CoreCategoricalDisplayedChainTransferCorrectionProposalInput =
    typeof rawProposal;

export type CoreCategoricalDisplayedChainTransferCorrectionProposalErrorCode =
    | 'DISPLAYED_CHAIN_TRANSFER_CORRECTION_PREREQUISITE_DRIFT'
    | 'DISPLAYED_CHAIN_TRANSFER_CORRECTION_BOUNDARY_DRIFT'
    | 'DISPLAYED_CHAIN_TRANSFER_CORRECTION_AUTHORITY_DRIFT';

export class
CoreCategoricalDisplayedChainTransferCorrectionProposalError extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedChainTransferCorrectionProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreCategoricalDisplayedChainTransferCorrectionProposalError';
    }
}

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL =
    deepFreeze(rawProposal);

export function
validateCoreCategoricalDisplayedChainTransferCorrectionProposal(
    proposal:
        CoreCategoricalDisplayedChainTransferCorrectionProposalInput =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL
): void {
    try {
        validateCoreCategoricalDisplayedChainProposal();
        validateCoreCategoricalDisplayedChainReview();
    } catch (error: unknown) {
        throw new
        CoreCategoricalDisplayedChainTransferCorrectionProposalError(
            'DISPLAYED_CHAIN_TRANSFER_CORRECTION_PREREQUISITE_DRIFT',
            'The approved D-012 prerequisite drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        proposal.revision !==
            'DISPLAYED-CHAIN-TRANSFER-CORRECTION-0A-PROPOSAL-1' ||
        proposal.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-chain-02' ||
        proposal.reviewGate !==
            'H-DTTLF-USABILITY-DISPLAYED-CHAIN-02' ||
        proposal.decisionId !== 'D-DTTLF-USABILITY-013' ||
        proposal.prerequisite.chainSpecificDeclarationPrerequisites
            .join(',') !==
            'sigma_map_func,fdapp1_int_cell,fdapp1_int_hom_fapp0' ||
        proposal.prerequisite
            .chainSpecificDeclarationPrerequisiteCount !== 3 ||
        proposal.discoveredGap.symbol !== 'Terminal_obj' ||
        proposal.discoveredGap.occurrenceCount !== 2 ||
        proposal.discoveredGap.presentInEarlierTypeScriptEnvironment ||
        proposal.discoveredGap.newMathematicsRequired ||
        proposal.discoveredGap.lambdapiEditRequired
    ) {
        throw new
        CoreCategoricalDisplayedChainTransferCorrectionProposalError(
            'DISPLAYED_CHAIN_TRANSFER_CORRECTION_PREREQUISITE_DRIFT',
            'The exact missing ambient dependency diagnosis drifted'
        );
    }

    const correction = proposal.proposedCorrection;
    if (
        correction.ambientDeclarationPrerequisites.join(',') !==
            'Terminal_obj' ||
        correction.ambientDeclarationPrerequisiteCount !== 1 ||
        correction.chainSpecificDeclarationPrerequisiteCountRemains !== 3 ||
        correction.totalExistingDeclarationsCompiledForSlice !== 4 ||
        correction.existingRuntimeRulePrerequisiteCountRemains !== 2 ||
        correction.mathematicalOwnerCountRemains !== 1 ||
        correction.mathematicalRuntimeRuleCountRemains !== 6 ||
        correction.mathematicalProofRuleCountRemains !== 0 ||
        correction.intrinsicCoreOwnerCountRemains !== 0 ||
        correction.activeLambdapiEditCount !== 0 ||
        proposal.alternatives.filter(
            alternative => alternative.disposition === 'recommend'
        ).map(alternative => alternative.id).join(',') !==
            'transfer-exact-ambient-signature' ||
        proposal.nonEffects.length !== 10
    ) {
        throw new
        CoreCategoricalDisplayedChainTransferCorrectionProposalError(
            'DISPLAYED_CHAIN_TRANSFER_CORRECTION_BOUNDARY_DRIFT',
            'The one-signature correction or its non-effects drifted'
        );
    }

    if (
        proposal.decisionEffects.authorityAuthorized ||
        proposal.decisionEffects.implementationAuthorized ||
        proposal.decisionEffects.nextIfApproved !==
            'displayed-chain-1a-generic-transfer-with-exact-ambient-dependency'
    ) {
        throw new
        CoreCategoricalDisplayedChainTransferCorrectionProposalError(
            'DISPLAYED_CHAIN_TRANSFER_CORRECTION_AUTHORITY_DRIFT',
            'The proposal must remain non-self-authorizing'
        );
    }
}

validateCoreCategoricalDisplayedChainTransferCorrectionProposal();
