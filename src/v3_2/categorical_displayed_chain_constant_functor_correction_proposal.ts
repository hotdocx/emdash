/**
 * Executable DISPLAYED-CHAIN-CONST-FUNCTOR-CORRECTION-0A proposal.
 *
 * D-013 authorized the first fail-closed ambient dependency,
 * `Terminal_obj`. A complete linkage-set audit then found exactly one
 * residual global used by the approved six rules: the active injective
 * `Const_func` owner. This proposal freezes that final ambient signature
 * correction and authorizes nothing by itself.
 */

import {
    validateCoreCategoricalDisplayedChainTransferCorrectionReview
} from './categorical_displayed_chain_transfer_correction_review';

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
        'DISPLAYED-CHAIN-CONST-FUNCTOR-CORRECTION-0A-PROPOSAL-1',
    status:
        'proposal-awaiting-h-dttlf-usability-displayed-chain-03',
    reviewGate: 'H-DTTLF-USABILITY-DISPLAYED-CHAIN-03',
    decisionId: 'D-DTTLF-USABILITY-014',
    prerequisite: {
        d012ReviewRevision: 'DISPLAYED-CHAIN-0A-REVIEWED-1',
        d013ReviewRevision:
            'DISPLAYED-CHAIN-TRANSFER-CORRECTION-0A-REVIEWED-1',
        d013ReviewCheckpoint:
            'b33a1621908425d06879898b05b1cfffda230eb4',
        d013AmbientDeclarations: ['Terminal_obj'],
        d013AmbientDeclarationCount: 1
    },
    exhaustiveLinkageAudit: {
        method:
            'compare-every-semantic-external-symbol-with-union-of-all-composed-linkages',
        externalSymbolCountAudited: 29,
        missingBeforeAmbientCorrections: [
            'Terminal_obj',
            'Const_func'
        ],
        missingAfterD013: ['Const_func'],
        missingAfterProposedCorrection: [],
        firstErrorOnlyDiagnosisCorrected: true,
        furtherUndeclaredGlobalsExpected: false
    },
    discoveredGap: {
        symbol: 'Const_func',
        activeAuthority:
            'injective symbol Const_func [A B : Cat] ' +
            '(b : τ (Obj B)) : τ (Functor A B);',
        authorityStatus: 'pre-existing-active-injective-owner',
        approvedRuleOccurrences: [
            'section-pullback-direct-object-component-rhs'
        ],
        occurrenceCount: 1,
        presentInEarlierTypeScriptEnvironment: false,
        newMathematicsRequired: false,
        lambdapiEditRequired: false
    },
    alternatives: [
        {
            id: 'terminal-point-composite',
            disposition: 'reject',
            reason:
                'Obj_func followed by Terminal_func changes the selected ' +
                'normal form and requires an additional computation path'
        },
        {
            id: 'intrinsic-core-constant-functor',
            disposition: 'reject',
            reason:
                'It would bypass the generic declaration compiler'
        },
        {
            id: 'transfer-exact-const-func-signature',
            disposition: 'recommend',
            reason:
                'It types the literal approved RHS without changing any rule'
        }
    ],
    proposedCorrection: {
        additionalAmbientDeclarationPrerequisites: ['Const_func'],
        additionalAmbientDeclarationPrerequisiteCount: 1,
        totalAmbientDeclarationPrerequisites: [
            'Terminal_obj',
            'Const_func'
        ],
        totalAmbientDeclarationPrerequisiteCount: 2,
        chainSpecificDeclarationPrerequisiteCountRemains: 3,
        totalExistingDeclarationsCompiledForSlice: 5,
        existingRuntimeRulePrerequisiteCountRemains: 2,
        mathematicalOwnerCountRemains: 1,
        mathematicalRuntimeRuleCountRemains: 6,
        activeLambdapiEditCount: 0,
        intrinsicCoreOwnerCountRemains: 0,
        compiler: 'generic-lf-declaration-compiler'
    },
    validationPlan: {
        exactDeclarationPartition:
            'three-chain-specific-plus-two-ambient',
        allExternalLinkagesResolvedBeforeCompilation: true,
        exactRuntimePartition: 'two-existing-plus-six-semantic',
        allDeclarationsAndRuleSubjectsChecked: true,
        objectAndInternalizedArrowEvidenceRequired: true,
        rootTypecheckLintAndTestsRequired: true,
        browserExclusionRequired: true
    },
    nonEffects: [
        'does-not-mutate-d-012-or-d-013',
        'does-not-add-or-edit-a-lambdapi-owner-or-rule',
        'does-not-add-a-runtime-rule',
        'does-not-change-an-approved-normal-form',
        'does-not-add-an-intrinsic-core-owner',
        'does-not-add-a-parser-rawexpr-or-second-checker',
        'does-not-authorize-general-nd-or-arbitrary-depth',
        'does-not-authorize-browser-or-bulk-transfer',
        'does-not-broaden-git-authority'
    ],
    decisionEffects: {
        authorityAuthorized: false,
        implementationAuthorized: false,
        nextIfApproved:
            'displayed-chain-1a-final-dependency-closed-generic-transfer',
        nextIfRejected:
            'displayed-chain-1a-typescript-transfer-blocked-on-const-func'
    }
} as const;

export type CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalInput =
    typeof rawProposal;

export type CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalErrorCode =
    | 'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_PREREQUISITE_DRIFT'
    | 'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_BOUNDARY_DRIFT'
    | 'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_AUTHORITY_DRIFT';

export class
CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalError';
    }
}

export const
CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL =
    deepFreeze(rawProposal);

export function
validateCoreCategoricalDisplayedChainConstantFunctorCorrectionProposal(
    proposal:
        CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalInput =
            CORE_CATEGORICAL_DISPLAYED_CHAIN_CONSTANT_FUNCTOR_CORRECTION_PROPOSAL
): void {
    try {
        validateCoreCategoricalDisplayedChainTransferCorrectionReview();
    } catch (error: unknown) {
        throw new
        CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalError(
            'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_PREREQUISITE_DRIFT',
            'The D-013 prerequisite drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        proposal.revision !==
            'DISPLAYED-CHAIN-CONST-FUNCTOR-CORRECTION-0A-PROPOSAL-1' ||
        proposal.decisionId !== 'D-DTTLF-USABILITY-014' ||
        proposal.discoveredGap.symbol !== 'Const_func' ||
        proposal.discoveredGap.occurrenceCount !== 1 ||
        proposal.discoveredGap.presentInEarlierTypeScriptEnvironment ||
        proposal.discoveredGap.newMathematicsRequired ||
        proposal.exhaustiveLinkageAudit.missingAfterD013.join(',') !==
            'Const_func' ||
        proposal.exhaustiveLinkageAudit
            .missingAfterProposedCorrection.length !== 0 ||
        !proposal.exhaustiveLinkageAudit.firstErrorOnlyDiagnosisCorrected ||
        proposal.exhaustiveLinkageAudit.furtherUndeclaredGlobalsExpected
    ) {
        throw new
        CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalError(
            'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_PREREQUISITE_DRIFT',
            'The exhaustive residual linkage diagnosis drifted'
        );
    }

    const correction = proposal.proposedCorrection;
    if (
        correction.additionalAmbientDeclarationPrerequisites.join(',') !==
            'Const_func' ||
        correction.totalAmbientDeclarationPrerequisites.join(',') !==
            'Terminal_obj,Const_func' ||
        correction.totalAmbientDeclarationPrerequisiteCount !== 2 ||
        correction.chainSpecificDeclarationPrerequisiteCountRemains !== 3 ||
        correction.totalExistingDeclarationsCompiledForSlice !== 5 ||
        correction.existingRuntimeRulePrerequisiteCountRemains !== 2 ||
        correction.mathematicalOwnerCountRemains !== 1 ||
        correction.mathematicalRuntimeRuleCountRemains !== 6 ||
        correction.activeLambdapiEditCount !== 0 ||
        correction.intrinsicCoreOwnerCountRemains !== 0 ||
        proposal.alternatives.filter(
            alternative => alternative.disposition === 'recommend'
        ).map(alternative => alternative.id).join(',') !==
            'transfer-exact-const-func-signature'
    ) {
        throw new
        CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalError(
            'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_BOUNDARY_DRIFT',
            'The final one-signature correction drifted'
        );
    }

    if (
        proposal.decisionEffects.authorityAuthorized ||
        proposal.decisionEffects.implementationAuthorized
    ) {
        throw new
        CoreCategoricalDisplayedChainConstantFunctorCorrectionProposalError(
            'DISPLAYED_CHAIN_CONST_FUNCTOR_CORRECTION_AUTHORITY_DRIFT',
            'The proposal must remain non-self-authorizing'
        );
    }
}

validateCoreCategoricalDisplayedChainConstantFunctorCorrectionProposal();
