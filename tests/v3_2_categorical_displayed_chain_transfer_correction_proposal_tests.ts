/**
 * Focused proposal tests for the exact Terminal_obj transfer prerequisite
 * correction.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL,
    CoreCategoricalDisplayedChainTransferCorrectionProposalError,
    validateCoreCategoricalDisplayedChainTransferCorrectionProposal
} from '../src/v3_2';

const clone = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

describe(
    'TypeScript v3.2 displayed-chain transfer correction proposal',
    () => {
        it('diagnoses exactly the missing active ambient constant', () => {
            const gap =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL
                    .discoveredGap;
            assert.equal(gap.symbol, 'Terminal_obj');
            assert.equal(gap.occurrenceCount, 2);
            assert.equal(gap.presentInEarlierTypeScriptEnvironment, false);
            assert.equal(gap.newMathematicsRequired, false);
            assert.equal(gap.lambdapiEditRequired, false);
        });

        it('preserves the D-012 three-plus-two chain prerequisites', () => {
            const prerequisite =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL
                    .prerequisite;
            assert.deepEqual(
                prerequisite.chainSpecificDeclarationPrerequisites,
                [
                    'sigma_map_func',
                    'fdapp1_int_cell',
                    'fdapp1_int_hom_fapp0'
                ]
            );
            assert.equal(
                prerequisite.chainSpecificDeclarationPrerequisiteCount,
                3
            );
            assert.equal(
                prerequisite.existingRuntimeRulePrerequisiteCount,
                2
            );
        });

        it('selects one ambient signature and no semantic broadening', () => {
            const correction =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL
                    .proposedCorrection;
            assert.deepEqual(
                correction.ambientDeclarationPrerequisites,
                ['Terminal_obj']
            );
            assert.equal(
                correction.totalExistingDeclarationsCompiledForSlice,
                4
            );
            assert.equal(correction.mathematicalOwnerCountRemains, 1);
            assert.equal(correction.mathematicalRuntimeRuleCountRemains, 6);
            assert.equal(correction.activeLambdapiEditCount, 0);
            assert.equal(correction.intrinsicCoreOwnerCountRemains, 0);
        });

        it('rejects wildcard, tt, altered-normal-form, and intrinsic escapes', () => {
            const alternatives =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL
                    .alternatives;
            assert.deepEqual(
                alternatives.filter(
                    item => item.disposition === 'recommend'
                ).map(item => item.id),
                ['transfer-exact-ambient-signature']
            );
            assert.deepEqual(
                alternatives.filter(
                    item => item.disposition === 'reject'
                ).map(item => item.id),
                [
                    'typed-wildcard-in-terminal-slot',
                    'reuse-arbitrary-source-term-on-rhs',
                    'replace-terminal-object-with-native-tt',
                    'intrinsic-core-terminal-object'
                ]
            );
        });

        it('keeps itself pending and browser/parser/Git scope closed', () => {
            const proposal =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL;
            assert.equal(
                proposal.decisionEffects.authorityAuthorized,
                false
            );
            assert.equal(
                proposal.decisionEffects.implementationAuthorized,
                false
            );
            assert.ok(
                proposal.nonEffects.includes(
                    'does-not-add-a-parser-rawexpr-or-second-checker'
                )
            );
            assert.ok(
                proposal.nonEffects.includes(
                    'does-not-broaden-git-authority'
                )
            );
            assert.doesNotMatch(
                readFileSync('src/v3_2/browser.ts', 'utf8'),
                /displayed_chain_transfer_correction|D-DTTLF-USABILITY-013/u
            );
        });

        it('is deeply frozen and rejects boundary or authority drift', () => {
            const proposal =
                CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_CORRECTION_PROPOSAL;
            assertDeepFrozen(proposal);
            assert.doesNotThrow(
                () =>
                    validateCoreCategoricalDisplayedChainTransferCorrectionProposal()
            );

            const changedBoundary: any = clone(proposal);
            changedBoundary.proposedCorrection.activeLambdapiEditCount = 1;
            assert.throws(
                () =>
                    validateCoreCategoricalDisplayedChainTransferCorrectionProposal(
                        changedBoundary
                    ),
                error =>
                    error instanceof
                        CoreCategoricalDisplayedChainTransferCorrectionProposalError &&
                    error.code ===
                        'DISPLAYED_CHAIN_TRANSFER_CORRECTION_BOUNDARY_DRIFT'
            );

            const changedAuthority: any = clone(proposal);
            changedAuthority.decisionEffects.implementationAuthorized = true;
            assert.throws(
                () =>
                    validateCoreCategoricalDisplayedChainTransferCorrectionProposal(
                        changedAuthority
                    ),
                error =>
                    error instanceof
                        CoreCategoricalDisplayedChainTransferCorrectionProposalError &&
                    error.code ===
                        'DISPLAYED_CHAIN_TRANSFER_CORRECTION_AUTHORITY_DRIFT'
            );
        });
    }
);
