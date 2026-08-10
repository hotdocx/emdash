/**
 * Focused PATHOUT-LIBRARY-FOUNDATION-1B0 proposal tests.
 */

import assert from 'node:assert/strict';
import { readdirSync, readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY
} from '../src/v3_2/categorical_displayed_chain_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_BOUNDARY
} from '../src/v3_2/categorical_displayed_nd_higher_foundation_transfer';
import {
    CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
} from '../src/v3_2/categorical_mixed_action_transfer';
import {
    CORE_DIRECTED_1A_PRIMITIVE_NAMES
} from '../src/v3_2/directed_1a';
import {
    CORE_DIRECTED_1B_PRIMITIVE_NAMES
} from '../src/v3_2/directed_1b';
import {
    CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL,
    CorePathoutFoundation1b0Proposal,
    CorePathoutFoundation1b0ProposalError,
    validateCorePathoutFoundation1b0Proposal
} from '../src/v3_2/pathout_foundation_proposal';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathoutFoundation1b0Proposal =>
    JSON.parse(JSON.stringify(
        CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL
    )) as CorePathoutFoundation1b0Proposal;

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

const assertProposalError = (
    mutate: (proposal: CorePathoutFoundation1b0Proposal) => void,
    expected: CorePathoutFoundation1b0ProposalError['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathoutFoundation1b0Proposal(proposal),
        error =>
            error instanceof CorePathoutFoundation1b0ProposalError &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-FOUNDATION-1B0 proposal', () => {
    it('pins corrected 0A and remains non-self-authorizing', () => {
        const proposal = validateCorePathoutFoundation1b0Proposal();
        assertDeepFrozen(proposal);
        assert.deepEqual(
            [
                proposal.parent.correctedAuditCheckpoint,
                proposal.parent.correctedLedgerCheckpoint,
                proposal.parent.supersededProposalCheckpoint,
                proposal.decision.status,
                proposal.decision.implementationAuthorized
            ],
            [
                '5a1ea75',
                '828b0d7',
                'dd69325',
                'proposal-only',
                false
            ]
        );
    });

    it('freezes exactly three opaque, five runtime, one proof, nine transparent',
        () => {
            const implementation =
                CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL
                    .exactImplementation;
            assert.deepEqual(
                implementation.prerequisiteDeclarations
                    .map(entry => entry.name),
                [
                    'hom_int_precomp_tele_func',
                    'hom_int_precomp_func',
                    'Sigma_func'
                ]
            );
            assert.deepEqual(
                implementation.runtimeRules.map(entry => entry.authorityLine),
                [8445, 8449, 8453, 12803, 13148]
            );
            assert.deepEqual(
                implementation.proofRules.map(entry => entry.authorityLine),
                [8463]
            );
            assert.deepEqual(
                implementation.libraryDefinitions.map(entry => entry.name),
                [
                    'Rep_catd_func',
                    'Rep_catd',
                    'Rep_transport_func',
                    'PathOut_cat',
                    'PathOut_cat_func',
                    'PathOut_transport_func',
                    'pathout_obj',
                    'pathout_refl_obj',
                    'pathout_refl_arrow'
                ]
            );
        });

    it('selects the smallest existing predecessor evidence', () => {
        const predecessor =
            CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL.selectedPredecessor;
        assert.equal(
            CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                .revision,
            predecessor.boundaryRevision
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_BOUNDARY
                .declarationNames.includes('hom_int'),
            true
        );
        assert.equal(
            CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY
                .declarationNames.includes('hom_'),
            true
        );
        assert.equal(
            CORE_CATEGORICAL_MIXED_ACTION_TRANSFER_BOUNDARY.runtimeRuleIds
                .includes(
                    'categorical.mixed-action.' +
                    'internal-hom-object-projection'
                ),
            true
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_BOUNDARY
                .existingPrerequisiteDeclarationNames
                .includes('sigma_map_func'),
            true
        );
        assert.equal(
            CORE_DIRECTED_1A_PRIMITIVE_NAMES['sigma-category'],
            'dttlf_Sigma_cat'
        );
        assert.equal(
            CORE_DIRECTED_1B_PRIMITIVE_NAMES['sigma-transport-arrow'],
            'dttlf_sigma_transport_arrow'
        );
        assert.equal(predecessor.importWholeScaleProfile, false);
        assert.equal(predecessor.reuseReviewedMixedActionDescendant, true);
        assert.equal(
            predecessor.extractOrDuplicateRepresentedHomSubset,
            false
        );
    });

    it('confirms the new owners are absent from pre-1B transfer modules',
        () => {
            const sourceDirectory = resolve(repositoryRoot, 'src/v3_2');
            const transferSources = readdirSync(sourceDirectory)
                .filter(name => name.endsWith('_transfer.ts'))
                .map(name => readFileSync(
                    resolve(sourceDirectory, name),
                    'utf8'
                ))
                .join('\n');
            assert.doesNotMatch(
                transferSources,
                /symbol hom_int_precomp_(?:tele_)?func\b/u
            );
            assert.doesNotMatch(
                transferSources,
                /(?:injective )?symbol Sigma_func\b/u
            );
        });

    it('separates the sealed profile from the safe transparent library',
        () => {
            const sealing =
                CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL.profileSealing;
            assert.deepEqual(
                [
                    sealing.publicSafeLibraryCanAddTransparentDefinitions,
                    sealing.publicSafeLibraryCanAddOpaqueOwners,
                    sealing.publicSafeLibraryCanAddRuntimeRules,
                    sealing.publicSafeLibraryCanAddProofRules,
                    sealing.lowLevelAuthoringApiRemainsExplicitlyTrustBearing
                ],
                [true, false, false, false, true]
            );
        });

    it('requires typed positives, strict negatives, and a bounded oracle',
        () => {
            const proposal = CORE_PATHOUT_FOUNDATION_1B0_PROPOSAL;
            assert.equal(proposal.positiveConsumers.length, 7);
            assert.equal(proposal.negativeConsumers.length, 8);
            assert.deepEqual(
                [
                    proposal.boundedOracle.timeoutMs,
                    proposal.boundedOracle.assertions.length,
                    proposal.boundedOracle
                        .requiredForImplementationAcceptance,
                    proposal.boundedOracle.requiredForProposalAcceptance
                ],
                [20_000, 6, true, false]
            );
        });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent as {
                    correctedAuditCheckpoint: string;
                }).correctedAuditCheckpoint = 'wrong';
            },
            'PATHOUT_FOUNDATION_PROPOSAL_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).pop();
            },
            'PATHOUT_FOUNDATION_PROPOSAL_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHOUT_FOUNDATION_PROPOSAL_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, or browser barrels', () => {
        for (
            const path of [
                'src/v3_2/index.ts',
                'src/v3_2/package_core.ts',
                'src/v3_2/package_authoring.ts',
                'src/v3_2/package_workspace.ts',
                'src/v3_2/browser.ts'
            ]
        ) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, path), 'utf8'),
                /pathout_foundation_proposal|CORE_PATHOUT_FOUNDATION/u,
                path
            );
        }
    });
});
