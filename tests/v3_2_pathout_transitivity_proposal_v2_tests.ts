/**
 * Focused tests for corrected, non-authorizing PathOut transitivity v2.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_BINDER_TRANSFER_BOUNDARY
} from '../src/v3_2/categorical_fibred_binder_transfer';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL
} from '../src/v3_2/pathout_transitivity_proposal';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW
} from '../src/v3_2/pathout_transitivity_review';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2,
    CorePathoutTransitivity1eProposalV2,
    CorePathoutTransitivity1eProposalV2Error,
    cloneCorePathoutTransitivity1eProposalV2,
    validateCorePathoutTransitivity1eProposalV2
} from '../src/v3_2/pathout_transitivity_proposal_v2';

const repositoryRoot = resolve(__dirname, '..');

const assertProposalError = (
    mutate: (proposal: CorePathoutTransitivity1eProposalV2) => void,
    expected: CorePathoutTransitivity1eProposalV2Error['code']
): void => {
    const proposal = cloneCorePathoutTransitivity1eProposalV2();
    mutate(proposal);
    assert.throws(
        () => validateCorePathoutTransitivity1eProposalV2(proposal),
        error =>
            error instanceof CorePathoutTransitivity1eProposalV2Error &&
            error.code === expected
    );
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

describe('PATHOUT-LIBRARY-TRANSITIVITY-1E corrected proposal v2', () => {
    it('pins and supersedes the exact reviewed v1 boundary', () => {
        const proposal = validateCorePathoutTransitivity1eProposalV2();
        assertDeepFrozen(proposal);
        assert.deepEqual(
            [
                proposal.parent.supersededProposalRevision,
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededProposalSha256,
                proposal.parent.supersededReviewRevision,
                proposal.parent.supersededReviewCheckpoint,
                proposal.parent.supersededReviewSha256,
                proposal.parent.supersededLedgerCheckpoint
            ],
            [
                CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL.revision,
                '50b9a56',
                '1951ff30d42ab95dfa9d77fadb747be9e' +
                    'ca3c4bf760a99ab283da07fc1351bfb',
                CORE_PATHOUT_TRANSITIVITY_1E_REVIEW.revision,
                'f60b36a',
                'cd1fead66d6447e0ed73fe5eaa6cbc67e' +
                    'f0a9dbb606897dbad4c6e7c0b6c76ca',
                '150e315'
            ]
        );
    });

    it('records the two exact cold-replay presentation residuals', () => {
        const evidence = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2
            .parent.counterevidence;
        assert.deepEqual(
            [
                evidence.coldFocusedGate,
                evidence.allFiveTransparentDefinitionsAdmitted,
                evidence.bothTypedConsumersAccepted,
                evidence.allEightNegativeConsumersRejected,
                evidence.failureCount,
                evidence.genericCompilerDiffEmpty
            ],
            [
                '8-tests-5-pass-2-fail-1-skip',
                true,
                true,
                true,
                2,
                true
            ]
        );
        assert.deepEqual(
            [
                evidence.sectionCategoryResidual.mismatch,
                evidence.sectionCategoryResidual.existingProvider,
                evidence.sectionCategoryResidual.newRuntimeRuleRequired,
                evidence.sectionComponentResidual.mismatch,
                evidence.sectionComponentResidual.normalizedLeftOwner,
                evidence.sectionComponentResidual.normalizedRightOwner,
                evidence.sectionComponentResidual
                    .completeParentLocalFusionRequired
            ],
            [
                'TAG_MISMATCH-at-root',
                'stress.sigma-pi.uncurrying',
                false,
                'TAG_MISMATCH-at-root',
                'functor-object',
                'hom_int_precomp_func',
                true
            ]
        );
    });

    it('freezes exactly one local subject-checked support rule', () => {
        const implementation = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2
            .exactImplementation;
        const rule = implementation.runtimeRules[0];
        assert.deepEqual(
            [
                implementation.exactBoundary,
                implementation.trustedDeclarations.length,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.localRuntimeSupportRuleCount,
                rule?.id,
                rule?.sourceOwner,
                rule?.mathematicalRule,
                rule?.compileAfterTransparentDefinitionCount,
                rule?.completeParentOnly,
                rule?.mustSubjectCheck
            ],
            [
                '0/1/0/5',
                0,
                1,
                0,
                5,
                1,
                CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
                'functor-object',
                false,
                5,
                true,
                true
            ]
        );
    });

    it('reuses one inherited proof provider without runtime collapse', () => {
        const implementation = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2
            .exactImplementation;
        const provider = implementation.inheritedProofProviders[0];
        assert.equal(implementation.localProofRuleCount, 0);
        assert.equal(implementation.inheritedProofProviderCount, 1);
        assert.equal(provider?.id, 'stress.sigma-pi.uncurrying');
        assert.equal(provider?.recheckAgainstDescendantEnvironment, true);
        assert.equal(provider?.runtimeClassifierCollapseAuthorized, false);
        assert.deepEqual(
            CORE_CATEGORICAL_FIBRED_BINDER_TRANSFER_BOUNDARY.proofRuleIds,
            ['stress.sigma-pi.uncurrying']
        );
    });

    it('preserves v1 consumers and partitions all eight observations', () => {
        const proposal = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2;
        assert.deepEqual(
            proposal.exactImplementation.transparentDefinitions,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL
                .exactImplementation.transparentDefinitions
        );
        assert.deepEqual(
            proposal.requiredExistingProviders,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL.requiredExistingProviders
        );
        assert.deepEqual(
            proposal.typedLibraryConsumers,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL.typedLibraryConsumers
        );
        assert.deepEqual(
            proposal.negativeConsumers,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL.negativeConsumers
        );
        assert.deepEqual(
            proposal.boundedOracle,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL.boundedOracle
        );
        const partition = proposal.exactImplementation
            .selectedObservationPartition;
        assert.deepEqual(
            [
                partition.runtimeDefinitional.length,
                partition.inheritedProofTime.length,
                new Set([
                    ...partition.runtimeDefinitional,
                    ...partition.inheritedProofTime
                ]).size
            ],
            [7, 1, 8]
        );
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent as {
                    supersededLedgerCheckpoint: string;
                }).supersededLedgerCheckpoint = 'wrong';
            },
            'PATHOUT_TRANSITIVITY_PROPOSAL_V2_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.exactImplementation as {
                    broadHomConRuntimeImportAdded: boolean;
                }).broadHomConRuntimeImportAdded = true;
            },
            'PATHOUT_TRANSITIVITY_PROPOSAL_V2_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHOUT_TRANSITIVITY_PROPOSAL_V2_AUTHORIZATION_DRIFT'
        );
    });

    it('remains root-only, non-public, and non-authorizing', () => {
        const proposal = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2;
        assert.equal(proposal.decision.implementationAuthorized, false);
        assert.equal(
            proposal.profileSealing.browserOrPublicPackageExportAuthorized,
            false
        );
        for (const relative of [
            'src/v3_2/index.ts',
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/browser.ts'
        ]) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, relative), 'utf8'),
                /pathout_transitivity_proposal_v2/u,
                relative
            );
        }
    });
});
