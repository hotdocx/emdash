/**
 * Focused corrected-v12 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12,
    CorePathindInternalized1dProposalV12,
    CorePathindInternalized1dProposalV12Error,
    validateCorePathindInternalized1dProposalV12
} from '../src/v3_2/pathind_internalized_proposal_v12';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV12 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12
    )) as CorePathindInternalized1dProposalV12;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV12) => void,
    expected: CorePathindInternalized1dProposalV12Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV12(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV12Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v12', () => {
    it('pins the exact v11 section-category counterevidence', () => {
        const proposal = validateCorePathindInternalized1dProposalV12();
        assert.equal(Object.isFrozen(proposal), true);
        const evidence = proposal.parent.counterevidence;
        assert.deepEqual(
            [
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                evidence.compiledDerivedTransparentDefinitionCount,
                evidence.failingDeclaration,
                evidence.comparisonSteps,
                evidence.comparisonMismatchCodes,
                evidence.primaryMismatchLeft,
                evidence.primaryMismatchRight
            ],
            [
                '2e1e593',
                '731dc32',
                5,
                'pathout_pi_transport_func',
                [318, 326, 54],
                ['TAG_MISMATCH', 'TAG_MISMATCH', 'TAG_MISMATCH'],
                'call:reference:dttlf_Functord_cat',
                'application:section-category'
            ]
        );
    });

    it('selects exactly 4/12/0/10 across the staged modules', () => {
        const implementation =
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12.exactImplementation;
        const partition = implementation.stagedModulePartition;
        assert.deepEqual(
            [
                implementation.trustedDeclarations.length,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.exactBoundary,
                implementation.mathematicalRuntimeProjectionCount,
                implementation.derivedRuntimeSupportRuleCount,
                partition.baseRuntimeRuleIds.length,
                partition.extensionRuntimeRuleIds.length,
                partition.prefixTransparentDefinitions.length,
                partition.suffixTransparentDefinitions.length
            ],
            [4, 12, 0, 10, '4/12/0/10', 5, 7, 9, 3, 3, 4]
        );
    });

    it('selects only the complete PathOut Pi transport parent', () => {
        const fusion = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12
            .dependencyClosure.pathoutPiTransportFunctorPresentationFusion;
        assert.equal(
            fusion.ruleId,
            'pathind.internalized.' +
                'pathout-pi-transport-functor-presentation-fusion'
        );
        assert.match(fusion.left, /Functord_cat/u);
        assert.match(fusion.right, /Pi_cat/u);
        assert.deepEqual(
            [
                fusion.sourceAndTargetCategoriesClosedTogether,
                fusion.underlyingCategoryRuntimeEqualitySelected,
                fusion.activeMathematicalRuleDelta,
                fusion.derivedSupportRuleDelta,
                fusion.proofRuleDelta,
                fusion.genericSectionCategoryRuleAuthorized
            ],
            [true, false, 0, 1, 0, false]
        );
    });

    it('preserves consumers, observations, negatives, and oracle scope', () => {
        const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V12;
        assert.deepEqual(
            [
                proposal.typedLibraryConsumers.length,
                proposal.selectedRuntimeObservations.length,
                proposal.negativeConsumers.length,
                proposal.boundedOracle.assertions.length
            ],
            [2, 10, 10, 12]
        );
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent.counterevidence as {
                    compiledDerivedTransparentDefinitionCount: number;
                }).compiledDerivedTransparentDefinitionCount = 0;
            },
            'PATHIND_INTERNALIZED_V12_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.stagedModulePartition
                        .extensionRuntimeRuleIds as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_V12_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V12_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, workspace, or browser barrels', () => {
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
                /pathind_internalized_proposal_v12/u,
                path
            );
        }
    });
});
