/**
 * Focused corrected-v13 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13,
    CorePathindInternalized1dProposalV13,
    CorePathindInternalized1dProposalV13Error,
    validateCorePathindInternalized1dProposalV13
} from '../src/v3_2/pathind_internalized_proposal_v13';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV13 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13
    )) as CorePathindInternalized1dProposalV13;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV13) => void,
    expected: CorePathindInternalized1dProposalV13Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV13(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV13Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v13', () => {
    it('pins the exact v12 pre-delta shadowing evidence', () => {
        const proposal = validateCorePathindInternalized1dProposalV13();
        assert.equal(Object.isFrozen(proposal), true);
        const evidence = proposal.parent.counterevidence;
        assert.deepEqual(
            [
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                evidence.compiledRuntimeRuleCount,
                evidence.failingDeclaration,
                evidence.predecessorRuleAppliedFirst,
                evidence.v12PreDeltaFusionSubjectChecked,
                evidence.v12PreDeltaFusionMatched,
                evidence.v12PreDeltaFusionShadowedByEarlierFragment,
                evidence.additionalRuntimeRuleRequired
            ],
            [
                '39abb02',
                '8833f8f',
                12,
                'pathout_pi_transport_func',
                'categorical.mixed-action.functor-classifier-definition',
                true,
                false,
                true,
                false
            ]
        );
    });

    it('preserves 4/12/0/10 while replacing one extension rule', () => {
        const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13;
        const implementation = proposal.exactImplementation;
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
                partition.semanticCountDelta
            ],
            [4, 12, 0, 10, '4/12/0/10', 5, 7, 9, 3, 0]
        );
        assert.equal(
            partition.extensionRuntimeRuleIds.at(-1),
            'pathind.internalized.' +
                'pathout-pi-transport-post-delta-presentation-fusion'
        );
        assert.equal(partition.extensionRuntimeRuleIds.includes(
            'pathind.internalized.' +
                'pathout-pi-transport-functor-presentation-fusion'
        ), false);
    });

    it('selects the stable decoded-object complete parent only', () => {
        const fusion = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13
            .dependencyClosure.pathoutPiTransportFunctorPresentationFusion;
        assert.match(fusion.left, /^τ\(Obj\(Functor_cat/u);
        assert.match(fusion.right, /^τ\(Obj\(Functor_cat/u);
        assert.deepEqual(
            [
                fusion.replacesUnreachableV12PreDeltaFusion,
                fusion.wrapsStablePresentationUnderDecodedObjectClassifier,
                fusion.sourceAndTargetCategoriesClosedTogether,
                fusion.underlyingCategoryRuntimeEqualitySelected,
                fusion.activeMathematicalRuleDelta,
                fusion.derivedSupportRuleDelta,
                fusion.proofRuleDelta
            ],
            [true, true, true, false, 0, 0, 0]
        );
    });

    it('preserves consumers, observations, negatives, and oracle scope', () => {
        const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V13;
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
                    v12PreDeltaFusionMatched: boolean;
                }).v12PreDeltaFusionMatched = true;
            },
            'PATHIND_INTERNALIZED_V13_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.stagedModulePartition
                        .extensionRuntimeRuleIds as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_V13_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V13_AUTHORIZATION_DRIFT'
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
                /pathind_internalized_proposal_v13/u,
                path
            );
        }
    });
});
