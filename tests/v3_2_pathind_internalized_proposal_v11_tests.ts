/**
 * Focused corrected-v11 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11,
    CorePathindInternalized1dProposalV11,
    CorePathindInternalized1dProposalV11Error,
    validateCorePathindInternalized1dProposalV11
} from '../src/v3_2/pathind_internalized_proposal_v11';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV11 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11
    )) as CorePathindInternalized1dProposalV11;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV11) => void,
    expected: CorePathindInternalized1dProposalV11Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV11(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV11Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v11', () => {
    it('pins the exact v10 target-fibre counterevidence', () => {
        const proposal = validateCorePathindInternalized1dProposalV11();
        assert.equal(Object.isFrozen(proposal), true);
        const evidence = proposal.parent.counterevidence;
        assert.deepEqual(
            [
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                evidence.directSourceFibreRuleFiredOnSource,
                evidence.directSourceFibreRuleFiredOnTarget,
                evidence.failingDeclaration,
                evidence.primaryComparisonStepsBeforeMismatch,
                evidence.primaryMismatchCode,
                evidence.primaryMismatchLeft,
                evidence.primaryMismatchRight
            ],
            [
                '270da40',
                '302c4a9',
                true,
                true,
                'PathIndSrc_transport_func',
                336,
                'BOUND_VARIABLE_MISMATCH',
                'bound:3',
                'bound:2'
            ]
        );
    });

    it('selects exactly 4/11/0/10 across the staged modules', () => {
        const implementation =
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11.exactImplementation;
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
            [4, 11, 0, 10, '4/11/0/10', 5, 6, 9, 2, 3, 4]
        );
    });

    it('selects only the complete-parent transported-motive fibre', () => {
        const fusion = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11
            .dependencyClosure.transportedMotiveReflexiveFibreFusion;
        assert.deepEqual(
            [fusion.ruleId, fusion.left, fusion.right],
            [
                'pathind.internalized.' +
                    'transported-motive-reflexive-fibre-' +
                    'presentation-fusion',
                'Fibre_cat(pathout_motive_transport_obj(Z,x,y,p,E),' +
                    'pathout_refl_obj(Z,y))',
                'Fibre_cat(E,pathout_obj(Z,x,y,p))'
            ]
        );
        assert.deepEqual(
            [
                fusion.activeMathematicalRuleDelta,
                fusion.derivedSupportRuleDelta,
                fusion.proofRuleDelta,
                fusion.declarationBodyOrTypeChangeAuthorized,
                fusion.genericComparisonChangeAuthorized
            ],
            [0, 1, 0, false, false]
        );
    });

    it('preserves consumers, observations, negatives, and oracle scope', () => {
        const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V11;
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
                    primaryComparisonStepsBeforeMismatch: number;
                }).primaryComparisonStepsBeforeMismatch = 0;
            },
            'PATHIND_INTERNALIZED_V11_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.stagedModulePartition
                        .extensionRuntimeRuleIds as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_V11_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V11_AUTHORIZATION_DRIFT'
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
                /pathind_internalized_proposal_v11/u,
                path
            );
        }
    });
});
