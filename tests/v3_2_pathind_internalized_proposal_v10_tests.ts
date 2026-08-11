/**
 * Focused corrected-v10 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10,
    CorePathindInternalized1dProposalV10,
    CorePathindInternalized1dProposalV10Error,
    validateCorePathindInternalized1dProposalV10
} from '../src/v3_2/pathind_internalized_proposal_v10';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV10 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10
    )) as CorePathindInternalized1dProposalV10;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV10) => void,
    expected: CorePathindInternalized1dProposalV10Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV10(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV10Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v10', () => {
    it('pins the exact v9 trace and unchanged failure', () => {
        const proposal = validateCorePathindInternalized1dProposalV10();
        assert.equal(Object.isFrozen(proposal), true);
        const evidence = proposal.parent.counterevidence;
        assert.deepEqual(
            [
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                evidence.allTenV9RuntimeRulesSubjectChecked,
                evidence.firstThreeTransparentDefinitionsCompiled,
                evidence.failingDeclaration,
                evidence.comparisonStepsBeforeMismatch,
                evidence.v9PostSigmaSupportAppearedInTrace,
                evidence.genericSigmaTelescopeFibreRuleAppearedInTrace,
                evidence.sourceCategoryChildSelectedBeforeFamilyProjection
            ],
            [
                'a735c40',
                '7b466d5',
                true,
                true,
                'PathIndSrc_transport_func',
                360,
                false,
                false,
                true
            ]
        );
    });

    it('retains exactly 4/10/0/10 across two runtime stages', () => {
        const implementation =
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10.exactImplementation;
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
            [4, 10, 0, 10, '4/10/0/10', 5, 5, 9, 1, 3, 4]
        );
    });

    it('selects the staged direct parent without changing declarations', () => {
        const fusion = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10
            .dependencyClosure
            .pathInductionSourceFibreStagedParentFusion;
        assert.deepEqual(
            [
                fusion.ruleId,
                fusion.left,
                fusion.right,
                fusion.pathIndSrcDeclaredByPrefixBeforeRuleCompilation,
                fusion.baseRuntimeRetainsOnlyFirstNineRules,
                fusion.extensionRuntimeContainsOnlyThisRule,
                fusion.suffixUsesComposedBaseAndExtensionRuntime
            ],
            [
                'pathind.internalized.' +
                    'path-ind-source-fibre-at-sigma-pair-' +
                    'presentation-fusion',
                'Fibre_cat(PathIndSrc_catd(Z),Struct_sigma(x,E))',
                'Fibre_cat(E,pathout_refl_obj(Z,x))',
                true,
                true,
                true,
                true
            ]
        );
        assert.deepEqual(
            [
                fusion.declarationBodyOrTypeChangeAuthorized,
                fusion.declarationSourceOrderChangeAuthorized,
                fusion.underlyingCategoryEqualityAuthorized,
                fusion.genericComparisonChangeAuthorized
            ],
            [false, false, false, false]
        );
    });

    it('preserves consumers, observations, negatives, and oracle scope', () => {
        const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V10;
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
                    comparisonStepsBeforeMismatch: number;
                }).comparisonStepsBeforeMismatch = 0;
            },
            'PATHIND_INTERNALIZED_V10_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.stagedModulePartition
                        .baseRuntimeRuleIds as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_V10_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V10_AUTHORIZATION_DRIFT'
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
                /pathind_internalized_proposal_v10/u,
                path
            );
        }
    });
});
