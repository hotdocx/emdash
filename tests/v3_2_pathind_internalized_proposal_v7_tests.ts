/**
 * Focused corrected-v7 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7,
    CorePathindInternalized1dProposalV7,
    CorePathindInternalized1dProposalV7Error,
    validateCorePathindInternalized1dProposalV7
} from '../src/v3_2/pathind_internalized_proposal_v7';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV7 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7
    )) as CorePathindInternalized1dProposalV7;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV7) => void,
    expected: CorePathindInternalized1dProposalV7Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV7(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV7Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v7', () => {
    it('pins completed generic prerequisites and the action mismatch', () => {
        const proposal = validateCorePathindInternalized1dProposalV7();
        assert.equal(Object.isFrozen(proposal), true);
        const evidence = proposal.parent.counterevidence;
        assert.deepEqual(
            [
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                evidence.allEightLocalRuntimeRulesCompiled,
                evidence.firstTransparentDefinitionCompiled,
                evidence.failingDeclaration,
                evidence.failingComparisonPath,
                evidence.effectiveComparisonStepLimit,
                evidence.comparisonStepLimitExceeded,
                evidence.comparisonStepsBeforeMismatch,
                proposal.parent.genericComparisonPrerequisite
                    .semanticCheckpoint,
                proposal.parent.declarationBudgetPrerequisite
                    .semanticCheckpoint
            ],
            [
                '19eb941',
                '2112543',
                true,
                true,
                'pathout_motive_transport_arrow',
                'application:functor-object:argument:0',
                512,
                false,
                284,
                'e560551',
                'e560551'
            ]
        );
    });

    it('adds one support rule to make exactly 4/9/0/10', () => {
        const implementation =
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7.exactImplementation;
        assert.deepEqual(
            [
                implementation.trustedDeclarations.length,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.exactBoundary,
                implementation.mathematicalRuntimeProjectionCount,
                implementation.derivedRuntimeSupportRuleCount
            ],
            [4, 9, 0, 10, '4/9/0/10', 5, 4]
        );
        assert.deepEqual(
            implementation.runtimeRules.map(rule => rule.order),
            [0, 1, 2, 3, 4, 5, 6, 7, 8]
        );
    });

    it('selects only the stable action-level presentation bridge', () => {
        const fusion = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7
            .dependencyClosure
            .motiveTransportActionCategoryPresentationFusion;
        assert.deepEqual(
            [
                fusion.ruleId,
                fusion.left,
                fusion.right,
                fusion.exactStablePostDeltaPairSelected,
                fusion.actionLevelPresentationOnly,
                fusion.activeMathematicalRuleDelta,
                fusion.derivedSupportRuleDelta,
                fusion.proofRuleDelta,
                fusion.underlyingCategoryCollapseAuthorized,
                fusion.genericDeclarationProofIntegrationAuthorized
            ],
            [
                'pathind.internalized.' +
                    'motive-transport-action-category-presentation-fusion',
                'fapp0(Functor_cat(K,Cat_cat),' +
                    'Functor_cat(L,Cat_cat),F,E)',
                'fapp0(Catd_cat(K),Catd_cat(L),F,E)',
                true,
                true,
                0,
                1,
                0,
                false,
                false
            ]
        );
    });

    it('preserves consumers, observations, negatives, and oracle scope', () => {
        const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V7;
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
            'PATHIND_INTERNALIZED_V7_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_V7_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V7_AUTHORIZATION_DRIFT'
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
                /pathind_internalized_proposal_v7/u,
                path
            );
        }
    });
});
