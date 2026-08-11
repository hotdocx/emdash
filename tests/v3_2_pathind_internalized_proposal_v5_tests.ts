/**
 * Focused corrected-v5 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5,
    CorePathindInternalized1dProposalV5,
    CorePathindInternalized1dProposalV5Error,
    validateCorePathindInternalized1dProposalV5
} from '../src/v3_2/pathind_internalized_proposal_v5';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV5 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5
    )) as CorePathindInternalized1dProposalV5;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV5) => void,
    expected: CorePathindInternalized1dProposalV5Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV5(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV5Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v5', () => {
    it('pins the measured paired miss and generic prerequisite', () => {
        const proposal = validateCorePathindInternalized1dProposalV5();
        assert.equal(Object.isFrozen(proposal), true);
        const evidence = proposal.parent.counterevidence;
        const prerequisite = proposal.parent.genericComparisonPrerequisite;
        assert.deepEqual(
            [
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                evidence.compiledLocalRuleCountBeforeFailure,
                evidence.typedWildcardFamilySlotCandidateSubjectChecked,
                evidence.pairedComparisonSteps,
                evidence.independentlyNormalizedLeftSteps,
                evidence.independentlyNormalizedRightSteps,
                evidence.independentlyNormalizedFormsExactlyEqual,
                prerequisite.proposalCheckpoint,
                prerequisite.reviewCheckpoint,
                prerequisite.semanticCheckpointRequiredBeforePathIndCheckpoint
            ],
            [
                '001a899',
                '7984efb',
                5,
                true,
                125,
                58,
                68,
                true,
                'cf8ed76',
                '778da06',
                true
            ]
        );
    });

    it('adds one active projection to make exactly 4/7/0/10', () => {
        const implementation =
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5.exactImplementation;
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
            [4, 7, 0, 10, '4/7/0/10', 5, 2]
        );
        assert.deepEqual(
            implementation.runtimeRules.map(rule => rule.order),
            [0, 1, 2, 3, 4, 5, 6]
        );
        assert.equal(
            implementation.runtimeRules[5].id,
            'pathind.internalized.pi-pullback-component'
        );
    });

    it('uses typed wildcard family slots for the exact active rule', () => {
        const projection = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5
            .dependencyClosure.piPullbackPointwiseProjection;
        assert.deepEqual(
            [
                projection.authorityPosition,
                projection.left,
                projection.right,
                projection.inferredFamilySlotsRemainTypedWildcards,
                projection.exactActiveRuleImportedOneForOne,
                projection.activeMathematicalRuleDelta,
                projection.derivedSupportRuleDelta,
                projection.proofRuleDelta
            ],
            [
                'emdash2/emdash3_2.lp:12680',
                'tapp0_fapp0(K,Cat_cat,_,_,x,' +
                    'Pi_pullback_funcd(K,G))',
                'Pi_func(fapp0(K,Op_cat(Cat_cat),G,x))',
                true,
                true,
                1,
                0,
                0
            ]
        );
    });

    it('adds one observation and one bounded oracle assertion', () => {
        const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V5;
        assert.deepEqual(
            [
                proposal.typedLibraryConsumers.length,
                proposal.selectedRuntimeObservations.length,
                proposal.negativeConsumers.length,
                proposal.boundedOracle.assertions.length,
                proposal.selectedRuntimeObservations.at(-1),
                proposal.boundedOracle.assertions.at(-1)
            ],
            [
                2,
                10,
                10,
                12,
                'Pi_pullback_funcd(G)[x]-reduces-to-Pi_func(G[x])',
                'PathOutPi-component-is-pointwise-Pi'
            ]
        );
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent.counterevidence as {
                    pairedComparisonSteps: number;
                }).pairedComparisonSteps = 124;
            },
            'PATHIND_INTERNALIZED_V5_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_V5_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V5_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, workspace, or browser barrels',
        () => {
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
                    /pathind_internalized_proposal_v5/u,
                    path
                );
            }
        });
});
