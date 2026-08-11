/**
 * Focused corrected-v6 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6,
    CorePathindInternalized1dProposalV6,
    CorePathindInternalized1dProposalV6Error,
    validateCorePathindInternalized1dProposalV6
} from '../src/v3_2/pathind_internalized_proposal_v6';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV6 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6
    )) as CorePathindInternalized1dProposalV6;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV6) => void,
    expected: CorePathindInternalized1dProposalV6Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV6(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV6Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v6', () => {
    it('pins the first transparent-library mismatch and corrected prerequisite',
        () => {
            const proposal = validateCorePathindInternalized1dProposalV6();
            assert.equal(Object.isFrozen(proposal), true);
            const evidence = proposal.parent.counterevidence;
            const prerequisite =
                proposal.parent.genericComparisonPrerequisite;
            assert.deepEqual(
                [
                    proposal.parent.supersededProposalCheckpoint,
                    proposal.parent.supersededReviewCheckpoint,
                    evidence.allSevenLocalRuntimeRulesCompiled,
                    evidence.failingDeclaration,
                    evidence.independentlyNormalizedBodyTypeSteps,
                    evidence.independentlyNormalizedExpectedTypeSteps,
                    evidence.independentlyNormalizedFormsExactlyEqual,
                    evidence.localTwoSidedClassifierFusionRequired,
                    prerequisite.proposalCheckpoint,
                    prerequisite.reviewCheckpoint,
                    prerequisite.originalSourceRootReplayRequired
                ],
                [
                    'fe0306d',
                    'a94c2f7',
                    true,
                    'pathout_motive_transport_obj',
                    37,
                    21,
                    false,
                    true,
                    'a42ffc9',
                    '5277885',
                    true
                ]
            );
        });

    it('adds one support rule to make exactly 4/8/0/10', () => {
        const implementation =
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6.exactImplementation;
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
            [4, 8, 0, 10, '4/8/0/10', 5, 3]
        );
        assert.deepEqual(
            implementation.runtimeRules.map(rule => rule.order),
            [0, 1, 2, 3, 4, 5, 6, 7]
        );
    });

    it('selects only the stable two-sided decoded classifier bridge', () => {
        const fusion = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6
            .dependencyClosure.motiveTransportCategoryPresentationFusion;
        assert.deepEqual(
            [
                fusion.ruleId,
                fusion.left,
                fusion.right,
                fusion.exactStablePostDeltaPairSelected,
                fusion.twoSidedCategoryPresentationOnly,
                fusion.activeMathematicalRuleDelta,
                fusion.derivedSupportRuleDelta,
                fusion.proofRuleDelta,
                fusion.underlyingCategoryCollapseAuthorized,
                fusion.genericDeclarationProofIntegrationAuthorized
            ],
            [
                'pathind.internalized.' +
                    'motive-transport-functor-category-presentation-fusion',
                'τ(Obj(Functor_cat(Functor_cat(K,Cat_cat),' +
                    'Functor_cat(L,Cat_cat))))',
                'τ(Obj(Functor_cat(Catd_cat(K),Catd_cat(L))))',
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

    it('preserves the v5 consumers, observations, negatives, and oracle',
        () => {
            const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V6;
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
                    failingDeclaration: string;
                }).failingDeclaration = 'wrong';
            },
            'PATHIND_INTERNALIZED_V6_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_V6_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V6_AUTHORIZATION_DRIFT'
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
                    /pathind_internalized_proposal_v6/u,
                    path
                );
            }
        });
});
