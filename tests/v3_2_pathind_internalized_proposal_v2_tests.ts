/**
 * Focused corrected-v2 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL
} from '../src/v3_2/pathind_internalized_proposal';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2,
    CorePathindInternalized1dProposalV2,
    CorePathindInternalized1dProposalV2Error,
    validateCorePathindInternalized1dProposalV2
} from '../src/v3_2/pathind_internalized_proposal_v2';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV2 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2
    )) as CorePathindInternalized1dProposalV2;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV2) => void,
    expected: CorePathindInternalized1dProposalV2Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV2(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV2Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v2', () => {
    it('preserves v1 and pins both failed admission experiments', () => {
        const proposal = validateCorePathindInternalized1dProposalV2();
        assert.equal(Object.isFrozen(proposal), true);
        assert.deepEqual(
            [
                proposal.parent.supersededProposalRevision,
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                proposal.parent.counterevidence.failureCode,
                proposal.parent.counterevidence
                    .fixedEvaluationDependencyExperimentSolved,
                proposal.parent.counterevidence
                    .categoryPresentationProofExperimentStatus,
                proposal.parent.counterevidence
                    .temporaryExperimentsRetained
            ],
            [
                CORE_PATHIND_INTERNALIZED_1D_PROPOSAL.revision,
                '188b8e5',
                'd3a0f31',
                'INVALID_RUNTIME_RULE_TYPE',
                false,
                'stuck',
                false
            ]
        );
    });

    it('adds one derived support fusion to make exactly 4/5/0/10', () => {
        const implementation =
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2.exactImplementation;
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
            [4, 5, 0, 10, '4/5/0/10', 4, 1]
        );
        assert.deepEqual(
            implementation.runtimeRules
                .filter(rule => 'authorityLine' in rule)
                .map(rule => ({
                    id: rule.id,
                    authorityLine: rule.authorityLine
                })),
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL
                .exactImplementation.runtimeRules.map(rule => ({
                    id: rule.id,
                    authorityLine: rule.authorityLine
                }))
        );
        assert.equal(
            implementation.runtimeRules[2].id,
            'pathind.internalized.' +
                'path-ind-functor-component-subject-fusion'
        );
    });

    it('keeps the correction local and denies both attempted substitutes',
        () => {
            const correction =
                CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2
                    .dependencyClosure
                    .componentSubjectPresentationCorrection;
            assert.deepEqual(
                [
                    correction.activeMathematicalRuleDelta,
                    correction.genericRuntimeMatcherChangeAuthorized,
                    correction.genericCheckerChangeAuthorized,
                    correction.inheritedProofProgramDependencyAuthorized,
                    correction.genericFixedEvaluationRuntimeImportAuthorized,
                    correction.alternatePathIndTypeAuthorized,
                    correction.alternateComponentBodyAuthorized
                ],
                [0, false, false, false, false, false, false]
            );
        });

    it('does not widen consumers, observations, negatives, or oracle', () => {
        const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V2;
        assert.deepEqual(
            [
                proposal.typedLibraryConsumers.length,
                proposal.selectedRuntimeObservations.length,
                proposal.negativeConsumers.length,
                proposal.boundedOracle.assertions.length
            ],
            [2, 9, 10, 11]
        );
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent.counterevidence as {
                    temporaryExperimentsRetained: boolean;
                }).temporaryExperimentsRetained = true;
            },
            'PATHIND_INTERNALIZED_V2_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).splice(2, 1);
            },
            'PATHIND_INTERNALIZED_V2_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V2_AUTHORIZATION_DRIFT'
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
                    /pathind_internalized_proposal_v2/u,
                    path
                );
            }
        });
});
