/**
 * Focused corrected-v4 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4,
    CorePathindInternalized1dProposalV4,
    CorePathindInternalized1dProposalV4Error,
    validateCorePathindInternalized1dProposalV4
} from '../src/v3_2/pathind_internalized_proposal_v4';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV4 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4
    )) as CorePathindInternalized1dProposalV4;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV4) => void,
    expected: CorePathindInternalized1dProposalV4Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV4(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV4Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v4', () => {
    it('pins the v3 green prefix and exact transfd mismatch', () => {
        const proposal = validateCorePathindInternalized1dProposalV4();
        assert.equal(Object.isFrozen(proposal), true);
        const evidence = proposal.parent.counterevidence;
        assert.deepEqual(
            [
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                evidence.compiledLocalRuleCountBeforeFailure,
                evidence.v3PostPrefixSupportRuleSubjectChecked,
                evidence.pathIndFunctorComponentRuleSubjectChecked,
                evidence.failingRule,
                evidence.mismatchLeft,
                evidence.mismatchRight,
                evidence.temporaryObserverRetained,
                evidence.genericCheckerDiffEmpty
            ],
            [
                '5a1d635',
                '6694c87',
                4,
                true,
                true,
                'pathind.internalized.path-ind-transfd-component',
                'Catd_cat(PathOut_cat(Z,x))',
                'Functor_cat(PathOut_cat(Z,x),Cat_cat)',
                false,
                true
            ]
        );
    });

    it('adds one support rule to make exactly 4/6/0/10', () => {
        const implementation =
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4.exactImplementation;
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
            [4, 6, 0, 10, '4/6/0/10', 4, 2]
        );
        assert.deepEqual(
            implementation.runtimeRules.map(rule => rule.order),
            [0, 1, 2, 3, 4, 5]
        );
        assert.equal(
            implementation.runtimeRules[4].id,
            'pathind.internalized.' +
                'path-ind-transfd-component-subject-fusion'
        );
    });

    it('scopes the new fusion under Transf_cat and denies collapse', () => {
        const correction = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4
            .dependencyClosure
            .transformationComponentSubjectPresentationCorrection;
        assert.deepEqual(
            [
                correction.measuredLeft,
                correction.measuredRight,
                correction
                    .wrapsCatdFunctorComparisonUnderTransforCategory,
                correction.subjectCheckRequiredBeforeImplementationCheckpoint,
                correction.activeMathematicalRuleDelta,
                correction.proofRuleDelta,
                correction.genericCategoryCollapseAuthorized,
                correction.genericRuntimeMatcherChangeAuthorized,
                correction.genericCheckerChangeAuthorized,
                correction.inheritedProofProgramDependencyAuthorized
            ],
            [
                'τ(Obj(Transf_cat(Catd_cat(PathOut_cat(Z,x)),Cat_cat,' +
                    'PathInd_src_catd(Z,x),PathInd_tgt_catd(Z,x))))',
                'τ(Obj(Transf_cat(Functor_cat(PathOut_cat(Z,x),Cat_cat),' +
                    'Cat_cat,PathInd_src_catd(Z,x),' +
                    'PathInd_tgt_catd(Z,x))))',
                true,
                true,
                0,
                0,
                false,
                false,
                false,
                false
            ]
        );
    });

    it('keeps every consumer, observation, negative, and oracle unchanged',
        () => {
            const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V4;
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
                    pathIndFunctorComponentRuleSubjectChecked: boolean;
                }).pathIndFunctorComponentRuleSubjectChecked = false;
            },
            'PATHIND_INTERNALIZED_V4_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_V4_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V4_AUTHORIZATION_DRIFT'
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
                    /pathind_internalized_proposal_v4/u,
                    path
                );
            }
        });
});
