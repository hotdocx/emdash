/**
 * Focused corrected-v3 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3,
    CorePathindInternalized1dProposalV3,
    CorePathindInternalized1dProposalV3Error,
    validateCorePathindInternalized1dProposalV3
} from '../src/v3_2/pathind_internalized_proposal_v3';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV3 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3
    )) as CorePathindInternalized1dProposalV3;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV3) => void,
    expected: CorePathindInternalized1dProposalV3Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV3(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV3Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v3', () => {
    it('pins the corrected base and dependency-prefix shadowing trace',
        () => {
            const proposal = validateCorePathindInternalized1dProposalV3();
            assert.equal(Object.isFrozen(proposal), true);
            const evidence = proposal.parent.counterevidence;
            assert.deepEqual(
                [
                    proposal.parent.supersededProposalCheckpoint,
                    proposal.parent.supersededReviewCheckpoint,
                    evidence.correctedEvaluationBase,
                    evidence.v2SupportRuleSubjectChecked,
                    evidence.compiledLocalRuleCountBeforeFailure,
                    evidence.v2PrePrefixFusionMatched,
                    evidence.v2PrePrefixFusionShadowedByDependencyPrefix,
                    evidence.temporaryObserversRetained,
                    evidence.genericCheckerDiffEmpty
                ],
                [
                    'fbfc4dd',
                    '2a250fb',
                    'Catd_cat(PathOut_cat(Z,x))',
                    true,
                    3,
                    false,
                    true,
                    false,
                    true
                ]
            );
            assert.deepEqual(
                evidence.dependencyRulesAppliedBeforeLocalSupport,
                [
                    'directed.category-hom.decode',
                    'categorical.mixed-action.functor-classifier-definition'
                ]
            );
        });

    it('replaces rule two without widening 4/5/0/10', () => {
        const implementation =
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3.exactImplementation;
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
            implementation.runtimeRules.map(rule => rule.order),
            [0, 1, 2, 3, 4]
        );
        assert.equal(
            implementation.runtimeRules[2].id,
            'pathind.internalized.' +
                'path-ind-functor-component-post-prefix-subject-fusion'
        );
        assert.equal(
            implementation.runtimeRules.some(rule =>
                rule.id.endsWith('component-subject-fusion')
            ),
            false
        );
    });

    it('pins the stable decoded type and keeps the correction local', () => {
        const correction = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3
            .dependencyClosure.componentSubjectPresentationCorrection;
        assert.deepEqual(
            [
                correction.measuredLeft,
                correction.measuredRight,
                correction.replacesUnreachableV2PrePrefixFusion,
                correction
                    .wrapsStablePostPrefixPresentationUnderDecodedObjectClassifier,
                correction.subjectCheckRequiredBeforeImplementationCheckpoint,
                correction.activeMathematicalRuleDelta,
                correction.additionalRuntimeRuleAuthorized,
                correction.genericRuntimeMatcherChangeAuthorized,
                correction.genericCheckerChangeAuthorized,
                correction.inheritedProofProgramDependencyAuthorized
            ],
            [
                'τ(Obj(Functor_cat(PathInd_src_catd(Z,x)[E],' +
                    'PathInd_tgt_catd(Z,x)[E])))',
                'τ(Obj(Functor_cat(Fibre_cat(E,pathout_refl_obj(Z,x)),' +
                    'Pi_cat(E))))',
                true,
                true,
                true,
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
            const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V3;
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
                    v2PrePrefixFusionMatched: boolean;
                }).v2PrePrefixFusionMatched = true;
            },
            'PATHIND_INTERNALIZED_V3_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).push({});
            },
            'PATHIND_INTERNALIZED_V3_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V3_AUTHORIZATION_DRIFT'
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
                    /pathind_internalized_proposal_v3/u,
                    path
                );
            }
        });
});
