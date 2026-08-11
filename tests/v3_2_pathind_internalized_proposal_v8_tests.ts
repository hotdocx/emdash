/**
 * Focused corrected-v8 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8,
    CorePathindInternalized1dProposalV8,
    CorePathindInternalized1dProposalV8Error,
    validateCorePathindInternalized1dProposalV8
} from '../src/v3_2/pathind_internalized_proposal_v8';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV8 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8
    )) as CorePathindInternalized1dProposalV8;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV8) => void,
    expected: CorePathindInternalized1dProposalV8Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV8(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV8Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v8', () => {
    it('pins the v7 replay through three transparent declarations', () => {
        const proposal = validateCorePathindInternalized1dProposalV8();
        assert.equal(Object.isFrozen(proposal), true);
        const evidence = proposal.parent.counterevidence;
        assert.deepEqual(
            [
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                evidence.allNineLocalRuntimeRulesCompiled,
                evidence.compiledTransparentDefinitions,
                evidence.failingDeclaration,
                evidence.effectiveComparisonStepLimit,
                evidence.comparisonStepLimitExceeded,
                evidence.comparisonStepsBeforeMismatch
            ],
            [
                'ef761e4',
                '8cdff35',
                true,
                [
                    'pathout_motive_transport_obj',
                    'pathout_motive_transport_arrow',
                    'PathIndSrc_catd'
                ],
                'PathIndSrc_transport_func',
                512,
                false,
                360
            ]
        );
    });

    it('adds one support rule to make exactly 4/10/0/10', () => {
        const implementation =
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8.exactImplementation;
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
            [4, 10, 0, 10, '4/10/0/10', 5, 5]
        );
        assert.deepEqual(
            implementation.runtimeRules.map(rule => rule.order),
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
        );
    });

    it('selects only the complete-parent source-fibre bridge', () => {
        const fusion = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8
            .dependencyClosure
            .pathInductionSourceFibrePresentationFusion;
        assert.deepEqual(
            [
                fusion.ruleId,
                fusion.left,
                fusion.right,
                fusion.exactCompleteParentPairSelected,
                fusion.sourceFibrePresentationOnly,
                fusion.activeMathematicalRuleDelta,
                fusion.derivedSupportRuleDelta,
                fusion.proofRuleDelta
            ],
            [
                'pathind.internalized.' +
                    'path-ind-source-fibre-at-sigma-pair-' +
                    'presentation-fusion',
                'Fibre_cat(PathIndSrc_catd(Z),Struct_sigma(x,E))',
                'Fibre_cat(E,pathout_refl_obj(Z,x))',
                true,
                true,
                0,
                1,
                0
            ]
        );
        assert.deepEqual(
            [
                fusion.underlyingCategoryEqualityAuthorized,
                fusion.genericSigmaFibreRuleAuthorized,
                fusion.genericComparisonChangeAuthorized,
                fusion.genericDeclarationProofIntegrationAuthorized
            ],
            [false, false, false, false]
        );
    });

    it('preserves consumers, observations, negatives, and oracle scope', () => {
        const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V8;
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
            'PATHIND_INTERNALIZED_V8_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_V8_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V8_AUTHORIZATION_DRIFT'
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
                /pathind_internalized_proposal_v8/u,
                path
            );
        }
    });
});
