/**
 * Focused corrected-v14 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14,
    CorePathindInternalized1dProposalV14,
    CorePathindInternalized1dProposalV14Error,
    validateCorePathindInternalized1dProposalV14
} from '../src/v3_2/pathind_internalized_proposal_v14';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV14 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14
    )) as CorePathindInternalized1dProposalV14;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV14) => void,
    expected: CorePathindInternalized1dProposalV14Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV14(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV14Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v14', () => {
    it('pins the exact v13 final target-fibre counterevidence', () => {
        const proposal = validateCorePathindInternalized1dProposalV14();
        assert.equal(Object.isFrozen(proposal), true);
        const evidence = proposal.parent.counterevidence;
        assert.deepEqual(
            [
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                evidence.pathoutPiTransportCompiled,
                evidence.compiledDerivedTransparentDefinitionCount,
                evidence.failingDeclaration,
                evidence.comparisonSteps,
                evidence.comparisonMismatchCodes,
                evidence.primaryMismatchLeft,
                evidence.primaryMismatchRight
            ],
            [
                'd77f0d7',
                'a8aff88',
                true,
                6,
                'PathIndTgt_transport_func',
                [464, 472, 96],
                ['OWNER_MISMATCH', 'OWNER_MISMATCH', 'OWNER_MISMATCH'],
                'application:section-category',
                'application:functor-object'
            ]
        );
    });

    it('selects exactly 4/13/0/10 across the staged modules', () => {
        const implementation =
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14.exactImplementation;
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
                partition.suffixTransparentDefinitions.length,
                partition.semanticCountDelta
            ],
            [4, 13, 0, 10, '4/13/0/10', 5, 8, 9, 4, 3, 4, 1]
        );
    });

    it('selects only the staged total-target fibre parent', () => {
        const fusion = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14
            .dependencyClosure.pathInductionTargetFibreStagedParentFusion;
        assert.deepEqual(
            [fusion.ruleId, fusion.left, fusion.right],
            [
                'pathind.internalized.' +
                    'path-ind-target-fibre-at-sigma-pair-' +
                    'presentation-fusion',
                'Fibre_cat(PathIndTgt_catd(Z),Struct_sigma(x,E))',
                'Pi_cat(PathOut_cat(Z,x),E)'
            ]
        );
        assert.deepEqual(
            [
                fusion.pathIndTgtDeclaredByPreludeBeforeRuleCompilation,
                fusion.sourceAndTargetFinalAliasFibresCoveredByOneRule,
                fusion.activeMathematicalRuleDelta,
                fusion.derivedSupportRuleDelta,
                fusion.proofRuleDelta,
                fusion.genericSigmaFibreRuleAuthorized
            ],
            [true, true, 0, 1, 0, false]
        );
    });

    it('preserves consumers, observations, negatives, and oracle scope', () => {
        const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V14;
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
                    pathoutPiTransportCompiled: boolean;
                }).pathoutPiTransportCompiled = false;
            },
            'PATHIND_INTERNALIZED_V14_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.stagedModulePartition
                        .extensionRuntimeRuleIds as unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_V14_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V14_AUTHORIZATION_DRIFT'
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
                /pathind_internalized_proposal_v14/u,
                path
            );
        }
    });
});
