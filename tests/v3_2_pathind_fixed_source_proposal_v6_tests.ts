/**
 * Focused tests for corrected PATHIND-TRUSTED-PROFILE-1C proposal v6.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6,
    CorePathindFixedSource1cProposalV6,
    CorePathindFixedSource1cProposalV6Error,
    validateCorePathindFixedSource1cProposalV6
} from '../src/v3_2/pathind_fixed_source_proposal_v6';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cProposalV6 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6
    )) as CorePathindFixedSource1cProposalV6;

const assertProposalError = (
    mutate: (proposal: CorePathindFixedSource1cProposalV6) => void,
    expected: CorePathindFixedSource1cProposalV6Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindFixedSource1cProposalV6(proposal),
        error =>
            error instanceof CorePathindFixedSource1cProposalV6Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected proposal v6', () => {
    it('preserves v5 and pins the exact measured residual', () => {
        const proposal = validateCorePathindFixedSource1cProposalV6();
        assert.equal(Object.isFrozen(proposal), true);
        assert.deepEqual(
            [
                proposal.parent.supersededProposalRevision,
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                proposal.parent.counterevidence.exactResidualLeft,
                proposal.parent.counterevidence.exactResidualRight,
                proposal.parent.counterevidence
                    .diagnosticCheckerHookRemovedCompletely
            ],
            [
                'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-5',
                '7219828',
                '3f95e7c',
                'Obj(fapp0(K,Cat_cat,FibCov_target_catd(K,E),x))',
                'Transf(K,Cat_cat,Rep_catd(K,x),E)',
                true
            ]
        );
    });

    it('adds only the exact residual fusion to make 5/11/0/6', () => {
        const implementation =
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6.exactImplementation;
        const fusion = implementation.runtimeRules[4] as {
            readonly id: string;
            readonly derivedFromAuthorityLines: readonly number[];
            readonly sourceOwner: string;
            readonly resultOwner: string;
            readonly policy: string;
        };
        assert.deepEqual(
            [
                implementation.trustedDeclarations.length,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.exactBoundary,
                fusion.id,
                fusion.sourceOwner,
                fusion.resultOwner,
                fusion.policy
            ],
            [
                5, 11, 0, 6, '5/11/0/6',
                'pathind.fixed-source.fib-cov-target-section-fusion',
                'Obj', 'Obj', 'runtime-rewrite-derived-head-fusion'
            ]
        );
        assert.deepEqual(
            implementation.runtimeRules.map(rule => rule.order),
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        );
        assert.deepEqual(
            fusion.derivedFromAuthorityLines,
            [
                5481, 7865, 8419, 9177, 13765,
                13767, 13773, 13775, 13923, 13928
            ]
        );
    });

    it('keeps the fusion forward, subject-checked, and engine-neutral', () => {
        const fusion = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6
            .dependencyClosure.fibreCovariantTargetSectionWeakHeadFusion;
        assert.deepEqual(
            [
                fusion.exactLeft,
                fusion.exactRight,
                fusion.subjectCheckedByGenericRuntimeCompiler,
                fusion.rightSidePreservesForwardTransfDeltaOrientation,
                fusion.newMathematicalRule,
                fusion.declarationUnfoldingEngineAuthorized,
                fusion.genericCheckerChangeAuthorized,
                fusion.alternateFibCovSignatureOrBodyAuthorized
            ],
            [
                'Obj(fapp0(K,Cat_cat,FibCov_target_catd(K,E),x))',
                'Obj(Transf_cat(K,Cat_cat,Rep_catd(K,x),E))',
                true, true, false, false, false, false
            ]
        );
    });

    it('keeps consumer and oracle scope unchanged', () => {
        const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V6;
        assert.deepEqual(
            [
                proposal.typedLibraryConsumer.count,
                proposal.negativeConsumers.length,
                proposal.selectedRuntimeObservations.length,
                proposal.boundedOracle.assertions.length
            ],
            [1, 8, 5, 9]
        );
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent.counterevidence as {
                    exactResidualLeft: string;
                }).exactResidualLeft = 'wrong';
            },
            'PATHIND_FIXED_SOURCE_V6_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.exactImplementation as {
                    exactBoundary: string;
                }).exactBoundary = '5/10/0/6';
            },
            'PATHIND_FIXED_SOURCE_V6_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_V6_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, or browser barrels', () => {
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
                /pathind_fixed_source_proposal_v6/u,
                path
            );
        }
    });
});
