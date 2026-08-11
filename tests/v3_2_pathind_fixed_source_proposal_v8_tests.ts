/**
 * Focused tests for corrected PATHIND-TRUSTED-PROFILE-1C proposal v8.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V8,
    CorePathindFixedSource1cProposalV8,
    CorePathindFixedSource1cProposalV8Error,
    validateCorePathindFixedSource1cProposalV8
} from '../src/v3_2/pathind_fixed_source_proposal_v8';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cProposalV8 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V8
    )) as CorePathindFixedSource1cProposalV8;

const assertProposalError = (
    mutate: (proposal: CorePathindFixedSource1cProposalV8) => void,
    expected: CorePathindFixedSource1cProposalV8Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindFixedSource1cProposalV8(proposal),
        error =>
            error instanceof CorePathindFixedSource1cProposalV8Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected proposal v8', () => {
    it('preserves v7 and pins the shadowing trace', () => {
        const proposal = validateCorePathindFixedSource1cProposalV8();
        assert.equal(Object.isFrozen(proposal), true);
        assert.deepEqual(
            [
                proposal.parent.supersededProposalRevision,
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                proposal.parent.counterevidence.compiledRuntimeRuleCount,
                proposal.parent.counterevidence.predecessorRuleAppliedFirst,
                proposal.parent.counterevidence.v7PreDeltaFusionMatched,
                proposal.parent.counterevidence
                    .v7PreDeltaFusionShadowedByEarlierFragment,
                proposal.parent.counterevidence
                    .diagnosticWrapperRemovedCompletely,
                proposal.parent.counterevidence.genericCheckerDiffEmpty
            ],
            [
                'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-7',
                'f0fd4a6',
                '0cefb73',
                12,
                'categorical.mixed-action.functor-classifier-definition',
                false,
                true,
                true,
                true
            ]
        );
    });

    it('replaces rule five without widening 5/12/0/6', () => {
        const implementation =
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V8.exactImplementation;
        const fusion = implementation.runtimeRules[5] as {
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
                5, 12, 0, 6, '5/12/0/6',
                'pathind.fixed-source.' +
                    'fixed-evaluation-post-delta-presentation-fusion',
                'τ', 'τ',
                'runtime-rewrite-derived-post-delta-type-fusion'
            ]
        );
        assert.deepEqual(
            implementation.runtimeRules.map(rule => rule.order),
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
        );
        assert.deepEqual(
            fusion.derivedFromAuthorityLines,
            [3316, 3317, 5457, 19067, 19068, 19069, 19072]
        );
    });

    it('pins the stable decoded form and retains global distinctions', () => {
        const fusion = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V8
            .dependencyClosure.fixedEvaluationSourcePresentationFusion;
        assert.deepEqual(
            [
                fusion.exactLeft,
                fusion.exactRight,
                fusion.replacesUnreachableV7PreDeltaFusion,
                fusion
                    .wrapsStablePostDeltaPresentationUnderDecodedObjectClassifier,
                fusion.subjectCheckRequiredBeforeImplementationCheckpoint,
                fusion.directRuntimeFunctorCategoryCollapseAuthorized,
                fusion.genericDeclarationProofIntegrationAuthorized,
                fusion.genericCheckerChangeAuthorized,
                fusion.newMathematicalRule
            ],
            [
                'τ(Obj(Functor_cat(Functor_cat(K,Cat_cat),Cat_cat)))',
                'τ(Obj(Functor_cat(Catd_cat(K),Cat_cat)))',
                true, true, true, false, false, false, false
            ]
        );
    });

    it('keeps consumer and oracle scope unchanged', () => {
        const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V8;
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
                    v7PreDeltaFusionMatched: boolean;
                }).v7PreDeltaFusionMatched = true;
            },
            'PATHIND_FIXED_SOURCE_V8_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.exactImplementation as {
                    exactBoundary: string;
                }).exactBoundary = '5/13/0/6';
            },
            'PATHIND_FIXED_SOURCE_V8_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_V8_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_proposal_v8/u,
                path
            );
        }
    });
});
