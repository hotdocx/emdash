/**
 * Focused tests for corrected, non-authorizing PathOut transitivity v3.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2
} from '../src/v3_2/pathout_transitivity_proposal_v2';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2
} from '../src/v3_2/pathout_transitivity_review_v2';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3,
    CorePathoutTransitivity1eProposalV3,
    CorePathoutTransitivity1eProposalV3Error,
    cloneCorePathoutTransitivity1eProposalV3,
    validateCorePathoutTransitivity1eProposalV3
} from '../src/v3_2/pathout_transitivity_proposal_v3';

const repositoryRoot = resolve(__dirname, '..');

const assertProposalError = (
    mutate: (proposal: CorePathoutTransitivity1eProposalV3) => void,
    expected: CorePathoutTransitivity1eProposalV3Error['code']
): void => {
    const proposal = cloneCorePathoutTransitivity1eProposalV3();
    mutate(proposal);
    assert.throws(
        () => validateCorePathoutTransitivity1eProposalV3(proposal),
        error =>
            error instanceof CorePathoutTransitivity1eProposalV3Error &&
            error.code === expected
    );
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

describe('PATHOUT-LIBRARY-TRANSITIVITY-1E corrected proposal v3', () => {
    it('pins and supersedes the exact reviewed v2 boundary', () => {
        const proposal = validateCorePathoutTransitivity1eProposalV3();
        assertDeepFrozen(proposal);
        assert.deepEqual(
            [
                proposal.parent.supersededProposalRevision,
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededProposalSha256,
                proposal.parent.supersededReviewRevision,
                proposal.parent.supersededReviewCheckpoint,
                proposal.parent.supersededReviewSha256,
                proposal.parent.supersededLedgerCheckpoint
            ],
            [
                CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2.revision,
                'b1e6f0f',
                '139dbc75984f229e879ac93ee01e2dafc' +
                    '8b39982ca19f5ea9120836b0f9c2b1c',
                CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V2.revision,
                '31f23db',
                'b24b2e0dfd77b541b52b7eb6f1388a0' +
                    '45f01ed7f08c2f9b6b137da57bb2a4d0a',
                '8668764'
            ]
        );
    });

    it('records the exact reviewed-v2 cold counterevidence', () => {
        const evidence = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3
            .parent.counterevidence;
        assert.deepEqual(
            [
                evidence.coldFocusedGate,
                evidence.allFiveTransparentDefinitionsAdmitted,
                evidence.v2LocalRuntimeRuleSubjectChecked,
                evidence.v2LocalRuntimeRuleFiredAtExactInstantiatedRedex,
                evidence.bothTypedConsumersAccepted,
                evidence.allEightNegativeConsumersRejected,
                evidence.failureCount,
                evidence.genericCompilerDiffEmpty
            ],
            [
                '9-tests-6-pass-2-fail-1-skip',
                true,
                true,
                true,
                true,
                true,
                2,
                true
            ]
        );
        assert.equal(
            evidence.inheritedProofAdapterResidual.errorCode,
            'UNBOUND_FREE_REFERENCE'
        );
        assert.equal(
            evidence.sectionComponentResidual
                .compTargetDeltaFiredBeforeLocalRuleConsulted,
            true
        );
        assert.equal(
            evidence.sectionComponentResidual
                .postDeltaCompleteParentReplacementRequired,
            true
        );
        assert.equal(
            evidence.sectionComponentResidual.additionalRuntimeRuleRequired,
            false
        );
    });

    it('replaces the pre-delta rule one-for-one at 0/1/0/5', () => {
        const implementation = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3
            .exactImplementation;
        const rule = implementation.runtimeRules[0];
        assert.deepEqual(
            [
                implementation.exactBoundary,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.semanticCountDeltaFromV2,
                implementation.v2PreDeltaSupportRetained,
                implementation.v3PostDeltaSupportSelected,
                rule?.id,
                rule?.replaces,
                rule?.stableAfterCompTargetDelta,
                rule?.completeParentOnly,
                rule?.mustSubjectCheck
            ],
            [
                '0/1/0/5',
                1,
                0,
                5,
                0,
                false,
                true,
                CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
                CORE_PATHOUT_TRANSITIVITY_1E_LOCAL_SUPPORT_RULE_ID,
                true,
                true,
                true
            ]
        );
        assert.doesNotMatch(
            rule?.left ?? '',
            /CompTarget_catd/u
        );
        assert.match(rule?.left ?? '', /hom_con/u);
    });

    it('retains inherited proof reuse with explicit descendant scope', () => {
        const implementation = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3
            .exactImplementation;
        assert.equal(implementation.localProofRuleCount, 0);
        assert.equal(implementation.inheritedProofProviderCount, 1);
        assert.equal(
            implementation.inheritedProofProviders[0]?.id,
            'stress.sigma-pi.uncurrying'
        );
        assert.equal(
            implementation
                .inheritedProofHelperAcceptsExplicitDescendantEnvironment,
            true
        );
        assert.equal(
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3.profileSealing
                .genericPiToFunctordRuntimeCollapseAuthorized,
            false
        );
    });

    it('preserves definitions, consumers, negatives, and oracle exactly',
        () => {
            const proposal = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3;
            assert.deepEqual(
                proposal.exactImplementation.transparentDefinitions,
                CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2
                    .exactImplementation.transparentDefinitions
            );
            assert.deepEqual(
                proposal.requiredExistingProviders,
                CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2
                    .requiredExistingProviders
            );
            assert.deepEqual(
                proposal.typedLibraryConsumers,
                CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2
                    .typedLibraryConsumers
            );
            assert.deepEqual(
                proposal.negativeConsumers,
                CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2.negativeConsumers
            );
            assert.deepEqual(
                proposal.boundedOracle,
                CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V2.boundedOracle
            );
        });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent as {
                    supersededLedgerCheckpoint: string;
                }).supersededLedgerCheckpoint = 'wrong';
            },
            'PATHOUT_TRANSITIVITY_PROPOSAL_V3_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.exactImplementation as {
                    v2PreDeltaSupportRetained: boolean;
                }).v2PreDeltaSupportRetained = true;
            },
            'PATHOUT_TRANSITIVITY_PROPOSAL_V3_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHOUT_TRANSITIVITY_PROPOSAL_V3_AUTHORIZATION_DRIFT'
        );
    });

    it('remains root-only, non-public, and non-authorizing', () => {
        const proposal = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3;
        assert.equal(proposal.decision.implementationAuthorized, false);
        assert.equal(
            proposal.profileSealing.browserOrPublicPackageExportAuthorized,
            false
        );
        for (const relative of [
            'src/v3_2/index.ts',
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/browser.ts'
        ]) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, relative), 'utf8'),
                /pathout_transitivity_proposal_v3/u,
                relative
            );
        }
    });
});
