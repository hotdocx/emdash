/**
 * Focused tests for corrected, non-authorizing PathOut transitivity v4.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3
} from '../src/v3_2/pathout_transitivity_proposal_v3';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3
} from '../src/v3_2/pathout_transitivity_review_v3';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID,
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4,
    CorePathoutTransitivity1eProposalV4,
    CorePathoutTransitivity1eProposalV4Error,
    cloneCorePathoutTransitivity1eProposalV4,
    validateCorePathoutTransitivity1eProposalV4
} from '../src/v3_2/pathout_transitivity_proposal_v4';

const repositoryRoot = resolve(__dirname, '..');

const assertProposalError = (
    mutate: (proposal: CorePathoutTransitivity1eProposalV4) => void,
    expected: CorePathoutTransitivity1eProposalV4Error['code']
): void => {
    const proposal = cloneCorePathoutTransitivity1eProposalV4();
    mutate(proposal);
    assert.throws(
        () => validateCorePathoutTransitivity1eProposalV4(proposal),
        error =>
            error instanceof CorePathoutTransitivity1eProposalV4Error &&
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

describe('PATHOUT-LIBRARY-TRANSITIVITY-1E corrected proposal v4', () => {
    it('pins and supersedes the exact reviewed v3 boundary', () => {
        const proposal = validateCorePathoutTransitivity1eProposalV4();
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
                CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3.revision,
                'fe1a9b7',
                '0d7448ae68d9aa6ae3bf91b9010a676f' +
                    '8ca3c9101976e1de2c88816a94e68dd9',
                CORE_PATHOUT_TRANSITIVITY_1E_REVIEW_V3.revision,
                '0834d00',
                '064e36392e6e7962912237d4f0d1abc2' +
                    '7ae0184e1f0b6e94009ce1b7842664f6',
                '5d0dad5'
            ]
        );
    });

    it('records the exact reviewed-v3 cold counterevidence', () => {
        const evidence = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4
            .parent.counterevidence;
        assert.deepEqual(
            [
                evidence.coldFocusedGate,
                evidence.isolatedObservationGate,
                evidence.allFiveTransparentDefinitionsAdmitted,
                evidence.v3LocalRuntimeRuleSubjectChecked,
                evidence.v3LocalRuntimeRuleFiredAtExactInstantiatedRedex,
                evidence.inheritedProofCorrection.providerSolved,
                evidence.failureCount,
                evidence.genericCompilerDiffEmpty
            ],
            [
                '9-tests-6-pass-2-fail-1-skip',
                '1-test-0-pass-1-fail',
                true,
                true,
                true,
                true,
                2,
                true
            ]
        );
        assert.equal(
            evidence.sectionComponentResidual
                .representableFamilyDeltaFiredBeforeV3PatternMatch,
            true
        );
        assert.equal(
            evidence.sectionComponentResidual
                .originalConsumerParentReplacementRequired,
            true
        );
        assert.equal(
            evidence.predecessorTestLinkageResidual
                .semanticBoundaryChangeRequired,
            false
        );
    });

    it('replaces v3 one-for-one with the original consumer parent', () => {
        const implementation = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4
            .exactImplementation;
        const rule = implementation.runtimeRules[0];
        assert.deepEqual(
            [
                implementation.exactBoundary,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.semanticCountDeltaFromV3,
                implementation.v3PostDeltaSupportRetained,
                implementation.v4ConsumerParentSupportSelected,
                rule?.id,
                rule?.replaces,
                rule?.originalConsumerParent,
                rule?.consultedBeforeDescendantDelta,
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
                CORE_PATHOUT_TRANSITIVITY_1E_CONSUMER_PARENT_SUPPORT_RULE_ID,
                CORE_PATHOUT_TRANSITIVITY_1E_POST_DELTA_SUPPORT_RULE_ID,
                true,
                true,
                true,
                true
            ]
        );
        assert.match(rule?.left ?? '', /CompTarget_catd/u);
        assert.match(rule?.left ?? '', /path_comp_sec/u);
        assert.doesNotMatch(rule?.left ?? '', /hom_con/u);
    });

    it('retains inherited proof reuse and every semantic inventory', () => {
        const proposal = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4;
        assert.equal(proposal.exactImplementation.localProofRuleCount, 0);
        assert.equal(
            proposal.exactImplementation
                .inheritedProofHelperAcceptsExplicitDescendantEnvironment,
            true
        );
        assert.deepEqual(
            proposal.exactImplementation.transparentDefinitions,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3
                .exactImplementation.transparentDefinitions
        );
        assert.deepEqual(
            proposal.requiredExistingProviders,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3
                .requiredExistingProviders
        );
        assert.deepEqual(
            proposal.typedLibraryConsumers,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3.typedLibraryConsumers
        );
        assert.deepEqual(
            proposal.negativeConsumers,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3.negativeConsumers
        );
        assert.deepEqual(
            proposal.boundedOracle,
            CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V3.boundedOracle
        );
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent as {
                    supersededLedgerCheckpoint: string;
                }).supersededLedgerCheckpoint = 'wrong';
            },
            'PATHOUT_TRANSITIVITY_PROPOSAL_V4_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.exactImplementation as {
                    v3PostDeltaSupportRetained: boolean;
                }).v3PostDeltaSupportRetained = true;
            },
            'PATHOUT_TRANSITIVITY_PROPOSAL_V4_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHOUT_TRANSITIVITY_PROPOSAL_V4_AUTHORIZATION_DRIFT'
        );
    });

    it('remains root-only, non-public, and non-authorizing', () => {
        const proposal = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL_V4;
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
                /pathout_transitivity_proposal_v4/u,
                relative
            );
        }
    });
});
