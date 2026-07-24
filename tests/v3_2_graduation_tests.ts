/**
 * Focused GRADUATE-1A tests for the H-05 recommendation boundary.
 */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CORE_MVP_DIFFERENTIAL_COMPLETION,
    CORE_MVP_GRADUATION_RECOMMENDATION,
    CORE_MVP_MANIFEST,
    CORE_RUNTIME_H04_REVIEW,
    LEGACY_MIGRATION_COMPLETION,
    CoreMvpGraduationError,
    CoreMvpGraduationRecommendationInput,
    validateCoreMvpGraduationRecommendation
} from '../src/v3_2';

const cloneRecommendation = (): CoreMvpGraduationRecommendationInput =>
    JSON.parse(JSON.stringify(CORE_MVP_GRADUATION_RECOMMENDATION));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    for (const child of Object.values(value as Record<string, unknown>)) {
        assertDeepFrozen(child);
    }
};

const expectRecommendationError = (
    mutate: (recommendation: any) => void
): CoreMvpGraduationError => {
    const recommendation = cloneRecommendation() as any;
    mutate(recommendation);
    try {
        validateCoreMvpGraduationRecommendation(recommendation);
    } catch (error) {
        assert.ok(error instanceof CoreMvpGraduationError);
        assert.equal(error.code, 'GRADUATION_RECOMMENDATION_MISMATCH');
        return error;
    }
    assert.fail('Expected GRADUATION_RECOMMENDATION_MISMATCH');
};

describe('TypeScript v3.2 GRADUATE-1A recommendation', () => {
    it('proposes only the exact H-03-reviewed deployed profile', () => {
        const proposal = CORE_MVP_GRADUATION_RECOMMENDATION;
        assert.equal(proposal.revision, 'GRADUATE-1A');
        assert.equal(proposal.status, 'proposed-awaiting-h05');
        assert.equal(proposal.reviewGate, 'H-05');
        assert.equal(proposal.decisionId, 'D-039');
        assert.equal(
            proposal.productAuthority.recommendation,
            'approve-typescript-as-authoritative-deployed-mvp-kernel'
        );
        assert.equal(
            proposal.productAuthority.manifestRevision,
            CORE_MVP_MANIFEST.revision
        );
        assert.equal(
            proposal.productAuthority.manifestContentHash,
            CORE_MVP_MANIFEST.contentHash
        );
        assert.deepEqual(
            proposal.productAuthority.ownerIds,
            CORE_MVP_MANIFEST.owners.map(entry => entry.owner)
        );
        assert.deepEqual(
            proposal.productAuthority.runtimeRuleIds,
            CORE_MVP_MANIFEST.rules.map(rule => rule.id)
        );
        assert.equal(
            proposal.productAuthority.lambdapiProductionRuntimeDependency,
            false
        );
        assert.equal(proposal.authorityAuthorized, false);
    });

    it('retains Lambdapi for the precise unresolved authority roles', () => {
        const policy =
            CORE_MVP_GRADUATION_RECOMMENDATION.lambdapiPolicy;
        assert.equal(
            policy.recommendation,
            'retain-as-selected-change-acceptance-authority'
        );
        assert.equal(policy.mathematicalSpecification, 'active');
        assert.equal(policy.frozenCorpusCiOracle, 'required');
        assert.equal(policy.subjectReductionOracle, 'required');
        assert.equal(policy.perTermProductionCheck, 'not-required');
        assert.deepEqual(policy.acceptanceTriggers, [
            'selected-owner-signature-change',
            'selected-runtime-rule-shape-or-authority-change',
            'owner-or-rule-promotion-into-product-profile',
            'termination-confluence-or-subject-reduction-claim-change',
            'shared-corpus-backend-binding-change'
        ]);
        assert.deepEqual(policy.changesNotRequiringNewAuthorityReview, [
            'implementation-refactor-preserving-frozen-profile',
            'surface-or-diagnostic-change-preserving-core-boundary',
            'packaging-change-preserving-browser-import-boundary'
        ]);
    });

    it('preserves the exact H-04 claim boundary', () => {
        const boundary =
            CORE_MVP_GRADUATION_RECOMMENDATION.claimBoundary;
        assert.equal(
            boundary.termination,
            CORE_RUNTIME_H04_REVIEW.authorization.termination
        );
        assert.equal(
            boundary.deterministicBoundedEvaluationAndComparison,
            CORE_RUNTIME_H04_REVIEW.authorization
                .deterministicBoundedEvaluationAndComparison
        );
        assert.equal(
            boundary.trustedRuntimeRules,
            CORE_RUNTIME_H04_REVIEW.authorization.trustedRuntimeRules
        );
        assert.equal(boundary.generalConfluence, 'withheld');
        assert.equal(boundary.typescriptSubjectReduction, 'withheld');
        assert.equal(boundary.additionalRuntimeRulesAuthorized, false);
    });

    it('binds parity, deletion, operations, and maintenance evidence', () => {
        const proposal = CORE_MVP_GRADUATION_RECOMMENDATION;
        assert.equal(
            proposal.evidence.parityStatus,
            CORE_MVP_DIFFERENTIAL_COMPLETION.status
        );
        assert.equal(
            proposal.evidence.ownerCaseCount,
            CORE_MVP_DIFFERENTIAL_COMPLETION.ownerCases.length
        );
        assert.equal(
            proposal.evidence.runtimeRuleCaseCount,
            CORE_MVP_DIFFERENTIAL_COMPLETION.ruleCases.length
        );
        assert.equal(
            proposal.evidence.higherCellPackageCount,
            CORE_MVP_DIFFERENTIAL_COMPLETION.higherCellCases.length
        );
        assert.equal(
            proposal.evidence.unclosedParityRows,
            CORE_MVP_DIFFERENTIAL_COMPLETION.unclosedRows.length
        );
        assert.equal(
            proposal.evidence.deletedLegacyTargetCount,
            LEGACY_MIGRATION_COMPLETION.deletedFiles.length
        );
        assert.equal(
            proposal.maintenanceBoundary.legacyTargetsRemoved,
            LEGACY_MIGRATION_COMPLETION.deletedFiles.length
        );
        assert.equal(
            proposal.performanceBoundary.checkerComparisonStepLimit,
            256
        );
        assert.equal(
            proposal.performanceBoundary.performanceClaim,
            'no-latency-throughput-or-scale-sla'
        );
        assert.equal(
            proposal.evidence.validationGates.includes(
                'shared-fragment-lambdapi-differential-probes'
            ),
            true
        );
    });

    it('defers release polish without treating it as semantic graduation', () => {
        const proposal = CORE_MVP_GRADUATION_RECOMMENDATION;
        assert.deepEqual(proposal.releaseFollowUps, [{
            id: 'C-18',
            disposition:
                'complete-backend-diagnostic-remapping-at-release-ready',
            blocksGraduation: false
        }, {
            id: 'PERFORMANCE-BASELINE',
            disposition: 'required-before-any-performance-sla',
            blocksGraduation: false
        }, {
            id: 'RELEASE-POLICY-SYNC',
            disposition:
                'synchronize-docs-manifests-examples-and-residual-oracle-policy',
            blocksGraduation: false
        }]);
        assert.equal(
            proposal.nonEffects.includes(
                'does-not-complete-release-ready'
            ),
            true
        );
        assert.equal(
            proposal.nonEffects.includes(
                'does-not-trigger-h02-or-h06'
            ),
            true
        );
    });

    it('publishes one self-contained yes-or-revise H-05 question', () => {
        assert.match(
            CORE_MVP_GRADUATION_RECOMMENDATION.decisionQuestion,
            /Approve H-05\/D-039 as proposed/
        );
        assert.match(
            CORE_MVP_GRADUATION_RECOMMENDATION.decisionQuestion,
            /16 owners and 3 runtime rules/
        );
        assert.match(
            CORE_MVP_GRADUATION_RECOMMENDATION.decisionQuestion,
            /acceptance authority/
        );
    });

    it('is deeply frozen and rejects scope, policy, or claim drift', () => {
        assertDeepFrozen(CORE_MVP_GRADUATION_RECOMMENDATION);
        assert.doesNotThrow(() =>
            validateCoreMvpGraduationRecommendation(
                CORE_MVP_GRADUATION_RECOMMENDATION
            )
        );

        assert.match(
            expectRecommendationError(recommendation => {
                recommendation.productAuthority.ownerIds.pop();
            }).message,
            /H-05 review input/
        );
        assert.match(
            expectRecommendationError(recommendation => {
                recommendation.lambdapiPolicy.recommendation =
                    'ci-only';
            }).message,
            /H-05 review input/
        );
        assert.match(
            expectRecommendationError(recommendation => {
                recommendation.claimBoundary.generalConfluence =
                    'authorized';
            }).message,
            /H-05 review input/
        );
        assert.match(
            expectRecommendationError(recommendation => {
                recommendation.authorityAuthorized = true;
            }).message,
            /H-05 review input/
        );
    });
});
