/**
 * Focused DIRECTED-GRADUATE-1 tests for the H-DTTLF-03 review boundary.
 */

import assert from 'node:assert/strict';
import {
    createHash
} from 'node:crypto';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_DIRECTED_GRADUATION_MANIFEST,
    CORE_DIRECTED_GRADUATION_RECOMMENDATION,
    CORE_MVP_MANIFEST,
    CoreDirectedGraduationProposalError,
    validateCoreDirectedGraduationManifest,
    validateCoreDirectedGraduationRecommendation
} from '../src/v3_2';

const clone = <T>(value: T): any =>
    JSON.parse(JSON.stringify(value));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const runtimeIds = [
    'directed.category-object.decode',
    'directed.displayed-family.decode',
    'directed.displayed-functor.decode',
    'directed.category-hom.decode',
    'directed.sigma-object.decode',
    'directed.sigma-first-projection.evaluate',
    'directed.sigma-telescope-fibre.evaluate',
    'projection.functor-hom.evaluate',
    'projection.transfor-component.evaluate',
    'projection.transfor-hom.evaluate'
] as const;

describe('TypeScript v3.2 DIRECTED-GRADUATE-1 proposal', () => {
    it('freezes the full 29-signature dependency closure', () => {
        const manifest = CORE_DIRECTED_GRADUATION_MANIFEST;
        assert.equal(
            manifest.revision,
            'emdash-v3.2-dttlf-directed-1'
        );
        assert.equal(
            manifest.status,
            'proposal-awaiting-h-dttlf-03'
        );
        assert.equal(manifest.baseOwnerSignatures.length, 20);
        assert.equal(manifest.candidateDeclarations.length, 9);
        assert.equal(
            manifest.composition.totalOwnerSignatureCount,
            29
        );
        assert.deepEqual(
            manifest.baseOwnerSignatures
                .filter(entry =>
                    entry.source === 'continuation-base-signature'
                )
                .map(entry => entry.owner),
            [
                'category-of-categories',
                'displayed-category-category',
                'constant-displayed-family',
                'section-category'
            ]
        );
        assert.equal(
            manifest.baseOwnerSignatures.filter(entry =>
                entry.source === 'frozen-mvp-signature'
            ).length,
            16
        );
    });

    it('pins the exact nine reviewed candidate declarations', () => {
        const declarations =
            CORE_DIRECTED_GRADUATION_MANIFEST.candidateDeclarations;
        assert.deepEqual(
            declarations.map(entry => entry.owner),
            [
                'displayed-functor-category',
                'sigma-category',
                'sigma-telescope-family',
                'decoded-dependent-pair',
                'dependent-pair',
                'sigma-first-projection',
                'sigma-transport-arrow',
                'sigma-telescope-transport',
                'section-object-evaluation'
            ]
        );
        assert.deepEqual(
            declarations.map(entry => entry.candidateDisposition),
            [
                'opaque-import',
                'opaque-import',
                'opaque-import',
                'opaque-import',
                'opaque-import',
                'opaque-import',
                'opaque-import',
                'transparent-checked-definition',
                'opaque-import'
            ]
        );
        assert.equal(
            declarations.filter(entry =>
                entry.bodyPolicy ===
                    'exact-checked-transparent-mirror'
            ).length,
            1
        );
        assert.equal(
            declarations.at(-1)?.coreName,
            'dttlf_piapp0'
        );
    });

    it('pins seven directed then three inherited MVP runtime rules', () => {
        const manifest = CORE_DIRECTED_GRADUATION_MANIFEST;
        assert.deepEqual(
            manifest.runtimeRules.map(entry => entry.id),
            runtimeIds
        );
        assert.deepEqual(
            manifest.runtimeRules.map(entry => entry.executionPhase),
            [
                ...Array(7).fill('catalog-runtime'),
                ...Array(3).fill('frozen-mvp-runtime')
            ]
        );
        assert.equal(manifest.runtimeRules.length, 10);
        assert.deepEqual(manifest.proofTimeRules, []);
        assert.equal(
            manifest.composition.runtimeOrder,
            'catalog-seven-before-frozen-mvp-three'
        );
        assert.equal(
            manifest.composition.oneSharedOuterLfBudget,
            true
        );
    });

    it('records the reviewed outer LF and preserves the deployed MVP', () => {
        const manifest = CORE_DIRECTED_GRADUATION_MANIFEST;
        assert.deepEqual(manifest.outerLf.transitionOrder, [
            'zonk',
            'beta',
            'delta',
            'reviewed-runtime'
        ]);
        assert.equal(manifest.outerLf.comparisonStepLimit, 256);
        assert.equal(manifest.outerLf.eta, 'disabled');
        assert.equal(
            manifest.outerLf.arbitraryUserRules,
            'excluded'
        );
        assert.deepEqual(manifest.preservedMvp, {
            revision: CORE_MVP_MANIFEST.revision,
            contentHash: CORE_MVP_MANIFEST.contentHash,
            ownerIds: CORE_MVP_MANIFEST.owners.map(entry => entry.owner),
            runtimeRuleIds: CORE_MVP_MANIFEST.rules.map(rule => rule.id),
            mutation: false
        });
    });

    it('has a fresh reproducible content hash', () => {
        const {
            contentHash,
            ...content
        } = CORE_DIRECTED_GRADUATION_MANIFEST;
        const recomputed = 'sha256:' + createHash('sha256')
            .update(JSON.stringify(content))
            .digest('hex');
        assert.equal(contentHash, recomputed);
        assert.notEqual(contentHash, CORE_MVP_MANIFEST.contentHash);
    });

    it('recommends only an opt-in continuation authority boundary', () => {
        const boundary =
            CORE_DIRECTED_GRADUATION_RECOMMENDATION.productBoundary;
        assert.equal(
            boundary.recommendation,
            'approve-authoritative-opt-in-continuation-kernel'
        );
        assert.equal(boundary.scope, 'exact-combined-profile-only');
        assert.equal(boundary.entryPoint, 'src/v3_2/index.ts');
        assert.equal(boundary.browserEntryPoint, 'excluded');
        assert.equal(boundary.deployedMvpProfile, 'unchanged');
        assert.equal(boundary.releaseReady, false);
        assert.equal(
            boundary.lambdapiProductionRuntimeDependency,
            false
        );
        assert.equal(
            CORE_DIRECTED_GRADUATION_RECOMMENDATION
                .authorityAuthorized,
            false
        );
    });

    it('retains the exact Lambdapi oracle and change-review policy', () => {
        const policy =
            CORE_DIRECTED_GRADUATION_RECOMMENDATION.lambdapiPolicy;
        assert.equal(policy.mathematicalSpecification, 'active');
        assert.equal(policy.fixedGraduationCorpus, 'required');
        assert.equal(policy.positiveAndNegativeOracle, 'required');
        assert.equal(policy.subjectReductionOracle, 'required');
        assert.equal(
            policy.selectedChangeAcceptanceAuthority,
            'retained'
        );
        assert.equal(policy.perTermRuntimeCheck, 'not-required');
        assert.deepEqual(policy.acceptanceTriggers, [
            'combined-base-or-candidate-owner-signature-change',
            'combined-runtime-rule-shape-order-or-authority-change',
            'outer-lf-transition-transparency-or-budget-change',
            'browser-release-or-deployed-profile-promotion',
            'termination-confluence-subject-reduction-or-performance-claim-change',
            'graduation-corpus-or-lambdapi-binding-change'
        ]);
    });

    it('withholds every unsupported combined claim', () => {
        const proposal = CORE_DIRECTED_GRADUATION_RECOMMENDATION;
        assert.deepEqual(proposal.claimBoundary, {
            deterministicBoundedChecking: 'implemented-exact-profile',
            boundedStopping: 'implemented',
            inheritedMvpThreeRuleTermination:
                'preserved-for-subprogram-only',
            combinedTermination: 'withheld',
            unrestrictedNormalization: 'withheld',
            confluence: 'withheld',
            typescriptSubjectReduction: 'withheld',
            performanceSla: 'withheld',
            additionalOwnerOrRuleAuthority: false
        });
        assert.equal(proposal.residualRisks.length, 6);
        assert.equal(proposal.explicitDeferrals.length, 7);
        assert.equal(
            proposal.nonEffects.includes(
                'does not authorize H-DTTLF-03 by construction'
            ),
            true
        );
    });

    it('binds the combined consumer and a self-contained H-DTTLF-03 question', () => {
        const proposal = CORE_DIRECTED_GRADUATION_RECOMMENDATION;
        assert.deepEqual(proposal.evidence.combinedTrace, [
            'beta',
            'directed.sigma-telescope-fibre.evaluate'
        ]);
        assert.equal(
            proposal.evidence.typescriptNegativeFamilyOrPairCount,
            2
        );
        assert.equal(
            proposal.evidence.generatedLambdapiNegativeCount,
            1
        );
        assert.match(
            proposal.decisionQuestion,
            /Approve H-DTTLF-03\/D-DTTLF-001 as proposed/
        );
        assert.match(
            proposal.decisionQuestion,
            /29 total/
        );
        assert.match(
            proposal.decisionQuestion,
            /10 total/
        );
        assert.match(
            proposal.decisionQuestion,
            /withhold unrestricted normalization/
        );
    });

    it('stays outside the browser and leaves the MVP identity exact', () => {
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /directed_graduation|DIRECTED_GRADUATE|DTTLF_DIRECTED/
        );
        assert.equal(CORE_MVP_MANIFEST.revision, 'emdash-v3.2-mvp-1');
        assert.equal(
            CORE_MVP_MANIFEST.contentHash,
            'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0'
        );
    });

    it('is deeply frozen and rejects manifest, hash, or authority drift', () => {
        assertDeepFrozen(CORE_DIRECTED_GRADUATION_MANIFEST);
        assertDeepFrozen(CORE_DIRECTED_GRADUATION_RECOMMENDATION);
        assert.doesNotThrow(() =>
            validateCoreDirectedGraduationManifest()
        );
        assert.doesNotThrow(() =>
            validateCoreDirectedGraduationRecommendation()
        );

        const manifest = clone(CORE_DIRECTED_GRADUATION_MANIFEST);
        manifest.candidateDeclarations.pop();
        assert.throws(
            () => validateCoreDirectedGraduationManifest(manifest),
            error =>
                error instanceof CoreDirectedGraduationProposalError &&
                error.code === 'GRADUATION_MANIFEST_DRIFT'
        );

        const hash = clone(CORE_DIRECTED_GRADUATION_MANIFEST);
        hash.contentHash = 'sha256:wrong';
        assert.throws(
            () => validateCoreDirectedGraduationManifest(hash),
            error =>
                error instanceof CoreDirectedGraduationProposalError &&
                error.code === 'GRADUATION_HASH_DRIFT'
        );

        const authority = clone(
            CORE_DIRECTED_GRADUATION_RECOMMENDATION
        );
        authority.authorityAuthorized = true;
        assert.throws(
            () => validateCoreDirectedGraduationRecommendation(authority),
            error =>
                error instanceof CoreDirectedGraduationProposalError &&
                error.code === 'GRADUATION_RECOMMENDATION_DRIFT'
        );

        const browser = clone(
            CORE_DIRECTED_GRADUATION_RECOMMENDATION
        );
        browser.productBoundary.browserEntryPoint =
            'src/v3_2/browser.ts';
        assert.throws(
            () => validateCoreDirectedGraduationRecommendation(browser),
            error =>
                error instanceof CoreDirectedGraduationProposalError &&
                error.code === 'GRADUATION_RECOMMENDATION_DRIFT'
        );
    });
});
