/**
 * Focused reviewed-profile tests for H-DTTLF-03/D-DTTLF-001.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_DIRECTED_CONTINUATION_PROFILE,
    CORE_DIRECTED_GRADUATION_MANIFEST,
    CORE_DIRECTED_GRADUATION_RECOMMENDATION,
    CORE_DIRECTED_GRADUATION_REVIEW,
    CORE_MVP_RELEASE_POLICY,
    CoreDirectedContinuationProfileError,
    CoreDirectedContinuationProfileInput,
    CoreDirectedGraduationReviewError,
    CoreDirectedGraduationReviewInput,
    createCoreDirectedContinuationKernel,
    validateCoreDirectedContinuationProfile,
    validateCoreDirectedGraduationReview
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const repositoryRoot = resolve(__dirname, '..');

const readRepositoryFile = (path: string): string =>
    readFileSync(resolve(repositoryRoot, path), 'utf8');

const cloneReview = (): CoreDirectedGraduationReviewInput =>
    JSON.parse(JSON.stringify(CORE_DIRECTED_GRADUATION_REVIEW));

const cloneProfile = (): CoreDirectedContinuationProfileInput =>
    JSON.parse(JSON.stringify(CORE_DIRECTED_CONTINUATION_PROFILE));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const expectReviewError = (
    mutate: (review: any) => void,
    code: CoreDirectedGraduationReviewError['code']
): void => {
    const review = cloneReview() as any;
    mutate(review);
    assert.throws(
        () => validateCoreDirectedGraduationReview(review),
        error =>
            error instanceof CoreDirectedGraduationReviewError &&
            error.code === code
    );
};

const expectProfileError = (
    mutate: (profile: any) => void,
    code: CoreDirectedContinuationProfileError['code']
): void => {
    const profile = cloneProfile() as any;
    mutate(profile);
    assert.throws(
        () => validateCoreDirectedContinuationProfile(profile),
        error =>
            error instanceof CoreDirectedContinuationProfileError &&
            error.code === code
    );
};

describe('TypeScript v3.2 reviewed directed continuation profile', () => {
    it('records the exact H-DTTLF-03/D-DTTLF-001 approval separately', () => {
        const review = CORE_DIRECTED_GRADUATION_REVIEW;
        assert.equal(
            review.revision,
            'DIRECTED-GRADUATE-1-REVIEWED'
        );
        assert.equal(review.status, 'reviewed-approved');
        assert.deepEqual(review.approval, {
            gate: 'H-DTTLF-03',
            decisionId: 'D-DTTLF-001',
            decision: 'approved-as-proposed',
            reviewedOn: '2026-07-24',
            decisionEvidence:
                'Approve H-DTTLF-03/D-DTTLF-001 as proposed'
        });
        assert.notEqual(
            review.recommendation,
            CORE_DIRECTED_GRADUATION_RECOMMENDATION
        );
        assert.deepEqual(
            review.recommendation,
            CORE_DIRECTED_GRADUATION_RECOMMENDATION
        );
        assert.equal(review.recommendation.authorityAuthorized, false);
    });

    it('authorizes only the exact 29-signature and ten-rule opt-in profile', () => {
        const authorization =
            CORE_DIRECTED_GRADUATION_REVIEW.authorization;
        assert.equal(
            authorization.typescriptContinuationKernelAuthority,
            'authorized-exact-opt-in-combined-profile'
        );
        assert.equal(
            authorization.profileRevision,
            CORE_DIRECTED_GRADUATION_MANIFEST.revision
        );
        assert.equal(
            authorization.manifestContentHash,
            CORE_DIRECTED_GRADUATION_MANIFEST.contentHash
        );
        assert.equal(authorization.baseOwnerSignatureCount, 20);
        assert.equal(authorization.candidateDeclarationCount, 9);
        assert.equal(authorization.totalOwnerSignatureCount, 29);
        assert.equal(authorization.directedRuntimeRuleCount, 7);
        assert.equal(authorization.inheritedMvpRuntimeRuleCount, 3);
        assert.equal(authorization.totalRuntimeRuleCount, 10);
        assert.equal(authorization.proofTimeRuleCount, 0);
        assert.equal(
            authorization.factoryExport,
            'createCoreDirectedContinuationKernel'
        );
        assert.equal(authorization.browserEntryPoint, 'excluded');
        assert.equal(authorization.deployedMvpProfile, 'unchanged');
        assert.equal(authorization.releaseReady, false);
        assert.equal(
            authorization.lambdapiProductionRuntimeDependency,
            'forbidden'
        );
        assert.equal(
            authorization.additionalOwnersOrRulesAuthorized,
            false
        );
    });

    it('exposes one reviewed root-only checker/evaluator factory', () => {
        const profile = CORE_DIRECTED_CONTINUATION_PROFILE;
        const catalog = createCoreDirectedContinuationKernel();
        assert.equal(profile.status, 'authoritative-opt-in');
        assert.equal(profile.signatureClosure.totalCount, 29);
        assert.equal(profile.runtimeClosure.totalCount, 10);
        assert.equal(catalog.environment.declarations.length, 9);
        assert.equal(catalog.runtimeProgram.ruleIds.length, 7);
        assert.doesNotThrow(() =>
            catalog.createChecker().validateEnvironment()
        );
        assert.deepEqual(
            profile.runtimeClosure.ruleIds,
            CORE_DIRECTED_GRADUATION_MANIFEST.runtimeRules.map(
                entry => entry.id
            )
        );
    });

    it('makes the fixed oracle mandatory only in the continuation lane', () => {
        const packageJson = JSON.parse(
            readRepositoryFile('package.json')
        ) as {
            scripts: Record<string, string>;
        };
        const conformance =
            CORE_DIRECTED_CONTINUATION_PROFILE.conformance;
        assert.equal(
            packageJson.scripts['check:directed-conformance'],
            conformance.scriptBody
        );
        assert.equal(
            packageJson.scripts['check:continuation'],
            conformance.continuationGateBody
        );
        assert.equal(conformance.timeoutSeconds, 60);
        assert.equal(conformance.mandatoryForProfileChanges, true);
        assert.equal(
            conformance.mandatoryInFrozenMvpCheckAll,
            false
        );
        assert.equal(
            packageJson.scripts['check:conformance'],
            CORE_MVP_RELEASE_POLICY.conformance.scriptBody
        );
        assert.equal(
            packageJson.scripts['check:all'],
            CORE_MVP_RELEASE_POLICY.conformance.repositoryGateBody
        );
    });

    it('pins positive, negative, and subject-reduction corpus witnesses', () => {
        const corpus =
            CORE_DIRECTED_CONTINUATION_PROFILE.conformance.fixedCorpus;
        assert.deepEqual(corpus, {
            typescriptPositiveConsumerCount: 1,
            typescriptNegativeFamilyOrPairCount: 2,
            generatedLambdapiPositiveCount: 1,
            generatedLambdapiNegativeCount: 1,
            subjectReductionConversionWitnesses: [
                'outer-beta-section-evaluation',
                'sigma-telescope-fibre'
            ]
        });

        const source = readRepositoryFile(
            'tests/v3_2_directed_1c_tests.ts'
        );
        assert.match(
            source,
            /has the generated combined consumer accepted by Lambdapi/
        );
        assert.match(
            source,
            /has a mismatched section family rejected by Lambdapi/
        );
        assert.match(
            source,
            /composes outer beta with directed telescope-fibre computation/
        );
        assert.match(
            source,
            /types section evaluation at the raw and computed telescope fibres/
        );
    });

    it('retains Lambdapi authority and every withheld claim', () => {
        const profile = CORE_DIRECTED_CONTINUATION_PROFILE;
        assert.deepEqual(profile.lambdapiPolicy, {
            ...CORE_DIRECTED_GRADUATION_REVIEW.lambdapiPolicy,
            acceptanceTriggers: [
                ...CORE_DIRECTED_GRADUATION_REVIEW
                    .lambdapiPolicy.acceptanceTriggers
            ]
        });
        assert.deepEqual(profile.claimBoundary, {
            deterministicBoundedChecking:
                'authorized-exact-profile',
            boundedStopping: 'authorized',
            inheritedMvpThreeRuleTermination:
                'preserved-for-subprogram-only',
            combinedTermination: 'withheld',
            unrestrictedNormalization: 'withheld',
            confluence: 'withheld',
            typescriptSubjectReduction: 'withheld',
            performanceSla: 'withheld',
            additionalOwnerOrRuleAuthority: false
        });
    });

    it('stays outside the browser and leaves the deployed MVP gate exact', () => {
        const browserSource = readRepositoryFile(
            'src/v3_2/browser.ts'
        );
        assert.doesNotMatch(
            browserSource,
            /directed_graduation|DirectedContinuation|DTTLF_DIRECTED/
        );
        assert.equal(
            Object.prototype.hasOwnProperty.call(
                browser,
                'CORE_DIRECTED_CONTINUATION_PROFILE'
            ),
            false
        );
        assert.equal(
            Object.prototype.hasOwnProperty.call(
                browser,
                'createCoreDirectedContinuationKernel'
            ),
            false
        );
        assert.equal(
            CORE_DIRECTED_CONTINUATION_PROFILE
                .productBoundary.deployedMvpProfile,
            'unchanged'
        );
    });

    it('is deeply frozen and rejects review or profile drift', () => {
        assertDeepFrozen(CORE_DIRECTED_GRADUATION_REVIEW);
        assertDeepFrozen(CORE_DIRECTED_CONTINUATION_PROFILE);
        assert.doesNotThrow(() =>
            validateCoreDirectedGraduationReview()
        );
        assert.doesNotThrow(() =>
            validateCoreDirectedContinuationProfile()
        );

        expectReviewError(
            review => {
                review.approval.decisionEvidence += '.';
            },
            'GRADUATION_REVIEW_DECISION_DRIFT'
        );
        expectReviewError(
            review => {
                review.recommendation.authorityAuthorized = true;
            },
            'GRADUATION_REVIEW_PREREQUISITE_DRIFT'
        );
        expectReviewError(
            review => {
                review.authorization.runtimeRuleIds.pop();
            },
            'GRADUATION_REVIEW_AUTHORIZATION_DRIFT'
        );
        expectProfileError(
            profile => {
                profile.productBoundary.browserEntryPoint =
                    'src/v3_2/browser.ts';
            },
            'CONTINUATION_PROFILE_BOUNDARY_DRIFT'
        );
        expectProfileError(
            profile => {
                profile.claimBoundary.combinedTermination =
                    'authorized';
            },
            'CONTINUATION_PROFILE_BOUNDARY_DRIFT'
        );
    });
});
