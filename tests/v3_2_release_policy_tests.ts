/**
 * Focused RELEASE-1B conformance and public-policy synchronization tests.
 */

import assert from 'node:assert';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_MVP_DIFFERENTIAL_COMPLETION,
    CORE_MVP_GRADUATION_REVIEW,
    CORE_MVP_MANIFEST,
    CORE_MVP_RELEASE_POLICY,
    CoreMvpReleasePolicyError,
    CoreMvpReleasePolicyInput,
    validateCoreMvpReleasePolicy
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const repositoryRoot = resolve(__dirname, '..');

const readRepositoryFile = (path: string): string =>
    readFileSync(resolve(repositoryRoot, path), 'utf8');

const clonePolicy = (): CoreMvpReleasePolicyInput =>
    JSON.parse(JSON.stringify(CORE_MVP_RELEASE_POLICY));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    for (const child of Object.values(value as Record<string, unknown>)) {
        assertDeepFrozen(child);
    }
};

const expectPolicyError = (
    mutate: (policy: any) => void
): CoreMvpReleasePolicyError => {
    const policy = clonePolicy() as any;
    mutate(policy);
    try {
        validateCoreMvpReleasePolicy(policy);
    } catch (error) {
        assert.ok(error instanceof CoreMvpReleasePolicyError);
        assert.equal(error.code, 'RELEASE_POLICY_BOUNDARY_MISMATCH');
        return error;
    }
    assert.fail('Expected RELEASE_POLICY_BOUNDARY_MISMATCH');
};

describe('TypeScript v3.2 RELEASE-1B release policy', () => {
    it('pins the exact approved product and retained oracle boundary', () => {
        const policy = CORE_MVP_RELEASE_POLICY;

        assert.equal(policy.revision, 'RELEASE-1B');
        assert.equal(policy.status, 'policy-synchronized');
        assert.equal(policy.graduationRevision, 'GRADUATE-1B');
        assert.equal(
            policy.productProfile.manifestRevision,
            CORE_MVP_MANIFEST.revision
        );
        assert.equal(
            policy.productProfile.manifestContentHash,
            CORE_MVP_MANIFEST.contentHash
        );
        assert.deepEqual(
            policy.productProfile.ownerIds,
            CORE_MVP_GRADUATION_REVIEW.ownerIds
        );
        assert.deepEqual(
            policy.productProfile.runtimeRuleIds,
            CORE_MVP_GRADUATION_REVIEW.runtimeRuleIds
        );
        assert.equal(
            policy.productProfile.productionLambdapiDependency,
            false
        );
        assert.deepEqual(
            policy.lambdapiPolicy.acceptanceTriggers,
            CORE_MVP_GRADUATION_REVIEW.acceptanceTriggers
        );
    });

    it('makes the three frozen differential suites mandatory in check:all', () => {
        const policy = CORE_MVP_RELEASE_POLICY;
        const packageJson = JSON.parse(
            readRepositoryFile('package.json')
        ) as {
            scripts: Record<string, string>;
        };

        assert.equal(
            packageJson.scripts['check:conformance'],
            policy.conformance.scriptBody
        );
        assert.equal(
            packageJson.scripts['check:all'],
            policy.conformance.repositoryGateBody
        );
        assert.equal(policy.conformance.timeoutSeconds, 60);
        assert.equal(policy.conformance.oracleProcessCount, 3);
        assert.equal(
            policy.conformance.mandatoryInRepositoryGate,
            true
        );
        assert.deepEqual(policy.conformance.sharedCorpus, {
            ownerCaseCount:
                CORE_MVP_DIFFERENTIAL_COMPLETION.ownerCases.length,
            runtimeRuleCaseCount:
                CORE_MVP_DIFFERENTIAL_COMPLETION.ruleCases.length,
            higherCellPackageCount:
                CORE_MVP_DIFFERENTIAL_COMPLETION
                    .higherCellCases.length,
            unclosedRowCount:
                CORE_MVP_DIFFERENTIAL_COMPLETION.unclosedRows.length
        });
    });

    it('synchronizes every named public document and browser example', () => {
        const policy = CORE_MVP_RELEASE_POLICY;
        const artifacts = [
            ...policy.synchronizedArtifacts.publicDocumentation,
            policy.synchronizedArtifacts.browserExample
        ];

        for (const artifact of artifacts) {
            const contents = readRepositoryFile(artifact);
            if (artifact === 'README.md') {
                assert.match(
                    contents,
                    /https:\/\/hotdocx\.github\.io\/emdash\//,
                    'README.md must route to the deployed reviewer'
                );
                assert.match(
                    contents,
                    /qualified depth-generic finite\s+Hom-category recursion/,
                    'README.md must state the current public boundary'
                );
            } else {
                assert.match(
                    contents,
                    /emdash-v3\.2-mvp-1/,
                    `${artifact} must name the exact deployed profile`
                );
            }
        }

        const rootReadme = readRepositoryFile('README.md');
        assert.match(rootReadme, /live integrated reviewer/);
        assert.match(rootReadme, /wholly\s+client-side/);
        assert.match(
            rootReadme,
            /does not require a Lambdapi process/
        );
        assert.match(rootReadme, /fails closed outside them/);

        const handoff = readRepositoryFile(
            'docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md'
        );
        assert.match(handoff, /five selected semantic-boundary changes/);
        assert.match(handoff, /general confluence remains withheld/i);

        const templateReadme = readRepositoryFile(
            'emdash-template/README.md'
        );
        assert.match(templateReadme, /CORE_MVP_MANIFEST/);
        assert.match(
            templateReadme,
            /does\s+not execute Lambdapi in production/
        );
    });

    it('exports the exact frozen manifest through the browser API only', () => {
        assert.equal(
            browser.CORE_MVP_MANIFEST.revision,
            'emdash-v3.2-mvp-1'
        );
        assert.equal(browser.CORE_MVP_MANIFEST.owners.length, 16);
        assert.equal(browser.CORE_MVP_MANIFEST.rules.length, 3);
        assert.equal(
            Object.prototype.hasOwnProperty.call(
                browser,
                'CORE_MVP_RELEASE_POLICY'
            ),
            false
        );
        assert.equal(
            Object.prototype.hasOwnProperty.call(
                browser,
                'checkLambdapiProbe'
            ),
            false
        );
    });

    it('preserves release non-claims and rejects policy drift', () => {
        const policy = CORE_MVP_RELEASE_POLICY;

        assert.equal(policy.generalConfluence, 'withheld');
        assert.equal(policy.typescriptSubjectReduction, 'withheld');
        assert.equal(policy.additionalOwnersOrRulesAuthorized, false);
        assert.equal(policy.performanceSlaAuthorized, false);
        assert.equal(policy.releaseReady, false);
        assert.equal(policy.nextSlice, 'RELEASE-1C');
        assertDeepFrozen(policy);
        assert.doesNotThrow(() =>
            validateCoreMvpReleasePolicy(policy)
        );

        assert.match(
            expectPolicyError(drift => {
                drift.conformance.testFiles.pop();
            }).message,
            /synchronized RELEASE-1B/
        );
        assert.match(
            expectPolicyError(drift => {
                drift.lambdapiPolicy.acceptanceTriggers.pop();
            }).message,
            /synchronized RELEASE-1B/
        );
        assert.match(
            expectPolicyError(drift => {
                drift.productProfile.productionLambdapiDependency = true;
            }).message,
            /synchronized RELEASE-1B/
        );
    });
});
