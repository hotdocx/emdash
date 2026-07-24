/**
 * Focused review-input tests for the follow-up decoded Cat-hom prerequisite.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_DIRECTED_1B_REVIEW,
    CORE_DIRECTED_FOUNDATION_2_PROPOSAL,
    CORE_DIRECTED_FOUNDATION_REVIEW,
    CORE_MVP_MANIFEST,
    CoreDirectedFoundation2ProposalError,
    LAMBDAPI_V32_DIRECTED_FOUNDATION_2_RULE_BINDING,
    validateCoreDirectedFoundation2Proposal
} from '../src/v3_2';

const clone = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

describe('TypeScript v3.2 DIRECTED foundation 2 proposal', () => {
    it('freezes one decoded Cat-hom rule and no owner or proof rule', () => {
        assert.doesNotThrow(() =>
            validateCoreDirectedFoundation2Proposal()
        );
        const proposal = CORE_DIRECTED_FOUNDATION_2_PROPOSAL;
        assert.deepEqual(
            proposal.runtimeRules.map(rule => rule.id),
            ['directed.category-hom.decode']
        );
        assert.deepEqual(proposal.ownerDeclarations, []);
        assert.deepEqual(proposal.proofTimeRules, []);
        assert.equal(
            proposal.runtimePolicy.redexScope,
            'decoded-category-hom-only'
        );
        assert.equal(
            proposal.runtimePolicy.rawClassifierRewrite,
            false
        );
        assert.equal(
            proposal.runtimePolicy.categoryHeadRewrite,
            false
        );
    });

    it('binds the proposal to the active Cat hom-category computation', () => {
        const binding =
            LAMBDAPI_V32_DIRECTED_FOUNDATION_2_RULE_BINDING;
        const source = readFileSync(
            binding.provenance.authorityPath,
            'utf8'
        );
        assert.equal(
            binding.authority,
            'runtime-rule-plus-transparent-classifier-definitions'
        );
        assert.equal(
            source.includes(binding.provenance.sourceFragment),
            true
        );
        assert.equal(
            CORE_DIRECTED_FOUNDATION_2_PROPOSAL.runtimeRules[0]
                .authority,
            'active-runtime-consequence-through-transparent-classifiers'
        );
    });

    it('preserves both approved prerequisites and their exact rule sets', () => {
        const prerequisite =
            CORE_DIRECTED_FOUNDATION_2_PROPOSAL.prerequisites;
        assert.equal(
            prerequisite.foundation1Revision,
            CORE_DIRECTED_FOUNDATION_REVIEW.revision
        );
        assert.deepEqual(
            prerequisite.foundation1RuleIds,
            CORE_DIRECTED_FOUNDATION_REVIEW.authorization
                .runtimeRuleIds
        );
        assert.equal(
            prerequisite.directed1bRevision,
            CORE_DIRECTED_1B_REVIEW.revision
        );
        assert.deepEqual(
            prerequisite.directed1bOwnRuntimeRuleIds,
            CORE_DIRECTED_1B_REVIEW.authorization.runtimeRuleIds
        );
        assert.equal(prerequisite.approvedArtifactsUnchanged, true);
    });

    it('preserves the deployed MVP and browser boundary', () => {
        const proposal = CORE_DIRECTED_FOUNDATION_2_PROPOSAL;
        assert.equal(
            proposal.preservedMvpProfile.contentHash,
            CORE_MVP_MANIFEST.contentHash
        );
        assert.deepEqual(
            proposal.preservedMvpProfile.runtimeRuleIds,
            CORE_MVP_MANIFEST.rules.map(rule => rule.id)
        );
        assert.doesNotMatch(
            readFileSync('src/v3_2/browser.ts', 'utf8'),
            /directed_foundation_2|CoreDirectedFoundation2/
        );
    });

    it('is deeply frozen and rejects prerequisite, rule, policy, binding, and content drift', () => {
        const proposal = CORE_DIRECTED_FOUNDATION_2_PROPOSAL;
        assert.equal(Object.isFrozen(proposal), true);
        assert.equal(
            Object.isFrozen(proposal.runtimeRules[0].left),
            true
        );

        const prerequisite = clone(proposal);
        (
            prerequisite.prerequisites as unknown as {
                approvedArtifactsUnchanged: boolean;
            }
        ).approvedArtifactsUnchanged = false;
        assert.throws(
            () => validateCoreDirectedFoundation2Proposal(
                prerequisite
            ),
            error =>
                error instanceof
                    CoreDirectedFoundation2ProposalError &&
                error.code === 'INVALID_PREREQUISITE'
        );

        const rule = clone(proposal);
        (
            rule.runtimeRules as unknown as {
                id: string;
            }[]
        )[0].id = 'changed';
        assert.throws(
            () => validateCoreDirectedFoundation2Proposal(rule),
            error =>
                error instanceof
                    CoreDirectedFoundation2ProposalError &&
                error.code === 'INVALID_RULE_SET'
        );

        const policy = clone(proposal);
        (
            policy.runtimePolicy as unknown as {
                rawClassifierRewrite: boolean;
            }
        ).rawClassifierRewrite = true;
        assert.throws(
            () => validateCoreDirectedFoundation2Proposal(policy),
            error =>
                error instanceof
                    CoreDirectedFoundation2ProposalError &&
                error.code === 'INVALID_RUNTIME_POLICY'
        );

        const binding = clone(
            LAMBDAPI_V32_DIRECTED_FOUNDATION_2_RULE_BINDING
        );
        (
            binding.provenance as unknown as {
                sourceFragment: string;
            }
        ).sourceFragment = 'changed';
        assert.throws(
            () => validateCoreDirectedFoundation2Proposal(
                proposal,
                binding
            ),
            error =>
                error instanceof
                    CoreDirectedFoundation2ProposalError &&
                error.code === 'INVALID_BACKEND_BINDING'
        );

        const content = clone(proposal);
        (
            content.nonEffects as unknown as string[]
        )[0] = 'changed';
        assert.throws(
            () => validateCoreDirectedFoundation2Proposal(content),
            error =>
                error instanceof
                    CoreDirectedFoundation2ProposalError &&
                error.code === 'PROPOSAL_DRIFT'
        );
    });
});
