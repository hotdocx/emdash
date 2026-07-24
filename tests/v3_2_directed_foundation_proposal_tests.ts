/**
 * Focused review-input tests for the DIRECTED-1B foundation dependency.
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
    CORE_DEPENDENT_BRIDGE_SCHEMAS,
    CORE_DIRECTED_1B_PROPOSAL,
    CORE_DIRECTED_1B_REVIEW,
    CORE_DIRECTED_FOUNDATION_PROPOSAL,
    CORE_MVP_MANIFEST,
    CoreDirectedFoundationProposalError,
    LAMBDAPI_V32_DIRECTED_FOUNDATION_RULE_BINDINGS,
    validateCoreDirectedFoundationProposal
} from '../src/v3_2';

const clone = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

describe('TypeScript v3.2 DIRECTED foundation proposal', () => {
    it('freezes exactly three prerequisite runtime rules and no declarations or proof rules', () => {
        assert.doesNotThrow(() =>
            validateCoreDirectedFoundationProposal()
        );
        assert.deepEqual(
            CORE_DIRECTED_FOUNDATION_PROPOSAL.runtimeRules.map(
                rule => rule.id
            ),
            [
                'directed.category-object.decode',
                'directed.displayed-family.decode',
                'directed.displayed-functor.decode'
            ]
        );
        assert.deepEqual(
            CORE_DIRECTED_FOUNDATION_PROPOSAL.ownerDeclarations,
            []
        );
        assert.deepEqual(
            CORE_DIRECTED_FOUNDATION_PROPOSAL.proofTimeRules,
            []
        );
        assert.equal(
            CORE_DIRECTED_FOUNDATION_PROPOSAL.runtimePolicy.scope,
            'directed-catalog-local'
        );
    });

    it('relocates every prerequisite to an exact active runtime rule', () => {
        const source = readFileSync('emdash2/emdash3_2.lp', 'utf8');
        for (
            const binding of
            LAMBDAPI_V32_DIRECTED_FOUNDATION_RULE_BINDINGS
        ) {
            assert.equal(binding.authority, 'runtime-rule');
            assert.equal(
                source.includes(binding.provenance.sourceFragment),
                true,
                binding.provenance.sourceFragment
            );
        }
        assert.equal(
            CORE_DEPENDENT_BRIDGE_SCHEMAS[
                'displayed-family-classifier'
            ].authority,
            'runtime-reduction'
        );
    });

    it('keeps the approved DIRECTED-1B review and own rule count unchanged', () => {
        assert.equal(
            CORE_DIRECTED_FOUNDATION_PROPOSAL
                .relationshipToDirected1b.approvedProposalUnchanged,
            true
        );
        assert.equal(
            CORE_DIRECTED_1B_PROPOSAL.runtimeRules.length,
            3
        );
        assert.equal(
            CORE_DIRECTED_1B_REVIEW.authorization.runtimeRuleIds.length,
            3
        );
        assert.equal(CORE_DIRECTED_1B_PROPOSAL.owners.length, 5);
    });

    it('preserves the deployed manifest and browser boundary', () => {
        assert.equal(
            CORE_DIRECTED_FOUNDATION_PROPOSAL.preservedMvpProfile
                .contentHash,
            CORE_MVP_MANIFEST.contentHash
        );
        assert.deepEqual(
            CORE_DIRECTED_FOUNDATION_PROPOSAL.preservedMvpProfile
                .runtimeRuleIds,
            CORE_MVP_MANIFEST.rules.map(rule => rule.id)
        );
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /directed_foundation|CoreDirectedFoundation/
        );
    });

    it('is deeply frozen and rejects rule, policy, binding, and exact-content drift', () => {
        assert.equal(
            Object.isFrozen(CORE_DIRECTED_FOUNDATION_PROPOSAL),
            true
        );
        assert.equal(
            Object.isFrozen(
                CORE_DIRECTED_FOUNDATION_PROPOSAL.runtimeRules[0].left
            ),
            true
        );

        const changedRule = clone(
            CORE_DIRECTED_FOUNDATION_PROPOSAL
        );
        (
            changedRule.runtimeRules as unknown as {
                id: string;
            }[]
        )[0].id = 'directed.changed';
        assert.throws(
            () => validateCoreDirectedFoundationProposal(changedRule),
            error =>
                error instanceof CoreDirectedFoundationProposalError &&
                error.code === 'INVALID_RULE_SET'
        );

        const changedPolicy = clone(
            CORE_DIRECTED_FOUNDATION_PROPOSAL
        );
        (
            changedPolicy.runtimePolicy as unknown as {
                defaultLfProfile: string;
            }
        ).defaultLfProfile = 'changed';
        assert.throws(
            () => validateCoreDirectedFoundationProposal(changedPolicy),
            error =>
                error instanceof CoreDirectedFoundationProposalError &&
                error.code === 'INVALID_RUNTIME_POLICY'
        );

        const changedBindings = clone(
            LAMBDAPI_V32_DIRECTED_FOUNDATION_RULE_BINDINGS
        );
        (
            changedBindings as unknown as {
                provenance: { sourceFragment: string };
            }[]
        )[0].provenance.sourceFragment = 'changed';
        assert.throws(
            () => validateCoreDirectedFoundationProposal(
                CORE_DIRECTED_FOUNDATION_PROPOSAL,
                changedBindings
            ),
            error =>
                error instanceof CoreDirectedFoundationProposalError &&
                error.code === 'INVALID_BACKEND_BINDINGS'
        );

        const changedNonEffect = clone(
            CORE_DIRECTED_FOUNDATION_PROPOSAL
        );
        (
            changedNonEffect.nonEffects as unknown as string[]
        )[0] = 'changed';
        assert.throws(
            () => validateCoreDirectedFoundationProposal(
                changedNonEffect
            ),
            error =>
                error instanceof CoreDirectedFoundationProposalError &&
                error.code === 'PROPOSAL_DRIFT'
        );
    });
});
