/**
 * Focused pre-review tests for the DIRECTED-1C H-DTTLF-02 proposal.
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
    CORE_DIRECTED_1A_PROPOSAL,
    CORE_DIRECTED_1B_PROPOSAL,
    CORE_DIRECTED_1C_PROPOSAL,
    CORE_DIRECTED_FOUNDATION_2_PROPOSAL,
    CORE_DIRECTED_FOUNDATION_PROPOSAL,
    CORE_MVP_MANIFEST,
    CORE_OWNER_SCHEMAS,
    CoreDirected1cProposalError,
    LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING,
    validateCoreDirected1cProposal
} from '../src/v3_2';

const cloneProposal = (): any =>
    JSON.parse(JSON.stringify(CORE_DIRECTED_1C_PROPOSAL));

const cloneBinding = (): any =>
    JSON.parse(JSON.stringify(
        LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING
    ));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const assertProposalError = (
    mutateProposal: (proposal: any) => void,
    expectedCode: CoreDirected1cProposalError['code'],
    mutateBinding: (binding: any) => void = () => undefined
): void => {
    const proposal = cloneProposal();
    const binding = cloneBinding();
    mutateProposal(proposal);
    mutateBinding(binding);
    assert.throws(
        () => validateCoreDirected1cProposal(proposal, binding),
        error =>
            error instanceof CoreDirected1cProposalError &&
            error.code === expectedCode
    );
};

describe('TypeScript v3.2 DIRECTED-1C H-DTTLF-02 proposal', () => {
    it('freezes one opaque owner and no new computation rule', () => {
        assert.equal(CORE_DIRECTED_1C_PROPOSAL.revision, 'DIRECTED-1C');
        assert.equal(
            CORE_DIRECTED_1C_PROPOSAL.reviewGate,
            'H-DTTLF-02/DIRECTED-1C'
        );
        assert.deepEqual(
            CORE_DIRECTED_1C_PROPOSAL.owners.map(owner => [
                owner.owner,
                owner.activeAuthority,
                owner.candidateDisposition
            ]),
            [[
                'section-object-evaluation',
                'transparent-definition',
                'opaque-import'
            ]]
        );
        assert.deepEqual(CORE_DIRECTED_1C_PROPOSAL.runtimeRules, []);
        assert.deepEqual(CORE_DIRECTED_1C_PROPOSAL.proofTimeRules, []);
        assert.equal(CORE_DIRECTED_1C_PROPOSAL.owners[0].body, undefined);
    });

    it('records the exact dependent piapp0 signature and plicities', () => {
        const owner = CORE_DIRECTED_1C_PROPOSAL.owners[0];
        assert.deepEqual(
            owner.slots.map(slot => [
                slot.name,
                slot.plicity,
                slot.role
            ]),
            [
                ['K', 'implicit', 'base-category'],
                ['E', 'implicit', 'displayed-family'],
                ['s', 'explicit', 'section-object'],
                ['k', 'explicit', 'base-object']
            ]
        );
        const serialized = JSON.stringify(owner);
        assert.match(serialized, /\"owner\":\"section-category\"/);
        assert.match(serialized, /\"owner\":\"functor-object\"/);
        assert.match(serialized, /\"owner\":\"object-classifier\"/);
        assert.match(serialized, /\"name\":\"k\"/);
    });

    it('reuses the already reviewed section and telescope closure', () => {
        assert.deepEqual(
            CORE_DIRECTED_1C_PROPOSAL.closurePolicy,
            {
                sectionCategory: 'reuse-existing-base-owner',
                telescopeFamily: 'reuse-reviewed-directed-1a-owner',
                telescopeFibreComputation:
                    'reuse-reviewed-directed-1b-runtime-rule',
                dependentPair: 'reuse-reviewed-directed-1b-owner',
                outerApplication: 'reuse-generic-outer-lf-beta',
                activeTransparentDefinition:
                    'import-signature-opaquely',
                emittedShadowDeclarations: false,
                defaultLfProfile: 'unchanged'
            }
        );
        assert.equal('section-category' in CORE_OWNER_SCHEMAS, true);
        assert.deepEqual(
            CORE_DIRECTED_1C_PROPOSAL.prerequisites.directed1aOwnerIds,
            CORE_DIRECTED_1A_PROPOSAL.owners.map(owner => owner.owner)
        );
        assert.deepEqual(
            CORE_DIRECTED_1C_PROPOSAL.prerequisites.directed1bOwnerIds,
            CORE_DIRECTED_1B_PROPOSAL.owners.map(owner => owner.owner)
        );
        assert.deepEqual(
            CORE_DIRECTED_1C_PROPOSAL.prerequisites
                .directed1bRuntimeRuleIds,
            CORE_DIRECTED_1B_PROPOSAL.runtimeRules.map(rule => rule.id)
        );
        assert.deepEqual(
            CORE_DIRECTED_1C_PROPOSAL.prerequisites.foundation1RuleIds,
            CORE_DIRECTED_FOUNDATION_PROPOSAL.runtimeRules.map(
                rule => rule.id
            )
        );
        assert.deepEqual(
            CORE_DIRECTED_1C_PROPOSAL.prerequisites.foundation2RuleIds,
            CORE_DIRECTED_FOUNDATION_2_PROPOSAL.runtimeRules.map(
                rule => rule.id
            )
        );
    });

    it('records the deliberately excluded internal-Pi closure', () => {
        assert.deepEqual(
            CORE_DIRECTED_1C_PROPOSAL.explicitDeferrals,
            [
                'section evaluator transparent body and evaluation functor',
                'fixed-base internal section functor and its action rules',
                'contravariant displayed-family functor and global internal sections',
                'pullback internal-section family and its fold and pointwise rules',
                'section hom action and section-arrow evaluation',
                'total-category projection-pullback section uncurrying',
                'displayed-transfor telescope uncurrying',
                'groupoidal product and section specialization and closure'
            ]
        );
        assert.equal(
            CORE_DIRECTED_1C_PROPOSAL.nonEffects.includes(
                'does not authorize product graduation or a metatheory claim'
            ),
            true
        );
    });

    it('keeps semantic data backend-neutral and relocates active piapp0', () => {
        const proposal = JSON.stringify(CORE_DIRECTED_1C_PROPOSAL);
        assert.doesNotMatch(
            proposal,
            /piapp0|Pi_func|Pi_int_funcd|emdash2\//
        );
        assert.deepEqual(
            [
                LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING.owner,
                LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING.serializedName
            ],
            ['section-object-evaluation', 'piapp0']
        );
        const source = readFileSync(
            LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING
                .provenance.authorityPath,
            'utf8'
        );
        assert.equal(
            source.includes(
                LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING
                    .provenance.sourceFragment
            ),
            true
        );
    });

    it('preserves the frozen MVP, owner schema, and browser boundary', () => {
        assert.deepEqual(
            CORE_DIRECTED_1C_PROPOSAL.preservedMvpProfile,
            {
                revision: CORE_MVP_MANIFEST.revision,
                contentHash: CORE_MVP_MANIFEST.contentHash,
                ownerIds: CORE_MVP_MANIFEST.owners.map(entry => entry.owner),
                runtimeRuleIds:
                    CORE_MVP_MANIFEST.rules.map(rule => rule.id)
            }
        );
        assert.equal(
            'section-object-evaluation' in CORE_OWNER_SCHEMAS,
            false
        );
        const browserSource = readFileSync(
            'src/v3_2/browser.ts',
            'utf8'
        );
        assert.doesNotMatch(
            browserSource,
            /directed_1c|CORE_DIRECTED_1C/
        );
    });

    it('is deeply frozen and validates unchanged', () => {
        assertDeepFrozen(CORE_DIRECTED_1C_PROPOSAL);
        assertDeepFrozen(LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING);
        assert.doesNotThrow(() => validateCoreDirected1cProposal());
    });

    it('rejects boundary, prerequisite, owner, and expression drift', () => {
        assertProposalError(
            proposal => {
                proposal.status = 'approved';
            },
            'INVALID_PROPOSAL_BOUNDARY'
        );
        assertProposalError(
            proposal => {
                proposal.prerequisites.directed1bOwnerIds.pop();
            },
            'INVALID_PREREQUISITE'
        );
        assertProposalError(
            proposal => {
                proposal.owners.push(proposal.owners[0]);
            },
            'INVALID_OWNER_SET'
        );
        assertProposalError(
            proposal => {
                proposal.owners[0].result.arguments[0]
                    .arguments[0].owner = 'section-object-evaluation';
            },
            'INVALID_EXPRESSION'
        );
    });

    it('rejects closure, binding, MVP, and exact-content drift', () => {
        assertProposalError(
            proposal => {
                proposal.closurePolicy.activeTransparentDefinition =
                    'checked-local-mirror';
            },
            'INVALID_CLOSURE_POLICY'
        );
        assertProposalError(
            () => undefined,
            'INVALID_BACKEND_BINDING',
            binding => {
                binding.serializedName = 'piapp0_func';
            }
        );
        assertProposalError(
            proposal => {
                proposal.preservedMvpProfile.ownerIds.pop();
            },
            'MVP_PROFILE_DRIFT'
        );
        assertProposalError(
            proposal => {
                proposal.explicitDeferrals.pop();
            },
            'PROPOSAL_DRIFT'
        );
    });
});
