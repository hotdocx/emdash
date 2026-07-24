/**
 * Focused pre-review tests for the exact H-DTTLF-02 proposal.
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
    CoreDirected1aProposalError,
    LAMBDAPI_V32_DIRECTED_1A_PROPOSAL_BINDINGS,
    validateCoreDirected1aProposal
} from '../src/v3_2/directed_1a_proposal';
import {
    LAMBDAPI_V32_OWNER_BINDINGS
} from '../src/v3_2/lambdapi';
import {
    CORE_MVP_MANIFEST
} from '../src/v3_2/manifest';
import {
    CORE_OWNER_SCHEMAS
} from '../src/v3_2/schema';

const cloneProposal = (): any =>
    JSON.parse(JSON.stringify(CORE_DIRECTED_1A_PROPOSAL));

const cloneBindings = (): any =>
    JSON.parse(JSON.stringify(
        LAMBDAPI_V32_DIRECTED_1A_PROPOSAL_BINDINGS
    ));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const assertProposalError = (
    mutateProposal: (proposal: any) => void,
    expectedCode: CoreDirected1aProposalError['code'],
    mutateBindings: (bindings: any) => void = () => undefined
): void => {
    const proposal = cloneProposal();
    const bindings = cloneBindings();
    mutateProposal(proposal);
    mutateBindings(bindings);
    assert.throws(
        () => validateCoreDirected1aProposal(proposal, bindings),
        error =>
            error instanceof CoreDirected1aProposalError &&
            error.code === expectedCode
    );
};

describe('TypeScript v3.2 DIRECTED-1A H-DTTLF-02 proposal', () => {
    it('freezes exactly three declaration signatures and zero rules', () => {
        assert.equal(CORE_DIRECTED_1A_PROPOSAL.revision, 'DIRECTED-1A');
        assert.equal(
            CORE_DIRECTED_1A_PROPOSAL.status,
            'proposal-awaiting-h-dttlf-02'
        );
        assert.equal(
            CORE_DIRECTED_1A_PROPOSAL.reviewGate,
            'H-DTTLF-02'
        );
        assert.deepEqual(
            CORE_DIRECTED_1A_PROPOSAL.owners.map(entry => entry.owner),
            [
                'displayed-functor-category',
                'sigma-category',
                'sigma-telescope-family'
            ]
        );
        assert.deepEqual(CORE_DIRECTED_1A_PROPOSAL.rules, []);
        assert.equal(
            CORE_DIRECTED_1A_PROPOSAL.owners.every(entry =>
                entry.authority === 'active-declaration-signature' &&
                entry.disposition ===
                    'candidate-awaiting-h-dttlf-02'
            ),
            true
        );
    });

    it('records the exact dependent plicities and owner dependencies', () => {
        const [functord, sigma, telescope] =
            CORE_DIRECTED_1A_PROPOSAL.owners;

        assert.deepEqual(
            functord.slots.map(entry => [
                entry.name,
                entry.plicity
            ]),
            [
                ['K', 'implicit'],
                ['E', 'explicit'],
                ['D', 'explicit']
            ]
        );
        assert.deepEqual(
            sigma.slots.map(entry => [
                entry.name,
                entry.plicity
            ]),
            [
                ['K', 'implicit'],
                ['E', 'explicit']
            ]
        );
        assert.deepEqual(
            telescope.slots.map(entry => [
                entry.name,
                entry.plicity
            ]),
            [
                ['K', 'implicit'],
                ['R', 'implicit'],
                ['FF', 'explicit']
            ]
        );

        const telescopeSignature = JSON.stringify(telescope);
        assert.match(
            telescopeSignature,
            /"owner":"displayed-functor-category"/
        );
        assert.match(telescopeSignature, /"owner":"sigma-category"/);
        assert.match(
            telescopeSignature,
            /"owner":"constant-displayed-family"/
        );
        assert.match(
            telescopeSignature,
            /"owner":"category-of-categories"/
        );
    });

    it('keeps the semantic proposal backend-neutral', () => {
        const proposal = JSON.stringify(CORE_DIRECTED_1A_PROPOSAL);
        assert.doesNotMatch(
            proposal,
            /Functord_cat|Sigma_cat|emdash2\/emdash3_2|emdash\.emdash3_2/
        );
        assert.deepEqual(
            LAMBDAPI_V32_DIRECTED_1A_PROPOSAL_BINDINGS.map(binding => [
                binding.owner,
                binding.serializedName
            ]),
            [
                ['displayed-functor-category', 'Functord_cat'],
                ['sigma-category', 'Sigma_cat'],
                [
                    'sigma-telescope-family',
                    'Sigma_catd_functord_catd'
                ]
            ]
        );
    });

    it('relocates every binding at its active declaration owner', () => {
        for (const binding of
            LAMBDAPI_V32_DIRECTED_1A_PROPOSAL_BINDINGS) {
            const source = readFileSync(
                binding.provenance.authorityPath,
                'utf8'
            );
            assert.equal(
                source.includes(binding.provenance.declaration),
                true,
                `${binding.owner} declaration did not relocate`
            );
        }
    });

    it('preserves the exact frozen MVP and current catalog boundary', () => {
        assert.deepEqual(
            CORE_DIRECTED_1A_PROPOSAL.preservedMvpProfile,
            {
                revision: CORE_MVP_MANIFEST.revision,
                contentHash: CORE_MVP_MANIFEST.contentHash,
                ownerIds: CORE_MVP_MANIFEST.owners.map(entry => entry.owner),
                runtimeRuleIds: CORE_MVP_MANIFEST.rules.map(rule => rule.id)
            }
        );

        for (const entry of CORE_DIRECTED_1A_PROPOSAL.owners) {
            assert.equal(entry.owner in CORE_OWNER_SCHEMAS, false);
            assert.equal(
                entry.owner in LAMBDAPI_V32_OWNER_BINDINGS,
                false
            );
            assert.equal(
                CORE_MVP_MANIFEST.owners.some(
                    manifestOwner => manifestOwner.owner === entry.owner
                ),
                false
            );
        }

        const browserSource = readFileSync(
            'src/v3_2/browser.ts',
            'utf8'
        );
        assert.doesNotMatch(
            browserSource,
            /directed_1a|CORE_DIRECTED_1A/
        );
    });

    it('is deeply frozen and validates unchanged', () => {
        assertDeepFrozen(CORE_DIRECTED_1A_PROPOSAL);
        assertDeepFrozen(
            LAMBDAPI_V32_DIRECTED_1A_PROPOSAL_BINDINGS
        );
        assert.doesNotThrow(() => validateCoreDirected1aProposal());
    });

    it('rejects boundary, owner, signature, and rule drift', () => {
        assertProposalError(
            proposal => {
                proposal.status = 'approved';
            },
            'INVALID_PROPOSAL_BOUNDARY'
        );
        assertProposalError(
            proposal => {
                proposal.owners[0].owner = 'category-universe';
            },
            'INVALID_OWNER_SET'
        );
        assertProposalError(
            proposal => {
                proposal.owners[2].slots[2].type.arguments = [];
            },
            'INVALID_SIGNATURE'
        );
        assertProposalError(
            proposal => {
                proposal.rules.push({ id: 'unreviewed' });
            },
            'INVALID_RULE_SET'
        );
    });

    it('rejects backend, MVP identity, and exact-content drift', () => {
        assertProposalError(
            () => undefined,
            'PROPOSAL_DRIFT',
            bindings => {
                bindings[0].serializedName = 'Transf_cat';
            }
        );
        assertProposalError(
            proposal => {
                proposal.preservedMvpProfile.contentHash = 'sha256:drift';
            },
            'MVP_PROFILE_DRIFT'
        );
        assertProposalError(
            proposal => {
                proposal.nonEffects.pop();
            },
            'PROPOSAL_DRIFT'
        );
    });
});
