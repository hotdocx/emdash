/**
 * Focused pre-review tests for the second H-DTTLF-02 proposal.
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
    CORE_DIRECTED_1A_REVIEW,
    CORE_DIRECTED_1B_PROPOSAL,
    CORE_LF_CONTINUATION_PROFILE_REVIEW,
    CORE_MVP_MANIFEST,
    CORE_OWNER_SCHEMAS,
    CoreDirected1bProposalError,
    LAMBDAPI_V32_DIRECTED_1B_OWNER_BINDINGS,
    LAMBDAPI_V32_DIRECTED_1B_RULE_BINDINGS,
    LAMBDAPI_V32_OWNER_BINDINGS,
    validateCoreDirected1bProposal
} from '../src/v3_2';

const cloneProposal = (): any =>
    JSON.parse(JSON.stringify(CORE_DIRECTED_1B_PROPOSAL));

const cloneOwnerBindings = (): any =>
    JSON.parse(JSON.stringify(
        LAMBDAPI_V32_DIRECTED_1B_OWNER_BINDINGS
    ));

const cloneRuleBindings = (): any =>
    JSON.parse(JSON.stringify(
        LAMBDAPI_V32_DIRECTED_1B_RULE_BINDINGS
    ));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(assertDeepFrozen);
};

const assertProposalError = (
    mutateProposal: (proposal: any) => void,
    expectedCode: CoreDirected1bProposalError['code'],
    mutateOwnerBindings: (bindings: any) => void = () => undefined,
    mutateRuleBindings: (bindings: any) => void = () => undefined
): void => {
    const proposal = cloneProposal();
    const ownerBindings = cloneOwnerBindings();
    const ruleBindings = cloneRuleBindings();
    mutateProposal(proposal);
    mutateOwnerBindings(ownerBindings);
    mutateRuleBindings(ruleBindings);
    assert.throws(
        () => validateCoreDirected1bProposal(
            proposal,
            ownerBindings,
            ruleBindings
        ),
        error =>
            error instanceof CoreDirected1bProposalError &&
            error.code === expectedCode
    );
};

describe('TypeScript v3.2 DIRECTED-1B H-DTTLF-02 proposal', () => {
    it('freezes exactly five owners, three runtime rules, and no proof-time rule', () => {
        assert.equal(CORE_DIRECTED_1B_PROPOSAL.revision, 'DIRECTED-1B');
        assert.equal(
            CORE_DIRECTED_1B_PROPOSAL.status,
            'proposal-awaiting-h-dttlf-02'
        );
        assert.deepEqual(
            CORE_DIRECTED_1B_PROPOSAL.owners.map(entry => entry.owner),
            [
                'decoded-dependent-pair',
                'dependent-pair',
                'sigma-first-projection',
                'sigma-transport-arrow',
                'sigma-telescope-transport'
            ]
        );
        assert.deepEqual(
            CORE_DIRECTED_1B_PROPOSAL.runtimeRules.map(entry => entry.id),
            [
                'directed.sigma-object.decode',
                'directed.sigma-first-projection.evaluate',
                'directed.sigma-telescope-fibre.evaluate'
            ]
        );
        assert.deepEqual(CORE_DIRECTED_1B_PROPOSAL.proofTimeRules, []);
    });

    it('records exact plicities and the intentionally partial transparency transfer', () => {
        assert.deepEqual(
            CORE_DIRECTED_1B_PROPOSAL.owners.map(owner =>
                owner.slots.map(slot => [
                    slot.name,
                    slot.plicity
                ])
            ),
            [
                [
                    ['a', 'implicit'],
                    ['P', 'explicit']
                ],
                [
                    ['a', 'implicit'],
                    ['P', 'implicit'],
                    ['pairFirst', 'explicit'],
                    ['pairSecond', 'explicit']
                ],
                [
                    ['K', 'implicit'],
                    ['E', 'explicit']
                ],
                [
                    ['K', 'implicit'],
                    ['E', 'explicit'],
                    ['x', 'implicit'],
                    ['y', 'implicit'],
                    ['p', 'explicit'],
                    ['u', 'explicit']
                ],
                [
                    ['K', 'implicit'],
                    ['R', 'implicit'],
                    ['FF', 'explicit'],
                    ['x', 'implicit'],
                    ['y', 'implicit'],
                    ['p', 'explicit'],
                    ['r', 'explicit']
                ]
            ]
        );

        const transport =
            CORE_DIRECTED_1B_PROPOSAL.owners[3];
        const telescopeTransport =
            CORE_DIRECTED_1B_PROPOSAL.owners[4];
        assert.equal(
            transport.activeAuthority,
            'transparent-definition'
        );
        assert.equal(transport.candidateDisposition, 'opaque-import');
        assert.equal(transport.body, undefined);
        assert.equal(
            telescopeTransport.candidateDisposition,
            'transparent-checked-definition'
        );
        assert.notEqual(telescopeTransport.body, undefined);
    });

    it('captures both LF dependent pairs and directed categorical computation', () => {
        const proposal = JSON.stringify(CORE_DIRECTED_1B_PROPOSAL);
        assert.match(proposal, /"owner":"decoded-dependent-pair"/);
        assert.match(proposal, /"owner":"dependent-pair"/);
        assert.match(proposal, /"tag":"pi"/);
        assert.match(proposal, /"tag":"lambda"/);
        assert.match(proposal, /"owner":"sigma-category"/);
        assert.match(proposal, /"owner":"sigma-telescope-family"/);
        assert.match(proposal, /"owner":"functor-hom-capped"/);
        assert.match(proposal, /"owner":"transfor-component-capped"/);
    });

    it('keeps the new runtime program catalog-scoped and globally budgeted', () => {
        assert.deepEqual(
            CORE_DIRECTED_1B_PROPOSAL.runtimeExtensionPolicy,
            {
                scope: 'directed-catalog-local',
                insertionPoint:
                    'reviewed-runtime-phase-before-frozen-mvp-program',
                budget: 'shared-outer-lf-global-budget',
                defaultLfProfile: 'unchanged',
                arbitraryUserRules: false
            }
        );
        assert.deepEqual(
            CORE_DIRECTED_1B_PROPOSAL.prerequisites,
            {
                lfProfileReview:
                    CORE_LF_CONTINUATION_PROFILE_REVIEW.revision,
                directed1aReview: CORE_DIRECTED_1A_REVIEW.revision,
                directed1aOwnerIds: [
                    'displayed-functor-category',
                    'sigma-category',
                    'sigma-telescope-family'
                ]
            }
        );
        assert.deepEqual(
            CORE_DIRECTED_1B_PROPOSAL.backendProjectionPolicy,
            {
                opaqueImports:
                    'signature-checked-external-references',
                transparentDefinitions:
                    'checked-local-mirror-mapped-to-active-owner',
                emittedShadowDeclarations: false,
                activeDefinitionBody:
                    'proposal-exact-and-lambdapi-oracle-checked'
            }
        );
    });

    it('makes the consumer-led deferrals explicit', () => {
        assert.deepEqual(
            CORE_DIRECTED_1B_PROPOSAL.explicitDeferrals,
            [
                'general Sigma-category Hom normalization',
                'sigma-arrow construction and computation',
                'sigma-transport-arrow unfolding',
                'constant-family Sigma-to-product computation',
                'Sigma projection pullback and proof-time uncurrying',
                'section/internal-Pi and displayed-transfor uncurrying',
                'groupoidal Sigma path elimination and closure'
            ]
        );
        assert.equal(
            CORE_DIRECTED_1B_PROPOSAL.nonEffects.includes(
                'does not alter the default LF-PROFILE-1 runtime component'
            ),
            true
        );
    });

    it('keeps semantic proposal data backend-neutral', () => {
        const proposal = JSON.stringify(CORE_DIRECTED_1B_PROPOSAL);
        assert.doesNotMatch(
            proposal,
            /Struct_sigma|Sigma_proj1_func|sigma_transport_arrow|emdash2\//
        );
        assert.deepEqual(
            LAMBDAPI_V32_DIRECTED_1B_OWNER_BINDINGS.map(binding => [
                binding.owner,
                binding.serializedName
            ]),
            [
                ['decoded-dependent-pair', 'τΣ_'],
                ['dependent-pair', 'Struct_sigma'],
                ['sigma-first-projection', 'Sigma_proj1_func'],
                ['sigma-transport-arrow', 'sigma_transport_arrow'],
                [
                    'sigma-telescope-transport',
                    'Sigma_catd_transport_func'
                ]
            ]
        );
    });

    it('relocates every active owner and rule binding', () => {
        for (const binding of [
            ...LAMBDAPI_V32_DIRECTED_1B_OWNER_BINDINGS,
            ...LAMBDAPI_V32_DIRECTED_1B_RULE_BINDINGS
        ]) {
            const source = readFileSync(
                binding.provenance.authorityPath,
                'utf8'
            );
            assert.equal(
                source.includes(binding.provenance.sourceFragment),
                true,
                `${'owner' in binding ? binding.owner : binding.id} ` +
                'authority fragment did not relocate'
            );
        }
    });

    it('preserves the frozen catalogs, MVP, and browser boundary', () => {
        assert.deepEqual(
            CORE_DIRECTED_1B_PROPOSAL.preservedMvpProfile,
            {
                revision: CORE_MVP_MANIFEST.revision,
                contentHash: CORE_MVP_MANIFEST.contentHash,
                ownerIds: CORE_MVP_MANIFEST.owners.map(entry => entry.owner),
                runtimeRuleIds: CORE_MVP_MANIFEST.rules.map(rule => rule.id)
            }
        );
        for (const entry of CORE_DIRECTED_1B_PROPOSAL.owners) {
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
            /directed_1b|CORE_DIRECTED_1B/
        );
    });

    it('is deeply frozen and validates unchanged', () => {
        assertDeepFrozen(CORE_DIRECTED_1B_PROPOSAL);
        assertDeepFrozen(LAMBDAPI_V32_DIRECTED_1B_OWNER_BINDINGS);
        assertDeepFrozen(LAMBDAPI_V32_DIRECTED_1B_RULE_BINDINGS);
        assert.doesNotThrow(() => validateCoreDirected1bProposal());
    });

    it('rejects boundary, prerequisite, owner, expression, and body drift', () => {
        assertProposalError(
            proposal => {
                proposal.status = 'approved';
            },
            'INVALID_PROPOSAL_BOUNDARY'
        );
        assertProposalError(
            proposal => {
                proposal.prerequisites.directed1aOwnerIds.pop();
            },
            'INVALID_PREREQUISITE'
        );
        assertProposalError(
            proposal => {
                proposal.owners[0].owner = 'sigma-category';
            },
            'INVALID_OWNER_SET'
        );
        assertProposalError(
            proposal => {
                proposal.owners[1].slots[3].type
                    .arguments[0].callee.name = 'missing';
            },
            'INVALID_EXPRESSION'
        );
        assertProposalError(
            proposal => {
                delete proposal.owners[4].body;
            },
            'INVALID_DEFINITION_SET'
        );
    });

    it('rejects rule, runtime-policy, binding, MVP, and exact-content drift', () => {
        assertProposalError(
            proposal => {
                proposal.runtimeRules.pop();
            },
            'INVALID_RULE_SET'
        );
        assertProposalError(
            proposal => {
                proposal.runtimeExtensionPolicy.defaultLfProfile = 'changed';
            },
            'INVALID_RUNTIME_POLICY'
        );
        assertProposalError(
            () => undefined,
            'PROPOSAL_DRIFT',
            bindings => {
                bindings[0].serializedName = 'Sigma_cat';
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
                proposal.explicitDeferrals.pop();
            },
            'PROPOSAL_DRIFT'
        );
    });
});
