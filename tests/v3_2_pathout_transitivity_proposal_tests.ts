/**
 * Focused tests for the non-authorizing PathOut transitivity proposal.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL,
    CorePathoutTransitivity1eProposal,
    CorePathoutTransitivity1eProposalError,
    cloneCorePathoutTransitivity1eProposal,
    validateCorePathoutTransitivity1eProposal
} from '../src/v3_2/pathout_transitivity_proposal';

const repositoryRoot = resolve(__dirname, '..');

const assertProposalError = (
    mutate: (proposal: CorePathoutTransitivity1eProposal) => void,
    code: CorePathoutTransitivity1eProposalError['code']
): void => {
    const proposal = cloneCorePathoutTransitivity1eProposal();
    mutate(proposal);
    assert.throws(
        () => validateCorePathoutTransitivity1eProposal(proposal),
        error =>
            error instanceof CorePathoutTransitivity1eProposalError &&
            error.code === code
    );
};

describe('PATHOUT-LIBRARY-TRANSITIVITY-1E proposal', () => {
    it('pins the completed internalized predecessor and active authority',
        () => {
            const proposal = validateCorePathoutTransitivity1eProposal();
            assert.equal(Object.isFrozen(proposal), true);
            assert.deepEqual(
                [
                    proposal.parent.internalizedRevision,
                    proposal.parent.internalizedReviewedAuthorization,
                    proposal.parent.internalizedSemanticCheckpoint,
                    proposal.parent.internalizedLedgerCheckpoint,
                    proposal.parent.internalizedBoundary,
                    proposal.parent.activeLambdapiOwnerDelta,
                    proposal.parent.activeLambdapiRuleDelta
                ],
                [
                    'PATHOUT-LIBRARY-INTERNALIZED-1D-TRANSFER-14',
                    'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-14',
                    'b6005b3',
                    '6225075',
                    '4/13/0/10',
                    0,
                    0
                ]
            );
        });

    it('selects exactly five transparent declarations in source order',
        () => {
            const definitions = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL
                .exactImplementation.transparentDefinitions;
            assert.deepEqual(
                definitions.map(entry => [
                    entry.order,
                    entry.name,
                    entry.authorityLine,
                    entry.sourceKind,
                    entry.sourceOpacity,
                    entry.sourceRigidity,
                    entry.policy
                ]),
                [
                    [
                        0,
                        'CompTarget_catd',
                        19363,
                        'injective-symbol',
                        'transparent',
                        'injective',
                        'checked-transparent-definition'
                    ],
                    [
                        1,
                        'CompTarget_fapp1_func',
                        19381,
                        'symbol',
                        'transparent',
                        'ordinary',
                        'checked-transparent-definition'
                    ],
                    [
                        2,
                        'CompMotive_catd',
                        19401,
                        'symbol',
                        'transparent',
                        'ordinary',
                        'checked-transparent-definition'
                    ],
                    [
                        3,
                        'path_comp_sec',
                        19687,
                        'symbol',
                        'transparent',
                        'ordinary',
                        'checked-transparent-definition'
                    ],
                    [
                        4,
                        'path_comp_func',
                        19701,
                        'symbol',
                        'transparent',
                        'ordinary',
                        'checked-transparent-definition'
                    ]
                ]
            );
        });

    it('freezes a behavior-free 0/0/0/5 TypeScript delta', () => {
        const implementation = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL
            .exactImplementation;
        assert.deepEqual(
            [
                implementation.exactBoundary,
                implementation.trustedDeclarations.length,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.sourceInjectiveModifierRecordedAsMetadata,
                implementation.typescriptInjectivityBehaviorAdded,
                implementation.typescriptIntrinsicCoreOwnerAdded,
                implementation.genericCheckerBranchAdded,
                implementation.genericEvaluatorBranchAdded,
                implementation.genericRuntimeOrProofRuleAdded
            ],
            [
                '0/0/0/5',
                0,
                0,
                0,
                5,
                true,
                false,
                false,
                false,
                false,
                false
            ]
        );
    });

    it('freezes consumers, observations, negatives, and the bounded oracle',
        () => {
            const proposal = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL;
            assert.deepEqual(
                [
                    proposal.requiredExistingProviders.length,
                    proposal.typedLibraryConsumers.length,
                    proposal.selectedDefinitionalObservations.length,
                    proposal.negativeConsumers.length,
                    proposal.boundedOracle.assertions.length,
                    proposal.boundedOracle.timeoutMs
                ],
                [11, 2, 8, 8, 8, 20_000]
            );
            assert.equal(
                proposal.profileSealing
                    .transitivityClaimStopsAtStablePrecompositionNormalForm,
                true
            );
            assert.equal(
                proposal.profileSealing
                    .rawCompositionComparisonRemainsProofTimeInActiveLambdapi,
                true
            );
        });

    it('matches all five active source declarations and bodies', () => {
        const lines = readFileSync(
            resolve(repositoryRoot, 'emdash2/emdash3_2.lp'),
            'utf8'
        ).split(/\r?\n/u);
        for (
            const entry of
                CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL
                    .authority.selectedDeclarations
        ) {
            const prefix = entry.sourceKind === 'injective-symbol'
                ? 'injective symbol'
                : 'symbol';
            assert.match(
                lines[entry.authorityLine - 1],
                new RegExp(`^${prefix} ${entry.name}\\b`, 'u'),
                entry.name
            );
            const nextDeclaration = lines.findIndex(
                (line, index) =>
                    index >= entry.authorityLine &&
                    /^(?:injective |constant )?symbol\s/u.test(line)
            );
            const end = nextDeclaration < 0
                ? lines.length
                : nextDeclaration;
            assert.equal(
                lines
                    .slice(entry.authorityLine - 1, end)
                    .some(line => line.includes('≔')),
                true,
                entry.name
            );
        }
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent as {
                    internalizedSemanticCheckpoint: string;
                }).internalizedSemanticCheckpoint = 'wrong';
            },
            'PATHOUT_TRANSITIVITY_PROPOSAL_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.exactImplementation as {
                    typescriptInjectivityBehaviorAdded: boolean;
                }).typescriptInjectivityBehaviorAdded = true;
            },
            'PATHOUT_TRANSITIVITY_PROPOSAL_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHOUT_TRANSITIVITY_PROPOSAL_AUTHORIZATION_DRIFT'
        );
    });

    it('remains non-public and non-authorizing', () => {
        const proposal = CORE_PATHOUT_TRANSITIVITY_1E_PROPOSAL;
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
                /pathout_transitivity/u,
                relative
            );
        }
    });
});
