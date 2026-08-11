/**
 * Focused PATHOUT-LIBRARY-INTERNALIZED-1D proposal tests.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE
} from '../src/v3_2/categorical_displayed_chain_transfer';
import {
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_LINKAGE
} from '../src/v3_2/categorical_fibred_dependent_target_transfer';
import {
    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE
} from '../src/v3_2/categorical_fibred_transfd_transfer';
import {
    CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE
} from '../src/v3_2/directed_continuation_transfer';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_REVISION,
    CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
} from '../src/v3_2/pathind_fixed_source_transfer';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL,
    CorePathindInternalized1dProposal,
    CorePathindInternalized1dProposalError,
    validateCorePathindInternalized1dProposal
} from '../src/v3_2/pathind_internalized_proposal';
import {
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT
} from '../src/v3_2/pathout_trust_boundary_audit';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposal =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL
    )) as CorePathindInternalized1dProposal;

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposal) => void,
    expected: CorePathindInternalized1dProposalError['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposal(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalError &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D proposal', () => {
    it('pins completed fixed-source PathInd and remains non-authorizing',
        () => {
            const proposal =
                validateCorePathindInternalized1dProposal();
            assertDeepFrozen(proposal);
            assert.deepEqual(
                [
                    proposal.parent.fixedSourceRevision,
                    proposal.parent.fixedSourceSemanticCheckpoint,
                    proposal.parent.fixedSourceLedgerCheckpoint,
                    proposal.decision.status,
                    proposal.decision.implementationAuthorized
                ],
                [
                    CORE_PATHIND_FIXED_SOURCE_1C_REVISION,
                    'a361dc3',
                    '033dbb8',
                    'proposal-only',
                    false
                ]
            );
            assert.deepEqual(
                proposal.parent.fixedSourceBoundary,
                {
                    trustedDeclarationCount: 5,
                    runtimeRuleCount: 12,
                    proofRuleCount: 0,
                    transparentDefinitionCount: 6
                }
            );
            assert.equal(
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .internalizedPathInductionIncluded,
                false
            );
        });

    it('freezes exactly four opaque, four runtime, zero proof, ten transparent',
        () => {
            const implementation =
                CORE_PATHIND_INTERNALIZED_1D_PROPOSAL.exactImplementation;
            assert.equal(implementation.exactBoundary, '4/4/0/10');
            assert.deepEqual(
                implementation.trustedDeclarations.map(entry => entry.name),
                [
                    'Sigma_transfd_funcd',
                    'PathOutReflEval_funcd',
                    'PathInd_func',
                    'PathInd_transfd'
                ]
            );
            assert.deepEqual(
                implementation.runtimeRules.map(entry =>
                    entry.authorityLine
                ),
                [14516, 19084, 19248, 19409]
            );
            assert.equal(implementation.proofRules.length, 0);
            assert.deepEqual(
                implementation.transparentDefinitions.map(entry =>
                    entry.name
                ),
                [
                    'PathOutMotives_catd',
                    'PathOutPi_funcd',
                    'PathIndTgt_catd',
                    'pathout_motive_transport_obj',
                    'pathout_motive_transport_arrow',
                    'PathIndSrc_catd',
                    'PathIndSrc_transport_func',
                    'PathInd_funcd',
                    'pathout_pi_transport_func',
                    'PathIndTgt_transport_func'
                ]
            );
        });

    it('selects only the missing Sigma owner over existing providers', () => {
        const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL;
        const providerGroups = [
            {
                name: 'CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE',
                entries: CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries
            },
            {
                name: 'CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE',
                entries:
                    CORE_CATEGORICAL_FIBRED_TRANSFD_TRANSFER_LINKAGE.entries
            },
            {
                name: 'CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE',
                entries:
                    CORE_CATEGORICAL_DISPLAYED_CHAIN_TRANSFER_LINKAGE.entries
            },
            {
                name:
                    'CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_' +
                    'TRANSFER_LINKAGE',
                entries:
                    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_LINKAGE
                        .entries
            }
        ];
        for (
            const required of
            proposal.dependencyClosure.requiredExistingProviders
        ) {
            const provider = providerGroups.find(group =>
                group.name === required.provider
            );
            assert.notEqual(provider, undefined, required.provider);
            assert.equal(
                provider?.entries.some(entry =>
                    entry.symbol.name === required.name
                ),
                true,
                required.name
            );
        }
        assert.equal(
            providerGroups.some(group =>
                group.entries.some(entry =>
                    entry.symbol.name === 'Sigma_transfd_funcd'
                )
            ),
            false
        );
        assert.equal(
            proposal.dependencyClosure
                .sigmaUncurryingOwnerRequiresSelectedTransfer,
            true
        );
        assert.equal(
            proposal.dependencyClosure.importWholeScaleStress2b3Profile,
            false
        );
        assert.deepEqual(
            proposal.dependencyClosure.sigmaTotalUncurrying,
            CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT
                .prerequisiteClosures[3]
        );
    });

    it('preserves primary internal naturality and derived Sigma presentation',
        () => {
            const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL;
            assert.deepEqual(
                proposal.typedLibraryConsumers.map(entry => entry.name),
                ['PathInd_transfd', 'PathInd_funcd']
            );
            assert.equal(
                proposal.typedLibraryConsumers[0]
                    .externalNaturalitySquareRequired,
                false
            );
            assert.equal(
                proposal.typedLibraryConsumers[1].primitiveTheorem,
                false
            );
            assert.equal(proposal.selectedRuntimeObservations.length, 9);
            assert.equal(proposal.negativeConsumers.length, 10);
            assert.equal(proposal.boundedOracle.assertions.length, 11);
            assert.equal(
                proposal.dependencyClosure
                    .sourceArrowCollapsedToExternalEquation,
                false
            );
            assert.equal(
                proposal.dependencyClosure
                    .higherActionCollapsedToExternalEquation,
                false
            );
        });

    it('pins active authority positions and the staged dependency order',
        () => {
            const source = readFileSync(
                resolve(repositoryRoot, 'emdash2/emdash3_2.lp'),
                'utf8'
            ).split('\n');
            const implementation =
                CORE_PATHIND_INTERNALIZED_1D_PROPOSAL.exactImplementation;
            for (const declaration of implementation.trustedDeclarations) {
                assert.match(
                    source[declaration.authorityLine - 1],
                    new RegExp(declaration.name, 'u'),
                    declaration.name
                );
            }
            for (const definition of implementation.transparentDefinitions) {
                assert.match(
                    source[definition.authorityLine - 1],
                    new RegExp(definition.name, 'u'),
                    definition.name
                );
            }
            for (const rule of implementation.runtimeRules) {
                assert.match(
                    source[rule.authorityLine - 1],
                    /^rule\s/u,
                    rule.id
                );
            }
            assert.deepEqual(
                implementation.implementationStages.map(stage => stage.id),
                [
                    'sigma-uncurrying-trusted-prerequisite',
                    'internalized-transparent-prelude',
                    'internalized-trusted-theorem-package',
                    'internalized-runtime-projections',
                    'derived-internalized-library'
                ]
            );
        });

    it('keeps profile authority separate and all later effects denied',
        () => {
            const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL;
            assert.deepEqual(
                [
                    proposal.profileSealing
                        .publicSafeLibraryCanAddTransparentDefinitions,
                    proposal.profileSealing
                        .publicSafeLibraryCanAddOpaqueOwners,
                    proposal.profileSealing
                        .publicSafeLibraryCanAddRuntimeRules,
                    proposal.profileSealing
                        .publicSafeLibraryCanAddProofRules,
                    proposal.profileSealing.packageOrBrowserExportAuthorized
                ],
                [true, false, false, false, false]
            );
            assert.equal(
                proposal.dependencyClosure.transitivityDefinitionsIncluded,
                false
            );
            assert.equal(
                proposal.dependencyClosure.pathCategoryProofBridgeIncluded,
                false
            );
            assert.equal(
                proposal.gitBoundary.pushMergePublishAuthorized,
                false
            );
        });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent as {
                    fixedSourceSemanticCheckpoint: string;
                }).fixedSourceSemanticCheckpoint = 'wrong';
            },
            'PATHIND_INTERNALIZED_PROPOSAL_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_PROPOSAL_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_PROPOSAL_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, workspace, or browser barrels',
        () => {
            for (
                const path of [
                    'src/v3_2/index.ts',
                    'src/v3_2/package_core.ts',
                    'src/v3_2/package_authoring.ts',
                    'src/v3_2/package_workspace.ts',
                    'src/v3_2/browser.ts'
                ]
            ) {
                assert.doesNotMatch(
                    readFileSync(resolve(repositoryRoot, path), 'utf8'),
                    /pathind_internalized|CORE_PATHIND_INTERNALIZED/u,
                    path
                );
            }
        });
});
