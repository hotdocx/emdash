/**
 * Focused PATHIND-TRUSTED-PROFILE-1C proposal tests.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL,
    CorePathindFixedSource1cProposal,
    CorePathindFixedSource1cProposalError,
    validateCorePathindFixedSource1cProposal
} from '../src/v3_2/pathind_fixed_source_proposal';
import {
    CORE_PATHOUT_FOUNDATION_1B_REVISION,
    CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
} from '../src/v3_2/pathout_foundation_transfer';
import {
    CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT
} from '../src/v3_2/pathout_trust_boundary_audit';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cProposal =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL
    )) as CorePathindFixedSource1cProposal;

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
    mutate: (proposal: CorePathindFixedSource1cProposal) => void,
    expected: CorePathindFixedSource1cProposalError['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindFixedSource1cProposal(proposal),
        error =>
            error instanceof CorePathindFixedSource1cProposalError &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C proposal', () => {
    it('pins the completed PathOut foundation and stays non-authorizing',
        () => {
            const proposal = validateCorePathindFixedSource1cProposal();
            assertDeepFrozen(proposal);
            assert.deepEqual(
                [
                    proposal.parent.foundationRevision,
                    proposal.parent.foundationSemanticCheckpoint,
                    proposal.parent.foundationLedgerCheckpoint,
                    proposal.decision.status,
                    proposal.decision.implementationAuthorized
                ],
                [
                    CORE_PATHOUT_FOUNDATION_1B_REVISION,
                    '550316a',
                    '349b6d4',
                    'proposal-only',
                    false
                ]
            );
            assert.deepEqual(
                proposal.parent.foundationBoundary,
                {
                    prerequisiteDeclarationCount: 5,
                    runtimeRuleCount: 13,
                    proofRuleCount: 2,
                    transparentLibraryDefinitionCount: 9
                }
            );
            assert.equal(
                CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                    .fixedSourcePathInductionIncluded,
                false
            );
        });

    it('freezes exactly five opaque, six runtime, zero proof, six transparent',
        () => {
            const implementation =
                CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL
                    .exactImplementation;
            assert.equal(implementation.exactBoundary, '5/6/0/6');
            assert.deepEqual(
                implementation.trustedDeclarations.map(entry => entry.name),
                [
                    'fib_cov_int',
                    'fib_cov_src_func',
                    'fib_cov_transf',
                    'path_ind_sec',
                    'path_ind_func_fapp0'
                ]
            );
            assert.deepEqual(
                implementation.runtimeRules.map(entry => entry.authorityLine),
                [13965, 13975, 13979, 19234, 19418, 19441]
            );
            assert.equal(implementation.proofRules.length, 0);
            assert.deepEqual(
                implementation.transparentDefinitions.map(entry =>
                    entry.name
                ),
                [
                    'FibCov_target_catd',
                    'pathout_refl_eval_func',
                    'pathout_refl_eval_base_func',
                    'pathout_refl_arrow_sec',
                    'PathInd_src_catd',
                    'PathInd_tgt_catd'
                ]
            );
        });

    it('selects the full audited covariant cascade without its alias',
        () => {
            const closure =
                CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL
                    .dependencyClosure.covariantFibre;
            assert.deepEqual(
                closure.opaqueOwners.map(entry => entry.name),
                ['fib_cov_int', 'fib_cov_src_func', 'fib_cov_transf']
            );
            assert.deepEqual(
                closure.runtimeRules.map(entry => entry.line),
                [13965, 13975, 13979]
            );
            assert.equal(
                closure.transparentDefinitions[0].name,
                'FibCov_target_catd'
            );
            assert.equal(
                closure.excludedAuxiliaryDefinitions[0].name,
                'FibCov_source_catd'
            );
            assert.deepEqual(
                closure,
                CORE_PATHOUT_TRUST_BOUNDARY_0A_AUDIT
                    .prerequisiteClosures[2]
            );
        });

    it('defers coherent and varying-source packages to 1D', () => {
        const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL;
        assert.deepEqual(
            proposal.dependencyClosure.selectedFixedSource
                .deferredOwnerNames,
            ['PathInd_func']
        );
        assert.deepEqual(
            proposal.deferred.internalizedOwners,
            [
                'PathOutReflEval_funcd',
                'PathInd_func',
                'PathInd_transfd'
            ]
        );
        assert.equal(
            proposal.dependencyClosure.internalizedInductionIncluded,
            false
        );
        assert.equal(
            proposal.dependencyClosure.transitivityDefinitionsIncluded,
            false
        );
        assert.equal(
            proposal.dependencyClosure.pathCategoryProofBridgeIncluded,
            false
        );
    });

    it('selects one typed library witness and bounded conformance', () => {
        const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL;
        assert.deepEqual(
            [
                proposal.typedLibraryConsumer.count,
                proposal.typedLibraryConsumer.name,
                proposal.typedLibraryConsumer.usesDirectTypedCore,
                proposal.typedLibraryConsumer.publicFacadeAuthorized
            ],
            [1, 'pathout_refl_arrow_sec', true, false]
        );
        assert.equal(proposal.selectedRuntimeObservations.length, 3);
        assert.equal(proposal.negativeConsumers.length, 8);
        assert.deepEqual(
            [
                proposal.boundedOracle.timeoutMs,
                proposal.boundedOracle.assertions.length,
                proposal.boundedOracle.requiredForImplementationAcceptance,
                proposal.boundedOracle.requiredForProposalAcceptance
            ],
            [20_000, 7, true, false]
        );
    });

    it('keeps profile authority distinct from safe library authority',
        () => {
            const sealing =
                CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL.profileSealing;
            assert.deepEqual(
                [
                    sealing.publicSafeLibraryCanAddTransparentDefinitions,
                    sealing.publicSafeLibraryCanAddOpaqueOwners,
                    sealing.publicSafeLibraryCanAddRuntimeRules,
                    sealing.publicSafeLibraryCanAddProofRules,
                    sealing.lowLevelAuthoringApiRemainsExplicitlyTrustBearing
                ],
                [true, false, false, false, true]
            );
        });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent as {
                    foundationSemanticCheckpoint: string;
                }).foundationSemanticCheckpoint = 'wrong';
            },
            'PATHIND_FIXED_SOURCE_PROPOSAL_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).pop();
            },
            'PATHIND_FIXED_SOURCE_PROPOSAL_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_PROPOSAL_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, or browser barrels', () => {
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
                /pathind_fixed_source_proposal|CORE_PATHIND_FIXED_SOURCE/u,
                path
            );
        }
    });
});
