/**
 * Focused tests for corrected PATHIND-TRUSTED-PROFILE-1C proposal v5.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5,
    CorePathindFixedSource1cProposalV5,
    CorePathindFixedSource1cProposalV5Error,
    validateCorePathindFixedSource1cProposalV5
} from '../src/v3_2/pathind_fixed_source_proposal_v5';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cProposalV5 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5
    )) as CorePathindFixedSource1cProposalV5;

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
    mutate: (proposal: CorePathindFixedSource1cProposalV5) => void,
    expected: CorePathindFixedSource1cProposalV5Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindFixedSource1cProposalV5(proposal),
        error =>
            error instanceof CorePathindFixedSource1cProposalV5Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected proposal v5', () => {
    it('preserves v4 and pins measured Transf-delta counterevidence', () => {
        const proposal = validateCorePathindFixedSource1cProposalV5();
        assertDeepFrozen(proposal);
        assert.deepEqual(
            [
                proposal.parent.supersededProposalRevision,
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                proposal.parent.counterevidence
                    .displayedHomObjectFusionSubjectChecked,
                proposal.parent.counterevidence
                    .predecessorImportsDeclarationLinkageButOmitsRuntimeDelta,
                proposal.parent.counterevidence
                    .activeTransparentDeltaAuthorityLines
            ],
            [
                'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-4',
                'f4101e2',
                '397472f',
                true,
                true,
                [9150, 9151]
            ]
        );
    });

    it('adds only the active Transf delta to make 5/10/0/6', () => {
        const implementation =
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5.exactImplementation;
        assert.deepEqual(
            [
                implementation.trustedDeclarations.length,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.exactBoundary,
                implementation.runtimeRules[3]
            ],
            [
                5,
                10,
                0,
                6,
                '5/10/0/6',
                {
                    order: 3,
                    id: 'pathind.fixed-source.transfor-classifier-delta',
                    authorityLine: 9151,
                    authorityLines: [9150, 9151],
                    sourceOwner: 'Transf',
                    resultOwner: 'Obj',
                    policy:
                        'runtime-rewrite-active-transparent-definition'
                }
            ]
        );
        assert.deepEqual(
            implementation.runtimeRules.map(rule => rule.order),
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
        );
    });

    it('imports a source delta without changing owners or engines', () => {
        const delta = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5
            .dependencyClosure.transforClassifierTransparentDelta;
        assert.deepEqual(
            [
                delta.activeAuthorityLines,
                delta.absentFromSelectedPredecessorRuntimeChain,
                delta.declarationOwnerAlreadyPresent,
                delta.duplicateDeclarationAuthorized,
                delta.newMathematicalRule,
                delta.genericCheckerChangeAuthorized,
                delta.reversedActiveReductionAuthorized
            ],
            [[9150, 9151], true, true, false, false, false, false]
        );
    });

    it('keeps consumer and oracle scope unchanged', () => {
        const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V5;
        assert.deepEqual(
            [
                proposal.typedLibraryConsumer.count,
                proposal.negativeConsumers.length,
                proposal.selectedRuntimeObservations.length,
                proposal.boundedOracle.assertions.length
            ],
            [1, 8, 5, 9]
        );
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent.counterevidence as unknown as {
                    activeTransparentDeltaAuthorityLines: number[];
                }).activeTransparentDeltaAuthorityLines = [9151];
            },
            'PATHIND_FIXED_SOURCE_V5_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.exactImplementation as {
                    exactBoundary: string;
                }).exactBoundary = '5/9/0/6';
            },
            'PATHIND_FIXED_SOURCE_V5_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_V5_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_proposal_v5/u,
                path
            );
        }
    });
});
