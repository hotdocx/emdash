/**
 * Focused corrected-v3 proposal tests for fixed-source PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2
} from '../src/v3_2/pathind_fixed_source_proposal_v2';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3,
    CorePathindFixedSource1cProposalV3,
    CorePathindFixedSource1cProposalV3Error,
    validateCorePathindFixedSource1cProposalV3
} from '../src/v3_2/pathind_fixed_source_proposal_v3';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cProposalV3 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3
    )) as CorePathindFixedSource1cProposalV3;

const assertProposalError = (
    mutate: (proposal: CorePathindFixedSource1cProposalV3) => void,
    expected: CorePathindFixedSource1cProposalV3Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindFixedSource1cProposalV3(proposal),
        error =>
            error instanceof CorePathindFixedSource1cProposalV3Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected proposal v3', () => {
    it('preserves v2 and pins measured line-9177 counterevidence', () => {
        const proposal = validateCorePathindFixedSource1cProposalV3();
        assert.equal(Object.isFrozen(proposal), true);
        assert.deepEqual(
            [
                proposal.parent.supersededProposalRevision,
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                proposal.parent.counterevidence.failureCode,
                proposal.parent.counterevidence.missingActiveAuthorityLine,
                proposal.parent.counterevidence
                    .line7865AdmitsFirstTwoFibCovProjections,
                proposal.parent.counterevidence
                    .predecessorTransfersFunctordObjectProjection
            ],
            [
                CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2.revision,
                '7413dd6',
                '3421647',
                'INVALID_RUNTIME_RULE_TYPE',
                9177,
                true,
                false
            ]
        );
    });

    it('adds only the displayed object bridge to make 5/8/0/6', () => {
        const implementation =
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3.exactImplementation;
        assert.deepEqual(
            [
                implementation.trustedDeclarations.length,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.exactBoundary
            ],
            [5, 8, 0, 6, '5/8/0/6']
        );
        assert.deepEqual(
            [
                implementation.runtimeRules[1].id,
                implementation.runtimeRules[1].authorityLine,
                implementation.runtimeRules[1].sourceOwner,
                implementation.runtimeRules[1].resultOwner
            ],
            [
                'pathind.fixed-source.displayed-functor-object',
                9177,
                'Obj',
                'Obj'
            ]
        );
        assert.deepEqual(
            implementation.runtimeRules
                .filter((_, index) => index !== 1)
                .map(rule => ({
                    id: rule.id,
                    authorityLine: rule.authorityLine
                })),
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2
                .exactImplementation.runtimeRules.map(rule => ({
                    id: rule.id,
                    authorityLine: rule.authorityLine
                }))
        );
    });

    it('requires exact active signatures and rejects checker substitutes',
        () => {
            const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3;
            const correction =
                proposal.dependencyClosure
                    .displayedFunctorObjectCorrection;
            assert.equal(
                proposal.parent.counterevidence
                    .exactActiveFibreSignaturesRestored,
                true
            );
            assert.deepEqual(
                [
                    correction.genericCheckerChangeAuthorized,
                    correction.canonicalSignatureSubstitutionAuthorized,
                    correction.duplicateClassifierDeclarationAuthorized
                ],
                [false, false, false]
            );
        });

    it('updates focused runtime and bounded-oracle evidence only', () => {
        const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3;
        assert.equal(proposal.selectedRuntimeObservations.length, 5);
        assert.equal(proposal.boundedOracle.assertions.length, 9);
        assert.equal(proposal.negativeConsumers.length, 8);
        assert.equal(proposal.typedLibraryConsumer.count, 1);
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent.counterevidence as {
                    missingActiveAuthorityLine: number;
                }).missingActiveAuthorityLine = 0;
            },
            'PATHIND_FIXED_SOURCE_V3_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).splice(1, 1);
            },
            'PATHIND_FIXED_SOURCE_V3_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_V3_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_proposal_v3/u,
                path
            );
        }
    });
});
