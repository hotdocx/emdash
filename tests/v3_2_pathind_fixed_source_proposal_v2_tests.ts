/**
 * Focused corrected-v2 proposal tests for fixed-source PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL
} from '../src/v3_2/pathind_fixed_source_proposal';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2,
    CorePathindFixedSource1cProposalV2,
    CorePathindFixedSource1cProposalV2Error,
    validateCorePathindFixedSource1cProposalV2
} from '../src/v3_2/pathind_fixed_source_proposal_v2';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cProposalV2 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2
    )) as CorePathindFixedSource1cProposalV2;

const assertProposalError = (
    mutate: (proposal: CorePathindFixedSource1cProposalV2) => void,
    expected: CorePathindFixedSource1cProposalV2Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindFixedSource1cProposalV2(proposal),
        error =>
            error instanceof CorePathindFixedSource1cProposalV2Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected proposal v2', () => {
    it('preserves v1 and pins measured line-7865 counterevidence', () => {
        const proposal = validateCorePathindFixedSource1cProposalV2();
        assert.equal(Object.isFrozen(proposal), true);
        assert.deepEqual(
            [
                proposal.parent.supersededProposalRevision,
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                proposal.parent.counterevidence.failureCode,
                proposal.parent.counterevidence.missingActiveAuthorityLine,
                proposal.parent.counterevidence
                    .predecessorTransfersHomConObjectProjection
            ],
            [
                CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL.revision,
                'cc639fc',
                '2deae91',
                'INVALID_RUNTIME_RULE_TYPE',
                7865,
                false
            ]
        );
    });

    it('adds only hom_con object projection to make 5/7/0/6', () => {
        const implementation =
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2.exactImplementation;
        assert.deepEqual(
            [
                implementation.trustedDeclarations.length,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.exactBoundary
            ],
            [5, 7, 0, 6, '5/7/0/6']
        );
        assert.deepEqual(
            implementation.runtimeRules.slice(1).map(rule => ({
                id: rule.id,
                authorityLine: rule.authorityLine
            })),
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL
                .exactImplementation.runtimeRules.map(rule => ({
                    id: rule.id,
                    authorityLine: rule.authorityLine
                }))
        );
        assert.deepEqual(
            [
                implementation.runtimeRules[0].id,
                implementation.runtimeRules[0].authorityLine,
                implementation.runtimeRules[0].sourceOwner,
                implementation.runtimeRules[0].resultOwner
            ],
            [
                'pathind.fixed-source.' +
                    'contravariant-representable-object',
                7865,
                'fapp0',
                'Hom_cat'
            ]
        );
    });

    it('rejects alternate bodies, checker changes, and duplicate owners',
        () => {
            const correction =
                CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2
                    .dependencyClosure
                    .contravariantRepresentableObjectCorrection;
            assert.deepEqual(
                [
                    correction.genericCheckerChangeAuthorized,
                    correction.alternativeFibCovBodyAuthorized,
                    correction.duplicateHomConDeclarationAuthorized
                ],
                [false, false, false]
            );
        });

    it('updates focused runtime and bounded-oracle evidence only', () => {
        const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V2;
        assert.equal(proposal.selectedRuntimeObservations.length, 4);
        assert.equal(proposal.boundedOracle.assertions.length, 8);
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
            'PATHIND_FIXED_SOURCE_V2_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).shift();
            },
            'PATHIND_FIXED_SOURCE_V2_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_V2_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_proposal_v2/u,
                path
            );
        }
    });
});
