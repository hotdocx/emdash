/**
 * Focused corrected-v4 proposal tests for fixed-source PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3
} from '../src/v3_2/pathind_fixed_source_proposal_v3';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4,
    CorePathindFixedSource1cProposalV4,
    CorePathindFixedSource1cProposalV4Error,
    validateCorePathindFixedSource1cProposalV4
} from '../src/v3_2/pathind_fixed_source_proposal_v4';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cProposalV4 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4
    )) as CorePathindFixedSource1cProposalV4;

const assertProposalError = (
    mutate: (proposal: CorePathindFixedSource1cProposalV4) => void,
    expected: CorePathindFixedSource1cProposalV4Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindFixedSource1cProposalV4(proposal),
        error =>
            error instanceof CorePathindFixedSource1cProposalV4Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected proposal v4', () => {
    it('preserves v3 and pins measured nested-head counterevidence', () => {
        const proposal = validateCorePathindFixedSource1cProposalV4();
        assert.equal(Object.isFrozen(proposal), true);
        assert.deepEqual(
            [
                proposal.parent.supersededProposalRevision,
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                proposal.parent.counterevidence.failureCode,
                proposal.parent.counterevidence.measuredOuterHead,
                proposal.parent.counterevidence.measuredNestedHead,
                proposal.parent.counterevidence
                    .line9177RegisteredButNestedHomCatNotNormalized
            ],
            [
                CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3.revision,
                'bfe09e3',
                '880593e',
                'INVALID_RUNTIME_RULE_TYPE',
                'Obj',
                'Hom_cat(Catd_cat(K),E,D)',
                true
            ]
        );
    });

    it('adds only one active-line fusion to make 5/9/0/6', () => {
        const implementation =
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4.exactImplementation;
        const fusion = implementation.runtimeRules[2] as {
            readonly id: string;
            readonly derivedFromAuthorityLines: readonly number[];
            readonly policy: string;
        };
        assert.deepEqual(
            [
                implementation.trustedDeclarations.length,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.exactBoundary
            ],
            [5, 9, 0, 6, '5/9/0/6']
        );
        assert.deepEqual(
            [
                fusion.id,
                fusion.derivedFromAuthorityLines,
                fusion.policy
            ],
            [
                'pathind.fixed-source.displayed-hom-object-fusion',
                [5481, 9177],
                'runtime-rewrite-derived-head-fusion'
            ]
        );
        assert.deepEqual(
            implementation.runtimeRules
                .filter((_, index) => index !== 2)
                .map(rule => rule.id),
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V3
                .exactImplementation.runtimeRules.map(rule => rule.id)
        );
    });

    it('freezes a subject-checked execution fusion, not new mathematics',
        () => {
            const fusion =
                CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4
                    .dependencyClosure.displayedHomObjectWeakHeadFusion;
            assert.deepEqual(
                [
                    fusion.executionStrategy,
                    fusion.subjectCheckedByGenericRuntimeCompiler,
                    fusion.newMathematicalRule,
                    fusion.nestedNormalizationEngineAuthorized,
                    fusion.genericCheckerChangeAuthorized,
                    fusion.canonicalSignatureSubstitutionAuthorized
                ],
                [
                    'head-only-no-nested-pattern-normalization',
                    true,
                    false,
                    false,
                    false,
                    false
                ]
            );
        });

    it('keeps consumer and oracle scope unchanged', () => {
        const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V4;
        assert.equal(proposal.selectedRuntimeObservations.length, 5);
        assert.equal(proposal.boundedOracle.assertions.length, 9);
        assert.equal(proposal.negativeConsumers.length, 8);
        assert.equal(proposal.typedLibraryConsumer.count, 1);
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent.counterevidence as {
                    line9177RegisteredButNestedHomCatNotNormalized: boolean;
                }).line9177RegisteredButNestedHomCatNotNormalized = false;
            },
            'PATHIND_FIXED_SOURCE_V4_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).splice(2, 1);
            },
            'PATHIND_FIXED_SOURCE_V4_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_V4_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_proposal_v4/u,
                path
            );
        }
    });
});
