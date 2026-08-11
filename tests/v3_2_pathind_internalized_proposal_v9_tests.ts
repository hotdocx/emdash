/**
 * Focused corrected-v9 proposal tests for internalized PathInd.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9,
    CorePathindInternalized1dProposalV9,
    CorePathindInternalized1dProposalV9Error,
    validateCorePathindInternalized1dProposalV9
} from '../src/v3_2/pathind_internalized_proposal_v9';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindInternalized1dProposalV9 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9
    )) as CorePathindInternalized1dProposalV9;

const assertProposalError = (
    mutate: (proposal: CorePathindInternalized1dProposalV9) => void,
    expected: CorePathindInternalized1dProposalV9Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindInternalized1dProposalV9(proposal),
        error =>
            error instanceof CorePathindInternalized1dProposalV9Error &&
            error.code === expected
    );
};

describe('PATHOUT-LIBRARY-INTERNALIZED-1D corrected proposal v9', () => {
    it('pins the exact v8 closed-module failure', () => {
        const proposal = validateCorePathindInternalized1dProposalV9();
        assert.equal(Object.isFrozen(proposal), true);
        const evidence = proposal.parent.counterevidence;
        assert.deepEqual(
            [
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                evidence.v8FailedBeforeRuntimeSubjectCheck,
                evidence.failingCode,
                evidence.failingPath,
                evidence.unresolvedGlobal,
                evidence.runtimeFragmentCompiledBeforeDerivedLibrary,
                evidence.pathIndSrcDeclarationIsInLaterDerivedLibrary
            ],
            [
                'f26d340',
                '1de3c95',
                true,
                'UNRESOLVED_GLOBAL',
                'module.referencedSymbols',
                'emdash.emdash3_2.PathIndSrc_catd',
                true,
                true
            ]
        );
    });

    it('replaces one support while retaining exactly 4/10/0/10', () => {
        const implementation =
            CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9.exactImplementation;
        assert.deepEqual(
            [
                implementation.trustedDeclarations.length,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.exactBoundary,
                implementation.mathematicalRuntimeProjectionCount,
                implementation.derivedRuntimeSupportRuleCount
            ],
            [4, 10, 0, 10, '4/10/0/10', 5, 5]
        );
        assert.deepEqual(
            implementation.runtimeRules.map(rule => rule.order),
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
        );
    });

    it('selects the closed post-Sigma parent with no forward reference', () => {
        const fusion = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9
            .dependencyClosure
            .pathInductionSourceFibrePostSigmaProjectionFusion;
        assert.deepEqual(
            [
                fusion.ruleId,
                fusion.left,
                fusion.right,
                fusion.exactStablePostSigmaProjectionParentSelected,
                fusion.usesOnlyEarlierDeclaredSymbols,
                fusion.replacedDerivedSupportRuleCount
            ],
            [
                'pathind.internalized.' +
                    'path-ind-source-fibre-post-sigma-projection-fusion',
                'fapp0(Fibre_cat(PathOutMotives_catd(Z),x),Cat_cat,' +
                    'PathOutReflEval_funcd(Z)[x],E)',
                'Fibre_cat(E,pathout_refl_obj(Z,x))',
                true,
                true,
                1
            ]
        );
        assert.deepEqual(
            [
                fusion.laterLibraryGlobalReferenceAuthorized,
                fusion.declarationRepartitionAuthorized,
                fusion.underlyingCategoryEqualityAuthorized,
                fusion.genericSigmaFibreRuleAuthorized,
                fusion.genericComparisonChangeAuthorized
            ],
            [false, false, false, false, false]
        );
    });

    it('preserves consumers, observations, negatives, and oracle scope', () => {
        const proposal = CORE_PATHIND_INTERNALIZED_1D_PROPOSAL_V9;
        assert.deepEqual(
            [
                proposal.typedLibraryConsumers.length,
                proposal.selectedRuntimeObservations.length,
                proposal.negativeConsumers.length,
                proposal.boundedOracle.assertions.length
            ],
            [2, 10, 10, 12]
        );
    });

    it('rejects authority, scope, and authorization drift', () => {
        assertProposalError(
            proposal => {
                (proposal.parent.counterevidence as {
                    unresolvedGlobal: string;
                }).unresolvedGlobal = 'wrong';
            },
            'PATHIND_INTERNALIZED_V9_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (
                    proposal.exactImplementation.runtimeRules as
                        unknown as unknown[]
                ).pop();
            },
            'PATHIND_INTERNALIZED_V9_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_INTERNALIZED_V9_AUTHORIZATION_DRIFT'
        );
    });

    it('does not enter contributor, npm, workspace, or browser barrels', () => {
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
                /pathind_internalized_proposal_v9/u,
                path
            );
        }
    });
});
