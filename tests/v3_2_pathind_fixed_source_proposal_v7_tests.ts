/**
 * Focused tests for corrected PATHIND-TRUSTED-PROFILE-1C proposal v7.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7,
    CorePathindFixedSource1cProposalV7,
    CorePathindFixedSource1cProposalV7Error,
    validateCorePathindFixedSource1cProposalV7
} from '../src/v3_2/pathind_fixed_source_proposal_v7';

const repositoryRoot = resolve(__dirname, '..');

const clone = (): CorePathindFixedSource1cProposalV7 =>
    JSON.parse(JSON.stringify(
        CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7
    )) as CorePathindFixedSource1cProposalV7;

const assertProposalError = (
    mutate: (proposal: CorePathindFixedSource1cProposalV7) => void,
    expected: CorePathindFixedSource1cProposalV7Error['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCorePathindFixedSource1cProposalV7(proposal),
        error =>
            error instanceof CorePathindFixedSource1cProposalV7Error &&
            error.code === expected
    );
};

describe('PATHIND-TRUSTED-PROFILE-1C corrected proposal v7', () => {
    it('preserves v6 and pins the first library residual', () => {
        const proposal = validateCorePathindFixedSource1cProposalV7();
        assert.equal(Object.isFrozen(proposal), true);
        assert.deepEqual(
            [
                proposal.parent.supersededProposalRevision,
                proposal.parent.supersededProposalCheckpoint,
                proposal.parent.supersededReviewCheckpoint,
                proposal.parent.counterevidence.compiledRuntimeRuleCount,
                proposal.parent.counterevidence
                    .allSelectedRuntimeRulesSubjectChecked,
                proposal.parent.counterevidence.failingDeclaration,
                proposal.parent.counterevidence.activeProofRule,
                proposal.parent.counterevidence
                    .declarationCompilerConsumesRuntimeButNotProofProgram
            ],
            [
                'PATHIND-TRUSTED-PROFILE-1C-PROPOSAL-6',
                'b41c3b0',
                '9b22034',
                11,
                true,
                'pathout_refl_eval_func',
                'categorical.dependent-target.category-presentation',
                true
            ]
        );
    });

    it('adds only the classifier-wrapped fusion to make 5/12/0/6', () => {
        const implementation =
            CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7.exactImplementation;
        const fusion = implementation.runtimeRules[5] as {
            readonly id: string;
            readonly derivedFromAuthorityLines: readonly number[];
            readonly sourceOwner: string;
            readonly resultOwner: string;
            readonly policy: string;
        };
        assert.deepEqual(
            [
                implementation.trustedDeclarations.length,
                implementation.runtimeRules.length,
                implementation.proofRules.length,
                implementation.transparentDefinitions.length,
                implementation.exactBoundary,
                fusion.id,
                fusion.sourceOwner,
                fusion.resultOwner,
                fusion.policy
            ],
            [
                5, 12, 0, 6, '5/12/0/6',
                'pathind.fixed-source.' +
                    'fixed-evaluation-source-presentation-fusion',
                'Functor', 'Functor',
                'runtime-rewrite-derived-type-presentation-fusion'
            ]
        );
        assert.deepEqual(
            implementation.runtimeRules.map(rule => rule.order),
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
        );
        assert.deepEqual(
            fusion.derivedFromAuthorityLines,
            [5457, 19067, 19068, 19069, 19072]
        );
    });

    it('keeps the bridge local, forward, and engine-neutral', () => {
        const fusion = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7
            .dependencyClosure.fixedEvaluationSourcePresentationFusion;
        assert.deepEqual(
            [
                fusion.exactLeft,
                fusion.exactRight,
                fusion
                    .wrapsProofTimeCategoryPresentationUnderFunctorClassifier,
                fusion.subjectCheckRequiredBeforeImplementationCheckpoint,
                fusion.directRuntimeFunctorCategoryCollapseAuthorized,
                fusion.genericDeclarationProofIntegrationAuthorized,
                fusion.genericCheckerChangeAuthorized,
                fusion.newMathematicalRule
            ],
            [
                'Functor(Functor_cat(K,Cat_cat),Cat_cat)',
                'Functor(Catd_cat(K),Cat_cat)',
                true, true, false, false, false, false
            ]
        );
    });

    it('keeps consumer and oracle scope unchanged', () => {
        const proposal = CORE_PATHIND_FIXED_SOURCE_1C_PROPOSAL_V7;
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
                (proposal.parent.counterevidence as {
                    failingDeclaration: string;
                }).failingDeclaration = 'wrong';
            },
            'PATHIND_FIXED_SOURCE_V7_AUTHORITY_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.exactImplementation as {
                    exactBoundary: string;
                }).exactBoundary = '5/11/0/6';
            },
            'PATHIND_FIXED_SOURCE_V7_SCOPE_DRIFT'
        );
        assertProposalError(
            proposal => {
                (proposal.decision as {
                    implementationAuthorized: boolean;
                }).implementationAuthorized = true;
            },
            'PATHIND_FIXED_SOURCE_V7_AUTHORIZATION_DRIFT'
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
                /pathind_fixed_source_proposal_v7/u,
                path
            );
        }
    });
});
