/** Focused tests for the non-authorizing PathOut library graduation proposal. */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL,
    CorePathoutLibraryGraduation0gProposal,
    CorePathoutLibraryGraduation0gProposalError,
    cloneCorePathoutLibraryGraduation0gProposal,
    validateCorePathoutLibraryGraduation0gProposal
} from '../src/v3_2/pathout_library_graduation_proposal';

const repositoryRoot = resolve(__dirname, '..');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen((value as Record<PropertyKey, unknown>)[key])
    );
};

describe('PATHOUT-TRUSTED-LIBRARY-GRADUATE-0G proposal', () => {
    it('pins every completed semantic and presentation predecessor', () => {
        const proposal = validateCorePathoutLibraryGraduation0gProposal();
        assertDeepFrozen(proposal);
        assert.equal(
            proposal.revision,
            'PATHOUT-TRUSTED-LIBRARY-GRADUATE-0G-PROPOSAL-1'
        );
        assert.equal(proposal.status, 'ready-for-separate-review');
        assert.deepEqual(proposal.parent, {
            trustAuditRevision: 'PATHOUT-TRUST-BOUNDARY-0A-AUDIT-1',
            trustAuditCheckpoint: 'a05493b',
            activeSourceSha256:
                'sha256:' +
                '0a117742d326bad82fe72cc73c624a0c174e3b48dd4047ebd8f6ed6ff7837860',
            activeChecksSha256:
                'sha256:' +
                'fbbe7ed4b7675c46ad79f65e2f6799dfc3c87b9287b593e6f1f0e1bd8e37f26a',
            foundationSemanticCheckpoint: '550316a',
            foundationLedgerCheckpoint: '349b6d4',
            fixedSourceSemanticCheckpoint: 'a361dc3',
            fixedSourceLedgerCheckpoint: '033dbb8',
            genericClosureCheckpoint: 'e560551',
            internalizedSemanticCheckpoint: 'b6005b3',
            internalizedLedgerCheckpoint: '6225075',
            transitivitySemanticCheckpoint: '3b113ad',
            transitivityLedgerCheckpoint: '10432ba',
            presentationProposalCheckpoint: '6ad0812',
            presentationReviewCheckpoint: 'f03ef01',
            presentationSemanticCheckpoint: '8d226cc',
            presentationLedgerCheckpoint: 'be487c9'
        });
    });

    it('separates five mathematical owners from nine sealed supports', () => {
        const trusted =
            CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL.sealedTrustedProfile;
        assert.deepEqual(trusted.mathematicalOpaqueOwners, [
            'PathOutReflEval_funcd',
            'path_ind_sec',
            'path_ind_func_fapp0',
            'PathInd_func',
            'PathInd_transfd'
        ]);
        assert.equal(trusted.mathematicalOpaqueOwnerCount, 5);
        assert.equal(trusted.sealedSupportingOwnerCount, 9);
        assert.equal(trusted.totalLocalSealedDeclarationCount, 14);
        assert.equal(trusted.runtimeRuleCount, 39);
        assert.equal(trusted.proofRuleCount, 2);
        assert.equal(trusted.ordinaryUsersMayAddOpaqueOwners, false);
        assert.equal(trusted.ordinaryUsersMayAddRuntimeRules, false);
        assert.equal(trusted.ordinaryUsersMayAddProofRules, false);
    });

    it('graduates exactly thirty transparent definitions by local slice',
        () => {
            const proposal = CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL;
            assert.equal(
                proposal.transparentDerivedLibrary.definitionCount,
                30
            );
            assert.equal(
                new Set(
                    proposal.transparentDerivedLibrary.definitionNames
                ).size,
                30
            );
            assert.deepEqual(
                proposal.localSliceBoundaries.map(boundary => [
                    boundary.exact,
                    boundary.sealedDeclarations,
                    boundary.runtimeRules,
                    boundary.proofRules,
                    boundary.transparentDefinitions
                ]),
                [
                    ['5/13/2/9', 5, 13, 2, 9],
                    ['5/12/0/6', 5, 12, 0, 6],
                    ['4/13/0/10', 4, 13, 0, 10],
                    ['0/1/0/5', 0, 1, 0, 5]
                ]
            );
        });

    it('states the bounded computation and presentation envelope', () => {
        const proposal = CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL;
        assert.equal(
            proposal.computationEnvelope.fixedSourcePointAndArrowComputation,
            true
        );
        assert.equal(
            proposal.computationEnvelope.internallyVaryingSourceAction,
            true
        );
        assert.equal(
            proposal.computationEnvelope.compositionNormalFormTarget,
            'stable-representable-precomposition'
        );
        assert.equal(
            proposal.computationEnvelope.pathCategoryComparisonLibraryIncluded,
            false
        );
        assert.equal(proposal.presentation.formCount, 4);
        assert.equal(proposal.presentation.browserLoadsSemanticTransfer, false);
        assert.equal(
            proposal.presentation.declarationOrBinderParserIncluded,
            false
        );
    });

    it('graduates source qualification without a public/package effect', () => {
        const proposal = CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL;
        assert.equal(proposal.distribution.contributorSourceQualified, true);
        assert.equal(proposal.distribution.contributorBarrelExported, false);
        assert.equal(proposal.distribution.npmBarrelExported, false);
        assert.equal(proposal.distribution.npmVersionChanged, false);
        assert.equal(proposal.distribution.releaseOrRegistryEffect, false);
        assert.equal(proposal.decision.proposalIsSelfAuthorizing, false);
        assert.equal(
            proposal.decision.separateImmutableReviewRequired,
            true
        );
        assert.ok(proposal.doesNotAuthorize.includes(
            'general inductive, HIT, or categorical-HIT declarations'
        ));
        assert.ok(proposal.doesNotAuthorize.includes(
            'package version, publication, release, push, merge, or deployment'
        ));
    });

    it('rejects prerequisite, classification, and general proposal drift',
        () => {
            const prerequisite = cloneCorePathoutLibraryGraduation0gProposal();
            (prerequisite.parent as {
                presentationSemanticCheckpoint: string;
            }).presentationSemanticCheckpoint = 'wrong';
            assert.throws(
                () => validateCorePathoutLibraryGraduation0gProposal(
                    prerequisite
                ),
                error =>
                    error instanceof
                        CorePathoutLibraryGraduation0gProposalError &&
                    error.code === 'PATHOUT_GRADUATION_PREREQUISITE_DRIFT'
            );

            const classification =
                cloneCorePathoutLibraryGraduation0gProposal();
            (classification.sealedTrustedProfile as {
                runtimeRuleCount: number;
            }).runtimeRuleCount = 40;
            assert.throws(
                () => validateCorePathoutLibraryGraduation0gProposal(
                    classification
                ),
                error =>
                    error instanceof
                        CorePathoutLibraryGraduation0gProposalError &&
                    error.code === 'PATHOUT_GRADUATION_CLASSIFICATION_DRIFT'
            );

            const general = cloneCorePathoutLibraryGraduation0gProposal();
            (general.productProfile as { productionBackend: string })
                .productionBackend = 'other';
            assert.throws(
                () => validateCorePathoutLibraryGraduation0gProposal(general),
                error =>
                    error instanceof
                        CorePathoutLibraryGraduation0gProposalError &&
                    error.code === 'PATHOUT_GRADUATION_PROPOSAL_DRIFT'
            );
        });

    it('adds no behavior or public-barrel dependency', () => {
        const source = readFileSync(resolve(
            repositoryRoot,
            'src/v3_2/pathout_library_graduation_proposal.ts'
        ), 'utf8');
        assert.doesNotMatch(source, /compileCorePath/u);
        assert.doesNotMatch(source, /createCoreLfChecker/u);
        assert.doesNotMatch(source, /coreLfDefinitionalCompare/u);
        for (const relative of [
            'src/v3_2/index.ts',
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/browser.ts'
        ]) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, relative), 'utf8'),
                /pathout_library_graduation/u,
                relative
            );
        }
        const clone = cloneCorePathoutLibraryGraduation0gProposal();
        assert.notEqual(
            clone as CorePathoutLibraryGraduation0gProposal,
            CORE_PATHOUT_LIBRARY_GRADUATION_0G_PROPOSAL
        );
    });
});
