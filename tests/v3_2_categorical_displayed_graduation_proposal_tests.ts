/**
 * Executable DISPLAYED-BRACKET-GRADUATE-1 proposal evidence.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL,
    CoreCategoricalDisplayedGraduationProposalError,
    validateCoreCategoricalDisplayedGraduationProposal
} from '../src/v3_2';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL
));

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
    mutate: (proposal: any) => void,
    expected:
        CoreCategoricalDisplayedGraduationProposalError['code']
): void => {
    const proposal = clone();
    mutate(proposal);
    assert.throws(
        () => validateCoreCategoricalDisplayedGraduationProposal(
            proposal
        ),
        error =>
            error instanceof
                CoreCategoricalDisplayedGraduationProposalError &&
            error.code === expected
    );
};

describe(
    'TypeScript v3.2 DISPLAYED-BRACKET-GRADUATE-1 proposal',
    () => {
        it('recommends only the exact qualified displayed envelope', () => {
            const proposal =
                CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL;
            assert.equal(
                proposal.reviewGate,
                'H-DTTLF-USABILITY-DISPLAYED-GRADUATE-01'
            );
            assert.equal(
                proposal.decisionId,
                'D-DTTLF-USABILITY-016'
            );
            assert.equal(
                proposal.recommendation
                    .mechanicallyReusableWithinEnvelope,
                true
            );
            assert.equal(
                proposal.recommendation
                    .ordinaryAndDisplayedWorkDiscardedOrBacktracked,
                false
            );
            assert.equal(
                proposal.recommendation.arbitraryTelescopeDepthClaimed,
                false
            );
            assert.equal(
                proposal.recommendation.generalNdCoherenceComplete,
                false
            );
        });

        it('pins the existing callback-to-Core architecture', () => {
            const proposal =
                CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL;
            assert.equal(proposal.compilationPipeline.length, 8);
            assert.deepEqual(
                proposal.architectureDistinction
                    .normalizedContextualIrVocabulary,
                [
                    'slot-reference',
                    'explicit-closed-core-term',
                    'typed-application',
                    'typed-pair',
                    'typed-composition'
                ]
            );
            assert.deepEqual(
                proposal.architectureDistinction
                    .ordinarySupportedRecursiveNodes,
                [
                    'slot-reference',
                    'explicit-closed-core-term',
                    'qualified-typed-application',
                    'nested-supported-abstraction'
                ]
            );
            assert.deepEqual(
                proposal.architectureDistinction
                    .displayedSupportedRecursiveNodes,
                [
                    'slot-reference',
                    'typed-fibre-pair',
                    'closed-displayed-functor-application',
                    'stable-displayed-evaluation-application'
                ]
            );
            assert.equal(
                proposal.architectureDistinction
                    .displayedExplicitCoreOrNestedAbstractionSupported,
                false
            );
            assert.equal(
                proposal.architectureDistinction
                    .secondRawAstOrCheckerRequired,
                false
            );
            assert.equal(
                proposal.architectureDistinction.stringParserRequired,
                false
            );
        });

        it('separates recursive bodies from the bounded presentation', () => {
            const distinction =
                CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL
                    .architectureDistinction;
            assert.match(
                distinction.recursiveBodyCompiler,
                /variables-may-occur-freely/u
            );
            assert.equal(
                distinction.contextPresentationCompiler,
                'independent-common-base-block-or-exact-one-genuine-edge'
            );
            assert.equal(distinction.presentDependentArity, 2);
            assert.equal(
                distinction.presentDependentShape,
                'k : K; a : A[k]; b : B[(k,a)]'
            );
            assert.equal(
                distinction.recursionImpliesArbitraryDepth,
                false
            );
        });

        it('freezes all nine implemented evidence classes', () => {
            const proposal =
                CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL;
            assert.deepEqual(
                proposal.evidenceMatrix.map(entry => entry.id),
                [
                    'outer-lf',
                    'ordinary-bracket',
                    'independent-displayed-siblings',
                    'stable-displayed-evaluation',
                    'direct-fd',
                    'direct-nd',
                    'weakening-reindexing',
                    'dependent-target',
                    'one-genuine-edge'
                ]
            );
            assert.equal(
                proposal.implementedEnvelope
                    .independentDisplayedSiblings
                    .dependencyFlagsSuppliedByUser,
                false
            );
            assert.equal(
                proposal.implementedEnvelope
                    .stableDisplayedEvaluation
                    .higherActionEvidence,
                true
            );
            assert.equal(
                proposal.implementedEnvelope.oneGenuineEdge
                    .hardBindingArity,
                2
            );
            assert.equal(
                proposal.implementedEnvelope.oneGenuineEdge
                    .computationEvidence.length,
                6
            );
        });

        it('pins the latest generic transfer accounting', () => {
            const evidence =
                CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL
                    .latestTransferEvidence;
            assert.deepEqual(evidence.displayedEvaluation, {
                status: 'displayed-eval-1a-generic-transfer',
                existingPrerequisiteDeclarations: 3,
                existingPrerequisiteRuntimeRules: 1,
                newMathematicalOwners: 2,
                newMathematicalRuntimeRules: 2,
                newMathematicalProofRules: 0,
                newIntrinsicCoreOwners: 0,
                genericEnginesOnly: true
            });
            assert.deepEqual(evidence.displayedChain, {
                status: 'displayed-chain-1a-generic-transfer',
                genericTransferDeclarations: 6,
                prerequisiteRuntimeRules: 6,
                newMathematicalOwners: 1,
                newMathematicalRuntimeRules: 6,
                objectLevelRules: 2,
                structuredArrowOrBaseActionRules: 4,
                newMathematicalProofRules: 0,
                newIntrinsicCoreOwners: 0,
                genericCoherenceRules: 0,
                genericEnginesOnly: true
            });
            assert.equal(evidence.perOwnerCheckerBranchesAdded, 0);
            assert.equal(evidence.perOwnerEvaluatorBranchesAdded, 0);
        });

        it('freezes one exact mixed three-level successor API', () => {
            const stress =
                CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL
                    .successorStress;
            assert.equal(stress.row, 'DISPLAYED-CHAIN-2A');
            assert.equal(
                stress.frontendApi.method,
                'displayedDependentContextLambda'
            );
            assert.deepEqual(
                stress.frontendApi.exactBindingNames,
                ['a', 'b', 'c', 'd']
            );
            assert.equal(
                stress.frontendApi.newParallelFrontendMethod,
                false
            );
            assert.equal(stress.telescope.displayedLevels, 3);
            assert.deepEqual(stress.telescope.siblingGroup, ['b', 'c']);
            assert.equal(
                stress.telescope.groupedMiddleFamily,
                'P = displayedProduct(B,C)-over-Sigma_cat(A)'
            );
            assert.equal(
                stress.telescope.result,
                'Functord_cat(D,Q)-over-Sigma_cat(P)'
            );
        });

        it('requires existing authority and halts on closure drift', () => {
            const closure =
                CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL
                    .successorStress.mathematicalClosure;
            assert.equal(
                closure.existingOwners.includes(
                    'sigma_functord_sec'
                ),
                true
            );
            assert.equal(
                closure.existingOwners.includes(
                    'section_pullback_func'
                ),
                true
            );
            assert.deepEqual(
                [
                    closure.expectedNewLambdapiOwners,
                    closure.expectedNewLambdapiRuntimeRules,
                    closure.expectedNewLambdapiProofRules,
                    closure.expectedNewIntrinsicCoreOwners,
                    closure.existingTransferEntryExpansionExpected
                ],
                [0, 0, 0, 0, 0]
            );
            assert.match(closure.stopCondition, /halt-and-propose/u);
        });

        it('requires object, arrow, reindexing, and negative evidence', () => {
            const corpus =
                CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL
                    .successorStress.requiredCorpus;
            assert.equal(corpus.object.length, 5);
            assert.equal(corpus.internalizedArrow.length, 4);
            assert.equal(corpus.reindexing.length, 2);
            assert.equal(corpus.negative.length, 9);
            assert.equal(
                corpus.evidenceRequirements.includes(
                    'bounded-lambdapi-conformance'
                ),
                true
            );
            assert.equal(
                corpus.negative.includes(
                    'mixed-variance-or-cell-level-request'
                ),
                true
            );
        });

        it('is non-self-authorizing and remains root-only', () => {
            const proposal =
                CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL;
            assert.equal(
                Object.values(
                    proposal.authority.currentProposalEffects
                ).every(value => value === false),
                true
            );
            assert.equal(
                proposal.authority.effectsIfApprovedExactly
                    .authorizesDisplayedChain2AImplementation,
                true
            );
            assert.equal(
                proposal.authority.effectsIfApprovedExactly
                    .additionalSemanticOwnerOrRuleAuthorized,
                false
            );
            assert.equal(
                proposal.trustBoundary.browserEntryPoint,
                'excluded'
            );
            const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
            assert.doesNotMatch(
                browser,
                /categorical_displayed_graduation|DISPLAYED-BRACKET-GRADUATE/u
            );
        });

        it('keeps infrastructure and the later sequence separate', () => {
            const proposal =
                CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL;
            assert.match(
                proposal.deferredInfrastructure
                    .canonicalLambdapiParsing,
                /optional-and-deferred/u
            );
            assert.match(
                proposal.deferredInfrastructure.declarationRefinement,
                /optional-deferred/u
            );
            assert.deepEqual(proposal.followingSequence, [
                'DISPLAYED-CHAIN-2A',
                'DISPLAYED-ND-0A',
                'SCALE-KIND-PI-1',
                'SCALE-INDUCTIVE-1B',
                'SCALE-STRESS-3C',
                'SCALE-BATCH-1',
                'SCALE-GRADUATE-1'
            ]);
        });

        it('asks one exact qualified approval question', () => {
            const question =
                CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL
                    .decisionQuestion;
            assert.match(
                question,
                /^Approve H-DTTLF-USABILITY-DISPLAYED-GRADUATE-01\//u
            );
            assert.match(question, /zero expected owner\/rule delta/u);
            assert.match(question, /mandatory stop on closure drift/u);
            assert.match(question, /whole-development claims as deferred/u);
        });

        it('is deeply frozen and fails closed on every drift class', () => {
            assertDeepFrozen(
                CORE_CATEGORICAL_DISPLAYED_GRADUATION_PROPOSAL
            );
            assert.doesNotThrow(
                () => validateCoreCategoricalDisplayedGraduationProposal()
            );
            assertProposalError(
                proposal => {
                    proposal.latestTransferEvidence.displayedChain
                        .newMathematicalRuntimeRules = 5;
                },
                'DISPLAYED_GRADUATION_EVIDENCE_DRIFT'
            );
            assertProposalError(
                proposal => {
                    proposal.recommendation
                        .arbitraryTelescopeDepthClaimed = true;
                },
                'DISPLAYED_GRADUATION_CLAIM_DRIFT'
            );
            assertProposalError(
                proposal => {
                    proposal.successorStress.telescope
                        .siblingGroup = ['b', 'd'];
                },
                'DISPLAYED_GRADUATION_SUCCESSOR_DRIFT'
            );
            assertProposalError(
                proposal => {
                    proposal.authority.currentProposalEffects
                        .authorizesDisplayedChain2AImplementation = true;
                },
                'DISPLAYED_GRADUATION_AUTHORITY_DRIFT'
            );
        });
    }
);
