/**
 * Focused DISPLAYED-EVAL-0B read-only audit tests.
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
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT,
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_LINKAGE,
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_MODULE,
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_POLICY,
    CoreCategoricalDisplayedEvaluationAuditError,
    CoreCategoricalProgram,
    CoreCheckerError,
    compileCoreCategoricalFibredDependentTargetTransfer,
    compileCoreLfDeclarations,
    measureCoreCategoricalDisplayedEvaluationProfileJoin,
    validateCoreCategoricalDisplayedEvaluationAudit
} from '../src/v3_2';

const clone = (): any => JSON.parse(JSON.stringify(
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const assertAuditError = (
    mutate: (audit: any) => void,
    expected: CoreCategoricalDisplayedEvaluationAuditError['code']
): void => {
    const audit = clone();
    mutate(audit);
    assert.throws(
        () => validateCoreCategoricalDisplayedEvaluationAudit(audit),
        error =>
            error instanceof
                CoreCategoricalDisplayedEvaluationAuditError &&
            error.code === expected
    );
};

describe('TypeScript v3.2 DISPLAYED-EVAL-0B authority audit', () => {
    it('starts from the exact reviewed D-010 checkpoint', () => {
        const prerequisite =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT.prerequisite;
        assert.equal(
            prerequisite.reviewGate,
            'H-DTTLF-USABILITY-DISPLAYED-LIFTING-01'
        );
        assert.equal(
            prerequisite.reviewDecision,
            'D-DTTLF-USABILITY-010'
        );
        assert.equal(
            prerequisite.reviewImplementationCheckpoint,
            '7badcd5b930bd098b178d89bf4488637695fb14d'
        );
        assert.equal(prerequisite.investigationAuthorized, true);
        assert.equal(
            prerequisite.semanticImplementationAuthorized,
            false
        );
    });

    it('retains the existing recursive typed-IR architecture', () => {
        const architecture =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
                .retainedArchitecture;
        assert.equal(
            architecture.sourceBoundary,
            'existing-typed-typescript-construction-ir'
        );
        assert.match(architecture.lowering, /recursive-contextual/u);
        assert.equal(architecture.rawExprLayerAdded, false);
        assert.equal(
            architecture.secondBidirectionalCheckerAdded,
            false
        );
        assert.equal(architecture.parserAdded, false);
        assert.equal(architecture.wholeBodyRecognizerAdded, false);
    });

    it('records the exact mixed-variance obstruction and specialization', () => {
        const finding =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
                .varianceFinding;
        assert.equal(finding.negativeProbeConstraint, 'Op_cat K = K');
        assert.equal(finding.negativeProbeExit, 1);
        assert.equal(finding.mathematicalImpossibilityClaim, false);
        assert.match(finding.feasibleSpecialization, /constant-domain/u);
    });

    it('distinguishes the feasible universe alternative from the stable route', () => {
        const comparison =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
                .existingAuthorityComparison;
        assert.equal(
            comparison.universeNaturalEvaluation.ownerPositionProbe,
            'accepted'
        );
        assert.equal(
            comparison.universeNaturalEvaluation
                .sufficientForSelectedStableFrontend,
            false
        );
        assert.equal(
            comparison.stableDisplayedEvaluation
                .existingDerivationFound,
            false
        );
        assert.equal(
            comparison.stableDisplayedEvaluation.candidateOwner,
            'Eval_funcd'
        );
        assert.equal(
            comparison.stableDisplayedEvaluation
                .varyingArgumentObjectBetaProbe,
            'accepted'
        );
    });

    it('selects reusable terminal weakening and derives fixed evaluation', () => {
        const fixed =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
                .existingAuthorityComparison.fixedArgumentWeakening;
        assert.equal(fixed.derivationProbe, 'rejected');
        assert.equal(fixed.candidateOwner, 'Terminal_funcd');
        assert.equal(fixed.candidateOwnerPositionProbe, 'accepted');
        assert.match(fixed.derivedConstantMap, /Const_funcd/u);
        assert.match(fixed.derivedFixedEvaluator, /Eval_at_funcd/u);
        assert.equal(fixed.fixedArgumentObjectBetaProbe, 'accepted');
    });

    it('keeps generic functoriality and higher action at the global calculus', () => {
        const coherence =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
                .reindexingAndHigherAction;
        assert.equal(coherence.pointComponentsComputational, true);
        assert.equal(coherence.offDiagonalStableAndIterable, true);
        assert.equal(
            coherence.extraIdentityCompositionNaturalityRulesSelected,
            false
        );
        assert.equal(
            coherence.representation,
            'generic-displayed-tapp1-and-naturality-calculus'
        );
    });

    it('records the bounded owner-position warning delta diagnostically', () => {
        const evidence =
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
                .ownerPositionEvidence;
        assert.deepEqual(evidence.activeKernelBaseline, {
            warningMarkers: 1175,
            unjoinableCriticalPairs: 1010,
            replaceablePatternVariables: 159
        });
        assert.deepEqual(evidence.combinedCandidateProbe, {
            quietCheck: 'pass-under-60-seconds',
            warningCheck: 'pass-under-60-seconds',
            warningMarkers: 1177,
            unjoinableCriticalPairs: 1012,
            replaceablePatternVariables: 159
        });
        assert.equal(
            evidence.warningDelta.unjoinableCriticalPairs,
            2
        );
        assert.match(evidence.warningDelta.interpretation, /not-an-/u);
    });

    it('reproduces the transfer-only profile mismatch and composed-runtime join', () => {
        const program = new CoreCategoricalProgram({
            sourceFile: 'displayed-eval-0b-profile-test.ts',
            profile: 'fibred-dependent-target-1'
        });
        const K = program.category('profileK');
        const E = program.displayedFamily('profileE', K);
        const D = program.displayedFamily('profileD', K);
        const Q = program.displayedFamily('profileQ', K);
        const FF = program.displayedFunctor('profileFF', E, D);
        const GG = program.displayedFunctor('profileGG', D, Q);
        const composition = program.displayedFunctorLambda(
            'profileA',
            E,
            Q,
            a => program.apply(
                GG,
                program.apply(FF, a, {
                    expectedShape: 'object-value'
                }),
                { expectedShape: 'object-value' }
            )
        );
        assert.throws(
            () => program.compile(composition),
            error =>
                error instanceof CoreCheckerError &&
                error.code === 'TYPE_MISMATCH'
        );

        const measurement =
            measureCoreCategoricalDisplayedEvaluationProfileJoin();
        assert.equal(measurement.prerequisiteRuntime, 'not-equal');
        assert.equal(measurement.composedRuntime, 'equal');
        assert.ok(
            measurement.composedSteps > measurement.prerequisiteSteps
        );
    });

    it('validates the standard final-recheck repair without installing it', () => {
        const compilation =
            compileCoreCategoricalFibredDependentTargetTransfer();
        const repaired = compileCoreLfDeclarations(
            CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_MODULE,
            CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_POLICY,
            CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_TRANSFER_LINKAGE,
            {
                initialEnvironment:
                    compilation.prerequisite.compiled.environment,
                runtimeProgram: compilation.composedRuntime
            }
        );
        assert.doesNotThrow(
            () => repaired.createChecker().validateEnvironment()
        );
        assert.equal(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
                .profileMismatch.repairImplementedByThisAudit,
            false
        );
    });

    it('is deeply frozen, fail-closed, and absent from the browser profile', () => {
        assertDeepFrozen(
            CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
        );
        assert.doesNotThrow(
            () => validateCoreCategoricalDisplayedEvaluationAudit()
        );
        assert.equal(
            Object.values(
                CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
                    .semanticDelta
            ).some(value => value !== 0),
            false
        );
        const browser = readFileSync('src/v3_2/browser.ts', 'utf8');
        assert.doesNotMatch(
            browser,
            /categorical_displayed_evaluation|DISPLAYED-EVAL/u
        );
    });

    it('rejects prerequisite, evidence, and authority drift', () => {
        assertAuditError(
            audit => {
                audit.prerequisite.reviewRevision = 'drift';
            },
            'DISPLAYED_EVALUATION_AUDIT_PREREQUISITE_DRIFT'
        );
        assertAuditError(
            audit => {
                audit.conclusion.selectedOwners.pop();
            },
            'DISPLAYED_EVALUATION_AUDIT_EVIDENCE_DRIFT'
        );
        assertAuditError(
            audit => {
                audit.semanticDelta.activeLambdapiOwners = 1;
            },
            'DISPLAYED_EVALUATION_AUDIT_BOUNDARY_DRIFT'
        );
    });
});
