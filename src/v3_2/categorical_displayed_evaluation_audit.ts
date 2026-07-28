/**
 * Executable DISPLAYED-EVAL-0B read-only authority audit.
 *
 * The audit keeps the existing typed TypeScript construction IR, recursive
 * contextual compiler, explicit Core, and generic checker unchanged. It
 * distinguishes:
 *
 * - a real mixed-variance obstruction for a fully varying source family;
 * - a feasible constant-domain displayed evaluator;
 * - the separate structural weakening needed by a fixed argument; and
 * - a pre-existing dependent-profile runtime-wiring defect.
 *
 * No Lambdapi/Core owner, runtime rule, frontend case, or profile repair is
 * installed here.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW,
    validateCoreCategoricalDisplayedLiftingReview
} from './categorical_displayed_lifting_review';
import {
    compileCoreCategoricalFibredDependentTargetTransfer
} from './categorical_fibred_dependent_target_transfer';
import {
    CORE_DIRECTED_1A_PRIMITIVE_NAMES
} from './directed_1a';
import {
    kernelApplication,
    kernelCall,
    kernelFree,
    provenance
} from './kernel';
import {
    coreLfDefinitionalCompare
} from './lf_conversion';

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const rawAudit = {
    revision: 'DISPLAYED-EVAL-0B-AUDIT-1',
    status: 'completed-read-only-authority-audit',
    row: 'DISPLAYED-EVAL-0B',
    prerequisite: {
        reviewRevision: 'DISPLAYED-LIFTING-0A-REVIEWED-1',
        reviewGate: 'H-DTTLF-USABILITY-DISPLAYED-LIFTING-01',
        reviewDecision: 'D-DTTLF-USABILITY-010',
        reviewImplementationCheckpoint:
            '7badcd5b930bd098b178d89bf4488637695fb14d',
        reviewLedgerCheckpoint:
            'e225211fff6373da1ab4b5d26df98c128f5f27df',
        investigationAuthorized: true,
        semanticImplementationAuthorized: false
    },
    retainedArchitecture: {
        sourceBoundary: 'existing-typed-typescript-construction-ir',
        lowering:
            'recursive-contextual-compilation-over-typed-subexpressions',
        target: 'backend-neutral-explicit-emdash-core',
        checker: 'existing-generic-core-lf-checker',
        rawExprLayerAdded: false,
        secondBidirectionalCheckerAdded: false,
        parserAdded: false,
        wholeBodyRecognizerAdded: false
    },
    authorityInventory: {
        stableMixedVarianceFamily: 'Functor_catd',
        stableMixedVariancePackage: 'Functor_catd_func',
        constantFamilies: 'Const_catd',
        ordinaryProductEvaluator: 'Eval_func',
        ordinaryFixedEvaluator: 'fapp0_func',
        transparentFibrewiseProduct:
            'uncurry(Product_cat_func)-after-Struct_sigma',
        displayedPairing: 'Product_pair_funcd',
        displayedComposition: 'comp_fapp0-at-Catd_cat',
        ordinaryTerminalFunctor: 'Terminal_func',
        sigmaIntroduction: 'sigma_intro_transf',
        coherentDisplayedEvaluatorLexicallyPresent: false,
        arbitraryDisplayedTerminalMapLexicallyPresent: false
    },
    varianceFinding: {
        genericSource:
            'A : Catd(Op_cat K), B : Catd K',
        invalidPlainArgument:
            'the-same-A-cannot-also-be-a-covariant-family-over-K',
        negativeProbeConstraint: 'Op_cat K = K',
        negativeProbeExit: 1,
        interpretation:
            'ordinary-same-base-fibrewise-pairing-does-not-supply-' +
            'evaluation-for-an-arbitrary-mixed-variance-domain',
        mathematicalImpossibilityClaim: false,
        feasibleSpecialization:
            'constant-domain-A-with-Const_catd(Op_cat-K,A)-and-' +
            'Const_catd(K,A)'
    },
    existingAuthorityComparison: {
        universeNaturalEvaluation: {
            candidate:
                'Eval_transf(A) : ' +
                'Transf(B |-> Product(Functor(A,B),A), id_Cat)',
            ownerPositionProbe: 'accepted',
            component:
                'tapp0_fapp0(B,Eval_transf(A)) -> Eval_func(A,B)',
            derivedPrecompositionOverB: 'accepted',
            limitation:
                'its-transparent-source-family-is-not-convertible-to-' +
                'the-stable-Functor_catd-constant-domain-family',
            sufficientForSelectedStableFrontend: false,
            retainedAsAlternative: true
        },
        stableDisplayedEvaluation: {
            existingDerivationFound: false,
            candidateOwner: 'Eval_funcd',
            candidateOwnerPositionProbe: 'accepted',
            candidateComponentProbe: 'accepted',
            varyingArgumentObjectBetaProbe: 'accepted',
            fullDisplayedCoherenceCarriedByOwnerType: true,
            constructorSpecificFunctorialityRulesRequired: false
        },
        fixedArgumentWeakening: {
            temptingExistingDerivation:
                'Terminal_func(Sigma_cat(E))-after-sigma_intro_transf(E)',
            derivationProbe: 'rejected',
            rejectedClassifierComparison:
                'Obj(Functor_cat(Sigma_cat(E),Terminal_cat))-' +
                'versus-Obj(Transf_cat(K,Cat_cat,Const(Sigma(E)),' +
                'Const(Terminal)))',
            candidateOwner: 'Terminal_funcd',
            candidateOwnerPositionProbe: 'accepted',
            candidateComponentProbe: 'accepted',
            derivedConstantMap:
                'Const_funcd(E,a)=Const_func(K,A,a)-after-' +
                'Terminal_funcd(E)',
            derivedFixedEvaluator:
                'Eval_at_funcd(B,a)=Eval_funcd(B)-after-' +
                'pair(id,Const_funcd(subject,a))',
            fixedArgumentObjectBetaProbe: 'accepted'
        }
    },
    reindexingAndHigherAction: {
        evaluatorLaw:
            'B[p]-after-Eval_k-equals-Eval_l-after-' +
            '(postcompose-by-B[p]-times-id_A)',
        terminalLaw:
            'the-component-at-k-is-Terminal_func(Fibre(E,k))',
        representation:
            'generic-displayed-tapp1-and-naturality-calculus',
        pointComponentsComputational: true,
        offDiagonalStableAndIterable: true,
        extraIdentityCompositionNaturalityRulesSelected: false,
        reason:
            'the-global-fapp-tapp-calculus-solely-owns-generic-' +
            'functoriality-and-naturality'
    },
    ownerPositionEvidence: {
        activeKernelBaseline: {
            warningMarkers: 1175,
            unjoinableCriticalPairs: 1010,
            replaceablePatternVariables: 159
        },
        combinedCandidateProbe: {
            quietCheck: 'pass-under-60-seconds',
            warningCheck: 'pass-under-60-seconds',
            warningMarkers: 1177,
            unjoinableCriticalPairs: 1012,
            replaceablePatternVariables: 159
        },
        warningDelta: {
            warningMarkers: 2,
            unjoinableCriticalPairs: 2,
            replaceablePatternVariables: 0,
            family:
                'Terminal_funcd-component-versus-generic-strict-' +
                'naturality-over-Cat_cat',
            interpretation:
                'diagnostic-interaction-to-retain-and-audit-not-an-' +
                'automatic-semantic-veto'
        },
        positiveConsumers: [
            'varying-subject-and-varying-coherent-argument',
            'varying-subject-and-fixed-argument',
            'generic-base-precomposition-of-universe-evaluation-alternative'
        ],
        negativeConsumers: [
            'arbitrary-mixed-variance-domain-reused-as-covariant-argument',
            'ordinary-terminal-functor-coerced-to-an-arbitrary-displayed-map'
        ]
    },
    profileMismatch: {
        profile: 'fibred-dependent-target-1',
        unchangedExplicitTerm:
            'comp_fapp0(Catd_cat(K),E,D,Q,GG,FF)',
        observedError: 'TYPE_MISMATCH',
        oldRuntimeComparison: 'not-equal',
        composedRuntimeComparison: 'equal',
        exactCause:
            'the-transfer-installs-transparent-Hom-as-Obj(Hom_cat)-and-' +
            'compiles-Hom_cat(Catd)-to-Functord_cat-but-returns-the-' +
            'declaration-checker-wired-to-the-prerequisite-runtime',
        standardRepair:
            'repeat-the-final-declaration-compilation-with-' +
            'consumerRuntimeFragment.runtime-as-neighboring-transfer-' +
            'stages-do',
        classification: 'transfer-runtime-wiring-only',
        categoricalSemanticFailure: false,
        recursiveBracketFailure: false,
        repairImplementedByThisAudit: false
    },
    conclusion: {
        activeAuthorityAloneSufficientForStableFrontend: false,
        constantDomainDisplayedEvaluationFeasible: true,
        fixedArgumentDisplayedEvaluationFeasible: true,
        generalArbitraryMixedVarianceEvaluationSelected: false,
        minimalStableOwnerCount: 2,
        selectedOwners: [
            'Eval_funcd',
            'Terminal_funcd'
        ],
        selectedRuntimeRuleCount: 2,
        nextProposal:
            'DISPLAYED-EVAL-OWNER-0C',
        nextGate:
            'H-DTTLF-USABILITY-DISPLAYED-EVAL-OWNER-01',
        nextDecision: 'D-DTTLF-USABILITY-011'
    },
    semanticDelta: {
        activeLambdapiOwners: 0,
        activeLambdapiRules: 0,
        intrinsicCoreOwners: 0,
        transferredRuntimeRules: 0,
        recursiveFrontendCases: 0,
        profileRepairs: 0,
        parserLayers: 0,
        checkerLayers: 0,
        browserPromotions: 0
    },
    nextDependencyState:
        'displayed-eval-owner-0c-proposal-ready-not-authorized'
} as const;

export type CoreCategoricalDisplayedEvaluationAuditInput =
    typeof rawAudit;

export type CoreCategoricalDisplayedEvaluationAuditErrorCode =
    | 'DISPLAYED_EVALUATION_AUDIT_PREREQUISITE_DRIFT'
    | 'DISPLAYED_EVALUATION_AUDIT_EVIDENCE_DRIFT'
    | 'DISPLAYED_EVALUATION_AUDIT_BOUNDARY_DRIFT';

export class CoreCategoricalDisplayedEvaluationAuditError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedEvaluationAuditErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDisplayedEvaluationAuditError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT =
    deepFreeze(rawAudit);

/**
 * Reproduce the exact classifier join that distinguishes the stale runtime
 * wiring from the fully composed dependent-target runtime.
 */
export function measureCoreCategoricalDisplayedEvaluationProfileJoin():
Readonly<{
    prerequisiteRuntime: 'not-equal';
    composedRuntime: 'equal';
    prerequisiteSteps: number;
    composedSteps: number;
}> {
    const compilation =
        compileCoreCategoricalFibredDependentTargetTransfer();
    const nodeProvenance = provenance(
        'derived',
        'DISPLAYED-EVAL-0B profile join measurement'
    );
    const K = kernelFree('displayed_eval_0b_K', nodeProvenance);
    const E = kernelFree('displayed_eval_0b_E', nodeProvenance);
    const D = kernelFree('displayed_eval_0b_D', nodeProvenance);
    const catd = kernelApplication(
        'displayed-category-category',
        [{ value: K }],
        nodeProvenance
    );
    const functord = kernelCall(
        kernelFree(
            CORE_DIRECTED_1A_PRIMITIVE_NAMES[
                'displayed-functor-category'
            ],
            nodeProvenance
        ),
        [
            { plicity: 'implicit', value: K },
            { plicity: 'explicit', value: E },
            { plicity: 'explicit', value: D }
        ],
        nodeProvenance
    );
    const homClassifier = kernelApplication(
        'hom-classifier',
        [
            { value: catd },
            { value: E },
            { value: D }
        ],
        nodeProvenance
    );
    const objectClassifier = kernelApplication(
        'object-classifier',
        [{ value: functord }],
        nodeProvenance
    );
    const prerequisite = coreLfDefinitionalCompare(
        compilation.compiled.environment,
        homClassifier,
        objectClassifier,
        128,
        undefined,
        compilation.prerequisite.composedRuntime
    );
    const composed = coreLfDefinitionalCompare(
        compilation.compiled.environment,
        homClassifier,
        objectClassifier,
        128,
        undefined,
        compilation.composedRuntime
    );
    if (
        prerequisite.status !== 'not-equal' ||
        composed.status !== 'equal'
    ) {
        throw new CoreCategoricalDisplayedEvaluationAuditError(
            'DISPLAYED_EVALUATION_AUDIT_EVIDENCE_DRIFT',
            'The dependent-target classifier join no longer reproduces ' +
                'the audited prerequisite/composed runtime distinction'
        );
    }
    return deepFreeze({
        prerequisiteRuntime: prerequisite.status,
        composedRuntime: composed.status,
        prerequisiteSteps: prerequisite.steps,
        composedSteps: composed.steps
    });
}

export function validateCoreCategoricalDisplayedEvaluationAudit(
    audit: CoreCategoricalDisplayedEvaluationAuditInput =
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT
): void {
    try {
        validateCoreCategoricalDisplayedLiftingReview();
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedEvaluationAuditError(
            'DISPLAYED_EVALUATION_AUDIT_PREREQUISITE_DRIFT',
            'The reviewed DISPLAYED-LIFTING-0A prerequisite drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }
    if (
        CORE_CATEGORICAL_DISPLAYED_LIFTING_REVIEW.revision !==
            audit.prerequisite.reviewRevision ||
        audit.revision !== 'DISPLAYED-EVAL-0B-AUDIT-1' ||
        audit.status !== 'completed-read-only-authority-audit' ||
        audit.row !== 'DISPLAYED-EVAL-0B'
    ) {
        throw new CoreCategoricalDisplayedEvaluationAuditError(
            'DISPLAYED_EVALUATION_AUDIT_PREREQUISITE_DRIFT',
            'The DISPLAYED-EVAL-0B identity or reviewed prerequisite drifted'
        );
    }
    if (
        audit.varianceFinding.negativeProbeConstraint !== 'Op_cat K = K' ||
        audit.existingAuthorityComparison
            .stableDisplayedEvaluation.existingDerivationFound ||
        audit.existingAuthorityComparison
            .universeNaturalEvaluation.sufficientForSelectedStableFrontend ||
        audit.profileMismatch.classification !==
            'transfer-runtime-wiring-only' ||
        audit.profileMismatch.categoricalSemanticFailure ||
        audit.profileMismatch.recursiveBracketFailure ||
        audit.ownerPositionEvidence.warningDelta
            .unjoinableCriticalPairs !== 2 ||
        audit.conclusion.minimalStableOwnerCount !== 2 ||
        audit.conclusion.selectedOwners.join(',') !==
            'Eval_funcd,Terminal_funcd'
    ) {
        throw new CoreCategoricalDisplayedEvaluationAuditError(
            'DISPLAYED_EVALUATION_AUDIT_EVIDENCE_DRIFT',
            'The variance, owner-position, or profile evidence drifted'
        );
    }
    if (
        Object.values(audit.semanticDelta).some(value => value !== 0) ||
        audit.prerequisite.semanticImplementationAuthorized ||
        audit.retainedArchitecture.rawExprLayerAdded ||
        audit.retainedArchitecture.secondBidirectionalCheckerAdded ||
        audit.retainedArchitecture.parserAdded ||
        audit.retainedArchitecture.wholeBodyRecognizerAdded ||
        audit.nextDependencyState !==
            'displayed-eval-owner-0c-proposal-ready-not-authorized' ||
        !sameData(audit, rawAudit)
    ) {
        throw new CoreCategoricalDisplayedEvaluationAuditError(
            'DISPLAYED_EVALUATION_AUDIT_BOUNDARY_DRIFT',
            'The read-only audit acquired semantic or frontend authority'
        );
    }
}

validateCoreCategoricalDisplayedEvaluationAudit();
