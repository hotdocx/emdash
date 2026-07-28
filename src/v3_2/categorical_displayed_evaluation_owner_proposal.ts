/**
 * Frozen DISPLAYED-EVAL-OWNER-0C proposal.
 *
 * The proposal is deliberately non-self-authorizing. It selects the smallest
 * stable-owner closure demonstrated by DISPLAYED-EVAL-0B and one bounded
 * vertical TypeScript consumer. It does not add a parallel surface language,
 * checker, parser, or whole-body recognizer.
 */

import {
    CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT,
    CoreCategoricalDisplayedEvaluationAuditInput,
    validateCoreCategoricalDisplayedEvaluationAudit
} from './categorical_displayed_evaluation_audit';

const cloneData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

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

const audit = CORE_CATEGORICAL_DISPLAYED_EVALUATION_AUDIT;

const rawProposal = {
    revision: 'DISPLAYED-EVAL-OWNER-0C-PROPOSAL-1',
    status:
        'proposal-awaiting-h-dttlf-usability-displayed-eval-owner-01',
    row: 'DISPLAYED-EVAL-OWNER-0C',
    reviewGate: 'H-DTTLF-USABILITY-DISPLAYED-EVAL-OWNER-01',
    decisionId: 'D-DTTLF-USABILITY-011',
    prerequisite:
        cloneData(audit) as CoreCategoricalDisplayedEvaluationAuditInput,
    selectedDomain: {
        base: 'K : Cat',
        constantDomain: 'A : Cat',
        varyingTarget: 'B : Catd K',
        stableSubjectFamily:
            'S(A,B)=Functor_catd(Const_catd(Op_cat K,A),B)',
        varyingArgumentFamily: 'Const_catd(K,A)',
        evaluationSource: 'P(S(A,B),Const_catd(K,A))',
        excludedGeneralization:
            'A : Catd(Op_cat K)-reused-as-a-covariant-argument-family'
    },
    proposedKernelOwners: [
        {
            order: 0,
            name: 'Eval_funcd',
            kind: 'injective-stable-displayed-functor',
            signature:
                '[K A : Cat] (B : Catd K) -> ' +
                'Functord(P(Functor_catd(Const_(Op K) A,B),' +
                'Const_K A),B)',
            ownerPosition:
                'after-Functor_catd-constructor-and-object-projection',
            purpose:
                'coherent-evaluation-of-a-varying-constant-domain-' +
                'fibre-functor-at-a-coherent-argument'
        },
        {
            order: 1,
            name: 'Terminal_funcd',
            kind: 'injective-stable-displayed-functor',
            signature:
                '[K : Cat] (E : Catd K) -> ' +
                'Functord(E,Const_catd(K,Terminal_cat))',
            ownerPosition:
                'generic-sigma-pi-weakening-helper-section',
            purpose:
                'reusable-dependent-weakening-from-an-arbitrary-' +
                'displayed-source-to-the-constant-terminal-family'
        }
    ],
    proposedRuntimeRules: [
        {
            order: 0,
            id: 'categorical.displayed-evaluation.component',
            left: 'tapp0_fapp0(k,Eval_funcd(K,A,B))',
            right: 'Eval_func(A,Fibre_cat(B,k))',
            inferredSlots: 'minimal-owner-headed-pattern',
            genericFunctorialityDuplicated: false
        },
        {
            order: 1,
            id: 'categorical.displayed-terminal.component',
            left: 'tapp0_fapp0(k,Terminal_funcd(K,E))',
            right: 'Terminal_func(Fibre_cat(E,k))',
            inferredSlots: 'minimal-owner-headed-pattern',
            genericFunctorialityDuplicated: false
        }
    ],
    derivedConstructions: {
        varyingArgument: {
            inputs:
                'FF : Functord(E,S(A,B)), xx : Functord(E,Const_K A)',
            result:
                'Eval_funcd(B) after Product_pair_funcd(FF,xx)',
            output: 'Functord(E,B)',
            newOwnerRequired: false
        },
        fixedArgument: {
            fixedInput: 'a : Obj A',
            constantMap:
                'Const_funcd(E,a) = Const_func(K,A,a) after ' +
                'Terminal_funcd(E)',
            fixedEvaluator:
                'Eval_at_funcd(B,a) = Eval_funcd(B) after ' +
                'Product_pair_funcd(id,Const_funcd(S(A,B),a))',
            output: 'Functord(S(A,B),B)',
            objectBeta: 'Eval_at_funcd(B,a)[k][F] -> F[a]',
            newFixedEvaluatorOwnerRequired: false
        }
    },
    coherenceContract: {
        pointEvaluationComputes: true,
        baseArrowActionRepresented: true,
        higherActionRemainsIterable: true,
        evaluatorReindexing:
            'B[p] after Eval_k = Eval_l after ' +
            '(postcompose(B[p]) times id_A)',
        terminalReindexing: 'unique-map-naturality',
        genericIdentityCompositionNaturalityOwner:
            'global-fapp-tapp-calculus',
        specializedIdentityRulesAdded: false,
        specializedCompositionRulesAdded: false,
        specializedNaturalityRulesAdded: false
    },
    profileRepair: {
        classification: 'mechanical-transfer-runtime-wiring',
        file:
            'categorical_fibred_dependent_target_transfer.ts',
        change:
            'repeat-final-declaration-compilation-against-' +
            'consumerRuntimeFragment.runtime',
        precedent: [
            'categorical_fibred_structure_transfer.ts',
            'categorical_fibred_transfd_transfer.ts',
            'categorical_fibred_weaken_reindex_transfer.ts'
        ],
        ownerOrRuleSemanticChange: false,
        requiredBeforeJoinedConsumer: true
    },
    typedFrontendSlice: {
        id: 'DISPLAYED-EVAL-1A',
        sourceBoundary: 'existing-typed-typescript-construction-ir',
        recursiveCompiler:
            'existing-displayed-contextual-compiler',
        existingApplicationNodeReused: true,
        bothOpenJudgment: {
            subject:
                'recursively-compiled-indexed-object-of-S(A,B)',
            argument:
                'recursively-compiled-indexed-object-of-Const_K(A)',
            lowering:
                'Eval_funcd-after-Product_pair_funcd-of-recursive-' +
                'subject-and-argument'
        },
        fixedArgumentJudgment: {
            subject:
                'recursively-compiled-indexed-object-of-S(A,B)',
            argument: 'closed-object-a-of-A',
            lowering:
                'Eval_funcd-after-pair-of-subject-and-derived-' +
                'Const_funcd-via-Terminal_funcd'
        },
        result:
            'recursively-usable-indexed-object-of-B',
        callbackEvaluationCount: 1,
        rawExprAdded: false,
        secondCheckerAdded: false,
        parserAdded: false,
        bracketPunctuationAdded: false,
        wholeBodyRecognizerAdded: false
    },
    validationPlan: {
        kernel: [
            'owner-position-full-file-probe',
            'positive-varying-and-fixed-object-betas',
            'negative-mixed-variance-probe',
            'bounded-make-check',
            'warning-comparison',
            'strict-lhs-audit',
            'affected-checks-and-examples',
            'catalog-and-health-synchronization'
        ],
        typescript: [
            'focused-transfer-and-profile-repair-tests',
            'focused-recursive-both-open-and-fixed-argument-tests',
            'wrong-family-and-variance-negative-tests',
            'backend-neutral-explicit-core-snapshots',
            'live-lambdapi-conformance',
            'root-check-ts'
        ],
        knownWarningDelta: {
            unjoinableCriticalPairs: 2,
            replaceablePatternVariables: 0,
            ownerFamily: 'Terminal_funcd-component',
            policy:
                'diagnostic-not-veto;retain-exact-baseline-comparison-' +
                'and-investigate-join-without-changing-semantic-intent'
        }
    },
    alternativesRetained: [
        {
            id: 'universe-natural-evaluation',
            status: 'feasible-not-selected-for-this-slice',
            reason:
                'transparent-source-does-not-join-the-stable-' +
                'Functor_catd-family'
        },
        {
            id: 'specialized-fixed-evaluator-owner',
            status: 'not-selected',
            reason:
                'Terminal_funcd-is-a-more-reusable-structural-weakening-' +
                'owner-and-already-derives-fixed-evaluation'
        },
        {
            id: 'pointwise-only-evaluation',
            status: 'rejected',
            reason:
                'does-not-carry-base-arrow-coherence-or-iterable-' +
                'higher-action'
        },
        {
            id: 'generic-arbitrary-mixed-variance-evaluator',
            status: 'deferred-requires-different-argument-notion',
            reason:
                'plain-same-base-covariant-argument-would-force-Op-K=K'
        }
    ],
    proposedSemanticDelta: {
        newLambdapiOwners: 2,
        newLambdapiRuntimeRules: 2,
        newLambdapiProofRules: 0,
        newTransferredFreeDeclarations: 2,
        newTransferredRuntimeRules: 2,
        newIntrinsicCoreOwners: 0,
        profileRuntimeWiringRepairs: 1,
        recursiveTypedApplicationJudgments: 2,
        newSurfaceAstLayers: 0,
        newCheckerLayers: 0,
        parserLayers: 0,
        browserPromotions: 0
    },
    withheld: [
        'arbitrary-varying-mixed-domain-argument',
        'general-dependent-chain-lowering',
        'general-nd-coherence',
        'new-constructor-specific-functoriality-or-naturality-rules',
        'global-Functor_catd-transparent-family-collapse',
        'full-product-curry-adjunction-coherence',
        'string-parser-or-lambdapi-parser',
        'bulk-transfer',
        'browser-or-deployed-profile',
        'push-merge-publish-or-history-rewrite'
    ],
    decisionEffects: {
        authorizesExactTwoKernelOwners: false,
        authorizesExactTwoRuntimeRules: false,
        authorizesMechanicalProfileRepair: false,
        authorizesTwoRecursiveTypedApplicationJudgments: false,
        authorizesRawExprOrSecondChecker: false,
        authorizesParser: false,
        authorizesGeneralDependentChain: false,
        authorizesGeneralNdCoherence: false,
        authorizesBrowserPromotion: false,
        authorizesBroaderGitMutation: false
    },
    nextDependencyState:
        'awaiting-exact-displayed-eval-owner-review',
    decisionQuestion:
        'Approve H-DTTLF-USABILITY-DISPLAYED-EVAL-OWNER-01/' +
        'D-DTTLF-USABILITY-011 as proposed: add exactly the stable ' +
        'Eval_funcd and Terminal_funcd owners and their two point-component ' +
        'rules; retain generic fapp/tapp ownership of functoriality and ' +
        'naturality; make the standard dependent-target final-runtime ' +
        'recheck; transfer the exact closure through the generic engines; ' +
        'and implement only the existing-IR recursive both-open and fixed-' +
        'argument displayed evaluation judgments, while withholding the ' +
        'generic mixed-domain case, dependent chains, general :^nd, parser/' +
        'bulk work, browser promotion, and broader Git authority?'
} as const;

export type CoreCategoricalDisplayedEvaluationOwnerProposalInput =
    typeof rawProposal;

export type CoreCategoricalDisplayedEvaluationOwnerProposalErrorCode =
    | 'DISPLAYED_EVALUATION_OWNER_PREREQUISITE_DRIFT'
    | 'DISPLAYED_EVALUATION_OWNER_SIGNATURE_DRIFT'
    | 'DISPLAYED_EVALUATION_OWNER_SCOPE_DRIFT';

export class CoreCategoricalDisplayedEvaluationOwnerProposalError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedEvaluationOwnerProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreCategoricalDisplayedEvaluationOwnerProposalError';
    }
}

export const
CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL =
    deepFreeze(rawProposal);

export function
validateCoreCategoricalDisplayedEvaluationOwnerProposal(
    proposal: CoreCategoricalDisplayedEvaluationOwnerProposalInput =
        CORE_CATEGORICAL_DISPLAYED_EVALUATION_OWNER_PROPOSAL
): void {
    try {
        validateCoreCategoricalDisplayedEvaluationAudit();
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedEvaluationOwnerProposalError(
            'DISPLAYED_EVALUATION_OWNER_PREREQUISITE_DRIFT',
            'The DISPLAYED-EVAL-0B audit drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }
    if (
        !sameData(proposal.prerequisite, audit) ||
        proposal.prerequisite.nextDependencyState !==
            'displayed-eval-owner-0c-proposal-ready-not-authorized' ||
        proposal.revision !==
            'DISPLAYED-EVAL-OWNER-0C-PROPOSAL-1' ||
        proposal.reviewGate !==
            'H-DTTLF-USABILITY-DISPLAYED-EVAL-OWNER-01' ||
        proposal.decisionId !== 'D-DTTLF-USABILITY-011'
    ) {
        throw new CoreCategoricalDisplayedEvaluationOwnerProposalError(
            'DISPLAYED_EVALUATION_OWNER_PREREQUISITE_DRIFT',
            'The proposal no longer snapshots the exact completed audit'
        );
    }
    if (
        proposal.proposedKernelOwners.length !== 2 ||
        proposal.proposedKernelOwners.map(owner => owner.name).join(',') !==
            'Eval_funcd,Terminal_funcd' ||
        proposal.proposedRuntimeRules.length !== 2 ||
        proposal.proposedRuntimeRules.some(
            rule => rule.genericFunctorialityDuplicated
        ) ||
        proposal.proposedSemanticDelta.newLambdapiOwners !== 2 ||
        proposal.proposedSemanticDelta.newLambdapiRuntimeRules !== 2 ||
        proposal.proposedSemanticDelta.newLambdapiProofRules !== 0 ||
        proposal.validationPlan.knownWarningDelta
            .unjoinableCriticalPairs !== 2
    ) {
        throw new CoreCategoricalDisplayedEvaluationOwnerProposalError(
            'DISPLAYED_EVALUATION_OWNER_SIGNATURE_DRIFT',
            'The exact two-owner/two-rule stable closure drifted'
        );
    }
    if (
        Object.values(proposal.decisionEffects).some(Boolean) ||
        proposal.typedFrontendSlice.rawExprAdded ||
        proposal.typedFrontendSlice.secondCheckerAdded ||
        proposal.typedFrontendSlice.parserAdded ||
        proposal.typedFrontendSlice.bracketPunctuationAdded ||
        proposal.typedFrontendSlice.wholeBodyRecognizerAdded ||
        proposal.nextDependencyState !==
            'awaiting-exact-displayed-eval-owner-review' ||
        !sameData(proposal, rawProposal)
    ) {
        throw new CoreCategoricalDisplayedEvaluationOwnerProposalError(
            'DISPLAYED_EVALUATION_OWNER_SCOPE_DRIFT',
            'The non-self-authorizing bounded proposal acquired authority'
        );
    }
}

validateCoreCategoricalDisplayedEvaluationOwnerProposal();
