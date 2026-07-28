/**
 * DISPLAYED-BRACKET-0A successor proposal.
 *
 * This proposal selects a generic first-order displayed contextual compiler
 * over extending the current rigid-chain recognizer, routing all terms
 * through total categories, or adding a kernel bracket owner. Its first
 * implementation row is restricted to finite independent siblings over one
 * common base and existing active authority.
 */

import {
    CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION
} from './categorical_context_dependencies';
import {
    CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT
} from './categorical_fibred_binder_contract';
import {
    CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW,
    validateCoreCategoricalFibredGraduationReview
} from './categorical_fibred_graduation_review';
import {
    CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY
} from './categorical_fibred_structure_transfer';
import {
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT
} from './categorical_fibred_weaken_reindex_contract';
import {
    CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT
} from './categorical_grouped_sequential_contract';

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

const rawProposal = {
    revision: 'DISPLAYED-BRACKET-0A-PROPOSAL-1',
    status:
        'proposal-awaiting-h-dttlf-usability-displayed-bracket-01',
    reviewGate: 'H-DTTLF-USABILITY-DISPLAYED-BRACKET-01',
    decisionId: 'D-DTTLF-USABILITY-009',
    prerequisite: {
        graduationDecision: 'D-DTTLF-USABILITY-008',
        graduationReviewRevision:
            CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW.revision,
        qualifiedArchitectureSettled: true,
        successorAutomaticallyAuthorized: false
    },
    problem: {
        currentDirectBinder:
            'one-hidden-base-plus-one-fibre-slot-rigid-body-recognizer',
        currentlyAcceptedBodies: [
            'identity',
            'eta',
            'finite-closed-displayed-functor-chain',
            'exact-closed-section-weakening'
        ],
        missingCapability:
            'first-order-contextual-displayed-body-compilation',
        usabilityTarget:
            'finite-context-variable-use-to-existing-displayed-structure',
        mustNotAssume: [
            'generic-total-category-pullback-or-equivalence',
            'sigma-introduction-arrow-action',
            'general-pointwise-coherence-synthesis',
            'new-kernel-bracket-owner'
        ]
    },
    implementationInventory: {
        contextualIrCurrentlyExecutable: [
            'slot-reference',
            'explicit-core-term',
            'typed-application',
            'categorical-abstraction'
        ],
        specifiedButNotExecutableAsNodes: [
            'typed-pair',
            'typed-composition'
        ],
        reusableGenericMechanisms: [
            'locally-nameless-slot-identity-and-usage',
            'callback-once-immediate-reification',
            'dependency-graph-and-sibling-analysis',
            'source-provenance-and-fail-closed-scope',
            'generic-explicit-core-checking-and-evaluation'
        ],
        reusableDisplayedAuthority: [
            'id_funcd',
            'comp_fapp0',
            'Product_projL_funcd',
            'Product_projR_funcd',
            'Product_pair_funcd',
            'section_pullback_func',
            'Pullback_catd_func'
        ]
    },
    alternatives: [
        {
            id: 'extend-rigid-body-recognizer',
            status: 'rejected',
            reason:
                'adds syntax-specific cases instead of compiling a ' +
                'first-order contextual language'
        },
        {
            id: 'generic-displayed-contextual-compiler',
            status: 'selected',
            reason:
                'reuses locally nameless dependency and structural planning ' +
                'while emitting only qualified existing owners'
        },
        {
            id: 'total-context-ordinary-bracket-only',
            status: 'deferred-not-selected',
            reason:
                'does not preserve the direct displayed presentation and ' +
                'depends on withheld total-category and arrow comparisons'
        },
        {
            id: 'new-kernel-displayed-bracket-owner',
            status: 'rejected-unnecessary',
            reason:
                'the first consumer factors through existing displayed ' +
                'identity-composition-projection-pairing authority'
        }
    ],
    selectedArchitecture: {
        id: 'generic-displayed-contextual-compiler',
        frontendLayer:
            'first-order-locally-nameless-displayed-contextual-ir',
        publicMethod: 'displayedContextLambda',
        pairConstructor: 'fibrePair',
        callbackEvaluationCount: 1,
        callbackStoredAfterConstruction: false,
        dependencyFlagsSuppliedByUser: false,
        primitiveCoreBinderModeAdded: false,
        ownerSpecificCheckerOrEvaluatorBranchAdded: false,
        directDisplayedPresentationPreserved: true
    },
    firstImplementationRow: {
        id: 'DISPLAYED-BRACKET-1A',
        profile: 'fibred-displayed-bracket-1',
        visibility: 'root-only',
        contextScope:
            'finite-nonempty-independent-sibling-block-over-common-base',
        sourcePresentation:
            'left-associated-transparent-displayed-product',
        bodyGrammar: [
            'displayed-slot-reference',
            'closed-displayed-functor-application',
            'typed-fibre-pair'
        ],
        requiredNewFrontendNode: 'typed-pair',
        typedCompositionNodeRequiredInitially: false,
        lowering: {
            singleSlot: 'id_funcd',
            siblingSelection:
                'nested-Product_projL_funcd-or-Product_projR_funcd',
            closedFunctorApplication:
                'comp_fapp0-with-compiled-argument',
            pair: 'Product_pair_funcd',
            exchange:
                'Product_pair_funcd-of-reordered-projections',
            contraction:
                'Product_pair_funcd-of-repeated-compiled-branch',
            exactClosedWeakening:
                'retain-existing-section_pullback_func-route'
        },
        structuralUsePolicy: {
            zeroUse:
                'discard-unused-product-factors-through-selected-projection',
            oneUse: 'identity-or-selected-projection',
            repeatedUse:
                'compile-each-branch-and-pair-no-primitive-diagonal-owner',
            permutation:
                'reorder-projection-wiring-no-primitive-swap-owner'
        },
        positiveCorpus: [
            'lambda-(b,c)-left-projection',
            'lambda-(b,c)-swap-pair',
            'lambda-b-diagonal-pair',
            'lambda-(b,c)-pair-of-FF-b-and-GG-c',
            'lambda-(a,b,c)-finite-left-associated-projection-and-pair',
            'existing-one-slot-identity-eta-composition-and-weakening'
        ],
        negativeCorpus: [
            'genuine-dependency-edge-in-requested-sibling-block',
            'families-over-different-bases',
            'body-over-wrong-target-family',
            'escaped-or-foreign-slot',
            'arbitrary-pointwise-coherence',
            'unsupported-open-displayed-functor-subject',
            'default-earlier-profile-access'
        ],
        semanticDelta: {
            newLambdapiOwners: 0,
            newLambdapiRuntimeRules: 0,
            newLambdapiProofRules: 0,
            newIntrinsicCoreOwners: 0,
            browserProfilePromotion: false
        }
    },
    scalabilityBoundary: {
        provenByFirstRow: [
            'finite-independent-sibling-count',
            'generic-usage-driven-projection-pairing',
            'exchange-and-contraction-as-derived-wiring',
            'composition-with-closed-displayed-functors',
            'one-first-order-compiler-not-body-shape-recognizers'
        ],
        notProvenByFirstRow: [
            'genuine-dependent-chain-body-compilation',
            'arbitrary-context-dependent-functor-subjects',
            'general-nd-coherence-synthesis',
            'total-category-equivalence',
            'sigma-arrow-action'
        ]
    },
    followOnRows: [
        {
            id: 'DISPLAYED-CHAIN-0A',
            purpose:
                'compare sequential-total, pullback-Sigma, and direct ' +
                'displayed lowerings for a genuine dependency edge',
            implementationAuthorized: false
        },
        {
            id: 'DISPLAYED-ND-0A',
            purpose:
                'audit general coherent displayed-transfor abstraction ' +
                'after the fd body compiler is established',
            implementationAuthorized: false
        },
        {
            id: 'DISPLAYED-BRACKET-GRADUATE-1',
            purpose:
                'reassess general displayed usability after independent ' +
                'and genuine-chain evidence',
            implementationAuthorized: false
        }
    ],
    decisionEffects: {
        selectsArchitecture: true,
        authorizesDisplayedBracket1A: true,
        addsKernelMathematicsByDecision: false,
        authorizesDisplayedChainImplementation: false,
        authorizesGeneralNdCoherence: false,
        authorizesTotalCategoryComparison: false,
        authorizesParsingOrBulkTransfer: false,
        authorizesBrowserPromotion: false,
        broadensGitAuthority: false
    },
    validationPlan: [
        'proposal-deep-freeze-and-live-boundary-validation',
        'focused-ir-lowering-and-negative-tests',
        'root-check-ts',
        'unchanged-live-lambdapi-conformance',
        'exact-staged-diff-and-local-checkpoint'
    ],
    decisionQuestion:
        'Approve H-DTTLF-USABILITY-DISPLAYED-BRACKET-01/' +
        'D-DTTLF-USABILITY-009 as proposed: select a generic first-order ' +
        'displayed contextual compiler instead of extending the rigid body ' +
        'recognizer; authorize root-only DISPLAYED-BRACKET-1A for finite ' +
        'independent sibling blocks using typed-pair IR plus existing ' +
        'identity, composition, projection, pairing, section-weakening, ' +
        'and reindexing authority; add no Lambdapi owner or rule; and keep ' +
        'genuine dependent-chain lowering, general :^nd coherence, Sigma ' +
        'arrow action, total-category comparison, parsing/bulk transfer, ' +
        'and browser promotion as separate rows?'
} as const;

export type CoreCategoricalDisplayedBracketProposalInput =
    typeof rawProposal;

export type CoreCategoricalDisplayedBracketProposalErrorCode =
    | 'DISPLAYED_BRACKET_PREREQUISITE_DRIFT'
    | 'DISPLAYED_BRACKET_SELECTION_DRIFT'
    | 'DISPLAYED_BRACKET_AUTHORITY_DRIFT'
    | 'DISPLAYED_BRACKET_PROPOSAL_DRIFT';

export class CoreCategoricalDisplayedBracketProposalError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDisplayedBracketProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDisplayedBracketProposalError';
    }
}

export const CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL =
    deepFreeze(rawProposal);

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCoreCategoricalDisplayedBracketProposal(
    proposal: CoreCategoricalDisplayedBracketProposalInput =
        CORE_CATEGORICAL_DISPLAYED_BRACKET_PROPOSAL
): void {
    try {
        validateCoreCategoricalFibredGraduationReview();
    } catch (error: unknown) {
        throw new CoreCategoricalDisplayedBracketProposalError(
            'DISPLAYED_BRACKET_PREREQUISITE_DRIFT',
            'The qualified fibred architecture review drifted: ' +
                (error instanceof Error ? error.message : String(error))
        );
    }

    if (
        proposal.prerequisite.graduationDecision !==
            'D-DTTLF-USABILITY-008' ||
        proposal.prerequisite.graduationReviewRevision !==
            CORE_CATEGORICAL_FIBRED_GRADUATION_REVIEW.revision ||
        !proposal.prerequisite.qualifiedArchitectureSettled ||
        proposal.prerequisite.successorAutomaticallyAuthorized ||
        CORE_CATEGORICAL_CONTEXT_DEPENDENCY_REVISION !==
            'FIBRED-CONTEXT-0B' ||
        CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT
            .supportedBodies.map(body => body.id).join(',') !==
                'identity,eta,composition' ||
        CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT
            .input.minimumSiblingCount !== 2 ||
        !CORE_CATEGORICAL_GROUPED_SEQUENTIAL_CONTRACT
            .input.genuineDependencyEdgeRejected
    ) {
        throw new CoreCategoricalDisplayedBracketProposalError(
            'DISPLAYED_BRACKET_PREREQUISITE_DRIFT',
            'The completed binder or dependency-planning boundary drifted'
        );
    }

    if (
        proposal.alternatives.filter(
            alternative => alternative.status === 'selected'
        ).map(alternative => alternative.id).join(',') !==
            'generic-displayed-contextual-compiler' ||
        proposal.selectedArchitecture.id !==
            'generic-displayed-contextual-compiler' ||
        proposal.selectedArchitecture.publicMethod !==
            'displayedContextLambda' ||
        proposal.firstImplementationRow.id !==
            'DISPLAYED-BRACKET-1A' ||
        proposal.firstImplementationRow.requiredNewFrontendNode !==
            'typed-pair' ||
        proposal.firstImplementationRow
            .typedCompositionNodeRequiredInitially
    ) {
        throw new CoreCategoricalDisplayedBracketProposalError(
            'DISPLAYED_BRACKET_SELECTION_DRIFT',
            'The generic first-order displayed-bracket selection drifted'
        );
    }

    const delta = proposal.firstImplementationRow.semanticDelta;
    if (
        Object.values(delta).some(Boolean) ||
        proposal.selectedArchitecture.primitiveCoreBinderModeAdded ||
        proposal.selectedArchitecture
            .ownerSpecificCheckerOrEvaluatorBranchAdded ||
        CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY
            .newOwnerNames.join(',') !==
                'Product_projL_funcd,Product_projR_funcd,' +
                'Product_pair_funcd' ||
        CORE_CATEGORICAL_FIBRED_STRUCTURE_TRANSFER_BOUNDARY
            .productFamilyOwnerAdded ||
        CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CONTRACT
            .surface.primitiveCoreBinderModeAdded ||
        proposal.decisionEffects.addsKernelMathematicsByDecision ||
        proposal.decisionEffects
            .authorizesDisplayedChainImplementation ||
        proposal.decisionEffects.authorizesGeneralNdCoherence ||
        proposal.decisionEffects.authorizesTotalCategoryComparison ||
        proposal.decisionEffects.authorizesParsingOrBulkTransfer ||
        proposal.decisionEffects.authorizesBrowserPromotion ||
        proposal.decisionEffects.broadensGitAuthority
    ) {
        throw new CoreCategoricalDisplayedBracketProposalError(
            'DISPLAYED_BRACKET_AUTHORITY_DRIFT',
            'The proposal would add mathematics or broaden a withheld row'
        );
    }

    if (
        proposal.revision !==
            'DISPLAYED-BRACKET-0A-PROPOSAL-1' ||
        proposal.status !==
            'proposal-awaiting-h-dttlf-usability-displayed-bracket-01' ||
        proposal.reviewGate !==
            'H-DTTLF-USABILITY-DISPLAYED-BRACKET-01' ||
        proposal.decisionId !== 'D-DTTLF-USABILITY-009' ||
        !proposal.decisionEffects.selectsArchitecture ||
        !proposal.decisionEffects.authorizesDisplayedBracket1A ||
        !sameData(proposal, rawProposal)
    ) {
        throw new CoreCategoricalDisplayedBracketProposalError(
            'DISPLAYED_BRACKET_PROPOSAL_DRIFT',
            'The exact displayed-bracket proposal or decision drifted'
        );
    }
}

validateCoreCategoricalDisplayedBracketProposal();
