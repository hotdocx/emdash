/**
 * USABILITY-DEPENDENT-PLAN-0 proposal for general binder usability.
 *
 * This immutable pre-review record selects a dependent-first semantic
 * architecture and one bounded non-eta witness. It deliberately does not
 * prescribe either shared or separate ordinary/displayed implementation
 * algorithms, and it installs no authority by itself.
 */

import {
    CORE_CATEGORICAL_PROGRAM_REVISION
} from './categorical_program';
import {
    CORE_CATEGORICAL_SURFACE_SPECIFICATION
} from './categorical_surface_spec';
import {
    CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW,
    validateCoreCategoricalUsabilityGraduationReview
} from './categorical_usability_graduation_review';

export interface CoreCategoricalDependentUsabilityProposalInput {
    readonly revision: 'USABILITY-DEPENDENT-PLAN-0';
    readonly status:
        'proposal-awaiting-h-dttlf-usability-dependent';
    readonly reviewGate: 'H-DTTLF-USABILITY-DEPENDENT';
    readonly decisionId: 'D-DTTLF-USABILITY-003';
    readonly recommendation: {
        readonly verdict:
            'approve-dependent-first-consumer-led-continuation';
        readonly semanticArchitecture:
            'contexts-categories-types-displayed-families-terms-sections';
        readonly ordinaryBridge:
            'authority-classified-constant-displayed-family';
        readonly implementationUniformityRequired: false;
        readonly implementationSeparationRequired: false;
        readonly authorityAuthorized: false;
    };
    readonly semanticInterpretation: {
        readonly context: 'category';
        readonly typeOverContext: 'displayed-family';
        readonly term: 'section-object-of-pi-category';
        readonly substitution: 'functorial-displayed-pullback';
        readonly ordinarySpecialization:
            'classified-constant-family-bridge-only';
    };
    readonly solutionCriterion: {
        readonly primary:
            'natural-scalable-generalizable-end-user-usability';
        readonly required: readonly [
            'deterministic-authority-backed-explicit-core',
            'scoped-dependency-and-substitution-preservation',
            'generic-typescript-lf-checking',
            'bounded-lambdapi-conformance',
            'precise-fail-closed-diagnostics',
            'no-owner-named-frontend-hack'
        ];
        readonly algorithmNeutrality:
            'shared-or-distinct-lowering-is-evidence-driven';
    };
    readonly architectureAlternativesRetained: readonly [
        {
            readonly id: 'progressively-shared-contextual-compiler';
            readonly disposition:
                'available-when-ordinary-and-displayed-laws-align';
        },
        {
            readonly id:
                'one-frontend-with-authority-specific-lowerers';
            readonly disposition:
                'available-when-stable-heads-or-owner-bases-differ';
        },
        {
            readonly id: 'data-driven-semantic-contextual-rule-table';
            readonly disposition:
                'consider-after-repeated-consumers-justify-abstraction';
        }
    ];
    readonly firstConsumer: {
        readonly slice: 'USABILITY-DEPENDENT-1A';
        readonly input:
            'λ k :^n K. FF[k](s[k])';
        readonly assumptions: readonly [
            'K : Cat',
            'E D : Catd K',
            'FF : Functord E D',
            's : Obj(Pi_cat E)'
        ];
        readonly output: 'Obj(Pi_cat D)';
        readonly lowering:
            'generic-comp_fapp0-at-Catd_cat-K';
        readonly pointwiseComputation:
            'Fibre_func(FF,k)[piapp0(s,k)]';
        readonly newMathematicalOwnerOrRuleRequired: false;
    };
    readonly proposedImplementation: readonly [
        'indexed-fibre-functor-contextual-classifier',
        'first-order-locally-nameless-FF-k-of-s-k',
        'semantic-section-composition-contextual-law',
        'minimal-active-composition-and-facade-transfer-closure',
        'generic-typescript-lf-infer-and-check',
        'runnable-root-only-demo-and-bounded-conformance'
    ];
    readonly prerequisiteSnapshot: {
        readonly graduationReview:
            'USABILITY-GRADUATE-1-REVIEWED';
        readonly reviewedProgramRevision:
            'USABILITY-2A1-CATEGORICAL-PROGRAM-1';
        readonly frozenApplicationJudgmentCount: 16;
        readonly graduatedEnvelopeUnchanged: true;
    };
    readonly nonEffects: readonly [
        'does-not-require-one-shared-ordinary-displayed-algorithm',
        'does-not-require-permanently-separate-algorithms',
        'does-not-complete-general-dependent-bracket-abstraction',
        'does-not-add-a-lambdapi-owner-or-mathematical-rule',
        'does-not-promote-a-browser-or-product-profile',
        'does-not-select-a-string-parser-or-acquisition-generator',
        'does-not-resume-bulk-library-transfer',
        'does-not-complete-displayed-structural-logic',
        'does-not-broaden-a-metatheory-claim'
    ];
    readonly decisionQuestion: string;
}

export type CoreCategoricalDependentUsabilityProposalErrorCode =
    | 'DEPENDENT_USABILITY_PREREQUISITE_DRIFT'
    | 'DEPENDENT_USABILITY_ARCHITECTURE_DRIFT'
    | 'DEPENDENT_USABILITY_BOUNDARY_DRIFT';

export class CoreCategoricalDependentUsabilityProposalError
extends Error {
    constructor(
        public readonly code:
            CoreCategoricalDependentUsabilityProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreCategoricalDependentUsabilityProposalError';
    }
}

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        Object.freeze(value);
    }
    return value;
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const rawProposal: CoreCategoricalDependentUsabilityProposalInput = {
    revision: 'USABILITY-DEPENDENT-PLAN-0',
    status:
        'proposal-awaiting-h-dttlf-usability-dependent',
    reviewGate: 'H-DTTLF-USABILITY-DEPENDENT',
    decisionId: 'D-DTTLF-USABILITY-003',
    recommendation: {
        verdict:
            'approve-dependent-first-consumer-led-continuation',
        semanticArchitecture:
            'contexts-categories-types-displayed-families-terms-sections',
        ordinaryBridge:
            'authority-classified-constant-displayed-family',
        implementationUniformityRequired: false,
        implementationSeparationRequired: false,
        authorityAuthorized: false
    },
    semanticInterpretation: {
        context: 'category',
        typeOverContext: 'displayed-family',
        term: 'section-object-of-pi-category',
        substitution: 'functorial-displayed-pullback',
        ordinarySpecialization:
            'classified-constant-family-bridge-only'
    },
    solutionCriterion: {
        primary:
            'natural-scalable-generalizable-end-user-usability',
        required: [
            'deterministic-authority-backed-explicit-core',
            'scoped-dependency-and-substitution-preservation',
            'generic-typescript-lf-checking',
            'bounded-lambdapi-conformance',
            'precise-fail-closed-diagnostics',
            'no-owner-named-frontend-hack'
        ],
        algorithmNeutrality:
            'shared-or-distinct-lowering-is-evidence-driven'
    },
    architectureAlternativesRetained: [
        {
            id: 'progressively-shared-contextual-compiler',
            disposition:
                'available-when-ordinary-and-displayed-laws-align'
        },
        {
            id: 'one-frontend-with-authority-specific-lowerers',
            disposition:
                'available-when-stable-heads-or-owner-bases-differ'
        },
        {
            id: 'data-driven-semantic-contextual-rule-table',
            disposition:
                'consider-after-repeated-consumers-justify-abstraction'
        }
    ],
    firstConsumer: {
        slice: 'USABILITY-DEPENDENT-1A',
        input: 'λ k :^n K. FF[k](s[k])',
        assumptions: [
            'K : Cat',
            'E D : Catd K',
            'FF : Functord E D',
            's : Obj(Pi_cat E)'
        ],
        output: 'Obj(Pi_cat D)',
        lowering:
            'generic-comp_fapp0-at-Catd_cat-K',
        pointwiseComputation:
            'Fibre_func(FF,k)[piapp0(s,k)]',
        newMathematicalOwnerOrRuleRequired: false
    },
    proposedImplementation: [
        'indexed-fibre-functor-contextual-classifier',
        'first-order-locally-nameless-FF-k-of-s-k',
        'semantic-section-composition-contextual-law',
        'minimal-active-composition-and-facade-transfer-closure',
        'generic-typescript-lf-infer-and-check',
        'runnable-root-only-demo-and-bounded-conformance'
    ],
    prerequisiteSnapshot: {
        graduationReview:
            'USABILITY-GRADUATE-1-REVIEWED',
        reviewedProgramRevision:
            'USABILITY-2A1-CATEGORICAL-PROGRAM-1',
        frozenApplicationJudgmentCount: 16,
        graduatedEnvelopeUnchanged: true
    },
    nonEffects: [
        'does-not-require-one-shared-ordinary-displayed-algorithm',
        'does-not-require-permanently-separate-algorithms',
        'does-not-complete-general-dependent-bracket-abstraction',
        'does-not-add-a-lambdapi-owner-or-mathematical-rule',
        'does-not-promote-a-browser-or-product-profile',
        'does-not-select-a-string-parser-or-acquisition-generator',
        'does-not-resume-bulk-library-transfer',
        'does-not-complete-displayed-structural-logic',
        'does-not-broaden-a-metatheory-claim'
    ],
    decisionQuestion:
        'Approve H-DTTLF-USABILITY-DEPENDENT/' +
        'D-DTTLF-USABILITY-003 as proposed: retain dependent-first ' +
        'contexts/families/sections and the classified constant-family ' +
        'bridge; select whichever shared or distinct authority-aware ' +
        'implementation naturally solves scalable end-user usability; and ' +
        'implement only USABILITY-DEPENDENT-1A for ' +
        'λ k :^n K. FF[k](s[k]) without a new kernel owner/rule, profile, ' +
        'parser, or bulk transfer?'
};

export const CORE_CATEGORICAL_DEPENDENT_USABILITY_PROPOSAL =
    deepFreeze(rawProposal);

export function validateCoreCategoricalDependentUsabilityProposal(
    proposal: CoreCategoricalDependentUsabilityProposalInput =
        CORE_CATEGORICAL_DEPENDENT_USABILITY_PROPOSAL
): void {
    try {
        validateCoreCategoricalUsabilityGraduationReview(
            CORE_CATEGORICAL_USABILITY_GRADUATION_REVIEW
        );
    } catch (error: unknown) {
        throw new CoreCategoricalDependentUsabilityProposalError(
            'DEPENDENT_USABILITY_PREREQUISITE_DRIFT',
            'Reviewed frontend prerequisite drifted: ' +
            (error instanceof Error ? error.message : String(error))
        );
    }
    if (
        CORE_CATEGORICAL_PROGRAM_REVISION !==
            'USABILITY-2A1-CATEGORICAL-PROGRAM-1' ||
        CORE_CATEGORICAL_SURFACE_SPECIFICATION
            .applications.length !== 16
    ) {
        throw new CoreCategoricalDependentUsabilityProposalError(
            'DEPENDENT_USABILITY_PREREQUISITE_DRIFT',
            'The reviewed program or frozen sixteen-row partition drifted'
        );
    }
    if (
        proposal.recommendation.implementationUniformityRequired ||
        proposal.recommendation.implementationSeparationRequired ||
        proposal.recommendation.authorityAuthorized ||
        proposal.solutionCriterion.algorithmNeutrality !==
            'shared-or-distinct-lowering-is-evidence-driven'
    ) {
        throw new CoreCategoricalDependentUsabilityProposalError(
            'DEPENDENT_USABILITY_ARCHITECTURE_DRIFT',
            'The proposal must remain neutral about shared versus distinct ' +
            'implementation algorithms'
        );
    }
    if (!sameData(proposal, rawProposal)) {
        throw new CoreCategoricalDependentUsabilityProposalError(
            'DEPENDENT_USABILITY_BOUNDARY_DRIFT',
            'USABILITY-DEPENDENT-PLAN-0 proposal drifted'
        );
    }
}

validateCoreCategoricalDependentUsabilityProposal();
