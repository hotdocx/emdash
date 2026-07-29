/**
 * SCALE-INDUCTIVE-1B2 minimal expanded-symbol proposal.
 *
 * HYBRID-0A establishes that importing an already Lambdapi-checked
 * `ind_nat` does not require a second inductive-generation or positivity
 * implementation. This file freezes the exact decision boundary; it adds no
 * semantic engine or product registration.
 */

import {
    CORE_LF_SCALE_INDUCTIVE_HYBRID_0A_AUDIT,
    compileCoreLfScaleInductiveHybrid0aAudit
} from './scale_inductive_hybrid_0a_audit';

export const CORE_LF_SCALE_INDUCTIVE_1B2_REVISION =
    'SCALE-INDUCTIVE-1B2-PROPOSAL-1' as const;

const DECISION_QUESTION =
    'Approve H-DTTLF-SCALE-INDUCTIVE-02/D-DTTLF-SCALE-INDUCTIVE-002 as proposed?' as const;

export interface CoreLfScaleInductive1b2Proposal {
    readonly revision: typeof CORE_LF_SCALE_INDUCTIVE_1B2_REVISION;
    readonly row: 'SCALE-INDUCTIVE-1B2';
    readonly parent: 'SCALE-INDUCTIVE-1B';
    readonly status: 'proposal-awaiting-separate-review';
    readonly selectedArchitecture: {
        readonly trustedSourceBoundary:
            'already-lambdapi-checked-expanded-artifacts';
        readonly generatedDeclaration:
            'ordinary-explicit-opaque-declaration';
        readonly generatedComputation:
            'ordinary-subject-checked-runtime-rules';
        readonly recursiveInductionHypothesis:
            'explicit-successor-rule-right-hand-side';
        readonly consumer:
            'checked-transparent-nat_elim-definition';
        readonly generatedBy:
            'optional-inert-provenance-retained';
        readonly associationDependency: 'none';
        readonly typescriptPositivityDependency: 'none';
    };
    readonly implementationEffects: readonly [
        'retain-HYBRID-0A-exact-ind_nat-type',
        'retain-HYBRID-0A-two-generated-betas',
        'retain-HYBRID-0A-nat_elim-consumer',
        'classify-expanded-owner-transfer-as-qualified',
        'close-SCALE-INDUCTIVE-1B-and-SCALE-INDUCTIVE-1'
    ];
    readonly deferredAlternatives: readonly [
        'recursive-generated-owner-association',
        'typescript-source-inductive-generation',
        'typescript-positivity-checker',
        'automatic-eliminator-synthesis',
        'end-user-inductive-declaration-api',
        'mutual-and-higher-order-inductives'
    ];
    readonly qualificationEvidence: {
        readonly typescript:
            'ordinary-declaration-runtime-conversion-engines-green';
        readonly lambdapi:
            'exact-type-two-betas-and-nat_elim-live-green';
        readonly productEffects: readonly [];
    };
    readonly doesNotAuthorize: readonly [
        'new-lf-connective-or-checker-intrinsic',
        'generated-owner-association-generalization',
        'positivity-or-eliminator-generation',
        'active-profile-or-browser-promotion',
        'lambdapi-source-change',
        'bulk-transfer-graduation',
        'remote-or-history-rewriting-git-operation'
    ];
    readonly decision: {
        readonly humanGate: 'H-DTTLF-SCALE-INDUCTIVE-02';
        readonly decisionId: 'D-DTTLF-SCALE-INDUCTIVE-002';
        readonly status: 'proposal-only';
        readonly question: typeof DECISION_QUESTION;
    };
}

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

const rawProposal: CoreLfScaleInductive1b2Proposal = {
    revision: CORE_LF_SCALE_INDUCTIVE_1B2_REVISION,
    row: 'SCALE-INDUCTIVE-1B2',
    parent: 'SCALE-INDUCTIVE-1B',
    status: 'proposal-awaiting-separate-review',
    selectedArchitecture: {
        trustedSourceBoundary:
            'already-lambdapi-checked-expanded-artifacts',
        generatedDeclaration:
            'ordinary-explicit-opaque-declaration',
        generatedComputation:
            'ordinary-subject-checked-runtime-rules',
        recursiveInductionHypothesis:
            'explicit-successor-rule-right-hand-side',
        consumer:
            'checked-transparent-nat_elim-definition',
        generatedBy:
            'optional-inert-provenance-retained',
        associationDependency: 'none',
        typescriptPositivityDependency: 'none'
    },
    implementationEffects: [
        'retain-HYBRID-0A-exact-ind_nat-type',
        'retain-HYBRID-0A-two-generated-betas',
        'retain-HYBRID-0A-nat_elim-consumer',
        'classify-expanded-owner-transfer-as-qualified',
        'close-SCALE-INDUCTIVE-1B-and-SCALE-INDUCTIVE-1'
    ],
    deferredAlternatives: [
        'recursive-generated-owner-association',
        'typescript-source-inductive-generation',
        'typescript-positivity-checker',
        'automatic-eliminator-synthesis',
        'end-user-inductive-declaration-api',
        'mutual-and-higher-order-inductives'
    ],
    qualificationEvidence: {
        typescript:
            'ordinary-declaration-runtime-conversion-engines-green',
        lambdapi:
            'exact-type-two-betas-and-nat_elim-live-green',
        productEffects: []
    },
    doesNotAuthorize: [
        'new-lf-connective-or-checker-intrinsic',
        'generated-owner-association-generalization',
        'positivity-or-eliminator-generation',
        'active-profile-or-browser-promotion',
        'lambdapi-source-change',
        'bulk-transfer-graduation',
        'remote-or-history-rewriting-git-operation'
    ],
    decision: {
        humanGate: 'H-DTTLF-SCALE-INDUCTIVE-02',
        decisionId: 'D-DTTLF-SCALE-INDUCTIVE-002',
        status: 'proposal-only',
        question: DECISION_QUESTION
    }
};

export const CORE_LF_SCALE_INDUCTIVE_1B2_PROPOSAL =
    deepFreeze(rawProposal);

export type CoreLfScaleInductive1b2ProposalErrorCode =
    | 'AUDIT_EVIDENCE_DRIFT'
    | 'PROPOSAL_BOUNDARY_DRIFT';

export class CoreLfScaleInductive1b2ProposalError extends Error {
    constructor(
        public readonly code:
            CoreLfScaleInductive1b2ProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfScaleInductive1b2ProposalError';
    }
}

const fail = (
    code: CoreLfScaleInductive1b2ProposalErrorCode,
    message: string
): never => {
    throw new CoreLfScaleInductive1b2ProposalError(
        code,
        message
    );
};

const sameData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

export function validateCoreLfScaleInductive1b2Proposal(
    proposal: CoreLfScaleInductive1b2Proposal =
        CORE_LF_SCALE_INDUCTIVE_1B2_PROPOSAL
): CoreLfScaleInductive1b2Proposal {
    const audit = CORE_LF_SCALE_INDUCTIVE_HYBRID_0A_AUDIT;
    const compiled = compileCoreLfScaleInductiveHybrid0aAudit();
    if (
        audit.conclusion.associationDependency !== 'none' ||
        audit.conclusion.positivityRequirement !==
            'not-required-for-expanded-symbol-transfer' ||
        compiled.contract.latestRuntime?.runtime.ruleIds.join(',') !==
            'inductive.expanded.nat-zero,' +
            'inductive.expanded.nat-succ,' +
            'inductive.expanded.nat-grpd-decode' ||
        compiled.contract.declarations.declaration(
            compiled.contractModule.declarations[2].symbol
        )?.status !== 'installed-transparent'
    ) {
        return fail(
            'AUDIT_EVIDENCE_DRIFT',
            'HYBRID-0A expanded ind_nat evidence drifted'
        );
    }
    if (
        proposal.status !== 'proposal-awaiting-separate-review' ||
        proposal.decision.status !== 'proposal-only' ||
        proposal.decision.question !== DECISION_QUESTION ||
        proposal.qualificationEvidence.productEffects.length !== 0 ||
        !sameData(proposal, rawProposal)
    ) {
        return fail(
            'PROPOSAL_BOUNDARY_DRIFT',
            'SCALE-INDUCTIVE-1B2 proposal boundary drifted'
        );
    }
    return proposal;
}

validateCoreLfScaleInductive1b2Proposal();
