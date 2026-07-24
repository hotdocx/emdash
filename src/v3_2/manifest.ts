/**
 * Reviewable, backend-neutral signature and rule-manifest vocabulary.
 *
 * TSK-1A records the pre-review proposal. TSK-1B preserves that proposal as
 * audit evidence and exposes a separate reviewed, frozen product profile.
 * Nothing in this module matches a rule, evaluates a term, or grants
 * proof-time comparison powers to the structural checker.
 */

import { createHash } from 'node:crypto';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId
} from './schema';
import {
    CORE_OWNER_TYPE_SCHEMAS,
    CoreOwnerTypeSchema,
    CoreSignatureExpression
} from './signature';

export const CORE_MANIFEST_CONSUMERS = {
    'elab-0-object-and-arrow': {
        description: 'ordinary object and arrow projection consumers'
    },
    'elab-1b-projection-ladder': {
        description: 'full/capped ordinary projection consumers'
    },
    'elab-1b-recursive-2-cell': {
        description: 'recursive reuse of the ordinary hom-action schema'
    },
    'elab-1c-internal-hom': {
        description: 'retained source- and target-varying internal homs'
    },
    'elab-2a3-signature-checker': {
        description: 'uniform owner signatures and structural checking'
    },
    'elab-2b-dependent-context': {
        description: 'displayed context, reindexing, family, and section route'
    },
    'elab-2b-constant-section': {
        description: 'constant-section comparison and non-collapse boundary'
    }
} as const;

export type CoreManifestConsumerId = keyof typeof CORE_MANIFEST_CONSUMERS;

export type CoreManifestOpenRisk =
    | 'consumer-scope'
    | 'rule-inventory'
    | 'termination'
    | 'confluence'
    | 'subject-reduction'
    | 'human-gate-h01';

export type CoreManifestOwnerMembership =
    | 'mvp-candidate'
    | 'conformance-only';

export interface CoreManifestOwnerExclusionInput {
    readonly reason: string;
    readonly openRisks: readonly CoreManifestOpenRisk[];
}

export interface CoreManifestOwnerEntryInput {
    readonly order: number;
    readonly owner: string;
    readonly membership: CoreManifestOwnerMembership;
    readonly consumers: readonly string[];
    readonly exclusion?: CoreManifestOwnerExclusionInput;
}

export type CoreRuleAuthorityClass =
    | 'runtime-reduction'
    | 'proof-time-comparison'
    | 'intentional-non-conversion';

export type CoreRuleDisposition =
    | 'mvp-candidate'
    | 'conformance-evidence';

export type CoreManifestRuleId =
    | 'projection.functor-hom.evaluate'
    | 'projection.transfor-component.evaluate'
    | 'projection.transfor-hom.evaluate'
    | 'comparison.constant-section'
    | 'nonconversion.constant-section.runtime';

export type CoreRulePatternInput =
    | {
        readonly tag: 'variable';
        readonly name: string;
    }
    | {
        readonly tag: 'owner-application';
        readonly owner: string;
        readonly arguments: readonly CoreRulePatternInput[];
    };

export interface CoreRuleComparisonInput {
    readonly left: CoreRulePatternInput;
    readonly right: CoreRulePatternInput;
}

export interface CoreRuleProvenanceInput {
    /**
     * Semantic evidence key. A conformance backend binds this key to its own
     * source path and spelling outside Core.
     */
    readonly evidence: string;
    readonly auditedOn: string;
}

export interface CoreManifestRuleInput {
    readonly order: number;
    readonly id: string;
    readonly authority: CoreRuleAuthorityClass;
    readonly disposition: CoreRuleDisposition;
    readonly variables: readonly string[];
    readonly left: CoreRulePatternInput;
    readonly right: CoreRulePatternInput;
    readonly consequences?: readonly CoreRuleComparisonInput[];
    readonly provenance: CoreRuleProvenanceInput;
    readonly consumers: readonly string[];
}

interface KnownCoreManifestRule extends CoreManifestRuleInput {
    readonly id: CoreManifestRuleId;
    readonly provenance: CoreRuleProvenanceInput & {
        readonly evidence: CoreManifestRuleId;
    };
}

export interface CoreManifestRuleFamilyExclusionInput {
    readonly order: number;
    readonly id: string;
    readonly ownerReferences: readonly string[];
    readonly reason: string;
    readonly openRisks: readonly CoreManifestOpenRisk[];
}

export interface CoreManifestRecommendationInput {
    readonly gate: string;
    readonly state: string;
    readonly ownerIds: readonly string[];
    readonly runtimeRuleIds: readonly string[];
    readonly proofTimeRuleIds: readonly string[];
    readonly nonConversionEvidenceIds: readonly string[];
    readonly rationale: string;
}

export interface CoreManifestProposalInput {
    readonly status: string;
    readonly ruleSelection: string;
    readonly owners: readonly CoreManifestOwnerEntryInput[];
    readonly rules: readonly CoreManifestRuleInput[];
    readonly excludedRuleFamilies:
        readonly CoreManifestRuleFamilyExclusionInput[];
    readonly recommendation: CoreManifestRecommendationInput;
}

export interface CoreManifestApprovalInput {
    readonly gate: string;
    readonly decision: string;
    readonly decisionId: string;
    readonly reviewedOn: string;
}

export interface CoreMvpOwnerSignatureInput {
    readonly order: number;
    readonly owner: string;
    readonly signature: CoreOwnerTypeSchema;
}

/**
 * Machine-readable boundary between the reviewed product profile, mechanisms
 * that exist but are not yet implemented for that profile, and surrounding
 * elaboration/conformance infrastructure.
 */
export interface CoreMvpTrustBoundaryInput {
    readonly implementedKernelMechanisms: readonly string[];
    readonly frozenButDeferredMechanisms: readonly string[];
    readonly outsideTrustedKernel: readonly string[];
    readonly conformanceOnlyOwnerIds: readonly string[];
    readonly conformanceEvidenceIds: readonly string[];
}

export interface CoreMvpManifestInput {
    readonly status: string;
    readonly revision: string;
    readonly ruleSelection: string;
    readonly approval: CoreManifestApprovalInput;
    readonly owners: readonly CoreMvpOwnerSignatureInput[];
    readonly rules: readonly CoreManifestRuleInput[];
    readonly trustBoundary: CoreMvpTrustBoundaryInput;
    readonly contentHash: string;
}

export type CoreManifestValidationCode =
    | 'INVALID_PROPOSAL_STATUS'
    | 'INVALID_FROZEN_STATUS'
    | 'INVALID_REVIEW_APPROVAL'
    | 'UNKNOWN_CONSUMER'
    | 'EMPTY_CONSUMER_COVERAGE'
    | 'UNKNOWN_OWNER'
    | 'DUPLICATE_OWNER'
    | 'INCOMPLETE_OWNER_COVERAGE'
    | 'OWNER_ORDER_MISMATCH'
    | 'OWNER_MEMBERSHIP_MISMATCH'
    | 'CANDIDATE_SIGNATURE_DEPENDENCY'
    | 'INVALID_RULE_ID'
    | 'DUPLICATE_RULE_ID'
    | 'RULE_ORDER_MISMATCH'
    | 'DUPLICATE_RULE_VARIABLE'
    | 'UNUSED_RULE_VARIABLE'
    | 'UNBOUND_RULE_VARIABLE'
    | 'MALFORMED_RULE_PATTERN'
    | 'UNKNOWN_RULE_OWNER'
    | 'RULE_OWNER_ARITY_MISMATCH'
    | 'RUNTIME_SCOPE_ESCAPE'
    | 'COMPARISON_CONSEQUENCE_SCOPE_ESCAPE'
    | 'AUTHORITY_SHAPE_MISMATCH'
    | 'CANDIDATE_RULE_USES_EXCLUDED_OWNER'
    | 'DUPLICATE_RULE_EVIDENCE'
    | 'INCOMPLETE_RULE_PROVENANCE'
    | 'RULE_FAMILY_ORDER_MISMATCH'
    | 'RECOMMENDATION_MISMATCH'
    | 'FROZEN_OWNER_MISMATCH'
    | 'FROZEN_SIGNATURE_MISMATCH'
    | 'FROZEN_RULE_MISMATCH'
    | 'TRUST_BOUNDARY_MISMATCH'
    | 'FROZEN_CONTENT_HASH_MISMATCH';

export class CoreManifestValidationError extends Error {
    constructor(
        public readonly code: CoreManifestValidationCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreManifestValidationError';
    }
}

const ownerIds = (): readonly CoreOwnerId[] =>
    Object.keys(CORE_OWNER_SCHEMAS) as CoreOwnerId[];

const isOwnerId = (owner: string): owner is CoreOwnerId =>
    Object.prototype.hasOwnProperty.call(CORE_OWNER_SCHEMAS, owner);

const validateConsumerCoverage = (
    consumers: readonly string[],
    role: string
): void => {
    if (consumers.length === 0) {
        throw new CoreManifestValidationError(
            'EMPTY_CONSUMER_COVERAGE',
            `${role} has no consumer coverage`
        );
    }
    for (const consumer of consumers) {
        if (!Object.prototype.hasOwnProperty.call(
            CORE_MANIFEST_CONSUMERS,
            consumer
        )) {
            throw new CoreManifestValidationError(
                'UNKNOWN_CONSUMER',
                `${role} refers to unknown consumer '${consumer}'`
            );
        }
    }
};

const collectSignatureOwnerReferences = (
    expression: CoreSignatureExpression,
    result: Set<CoreOwnerId>
): void => {
    switch (expression.tag) {
        case 'universe':
        case 'slot':
            return;
        case 'owner-application':
            result.add(expression.owner);
            expression.arguments.forEach(argument =>
                collectSignatureOwnerReferences(argument, result)
            );
            return;
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const validateOwners = (
    entries: readonly CoreManifestOwnerEntryInput[]
): ReadonlySet<CoreOwnerId> => {
    const catalogOwners = ownerIds();
    const seen = new Set<string>();

    for (const entry of entries) {
        if (!isOwnerId(entry.owner)) {
            throw new CoreManifestValidationError(
                'UNKNOWN_OWNER',
                `Manifest owner entry refers to unknown owner '${entry.owner}'`
            );
        }
        if (seen.has(entry.owner)) {
            throw new CoreManifestValidationError(
                'DUPLICATE_OWNER',
                `Manifest owner '${entry.owner}' occurs more than once`
            );
        }
        seen.add(entry.owner);
    }

    if (entries.length !== catalogOwners.length) {
        const missing = catalogOwners.filter(owner => !seen.has(owner));
        throw new CoreManifestValidationError(
            'INCOMPLETE_OWNER_COVERAGE',
            `Manifest owner coverage has ${entries.length} entries, expected ` +
            `${catalogOwners.length}; missing: ${missing.join(', ') || 'none'}`
        );
    }

    entries.forEach((entry, index) => {
        const expected = catalogOwners[index];
        if (entry.order !== index || entry.owner !== expected) {
            throw new CoreManifestValidationError(
                'OWNER_ORDER_MISMATCH',
                `Manifest owner entry ${index} is order ${entry.order} ` +
                `'${entry.owner}', expected order ${index} '${expected}'`
            );
        }
        validateConsumerCoverage(
            entry.consumers,
            `Manifest owner '${entry.owner}'`
        );
        if (
            entry.membership !== 'mvp-candidate' &&
            entry.membership !== 'conformance-only'
        ) {
            throw new CoreManifestValidationError(
                'OWNER_MEMBERSHIP_MISMATCH',
                `Manifest owner '${entry.owner}' has unknown membership ` +
                `'${entry.membership}'`
            );
        }
        if (entry.membership === 'mvp-candidate' && entry.exclusion) {
            throw new CoreManifestValidationError(
                'OWNER_MEMBERSHIP_MISMATCH',
                `MVP candidate owner '${entry.owner}' cannot carry exclusion ` +
                'metadata'
            );
        }
        if (entry.membership === 'conformance-only') {
            if (
                !entry.exclusion ||
                entry.exclusion.reason.trim().length === 0 ||
                entry.exclusion.openRisks.length === 0
            ) {
                throw new CoreManifestValidationError(
                    'OWNER_MEMBERSHIP_MISMATCH',
                    `Conformance-only owner '${entry.owner}' requires a ` +
                    'reason and at least one open risk'
                );
            }
        }
    });

    const candidates = new Set(
        entries
            .filter(entry => entry.membership === 'mvp-candidate')
            .map(entry => entry.owner as CoreOwnerId)
    );

    for (const owner of candidates) {
        const references = new Set<CoreOwnerId>();
        const signature: CoreOwnerTypeSchema =
            CORE_OWNER_TYPE_SCHEMAS[owner];
        signature.slots.forEach(slot =>
            collectSignatureOwnerReferences(slot.type, references)
        );
        collectSignatureOwnerReferences(signature.result, references);
        for (const reference of references) {
            if (!candidates.has(reference)) {
                throw new CoreManifestValidationError(
                    'CANDIDATE_SIGNATURE_DEPENDENCY',
                    `MVP candidate owner '${owner}' signature depends on ` +
                    `excluded owner '${reference}'`
                );
            }
        }
    }

    return candidates;
};

interface CollectedPattern {
    readonly owners: ReadonlySet<CoreOwnerId>;
    readonly variables: ReadonlySet<string>;
}

const validatePattern = (
    pattern: CoreRulePatternInput,
    declaredVariables: ReadonlySet<string>,
    role: string,
    owners: Set<CoreOwnerId>,
    variables: Set<string>
): void => {
    switch (pattern.tag) {
        case 'variable':
            if (!declaredVariables.has(pattern.name)) {
                throw new CoreManifestValidationError(
                    'UNBOUND_RULE_VARIABLE',
                    `${role} refers to undeclared variable '${pattern.name}'`
                );
            }
            variables.add(pattern.name);
            return;
        case 'owner-application':
            if (!isOwnerId(pattern.owner)) {
                throw new CoreManifestValidationError(
                    'UNKNOWN_RULE_OWNER',
                    `${role} refers to unknown owner '${pattern.owner}'`
                );
            }
            owners.add(pattern.owner);
            if (
                pattern.arguments.length !==
                CORE_OWNER_SCHEMAS[pattern.owner].slots.length
            ) {
                throw new CoreManifestValidationError(
                    'RULE_OWNER_ARITY_MISMATCH',
                    `${role} applies owner '${pattern.owner}' to ` +
                    `${pattern.arguments.length} arguments, expected ` +
                    CORE_OWNER_SCHEMAS[pattern.owner].slots.length
                );
            }
            pattern.arguments.forEach((argument, index) =>
                validatePattern(
                    argument,
                    declaredVariables,
                    `${role}, ${pattern.owner} argument ${index}`,
                    owners,
                    variables
                )
            );
            return;
        default: {
            throw new CoreManifestValidationError(
                'MALFORMED_RULE_PATTERN',
                `${role} has unknown pattern tag ` +
                `'${(pattern as { tag?: string }).tag ?? 'missing'}'`
            );
        }
    }
};

const collectValidatedPattern = (
    pattern: CoreRulePatternInput,
    declaredVariables: ReadonlySet<string>,
    role: string
): CollectedPattern => {
    const owners = new Set<CoreOwnerId>();
    const variables = new Set<string>();
    validatePattern(
        pattern,
        declaredVariables,
        role,
        owners,
        variables
    );
    return { owners, variables };
};

const setUnion = <T>(
    left: ReadonlySet<T>,
    right: ReadonlySet<T>
): Set<T> => new Set([...left, ...right]);

const validateAuthorityShape = (
    rule: CoreManifestRuleInput,
    leftVariables: ReadonlySet<string>,
    rightVariables: ReadonlySet<string>
): void => {
    const consequences = rule.consequences ?? [];
    switch (rule.authority) {
        case 'runtime-reduction':
            if (consequences.length > 0) {
                throw new CoreManifestValidationError(
                    'AUTHORITY_SHAPE_MISMATCH',
                    `Runtime rule '${rule.id}' cannot carry proof-time ` +
                    'consequences'
                );
            }
            if (rule.left.tag !== 'owner-application') {
                throw new CoreManifestValidationError(
                    'AUTHORITY_SHAPE_MISMATCH',
                    `Runtime rule '${rule.id}' must have an owner application ` +
                    'at its left root'
                );
            }
            for (const variable of rightVariables) {
                if (!leftVariables.has(variable)) {
                    throw new CoreManifestValidationError(
                        'RUNTIME_SCOPE_ESCAPE',
                        `Runtime rule '${rule.id}' right side introduces ` +
                        `variable '${variable}' absent from its left side`
                    );
                }
            }
            return;
        case 'proof-time-comparison':
            if (consequences.length === 0) {
                throw new CoreManifestValidationError(
                    'AUTHORITY_SHAPE_MISMATCH',
                    `Proof-time rule '${rule.id}' requires at least one ` +
                    'comparison consequence'
                );
            }
            if (
                rule.left.tag !== 'owner-application' ||
                rule.right.tag !== 'owner-application'
            ) {
                throw new CoreManifestValidationError(
                    'AUTHORITY_SHAPE_MISMATCH',
                    `Proof-time rule '${rule.id}' must compare two owner ` +
                    'applications'
                );
            }
            return;
        case 'intentional-non-conversion':
            if (
                consequences.length > 0 ||
                rule.disposition !== 'conformance-evidence' ||
                rule.left.tag !== 'owner-application' ||
                rule.right.tag !== 'owner-application'
            ) {
                throw new CoreManifestValidationError(
                    'AUTHORITY_SHAPE_MISMATCH',
                    `Intentional non-conversion '${rule.id}' must be ` +
                    'non-executable conformance evidence with no consequences'
                );
            }
            return;
        default: {
            const exhaustive: never = rule.authority;
            return exhaustive;
        }
    }
};

const validateRules = (
    rules: readonly CoreManifestRuleInput[],
    candidateOwners: ReadonlySet<CoreOwnerId>
): void => {
    const seenIds = new Set<string>();
    const seenEvidence = new Set<string>();
    const validRuleId = /^[a-z][a-z0-9]*(?:[.-][a-z0-9]+)*$/;
    const validVariable = /^[A-Za-z][A-Za-z0-9_]*$/;

    rules.forEach((rule, index) => {
        if (
            rule.authority !== 'runtime-reduction' &&
            rule.authority !== 'proof-time-comparison' &&
            rule.authority !== 'intentional-non-conversion'
        ) {
            throw new CoreManifestValidationError(
                'AUTHORITY_SHAPE_MISMATCH',
                `Manifest rule '${rule.id}' has unknown authority ` +
                `'${rule.authority}'`
            );
        }
        if (
            rule.disposition !== 'mvp-candidate' &&
            rule.disposition !== 'conformance-evidence'
        ) {
            throw new CoreManifestValidationError(
                'AUTHORITY_SHAPE_MISMATCH',
                `Manifest rule '${rule.id}' has unknown disposition ` +
                `'${rule.disposition}'`
            );
        }
        if (!validRuleId.test(rule.id)) {
            throw new CoreManifestValidationError(
                'INVALID_RULE_ID',
                `Manifest rule id '${rule.id}' is not canonical`
            );
        }
        if (seenIds.has(rule.id)) {
            throw new CoreManifestValidationError(
                'DUPLICATE_RULE_ID',
                `Manifest rule id '${rule.id}' occurs more than once`
            );
        }
        seenIds.add(rule.id);
        if (rule.order !== index) {
            throw new CoreManifestValidationError(
                'RULE_ORDER_MISMATCH',
                `Manifest rule '${rule.id}' has order ${rule.order}, ` +
                `expected ${index}`
            );
        }
        if (seenEvidence.has(rule.provenance.evidence)) {
            throw new CoreManifestValidationError(
                'DUPLICATE_RULE_EVIDENCE',
                `Manifest evidence key '${rule.provenance.evidence}' is reused`
            );
        }
        seenEvidence.add(rule.provenance.evidence);
        if (
            rule.provenance.evidence.trim().length === 0 ||
            rule.provenance.auditedOn.trim().length === 0
        ) {
            throw new CoreManifestValidationError(
                'INCOMPLETE_RULE_PROVENANCE',
                `Manifest rule '${rule.id}' has incomplete provenance`
            );
        }
        validateConsumerCoverage(
            rule.consumers,
            `Manifest rule '${rule.id}'`
        );

        const declared = new Set<string>();
        for (const variable of rule.variables) {
            if (!validVariable.test(variable) || declared.has(variable)) {
                throw new CoreManifestValidationError(
                    'DUPLICATE_RULE_VARIABLE',
                    `Manifest rule '${rule.id}' has invalid or duplicate ` +
                    `variable '${variable}'`
                );
            }
            declared.add(variable);
        }

        const left = collectValidatedPattern(
            rule.left,
            declared,
            `Manifest rule '${rule.id}' left side`
        );
        const right = collectValidatedPattern(
            rule.right,
            declared,
            `Manifest rule '${rule.id}' right side`
        );
        const comparisonVariables = setUnion(
            left.variables,
            right.variables
        );
        const usedVariables = new Set(comparisonVariables);
        const usedOwners = setUnion(left.owners, right.owners);

        for (const [consequenceIndex, consequence] of
            (rule.consequences ?? []).entries()) {
            const consequenceLeft = collectValidatedPattern(
                consequence.left,
                declared,
                `Manifest rule '${rule.id}' consequence ${consequenceIndex} ` +
                'left side'
            );
            const consequenceRight = collectValidatedPattern(
                consequence.right,
                declared,
                `Manifest rule '${rule.id}' consequence ${consequenceIndex} ` +
                'right side'
            );
            consequenceLeft.variables.forEach(variable => {
                if (!comparisonVariables.has(variable)) {
                    throw new CoreManifestValidationError(
                        'COMPARISON_CONSEQUENCE_SCOPE_ESCAPE',
                        `Manifest rule '${rule.id}' consequence ` +
                        `${consequenceIndex} introduces variable ` +
                        `'${variable}' absent from both comparison sides`
                    );
                }
                usedVariables.add(variable);
            });
            consequenceRight.variables.forEach(variable => {
                if (!comparisonVariables.has(variable)) {
                    throw new CoreManifestValidationError(
                        'COMPARISON_CONSEQUENCE_SCOPE_ESCAPE',
                        `Manifest rule '${rule.id}' consequence ` +
                        `${consequenceIndex} introduces variable ` +
                        `'${variable}' absent from both comparison sides`
                    );
                }
                usedVariables.add(variable);
            });
            consequenceLeft.owners.forEach(owner => usedOwners.add(owner));
            consequenceRight.owners.forEach(owner => usedOwners.add(owner));
        }

        for (const variable of declared) {
            if (!usedVariables.has(variable)) {
                throw new CoreManifestValidationError(
                    'UNUSED_RULE_VARIABLE',
                    `Manifest rule '${rule.id}' declares unused variable ` +
                    `'${variable}'`
                );
            }
        }

        validateAuthorityShape(rule, left.variables, right.variables);

        if (rule.disposition === 'mvp-candidate') {
            for (const owner of usedOwners) {
                if (!candidateOwners.has(owner)) {
                    throw new CoreManifestValidationError(
                        'CANDIDATE_RULE_USES_EXCLUDED_OWNER',
                        `MVP rule '${rule.id}' refers to conformance-only ` +
                        `owner '${owner}'`
                    );
                }
            }
        }
    });
};

const validateRuleFamilyExclusions = (
    exclusions: readonly CoreManifestRuleFamilyExclusionInput[],
    ruleIds: ReadonlySet<string>
): void => {
    const seen = new Set<string>();
    exclusions.forEach((exclusion, index) => {
        if (exclusion.order !== index) {
            throw new CoreManifestValidationError(
                'RULE_FAMILY_ORDER_MISMATCH',
                `Excluded rule family '${exclusion.id}' has order ` +
                `${exclusion.order}, expected ${index}`
            );
        }
        if (seen.has(exclusion.id) || ruleIds.has(exclusion.id)) {
            throw new CoreManifestValidationError(
                'DUPLICATE_RULE_ID',
                `Excluded rule family id '${exclusion.id}' collides with ` +
                'another rule identity'
            );
        }
        seen.add(exclusion.id);
        if (
            exclusion.reason.trim().length === 0 ||
            exclusion.openRisks.length === 0
        ) {
            throw new CoreManifestValidationError(
                'AUTHORITY_SHAPE_MISMATCH',
                `Excluded rule family '${exclusion.id}' requires a reason ` +
                'and at least one open risk'
            );
        }
        for (const owner of exclusion.ownerReferences) {
            if (!isOwnerId(owner)) {
                throw new CoreManifestValidationError(
                    'UNKNOWN_RULE_OWNER',
                    `Excluded rule family '${exclusion.id}' refers to unknown ` +
                    `owner '${owner}'`
                );
            }
        }
    });
};

const sameStrings = (
    actual: readonly string[],
    expected: readonly string[]
): boolean =>
    actual.length === expected.length &&
    actual.every((value, index) => value === expected[index]);

const validateRecommendation = (
    proposal: CoreManifestProposalInput
): void => {
    const recommendation = proposal.recommendation;
    const candidates = proposal.owners
        .filter(owner => owner.membership === 'mvp-candidate')
        .map(owner => owner.owner);
    const runtimeRules = proposal.rules
        .filter(rule =>
            rule.disposition === 'mvp-candidate' &&
            rule.authority === 'runtime-reduction'
        )
        .map(rule => rule.id);
    const proofRules = proposal.rules
        .filter(rule =>
            rule.disposition === 'mvp-candidate' &&
            rule.authority === 'proof-time-comparison'
        )
        .map(rule => rule.id);
    const nonConversions = proposal.rules
        .filter(rule => rule.authority === 'intentional-non-conversion')
        .map(rule => rule.id);

    if (
        recommendation.gate !== 'H-03' ||
        recommendation.state !== 'awaiting-human-review' ||
        recommendation.rationale.trim().length === 0 ||
        !sameStrings(recommendation.ownerIds, candidates) ||
        !sameStrings(recommendation.runtimeRuleIds, runtimeRules) ||
        !sameStrings(recommendation.proofTimeRuleIds, proofRules) ||
        !sameStrings(
            recommendation.nonConversionEvidenceIds,
            nonConversions
        )
    ) {
        throw new CoreManifestValidationError(
            'RECOMMENDATION_MISMATCH',
            'H-03 recommendation does not exactly match the proposed ' +
            'candidate owners, executable rules, and non-conversion evidence'
        );
    }
};

/**
 * Validate the closed-world TSK-1A proposal without compiling or evaluating
 * any rule.
 */
export function validateCoreManifestProposal(
    proposal: CoreManifestProposalInput
): void {
    if (
        proposal.status !== 'proposal-awaiting-h03' ||
        proposal.ruleSelection !== 'closed-world'
    ) {
        throw new CoreManifestValidationError(
            'INVALID_PROPOSAL_STATUS',
            'TSK-1A manifest must remain a closed-world proposal awaiting H-03'
        );
    }
    const candidates = validateOwners(proposal.owners);
    validateRules(proposal.rules, candidates);
    validateRuleFamilyExclusions(
        proposal.excludedRuleFamilies,
        new Set(proposal.rules.map(rule => rule.id))
    );
    validateRecommendation(proposal);
}

const variable = (name: string): CoreRulePatternInput => ({
    tag: 'variable',
    name
});

const application = (
    owner: CoreOwnerId,
    ...arguments_: readonly CoreRulePatternInput[]
): CoreRulePatternInput => ({
    tag: 'owner-application',
    owner,
    arguments: arguments_
});

const homCategory = (
    category: CoreRulePatternInput,
    source: CoreRulePatternInput,
    target: CoreRulePatternInput
): CoreRulePatternInput => application(
    'hom-category',
    category,
    source,
    target
);

const transforCategory = (
    sourceCategory: CoreRulePatternInput,
    targetCategory: CoreRulePatternInput,
    sourceFunctor: CoreRulePatternInput,
    targetFunctor: CoreRulePatternInput
): CoreRulePatternInput => application(
    'transfor-category',
    sourceCategory,
    targetCategory,
    sourceFunctor,
    targetFunctor
);

const functorObject = (
    sourceCategory: CoreRulePatternInput,
    targetCategory: CoreRulePatternInput,
    functor: CoreRulePatternInput,
    object: CoreRulePatternInput
): CoreRulePatternInput => application(
    'functor-object',
    sourceCategory,
    targetCategory,
    functor,
    object
);

const candidateOwner = (
    order: number,
    owner: CoreOwnerId,
    ...consumers: readonly CoreManifestConsumerId[]
): CoreManifestOwnerEntryInput => ({
    order,
    owner,
    membership: 'mvp-candidate',
    consumers
});

const conformanceOwner = (
    order: number,
    owner: CoreOwnerId,
    consumers: readonly CoreManifestConsumerId[],
    reason: string,
    ...openRisks: readonly CoreManifestOpenRisk[]
): CoreManifestOwnerEntryInput => ({
    order,
    owner,
    membership: 'conformance-only',
    consumers,
    exclusion: {
        reason,
        openRisks
    }
});

const ownerEntries: readonly CoreManifestOwnerEntryInput[] = [
    candidateOwner(
        0,
        'groupoid-universe',
        'elab-2a3-signature-checker'
    ),
    candidateOwner(
        1,
        'category-universe',
        'elab-0-object-and-arrow',
        'elab-2a3-signature-checker'
    ),
    candidateOwner(
        2,
        'decode',
        'elab-0-object-and-arrow',
        'elab-2a3-signature-checker'
    ),
    candidateOwner(
        3,
        'object-classifier',
        'elab-0-object-and-arrow',
        'elab-1b-recursive-2-cell'
    ),
    candidateOwner(
        4,
        'functor-classifier',
        'elab-0-object-and-arrow',
        'elab-1b-projection-ladder'
    ),
    candidateOwner(
        5,
        'hom-classifier',
        'elab-0-object-and-arrow',
        'elab-1b-recursive-2-cell'
    ),
    candidateOwner(
        6,
        'transfor-classifier',
        'elab-1b-projection-ladder'
    ),
    conformanceOwner(
        7,
        'category-of-categories',
        [
            'elab-2a3-signature-checker',
            'elab-2b-constant-section'
        ],
        'The signature catalog needs this active universe category, but the ' +
        'bounded projection evaluator has no direct product consumer for it.',
        'consumer-scope',
        'rule-inventory'
    ),
    conformanceOwner(
        8,
        'opposite-category',
        ['elab-1c-internal-hom'],
        'Its first consumer is the target-varying internal-hom extension; ' +
        'opposite involution and variance reductions are outside the first ' +
        'projection evaluator.',
        'rule-inventory',
        'termination',
        'confluence',
        'subject-reduction'
    ),
    candidateOwner(
        9,
        'hom-category',
        'elab-0-object-and-arrow',
        'elab-1b-recursive-2-cell'
    ),
    candidateOwner(
        10,
        'transfor-category',
        'elab-1b-projection-ladder'
    ),
    conformanceOwner(
        11,
        'displayed-category-category',
        ['elab-1c-internal-hom', 'elab-2b-dependent-context'],
        'Displayed-family and internal-hom extensions remain outside the ' +
        'ordinary projection MVP recommendation while H-01 is open.',
        'rule-inventory',
        'human-gate-h01',
        'subject-reduction'
    ),
    conformanceOwner(
        12,
        'internal-hom-source',
        ['elab-1c-internal-hom'],
        'The retained source-varying family is conformance-backed, but its ' +
        'variance conversions are not part of the bounded projection rule set.',
        'rule-inventory',
        'termination',
        'confluence',
        'subject-reduction'
    ),
    conformanceOwner(
        13,
        'internal-hom-target',
        ['elab-1c-internal-hom'],
        'The retained target-varying family is conformance-backed, but its ' +
        'opposite-variance conversions are not in the bounded rule set.',
        'rule-inventory',
        'termination',
        'confluence',
        'subject-reduction'
    ),
    conformanceOwner(
        14,
        'displayed-pullback',
        ['elab-2b-dependent-context'],
        'Displayed reindexing is exercised, but its runtime and proof-time ' +
        'bridge family depends on the still-open dependent representation.',
        'rule-inventory',
        'human-gate-h01',
        'termination',
        'confluence',
        'subject-reduction'
    ),
    conformanceOwner(
        15,
        'constant-displayed-family',
        ['elab-2b-dependent-context', 'elab-2b-constant-section'],
        'Constant-family specialization is retained as conformance evidence ' +
        'until the dependent representation and its bridge rules are reviewed.',
        'rule-inventory',
        'human-gate-h01',
        'termination',
        'confluence',
        'subject-reduction'
    ),
    conformanceOwner(
        16,
        'section-category',
        ['elab-2b-dependent-context', 'elab-2b-constant-section'],
        'Section categories participate in proof-time-only bridges and must ' +
        'not silently enter the first runtime evaluator.',
        'rule-inventory',
        'human-gate-h01',
        'confluence',
        'subject-reduction'
    ),
    candidateOwner(
        17,
        'functor-object',
        'elab-0-object-and-arrow',
        'elab-1b-projection-ladder',
        'elab-1b-recursive-2-cell'
    ),
    candidateOwner(
        18,
        'functor-hom-full',
        'elab-1b-projection-ladder',
        'elab-1b-recursive-2-cell'
    ),
    candidateOwner(
        19,
        'functor-hom-capped',
        'elab-0-object-and-arrow',
        'elab-1b-projection-ladder'
    ),
    candidateOwner(
        20,
        'transfor-component-full',
        'elab-1b-projection-ladder'
    ),
    candidateOwner(
        21,
        'transfor-component-capped',
        'elab-1b-projection-ladder'
    ),
    candidateOwner(
        22,
        'transfor-hom-full',
        'elab-1b-projection-ladder'
    ),
    candidateOwner(
        23,
        'transfor-hom-capped',
        'elab-0-object-and-arrow',
        'elab-1b-projection-ladder'
    )
];

const runtimeRule = (
    order: number,
    id: CoreManifestRuleId,
    variables: readonly string[],
    left: CoreRulePatternInput,
    right: CoreRulePatternInput,
    ...consumers: readonly CoreManifestConsumerId[]
): KnownCoreManifestRule => ({
    order,
    id,
    authority: 'runtime-reduction',
    disposition: 'mvp-candidate',
    variables,
    left,
    right,
    provenance: {
        evidence: id,
        auditedOn: '2026-07-23'
    },
    consumers
});

const A = variable('A');
const B = variable('B');
const F = variable('F');
const G = variable('G');
const X = variable('X');
const Y = variable('Y');
const f = variable('f');
const eta = variable('eta');

const functorHomTarget = homCategory(
    B,
    functorObject(A, B, F, X),
    functorObject(A, B, F, Y)
);

const rules: readonly KnownCoreManifestRule[] = [
    runtimeRule(
        0,
        'projection.functor-hom.evaluate',
        ['A', 'B', 'F', 'X', 'Y', 'f'],
        functorObject(
            homCategory(A, X, Y),
            functorHomTarget,
            application('functor-hom-full', A, B, F, X, Y),
            f
        ),
        application('functor-hom-capped', A, B, F, X, Y, f),
        'elab-1b-projection-ladder',
        'elab-1b-recursive-2-cell'
    ),
    runtimeRule(
        1,
        'projection.transfor-component.evaluate',
        ['A', 'B', 'F', 'G', 'Y', 'eta'],
        functorObject(
            transforCategory(A, B, F, G),
            homCategory(
                B,
                functorObject(A, B, F, Y),
                functorObject(A, B, G, Y)
            ),
            application(
                'transfor-component-full',
                A,
                B,
                F,
                G,
                Y
            ),
            eta
        ),
        application(
            'transfor-component-capped',
            A,
            B,
            F,
            G,
            Y,
            eta
        ),
        'elab-1b-projection-ladder'
    ),
    runtimeRule(
        2,
        'projection.transfor-hom.evaluate',
        ['A', 'B', 'F', 'G', 'X', 'Y', 'eta', 'f'],
        functorObject(
            homCategory(A, X, Y),
            homCategory(
                B,
                functorObject(A, B, F, X),
                functorObject(A, B, G, Y)
            ),
            application(
                'transfor-hom-full',
                A,
                B,
                F,
                G,
                X,
                Y,
                eta
            ),
            f
        ),
        application(
            'transfor-hom-capped',
            A,
            B,
            F,
            G,
            X,
            Y,
            eta,
            f
        ),
        'elab-1b-projection-ladder'
    ),
    {
        order: 3,
        id: 'comparison.constant-section',
        authority: 'proof-time-comparison',
        disposition: 'conformance-evidence',
        variables: ['K', 'A', 'KPrime', 'APrime'],
        left: application(
            'section-category',
            variable('K'),
            application(
                'constant-displayed-family',
                variable('K'),
                variable('A')
            )
        ),
        right: homCategory(
            application('category-of-categories'),
            variable('KPrime'),
            variable('APrime')
        ),
        consequences: [
            {
                left: variable('K'),
                right: variable('KPrime')
            },
            {
                left: variable('A'),
                right: variable('APrime')
            }
        ],
        provenance: {
            evidence: 'comparison.constant-section',
            auditedOn: '2026-07-23'
        },
        consumers: ['elab-2b-constant-section']
    },
    {
        order: 4,
        id: 'nonconversion.constant-section.runtime',
        authority: 'intentional-non-conversion',
        disposition: 'conformance-evidence',
        variables: ['K', 'A'],
        left: application(
            'section-category',
            variable('K'),
            application(
                'constant-displayed-family',
                variable('K'),
                variable('A')
            )
        ),
        right: homCategory(
            application('category-of-categories'),
            variable('K'),
            variable('A')
        ),
        provenance: {
            evidence: 'nonconversion.constant-section.runtime',
            auditedOn: '2026-07-23'
        },
        consumers: ['elab-2b-constant-section']
    }
];

const excludedRuleFamilies:
readonly CoreManifestRuleFamilyExclusionInput[] = [
    {
        order: 0,
        id: 'classifier.presentation-and-inversion',
        ownerReferences: [
            'object-classifier',
            'hom-classifier',
            'transfor-classifier',
            'hom-category',
            'transfor-category'
        ],
        reason:
            'Core treats its semantic classifiers as primitive signatures. ' +
            'Backend presentation folds and proof-time inversion helpers need ' +
            'a separate necessity and interaction inventory.',
        openRisks: [
            'consumer-scope',
            'rule-inventory',
            'confluence',
            'subject-reduction'
        ]
    },
    {
        order: 1,
        id: 'ordinary.identity-and-composition',
        ownerReferences: [
            'functor-object',
            'functor-hom-capped'
        ],
        reason:
            'Identity, composition, and their strict functorial cuts use ' +
            'owners outside the current semantic catalog and are not needed ' +
            'to evaluate the three full/capped projection consumers.',
        openRisks: [
            'consumer-scope',
            'rule-inventory',
            'termination',
            'confluence',
            'subject-reduction'
        ]
    },
    {
        order: 2,
        id: 'internal-hom.variance-conversions',
        ownerReferences: [
            'opposite-category',
            'displayed-category-category',
            'internal-hom-source',
            'internal-hom-target',
            'functor-object'
        ],
        reason:
            'The ELAB-1C conversions remain oracle-backed extensions until ' +
            'their complete variance and reduction neighborhood is bounded.',
        openRisks: [
            'rule-inventory',
            'termination',
            'confluence',
            'subject-reduction'
        ]
    },
    {
        order: 3,
        id: 'displayed.reindexing-reductions',
        ownerReferences: [
            'displayed-category-category',
            'displayed-pullback',
            'constant-displayed-family',
            'functor-object'
        ],
        reason:
            'General and constant pullback reductions belong to the dependent ' +
            'extension whose representation still awaits H-01.',
        openRisks: [
            'rule-inventory',
            'human-gate-h01',
            'termination',
            'confluence',
            'subject-reduction'
        ]
    },
    {
        order: 4,
        id: 'displayed.section-bridges',
        ownerReferences: [
            'section-category',
            'constant-displayed-family',
            'functor-classifier'
        ],
        reason:
            'Section bridges are recorded as proof-time and non-conversion ' +
            'evidence, not proposed as executable MVP rules.',
        openRisks: [
            'rule-inventory',
            'human-gate-h01',
            'confluence',
            'subject-reduction'
        ]
    },
    {
        order: 5,
        id: 'all-unlisted-active-rules',
        ownerReferences: [],
        reason:
            'Rule selection is closed-world: no active rule outside the five ' +
            'records above is included merely because its head is serializable.',
        openRisks: [
            'consumer-scope',
            'rule-inventory',
            'termination',
            'confluence',
            'subject-reduction'
        ]
    }
];

const recommendedOwnerIds = ownerEntries
    .filter(owner => owner.membership === 'mvp-candidate')
    .map(owner => owner.owner);

const recommendedRuntimeRuleIds = rules
    .filter(rule => rule.disposition === 'mvp-candidate')
    .map(rule => rule.id);

const rawProposal: CoreManifestProposalInput = {
    status: 'proposal-awaiting-h03',
    ruleSelection: 'closed-world',
    owners: ownerEntries,
    rules,
    excludedRuleFamilies,
    recommendation: {
        gate: 'H-03',
        state: 'awaiting-human-review',
        ownerIds: recommendedOwnerIds,
        runtimeRuleIds: recommendedRuntimeRuleIds,
        proofTimeRuleIds: [],
        nonConversionEvidenceIds: [
            'nonconversion.constant-section.runtime'
        ],
        rationale:
            'Freeze, if H-03 approves, the dependency-closed 16-owner ' +
            'ordinary classifier/projection signature and exactly the three ' +
            'generic full-to-capped runtime projection rules. Freeze no ' +
            'proof-time comparison rule yet; retain the constant-section ' +
            'comparison and runtime non-conversion only as conformance ' +
            'boundary evidence.'
    }
};

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(item =>
            deepFreeze(item)
        );
        Object.freeze(value);
    }
    return value;
};

validateCoreManifestProposal(rawProposal);

/**
 * The exact TSK-1A review input. It remains an immutable proposal as audit
 * evidence even after H-03; product-kernel consumers must use the separately
 * reviewed `CORE_MVP_MANIFEST`.
 */
export const CORE_MVP_MANIFEST_PROPOSAL = deepFreeze(rawProposal);

const mvpRevision = 'emdash-v3.2-mvp-1';

const expectedApproval: CoreManifestApprovalInput = {
    gate: 'H-03',
    decision: 'approved-as-proposed',
    decisionId: 'D-023',
    reviewedOn: '2026-07-24'
};

const implementedKernelMechanisms = [
    'core-scope-and-substitution',
    'structural-signature-checking',
    'closed-world-manifest-structure-validation'
] as const;

const frozenButDeferredMechanisms = [
    'runtime-pattern-compilation',
    'executable-rule-validation',
    'weak-head-evaluation',
    'definitional-comparison',
    'proof-time-comparison'
] as const;

const outsideTrustedKernel = [
    'surface-and-macro-elaboration',
    'elaboration-metavariables-and-constraints',
    'conformance-only-owner-signatures',
    'conformance-evidence-rules',
    'lambdapi-backend'
] as const;

const cloneManifestData = <T>(value: T): T =>
    JSON.parse(JSON.stringify(value)) as T;

const sameManifestData = (left: unknown, right: unknown): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

const frozenCandidateOwnerIds = CORE_MVP_MANIFEST_PROPOSAL
    .recommendation.ownerIds;

const frozenCandidateRules = CORE_MVP_MANIFEST_PROPOSAL.rules.filter(
    rule => rule.disposition === 'mvp-candidate'
);

const conformanceOnlyOwnerIds = CORE_MVP_MANIFEST_PROPOSAL.owners
    .filter(owner => owner.membership === 'conformance-only')
    .map(owner => owner.owner);

const conformanceEvidenceIds = CORE_MVP_MANIFEST_PROPOSAL.rules
    .filter(rule => rule.disposition === 'conformance-evidence')
    .map(rule => rule.id);

const rawMvpManifestContent: Omit<
    CoreMvpManifestInput,
    'contentHash'
> = {
    status: 'frozen-reviewed',
    revision: mvpRevision,
    ruleSelection: 'closed-world',
    approval: expectedApproval,
    owners: frozenCandidateOwnerIds.map((owner, order) => ({
        order,
        owner,
        signature: cloneManifestData(
            CORE_OWNER_TYPE_SCHEMAS[owner as CoreOwnerId]
        )
    })),
    rules: cloneManifestData(frozenCandidateRules),
    trustBoundary: {
        implementedKernelMechanisms,
        frozenButDeferredMechanisms,
        outsideTrustedKernel,
        conformanceOnlyOwnerIds,
        conformanceEvidenceIds
    }
};

const reviewedMvpContentHash =
    'sha256:28834e9c0361b98e9f14f66f02aac8f59900a98b9c8c1ce1c62ae0e5396f8ff0';

const rawMvpManifest: CoreMvpManifestInput = {
    ...rawMvpManifestContent,
    contentHash: reviewedMvpContentHash
};

const coreMvpContentHash = (
    manifest: CoreMvpManifestInput
): string => {
    const { contentHash: _contentHash, ...content } = manifest;
    return 'sha256:' + createHash('sha256')
        .update(JSON.stringify(content))
        .digest('hex');
};

const validateFrozenOwners = (
    owners: readonly CoreMvpOwnerSignatureInput[]
): void => {
    if (owners.length !== frozenCandidateOwnerIds.length) {
        throw new CoreManifestValidationError(
            'FROZEN_OWNER_MISMATCH',
            `Frozen MVP manifest has ${owners.length} owners, expected ` +
            frozenCandidateOwnerIds.length
        );
    }

    owners.forEach((entry, order) => {
        const expectedOwner = frozenCandidateOwnerIds[order];
        if (
            entry.order !== order ||
            entry.owner !== expectedOwner
        ) {
            throw new CoreManifestValidationError(
                'FROZEN_OWNER_MISMATCH',
                `Frozen MVP owner ${order} is order ${entry.order} ` +
                `'${entry.owner}', expected order ${order} ` +
                `'${expectedOwner}'`
            );
        }
        if (
            !isOwnerId(entry.owner) ||
            !sameManifestData(
                entry.signature,
                CORE_OWNER_TYPE_SCHEMAS[entry.owner]
            )
        ) {
            throw new CoreManifestValidationError(
                'FROZEN_SIGNATURE_MISMATCH',
                `Frozen MVP signature for '${entry.owner}' differs from the ` +
                'reviewed Core owner signature'
            );
        }
    });
};

const validateFrozenRules = (
    rules_: readonly CoreManifestRuleInput[]
): void => {
    if (rules_.length !== frozenCandidateRules.length) {
        throw new CoreManifestValidationError(
            'FROZEN_RULE_MISMATCH',
            `Frozen MVP manifest has ${rules_.length} rules, expected ` +
            frozenCandidateRules.length
        );
    }

    rules_.forEach((rule, order) => {
        const expectedRule = frozenCandidateRules[order];
        if (!sameManifestData(rule, expectedRule)) {
            throw new CoreManifestValidationError(
                'FROZEN_RULE_MISMATCH',
                `Frozen MVP rule ${order} '${rule.id}' differs from reviewed ` +
                `rule '${expectedRule.id}'`
            );
        }
        if (
            rule.disposition !== 'mvp-candidate' ||
            rule.authority !== 'runtime-reduction'
        ) {
            throw new CoreManifestValidationError(
                'FROZEN_RULE_MISMATCH',
                `Frozen MVP rule '${rule.id}' must be an approved runtime ` +
                'candidate'
            );
        }
    });
};

const validateTrustBoundary = (
    boundary: CoreMvpTrustBoundaryInput
): void => {
    const expected: CoreMvpTrustBoundaryInput =
        rawMvpManifestContent.trustBoundary;
    if (
        !sameStrings(
            boundary.implementedKernelMechanisms,
            expected.implementedKernelMechanisms
        ) ||
        !sameStrings(
            boundary.frozenButDeferredMechanisms,
            expected.frozenButDeferredMechanisms
        ) ||
        !sameStrings(
            boundary.outsideTrustedKernel,
            expected.outsideTrustedKernel
        ) ||
        !sameStrings(
            boundary.conformanceOnlyOwnerIds,
            expected.conformanceOnlyOwnerIds
        ) ||
        !sameStrings(
            boundary.conformanceEvidenceIds,
            expected.conformanceEvidenceIds
        )
    ) {
        throw new CoreManifestValidationError(
            'TRUST_BOUNDARY_MISMATCH',
            'Frozen MVP trusted-core boundary differs from reviewed D-023'
        );
    }
};

/**
 * Validate the exact H-03-reviewed product profile without compiling,
 * matching, or evaluating any rule.
 */
export function validateCoreMvpManifest(
    manifest: CoreMvpManifestInput
): void {
    validateCoreManifestProposal(CORE_MVP_MANIFEST_PROPOSAL);
    if (
        manifest.status !== 'frozen-reviewed' ||
        manifest.revision !== mvpRevision ||
        manifest.ruleSelection !== 'closed-world'
    ) {
        throw new CoreManifestValidationError(
            'INVALID_FROZEN_STATUS',
            'TSK-1B manifest must be the closed-world reviewed MVP revision'
        );
    }
    if (!sameManifestData(manifest.approval, expectedApproval)) {
        throw new CoreManifestValidationError(
            'INVALID_REVIEW_APPROVAL',
            'TSK-1B manifest requires the exact H-03 approval of D-023'
        );
    }
    validateFrozenOwners(manifest.owners);
    validateFrozenRules(manifest.rules);
    validateTrustBoundary(manifest.trustBoundary);
    if (
        manifest.contentHash !== reviewedMvpContentHash ||
        coreMvpContentHash(manifest) !== reviewedMvpContentHash
    ) {
        throw new CoreManifestValidationError(
            'FROZEN_CONTENT_HASH_MISMATCH',
            'Frozen MVP content differs from reviewed revision ' +
            `${mvpRevision}`
        );
    }
}

validateCoreMvpManifest(rawMvpManifest);

/**
 * The H-03-reviewed product profile. Its signature snapshots and three
 * runtime rule declarations are immutable. Runtime pattern compilation,
 * executable-rule validation, evaluation, and comparison remain TSK-2 work.
 *
 * The general structural checker and the Lambdapi backend remain conformance
 * supersets; inclusion there does not grant an owner or rule membership in
 * this closed-world product profile.
 */
export const CORE_MVP_MANIFEST = deepFreeze(rawMvpManifest);
