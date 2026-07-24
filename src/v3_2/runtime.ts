/**
 * Candidate runtime compilation for the H-03-reviewed MVP fragment.
 *
 * TSK-2A compiles and audits rule patterns only. It deliberately does not
 * match a Core term, rewrite one, or authorize the termination, confluence,
 * and subject-reduction claims reserved for H-04.
 */

import {
    CORE_MVP_MANIFEST,
    CoreManifestRuleInput,
    CoreMvpManifestInput,
    CoreRulePatternInput,
    validateCoreMvpManifest
} from './manifest';
import {
    CORE_OWNER_SCHEMAS,
    PROJECTION_PAIR_SCHEMAS,
    CoreOwnerId,
    ProjectionPairSchema
} from './schema';

export type CoreProjectionPairId =
    keyof typeof PROJECTION_PAIR_SCHEMAS;

export type CoreCompiledRulePattern =
    | {
        readonly tag: 'variable';
        readonly slot: number;
    }
    | {
        readonly tag: 'owner-application';
        readonly owner: CoreOwnerId;
        readonly arguments: readonly CoreCompiledRulePattern[];
    };

export interface CoreRuntimeRuleSafetyEvidence {
    readonly projectionPair: CoreProjectionPairId;
    readonly evaluatorOwner: CoreOwnerId;
    readonly eliminatedFullOwner: CoreOwnerId;
    readonly introducedCappedOwner: CoreOwnerId;
    readonly explicitFullOwnerDecrease: 1;
    readonly nonDuplicatingVariables: true;
    readonly leftVariableOccurrences: readonly number[];
    readonly rightVariableOccurrences: readonly number[];
}

export interface CoreCompiledRuntimeRule {
    readonly order: number;
    readonly id: string;
    readonly variables: readonly string[];
    readonly left: CoreCompiledRulePattern;
    readonly right: CoreCompiledRulePattern;
    readonly rootOwner: CoreOwnerId;
    readonly evidence: string;
    readonly auditedOn: string;
    readonly safety: CoreRuntimeRuleSafetyEvidence;
}

export interface CoreRuntimeProgramSafetyEvidence {
    /**
     * A conservative first-order check found a rigid disagreement between
     * every pair of left patterns. This is evidence, not a confluence proof.
     */
    readonly pairwiseLeftOverlapFree: true;
    /**
     * The reviewed rules repeat variables in their left patterns.
     */
    readonly leftLinear: boolean;
    readonly terminationEvidence:
        'one-explicit-full-owner-decrease-without-variable-duplication';
    readonly confluenceEvidence:
        'pairwise-rigid-left-discrimination-only';
    readonly subjectReductionEvidence:
        'reviewed-lambdapi-provenance-only';
    readonly claimsAuthorized: false;
    readonly reviewGate: 'H-04';
}

export interface CoreMvpRuntimeProgram {
    readonly status: 'candidate-awaiting-h04';
    readonly manifestRevision: string;
    readonly manifestContentHash: string;
    readonly ownerIds: readonly CoreOwnerId[];
    readonly rules: readonly CoreCompiledRuntimeRule[];
    readonly ruleIndicesByRoot:
        Readonly<Partial<Record<CoreOwnerId, readonly number[]>>>;
    readonly safety: CoreRuntimeProgramSafetyEvidence;
}

export type CoreRuntimeCompilationErrorCode =
    | 'NON_RUNTIME_RULE'
    | 'INVALID_COMPILED_VARIABLES'
    | 'UNKNOWN_COMPILED_VARIABLE'
    | 'UNKNOWN_COMPILED_OWNER'
    | 'INVALID_COMPILED_OWNER_ARITY'
    | 'MALFORMED_COMPILED_PATTERN'
    | 'INVALID_RUNTIME_LEFT_ROOT'
    | 'INVALID_PROJECTION_DECREASE'
    | 'DUPLICATING_RUNTIME_VARIABLE'
    | 'AMBIGUOUS_RUNTIME_RULES';

export class CoreRuntimeCompilationError extends Error {
    constructor(
        public readonly code: CoreRuntimeCompilationErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreRuntimeCompilationError';
    }
}

const isOwnerId = (owner: string): owner is CoreOwnerId =>
    Object.prototype.hasOwnProperty.call(CORE_OWNER_SCHEMAS, owner);

const compilePattern = (
    pattern: CoreRulePatternInput,
    variableSlots: ReadonlyMap<string, number>,
    selectedOwners: ReadonlySet<CoreOwnerId>,
    ruleId: string
): CoreCompiledRulePattern => {
    switch (pattern.tag) {
        case 'variable': {
            const slot = variableSlots.get(pattern.name);
            if (slot === undefined) {
                throw new CoreRuntimeCompilationError(
                    'UNKNOWN_COMPILED_VARIABLE',
                    `Runtime rule '${ruleId}' pattern variable ` +
                    `'${pattern.name}' has no compiled slot`
                );
            }
            return {
                tag: 'variable',
                slot
            };
        }
        case 'owner-application':
            if (
                !isOwnerId(pattern.owner) ||
                !selectedOwners.has(pattern.owner)
            ) {
                throw new CoreRuntimeCompilationError(
                    'UNKNOWN_COMPILED_OWNER',
                    `Runtime rule '${ruleId}' pattern owner ` +
                    `'${pattern.owner}' is outside the reviewed MVP owners`
                );
            }
            if (!Array.isArray(pattern.arguments)) {
                throw new CoreRuntimeCompilationError(
                    'MALFORMED_COMPILED_PATTERN',
                    `Runtime rule '${ruleId}' owner '${pattern.owner}' has ` +
                    'no argument list'
                );
            }
            if (
                pattern.arguments.length !==
                CORE_OWNER_SCHEMAS[pattern.owner].slots.length
            ) {
                throw new CoreRuntimeCompilationError(
                    'INVALID_COMPILED_OWNER_ARITY',
                    `Runtime rule '${ruleId}' applies owner ` +
                    `'${pattern.owner}' to ${pattern.arguments.length} ` +
                    'arguments, expected ' +
                    CORE_OWNER_SCHEMAS[pattern.owner].slots.length
                );
            }
            return {
                tag: 'owner-application',
                owner: pattern.owner,
                arguments: pattern.arguments.map(argument =>
                    compilePattern(
                        argument,
                        variableSlots,
                        selectedOwners,
                        ruleId
                    )
                )
            };
        default: {
            throw new CoreRuntimeCompilationError(
                'MALFORMED_COMPILED_PATTERN',
                `Runtime rule '${ruleId}' has unknown pattern tag ` +
                `'${String((pattern as { tag?: unknown }).tag)}'`
            );
        }
    }
};

const countVariableOccurrences = (
    pattern: CoreCompiledRulePattern,
    counts: number[]
): void => {
    switch (pattern.tag) {
        case 'variable':
            counts[pattern.slot]++;
            return;
        case 'owner-application':
            pattern.arguments.forEach(argument =>
                countVariableOccurrences(argument, counts)
            );
            return;
        default: {
            const exhaustive: never = pattern;
            return exhaustive;
        }
    }
};

const countOwnerOccurrences = (
    pattern: CoreCompiledRulePattern,
    owners: ReadonlySet<CoreOwnerId>
): number => {
    switch (pattern.tag) {
        case 'variable':
            return 0;
        case 'owner-application':
            return (owners.has(pattern.owner) ? 1 : 0) +
                pattern.arguments.reduce(
                    (count, argument) =>
                        count + countOwnerOccurrences(argument, owners),
                    0
                );
        default: {
            const exhaustive: never = pattern;
            return exhaustive;
        }
    }
};

const projectionPairEntries = Object.entries(
    PROJECTION_PAIR_SCHEMAS
) as [CoreProjectionPairId, ProjectionPairSchema][];

const projectionFullOwners = new Set<CoreOwnerId>(
    projectionPairEntries.map(([, pair]) => pair.full)
);

const projectionPairForRule = (
    left: CoreCompiledRulePattern,
    right: CoreCompiledRulePattern,
    ruleId: string
): [CoreProjectionPairId, ProjectionPairSchema] => {
    if (left.tag !== 'owner-application') {
        throw new CoreRuntimeCompilationError(
            'INVALID_RUNTIME_LEFT_ROOT',
            `Runtime rule '${ruleId}' left side is not rooted at an owner`
        );
    }

    const candidates = projectionPairEntries.filter(([, pair]) =>
        left.owner === pair.evaluator &&
        countOwnerOccurrences(left, new Set([pair.full])) === 1 &&
        countOwnerOccurrences(right, new Set([pair.capped])) === 1
    );
    const leftFullCount = countOwnerOccurrences(
        left,
        projectionFullOwners
    );
    const rightFullCount = countOwnerOccurrences(
        right,
        projectionFullOwners
    );
    if (
        candidates.length !== 1 ||
        leftFullCount !== 1 ||
        rightFullCount !== 0
    ) {
        throw new CoreRuntimeCompilationError(
            'INVALID_PROJECTION_DECREASE',
            `Runtime rule '${ruleId}' must eliminate exactly one reviewed ` +
            'full projection through its matching evaluator and introduce ' +
            'the corresponding capped projection'
        );
    }
    return candidates[0];
};

const compileRuntimeRule = (
    rule: CoreManifestRuleInput,
    selectedOwners: ReadonlySet<CoreOwnerId>
): CoreCompiledRuntimeRule => {
    if (
        rule.authority !== 'runtime-reduction' ||
        rule.disposition !== 'mvp-candidate'
    ) {
        throw new CoreRuntimeCompilationError(
            'NON_RUNTIME_RULE',
            `Rule '${rule.id}' is not an H-03-reviewed runtime rule`
        );
    }

    const validVariable = /^[A-Za-z][A-Za-z0-9_]*$/;
    if (
        !Array.isArray(rule.variables) ||
        rule.variables.some(variable => !validVariable.test(variable))
    ) {
        throw new CoreRuntimeCompilationError(
            'INVALID_COMPILED_VARIABLES',
            `Runtime rule '${rule.id}' has a noncanonical variable list`
        );
    }
    const variableSlots = new Map(
        rule.variables.map((variable, slot) => [variable, slot])
    );
    if (variableSlots.size !== rule.variables.length) {
        throw new CoreRuntimeCompilationError(
            'INVALID_COMPILED_VARIABLES',
            `Runtime rule '${rule.id}' has duplicate variable names`
        );
    }
    const left = compilePattern(
        rule.left,
        variableSlots,
        selectedOwners,
        rule.id
    );
    const right = compilePattern(
        rule.right,
        variableSlots,
        selectedOwners,
        rule.id
    );
    if (left.tag !== 'owner-application') {
        throw new CoreRuntimeCompilationError(
            'INVALID_RUNTIME_LEFT_ROOT',
            `Runtime rule '${rule.id}' left side is not rooted at an owner`
        );
    }

    const leftVariableOccurrences = rule.variables.map(() => 0);
    const rightVariableOccurrences = rule.variables.map(() => 0);
    countVariableOccurrences(left, leftVariableOccurrences);
    countVariableOccurrences(right, rightVariableOccurrences);
    if (rightVariableOccurrences.some(
        (count, slot) => count > leftVariableOccurrences[slot]
    )) {
        throw new CoreRuntimeCompilationError(
            'DUPLICATING_RUNTIME_VARIABLE',
            `Runtime rule '${rule.id}' duplicates a matched variable on its ` +
            'right side'
        );
    }

    const [projectionPair, pair] = projectionPairForRule(
        left,
        right,
        rule.id
    );
    return {
        order: rule.order,
        id: rule.id,
        variables: [...rule.variables],
        left,
        right,
        rootOwner: left.owner,
        evidence: rule.provenance.evidence,
        auditedOn: rule.provenance.auditedOn,
        safety: {
            projectionPair,
            evaluatorOwner: pair.evaluator,
            eliminatedFullOwner: pair.full,
            introducedCappedOwner: pair.capped,
            explicitFullOwnerDecrease: 1,
            nonDuplicatingVariables: true,
            leftVariableOccurrences,
            rightVariableOccurrences
        }
    };
};

/**
 * Conservatively decide whether two compiled left patterns may share a
 * ground instance. Variables are wildcards; therefore `false` is a rigid
 * non-overlap witness while `true` requires more analysis.
 */
export const coreRuntimePatternsMayOverlap = (
    left: CoreCompiledRulePattern,
    right: CoreCompiledRulePattern
): boolean => {
    if (left.tag === 'variable' || right.tag === 'variable') return true;
    return left.owner === right.owner &&
        left.arguments.length === right.arguments.length &&
        left.arguments.every((argument, index) =>
            coreRuntimePatternsMayOverlap(
                argument,
                right.arguments[index]
            )
        );
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

/**
 * Compile and audit one prospective runtime rule without granting it product
 * membership. This is useful for focused diagnostics and future manifest
 * review; only `compileCoreMvpRuntime` binds rules to the content-hashed
 * reviewed program.
 */
export function compileCoreRuntimeRuleCandidate(
    rule: CoreManifestRuleInput,
    selectedOwnerIds: readonly CoreOwnerId[]
): CoreCompiledRuntimeRule {
    return deepFreeze(compileRuntimeRule(
        rule,
        new Set(selectedOwnerIds)
    ));
}

/**
 * Compile only the exact content-hashed H-03 product profile.
 *
 * `validateCoreMvpManifest` intentionally rejects a modified profile before
 * executable compilation begins. The result remains an H-04-pending
 * candidate and exposes no matcher or evaluator.
 */
export function compileCoreMvpRuntime(
    manifest: CoreMvpManifestInput
): CoreMvpRuntimeProgram {
    validateCoreMvpManifest(manifest);

    const ownerIds = manifest.owners.map(entry => {
        if (!isOwnerId(entry.owner)) {
            throw new CoreRuntimeCompilationError(
                'UNKNOWN_COMPILED_OWNER',
                `Reviewed manifest owner '${entry.owner}' is unknown`
            );
        }
        return entry.owner;
    });
    const selectedOwners = new Set(ownerIds);
    const rules = manifest.rules.map(rule =>
        compileRuntimeRule(rule, selectedOwners)
    );

    for (let leftIndex = 0; leftIndex < rules.length; leftIndex++) {
        for (
            let rightIndex = leftIndex + 1;
            rightIndex < rules.length;
            rightIndex++
        ) {
            if (coreRuntimePatternsMayOverlap(
                rules[leftIndex].left,
                rules[rightIndex].left
            )) {
                throw new CoreRuntimeCompilationError(
                    'AMBIGUOUS_RUNTIME_RULES',
                    `Runtime rules '${rules[leftIndex].id}' and ` +
                    `'${rules[rightIndex].id}' lack a rigid left-pattern ` +
                    'discriminator'
                );
            }
        }
    }

    const leftLinear = rules.every(rule =>
        rule.safety.leftVariableOccurrences.every(count => count <= 1)
    );

    const mutableRuleIndicesByRoot:
        Partial<Record<CoreOwnerId, number[]>> = {};
    rules.forEach((rule, index) => {
        const bucket = mutableRuleIndicesByRoot[rule.rootOwner] ?? [];
        bucket.push(index);
        mutableRuleIndicesByRoot[rule.rootOwner] = bucket;
    });

    return deepFreeze({
        status: 'candidate-awaiting-h04',
        manifestRevision: manifest.revision,
        manifestContentHash: manifest.contentHash,
        ownerIds,
        rules,
        ruleIndicesByRoot: mutableRuleIndicesByRoot,
        safety: {
            pairwiseLeftOverlapFree: true,
            leftLinear,
            terminationEvidence:
                'one-explicit-full-owner-decrease-without-variable-duplication',
            confluenceEvidence:
                'pairwise-rigid-left-discrimination-only',
            subjectReductionEvidence:
                'reviewed-lambdapi-provenance-only',
            claimsAuthorized: false,
            reviewGate: 'H-04'
        }
    });
}

export const CORE_MVP_RUNTIME_PROGRAM = compileCoreMvpRuntime(
    CORE_MVP_MANIFEST
);
