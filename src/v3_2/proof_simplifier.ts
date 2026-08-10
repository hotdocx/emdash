/**
 * Deterministic proof-producing simplification for closed decoded goals.
 *
 * This is a browser-safe management layer. It discovers no rules, retains no
 * checker session, and adds no Core or proof-plan constructor. Every accepted
 * rewrite carries a freshly checked equality proof, and the final backward
 * transport is checked again before it is lowered to existing `have` and
 * `exact` plan nodes.
 */

import {
    CoreCheckerError,
    isCoreKind
} from './checker';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    BinderMode,
    KernelBinder,
    KernelExpression,
    KernelReference,
    Provenance,
    binderMode,
    formatSourceSpan,
    kernelApplication,
    kernelAssertScoped,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelInstantiateSpine,
    kernelLambda
} from './kernel';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    createCoreProofChecker
} from './proof_checker';
import {
    CoreProofPlan,
    coreProofPlanExact,
    coreProofPlanHave,
    validateCoreProofPlan
} from './proof_plan';

export const CORE_PROOF_SIMPLIFIER_PROFILE = Object.freeze({
    revision: 'emdash-proof-simplifier-v1' as const,
    target: 'closed-canonical-decoded-root' as const,
    equality: 'canonical-decoded-global-equality' as const,
    transport: 'canonical-backward-ind-eq' as const,
    rules: 'ordered-unconditional-global-theorems' as const,
    orientation: 'forward-only' as const,
    matching: 'provenance-insensitive-first-order-structural' as const,
    traversal: 'postorder-left-to-right-restart' as const,
    binderTraversal: 'opaque' as const,
    cycleKey: 'EMDASH-CORE-SEXP-1' as const,
    lowering: 'single-have-with-nested-checked-transport' as const,
    maximumRuleBinders: 64 as const,
    defaultLimits: Object.freeze({
        maximumRewrites: 64,
        maximumVisits: 4096,
        maximumRuleAttempts: 16384
    }),
    addsCoreExpressionTags: false as const,
    addsProofPlanTags: false as const,
    retainsCallbacks: false as const,
    retainsCheckerSession: false as const,
    retainsMetavariables: false as const,
    nodeBuiltinDependency: false as const,
    productionLambdapiDependency: false as const
});

export interface CoreProofSimplifierAdapter {
    readonly equality: KernelReference;
    readonly backwardTransport: KernelReference;
}

export const coreProofSimplifierAdapter = (
    equality: KernelReference,
    backwardTransport: KernelReference
): CoreProofSimplifierAdapter => Object.freeze({
    equality,
    backwardTransport
});

export interface CoreProofSimplifierRule {
    readonly id: string;
    readonly orientation: 'forward';
    readonly theorem: KernelReference;
}

export const coreProofSimplifierRule = (
    id: string,
    theorem: KernelReference
): CoreProofSimplifierRule => Object.freeze({
    id,
    orientation: 'forward',
    theorem
});

export interface CoreProofSimplifierLimits {
    readonly maximumRewrites: number;
    readonly maximumVisits: number;
    readonly maximumRuleAttempts: number;
}

export interface CoreProofSimplifierLimitsInput {
    readonly maximumRewrites?: number;
    readonly maximumVisits?: number;
    readonly maximumRuleAttempts?: number;
}

export interface CoreProofSimplifierTheoremOrigin {
    readonly kind: 'global-declaration';
    readonly name: string;
}

export interface CoreProofSimplifierTraceEntry {
    readonly step: number;
    readonly ruleId: string;
    readonly orientation: 'forward';
    readonly occurrencePath: string;
    readonly theoremOrigin: CoreProofSimplifierTheoremOrigin;
    readonly beforeClassifier: KernelExpression;
    readonly afterClassifier: KernelExpression;
    readonly before: KernelExpression;
    readonly after: KernelExpression;
    readonly elementClassifier: KernelExpression;
    readonly equalityProof: KernelExpression;
}

export interface CoreProofSimplifierInput {
    readonly environment: CoreLfDeclarationEnvironment;
    readonly target: KernelExpression;
    readonly adapter: CoreProofSimplifierAdapter;
    readonly rules: readonly CoreProofSimplifierRule[];
    /** A base plan for the resulting simplified target. */
    readonly continuation: CoreProofPlan;
    readonly provenance: Provenance;
    readonly bindingName?: string;
    readonly limits?: CoreProofSimplifierLimitsInput;
}

export interface CoreProofSimplifierResult {
    readonly revision: typeof CORE_PROOF_SIMPLIFIER_PROFILE.revision;
    readonly target: KernelExpression;
    readonly simplifiedTarget: KernelExpression;
    readonly rewriteCount: number;
    readonly visitCount: number;
    readonly ruleAttemptCount: number;
    readonly limits: CoreProofSimplifierLimits;
    readonly trace: readonly CoreProofSimplifierTraceEntry[];
    /** Present exactly when at least one rewrite occurred. */
    readonly transportTerm?: KernelExpression;
    readonly plan: CoreProofPlan;
}

export type CoreProofSimplifierErrorCode =
    | 'INVALID_TARGET'
    | 'INVALID_ADAPTER'
    | 'INVALID_RULE'
    | 'DUPLICATE_RULE_ID'
    | 'INVALID_CONTINUATION'
    | 'INVALID_LIMIT'
    | 'VISIT_LIMIT_EXCEEDED'
    | 'RULE_ATTEMPT_LIMIT_EXCEEDED'
    | 'REWRITE_LIMIT_EXCEEDED'
    | 'CYCLE_DETECTED'
    | 'INVALID_TRANSPORT';

export class CoreProofSimplifierError extends Error {
    constructor(
        public readonly code: CoreProofSimplifierErrorCode,
        public readonly path: string,
        public readonly provenance: Provenance,
        message: string,
        public readonly underlying?: Error
    ) {
        const location = provenance.span
            ? ` at ${formatSourceSpan(provenance.span)}`
            : '';
        super(`${message} (${path})${location}`);
        this.name = 'CoreProofSimplifierError';
    }
}

const fail = (
    code: CoreProofSimplifierErrorCode,
    path: string,
    nodeProvenance: Provenance,
    message: string,
    underlying?: Error
): never => {
    throw new CoreProofSimplifierError(
        code,
        path,
        nodeProvenance,
        message,
        underlying
    );
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const SAFE_BINDER = /^[A-Za-z][A-Za-z0-9_]*$/u;

interface PiTelescope {
    readonly binders: readonly KernelBinder[];
    readonly body: KernelExpression;
}

const peelPis = (expression: KernelExpression): PiTelescope => {
    const binders: KernelBinder[] = [];
    let body = expression;
    while (body.tag === 'pi') {
        binders.push(body.binder);
        body = body.body;
    }
    return Object.freeze({
        binders: Object.freeze(binders),
        body
    });
};

const isBound = (
    expression: KernelExpression,
    index: number
): boolean => expression.tag === 'bound' && expression.index === index;

const isGroupoidUniverse = (
    expression: KernelExpression
): boolean => expression.tag === 'application' &&
    expression.owner === 'groupoid-universe' &&
    expression.arguments.length === 0;

const decodedClassifier = (
    expression: KernelExpression
): KernelExpression | undefined => expression.tag === 'application' &&
    expression.owner === 'decode' &&
    expression.arguments.length === 1
    ? expression.arguments[0].value
    : undefined;

const isDecodedBound = (
    expression: KernelExpression,
    index: number
): boolean => {
    const classifier = decodedClassifier(expression);
    return classifier !== undefined && isBound(classifier, index);
};

interface EqualityCallParts {
    readonly classifier: KernelExpression;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
}

const equalityCallParts = (
    expression: KernelExpression,
    equality: KernelReference
): EqualityCallParts | undefined => {
    if (
        expression.tag !== 'call' ||
        !kernelExpressionEquals(expression.callee, equality) ||
        expression.arguments.length !== 3 ||
        expression.arguments[0].plicity !== 'implicit' ||
        expression.arguments[1].plicity !== 'explicit' ||
        expression.arguments[2].plicity !== 'explicit'
    ) {
        return undefined;
    }
    return Object.freeze({
        classifier: expression.arguments[0].value,
        left: expression.arguments[1].value,
        right: expression.arguments[2].value
    });
};

const isExplicitBoundCall = (
    expression: KernelExpression,
    calleeIndex: number,
    argumentIndex: number
): boolean => expression.tag === 'call' &&
    isBound(expression.callee, calleeIndex) &&
    expression.arguments.length === 1 &&
    expression.arguments[0].plicity === 'explicit' &&
    isBound(expression.arguments[0].value, argumentIndex);

interface ValidatedAdapter {
    readonly input: CoreProofSimplifierAdapter;
    readonly motiveBinderMode: BinderMode;
}

const inferReferenceType = (
    environment: CoreLfDeclarationEnvironment,
    reference: KernelReference,
    code: 'INVALID_ADAPTER' | 'INVALID_RULE',
    path: string
): KernelExpression => {
    if (!environment.lookup(reference.name)) {
        fail(
            code,
            path,
            reference.provenance,
            `Global theorem '${reference.name}' is not declared in the ` +
                'supplied exact LF environment'
        );
    }
    try {
        const checker = createCoreProofChecker(environment);
        const inferred = checker.infer(checker.rootContext, reference);
        const type = inferred.type;
        if (isCoreKind(type)) {
            return fail(
                code,
                path,
                reference.provenance,
                `Global theorem '${reference.name}' has checker sort KIND`
            );
        }
        return type;
    } catch (error: unknown) {
        if (error instanceof CoreProofSimplifierError) throw error;
        const underlying = error instanceof Error ? error : undefined;
        fail(
            code,
            path,
            reference.provenance,
            `Cannot infer global theorem '${reference.name}'`,
            underlying
        );
    }
};

const validateAdapter = (
    environment: CoreLfDeclarationEnvironment,
    adapter: CoreProofSimplifierAdapter,
    nodeProvenance: Provenance
): ValidatedAdapter => {
    if (
        adapter === null ||
        typeof adapter !== 'object' ||
        adapter.equality?.tag !== 'reference' ||
        adapter.backwardTransport?.tag !== 'reference'
    ) {
        fail(
            'INVALID_ADAPTER',
            'adapter',
            nodeProvenance,
            'Proof simplifier adapter requires equality and backward-' +
                'transport free references'
        );
    }

    const equalityType = inferReferenceType(
        environment,
        adapter.equality,
        'INVALID_ADAPTER',
        'adapter.equality'
    );
    const equalityTelescope = peelPis(equalityType);
    const equalityBinders = equalityTelescope.binders;
    const equalityShape = equalityBinders.length === 3 &&
        equalityBinders[0].mode.plicity === 'implicit' &&
        equalityBinders[1].mode.plicity === 'explicit' &&
        equalityBinders[2].mode.plicity === 'explicit' &&
        isGroupoidUniverse(equalityBinders[0].type) &&
        isDecodedBound(equalityBinders[1].type, 0) &&
        isDecodedBound(equalityBinders[2].type, 1) &&
        isGroupoidUniverse(equalityTelescope.body);
    if (!equalityShape) {
        fail(
            'INVALID_ADAPTER',
            'adapter.equality',
            adapter.equality.provenance,
            `Equality '${adapter.equality.name}' must have canonical shape ` +
                'Π [A : Grpd], τ A -> τ A -> Grpd'
        );
    }

    const transportType = inferReferenceType(
        environment,
        adapter.backwardTransport,
        'INVALID_ADAPTER',
        'adapter.backwardTransport'
    );
    const transportTelescope = peelPis(transportType);
    const binders = transportTelescope.binders;
    if (
        binders.length !== 6 ||
        binders[0].mode.plicity !== 'implicit' ||
        binders[1].mode.plicity !== 'implicit' ||
        binders[2].mode.plicity !== 'implicit' ||
        binders[3].mode.plicity !== 'explicit' ||
        binders[4].mode.plicity !== 'explicit' ||
        binders[5].mode.plicity !== 'explicit' ||
        !isGroupoidUniverse(binders[0].type) ||
        !isDecodedBound(binders[1].type, 0) ||
        !isDecodedBound(binders[2].type, 1)
    ) {
        fail(
            'INVALID_ADAPTER',
            'adapter.backwardTransport',
            adapter.backwardTransport.provenance,
            `Backward transport '${adapter.backwardTransport.name}' does ` +
                'not have the canonical six-binder ind_eq prefix'
        );
    }

    const pathClassifier = decodedClassifier(binders[3].type);
    const path = pathClassifier
        ? equalityCallParts(pathClassifier, adapter.equality)
        : undefined;
    if (
        !path ||
        !isBound(path.classifier, 2) ||
        !isBound(path.left, 1) ||
        !isBound(path.right, 0)
    ) {
        fail(
            'INVALID_ADAPTER',
            'adapter.backwardTransport.path',
            binders[3].provenance,
            'Backward transport path must be τ (Eq A x y)'
        );
    }

    const motiveType = binders[4].type;
    if (motiveType.tag !== 'pi') {
        return fail(
            'INVALID_ADAPTER',
            'adapter.backwardTransport.motive',
            binders[4].provenance,
            'Backward transport motive must have shape τ A -> Grpd'
        );
    }
    if (
        motiveType.binder.mode.plicity !== 'explicit' ||
        !isDecodedBound(motiveType.binder.type, 3) ||
        !isGroupoidUniverse(motiveType.body)
    ) {
        fail(
            'INVALID_ADAPTER',
            'adapter.backwardTransport.motive',
            binders[4].provenance,
            'Backward transport motive must have shape τ A -> Grpd'
        );
    }

    const baseClassifier = decodedClassifier(binders[5].type);
    const resultClassifier = decodedClassifier(transportTelescope.body);
    if (
        !baseClassifier ||
        !isExplicitBoundCall(baseClassifier, 0, 2) ||
        !resultClassifier ||
        !isExplicitBoundCall(resultClassifier, 1, 4)
    ) {
        fail(
            'INVALID_ADAPTER',
            'adapter.backwardTransport.direction',
            adapter.backwardTransport.provenance,
            'Backward transport must map τ (P y) to τ (P x)'
        );
    }

    return Object.freeze({
        input: adapter,
        motiveBinderMode: Object.freeze({ ...motiveType.binder.mode })
    });
};

const assertFirstOrder = (
    expression: KernelExpression,
    path: string,
    rule: CoreProofSimplifierRule
): void => {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
        case 'bound':
            return;
        case 'meta':
            return fail(
                'INVALID_RULE',
                path,
                expression.provenance,
                `Simplifier rule '${rule.id}' contains a metavariable`
            );
        case 'application':
            expression.arguments.forEach((argument, index) =>
                assertFirstOrder(
                    argument.value,
                    `${path}.arguments[${index}]`,
                    rule
                )
            );
            return;
        case 'call':
            assertFirstOrder(expression.callee, `${path}.callee`, rule);
            expression.arguments.forEach((argument, index) =>
                assertFirstOrder(
                    argument.value,
                    `${path}.arguments[${index}]`,
                    rule
                )
            );
            return;
        case 'pi':
        case 'lambda':
            return fail(
                'INVALID_RULE',
                path,
                expression.provenance,
                `Simplifier rule '${rule.id}' contains an opaque ` +
                    `${expression.tag} inside its first-order equality`
            );
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const collectBoundIndices = (
    expression: KernelExpression,
    result: Set<number>
): void => {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
            return;
        case 'bound':
            result.add(expression.index);
            return;
        case 'meta':
            expression.spine.forEach(item =>
                collectBoundIndices(item, result)
            );
            return;
        case 'application':
            expression.arguments.forEach(argument =>
                collectBoundIndices(argument.value, result)
            );
            return;
        case 'call':
            collectBoundIndices(expression.callee, result);
            expression.arguments.forEach(argument =>
                collectBoundIndices(argument.value, result)
            );
            return;
        case 'pi':
        case 'lambda':
            collectBoundIndices(expression.binder.type, result);
            collectBoundIndices(expression.body, result);
            return;
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

interface ValidatedRule {
    readonly input: CoreProofSimplifierRule;
    readonly binders: readonly KernelBinder[];
    readonly equalityClassifier: KernelExpression;
    readonly elementClassifier: KernelExpression;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
}

const validateRule = (
    environment: CoreLfDeclarationEnvironment,
    equality: KernelReference,
    rule: CoreProofSimplifierRule,
    index: number
): ValidatedRule => {
    const path = `rules[${index}]`;
    if (
        rule === null ||
        typeof rule !== 'object' ||
        !SAFE_ID.test(rule.id) ||
        rule.orientation !== 'forward' ||
        rule.theorem?.tag !== 'reference'
    ) {
        fail(
            'INVALID_RULE',
            path,
            rule?.theorem?.provenance ?? equality.provenance,
            'Simplifier rules require a stable ID, explicit forward ' +
                'orientation, and one global theorem reference'
        );
    }

    const theoremType = inferReferenceType(
        environment,
        rule.theorem,
        'INVALID_RULE',
        `${path}.theorem`
    );
    const telescope = peelPis(theoremType);
    if (
        telescope.binders.length >
        CORE_PROOF_SIMPLIFIER_PROFILE.maximumRuleBinders
    ) {
        fail(
            'INVALID_RULE',
            `${path}.theorem`,
            rule.theorem.provenance,
            `Simplifier rule '${rule.id}' has ${telescope.binders.length} ` +
                'binders, exceeding the profile limit of ' +
                CORE_PROOF_SIMPLIFIER_PROFILE.maximumRuleBinders
        );
    }

    const equalityClassifier = decodedClassifier(telescope.body);
    const equalityParts = equalityClassifier
        ? equalityCallParts(equalityClassifier, equality)
        : undefined;
    if (!equalityClassifier || !equalityParts) {
        fail(
            'INVALID_RULE',
            `${path}.theorem.type`,
            rule.theorem.provenance,
            `Simplifier theorem '${rule.theorem.name}' must end in the ` +
                'canonical decoded equality selected by the adapter'
        );
    }

    assertFirstOrder(
        equalityParts.classifier,
        `${path}.classifier`,
        rule
    );
    assertFirstOrder(equalityParts.left, `${path}.left`, rule);
    assertFirstOrder(equalityParts.right, `${path}.right`, rule);
    if (equalityParts.left.tag === 'bound') {
        fail(
            'INVALID_RULE',
            `${path}.left`,
            equalityParts.left.provenance,
            `Simplifier rule '${rule.id}' cannot have a bare theorem ` +
                'parameter as its left side'
        );
    }

    const determined = new Set<number>();
    collectBoundIndices(equalityParts.classifier, determined);
    collectBoundIndices(equalityParts.left, determined);
    for (let binderIndex = 0;
        binderIndex < telescope.binders.length;
        binderIndex++
    ) {
        if (determined.has(binderIndex)) continue;
        fail(
            'INVALID_RULE',
            `${path}.theorem.binders`,
            telescope.binders[
                telescope.binders.length - binderIndex - 1
            ].provenance,
            `Simplifier rule '${rule.id}' has a condition or right-only ` +
                `binder at De Bruijn index ${binderIndex}`
        );
    }

    return Object.freeze({
        input: rule,
        binders: telescope.binders,
        equalityClassifier,
        elementClassifier: equalityParts.classifier,
        left: equalityParts.left,
        right: equalityParts.right
    });
};

const validateRules = (
    environment: CoreLfDeclarationEnvironment,
    equality: KernelReference,
    rules: readonly CoreProofSimplifierRule[],
    nodeProvenance: Provenance
): readonly ValidatedRule[] => {
    if (!Array.isArray(rules)) {
        fail(
            'INVALID_RULE',
            'rules',
            nodeProvenance,
            'Proof simplifier rules must be an explicit ordered array'
        );
    }
    const ids = new Set<string>();
    return Object.freeze(rules.map((rule, index) => {
        const validated = validateRule(environment, equality, rule, index);
        if (ids.has(validated.input.id)) {
            fail(
                'DUPLICATE_RULE_ID',
                `rules[${index}].id`,
                validated.input.theorem.provenance,
                `Duplicate simplifier rule ID '${validated.input.id}'`
            );
        }
        ids.add(validated.input.id);
        return validated;
    }));
};

const containsMeta = (expression: KernelExpression): boolean => {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
        case 'bound':
            return false;
        case 'meta':
            return true;
        case 'application':
            return expression.arguments.some(argument =>
                containsMeta(argument.value)
            );
        case 'call':
            return containsMeta(expression.callee) ||
                expression.arguments.some(argument =>
                    containsMeta(argument.value)
                );
        case 'pi':
        case 'lambda':
            return containsMeta(expression.binder.type) ||
                containsMeta(expression.body);
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const validateTarget = (
    environment: CoreLfDeclarationEnvironment,
    target: KernelExpression,
    nodeProvenance: Provenance
): KernelExpression => {
    try {
        kernelAssertScoped(target, 0);
    } catch (error: unknown) {
        const underlying = error instanceof Error ? error : undefined;
        fail(
            'INVALID_TARGET',
            'target',
            target?.provenance ?? nodeProvenance,
            'Proof simplifier target must be closed',
            underlying
        );
    }
    if (containsMeta(target)) {
        fail(
            'INVALID_TARGET',
            'target',
            target.provenance,
            'Proof simplifier target must be meta-free'
        );
    }
    const classifier = decodedClassifier(target);
    if (!classifier) {
        fail(
            'INVALID_TARGET',
            'target',
            target.provenance,
            'Proof simplifier root target must be canonical τ classifier'
        );
    }
    try {
        const checker = createCoreProofChecker(environment);
        const inferred = checker.infer(checker.rootContext, target);
        if (isCoreKind(inferred.type) || inferred.type.tag !== 'universe') {
            fail(
                'INVALID_TARGET',
                'target',
                target.provenance,
                'Proof simplifier root target must inhabit TYPE'
            );
        }
    } catch (error: unknown) {
        if (error instanceof CoreProofSimplifierError) throw error;
        const underlying = error instanceof Error ? error : undefined;
        fail(
            'INVALID_TARGET',
            'target',
            target.provenance,
            'Proof simplifier root target does not check',
            underlying
        );
    }
    return classifier;
};

const normalizeLimits = (
    input: CoreProofSimplifierLimitsInput | undefined,
    nodeProvenance: Provenance
): CoreProofSimplifierLimits => {
    const limits = {
        maximumRewrites:
            input?.maximumRewrites ??
            CORE_PROOF_SIMPLIFIER_PROFILE.defaultLimits.maximumRewrites,
        maximumVisits:
            input?.maximumVisits ??
            CORE_PROOF_SIMPLIFIER_PROFILE.defaultLimits.maximumVisits,
        maximumRuleAttempts:
            input?.maximumRuleAttempts ??
            CORE_PROOF_SIMPLIFIER_PROFILE.defaultLimits.maximumRuleAttempts
    };
    for (const [name, value] of Object.entries(limits)) {
        if (Number.isSafeInteger(value) && value >= 0) continue;
        fail(
            'INVALID_LIMIT',
            `limits.${name}`,
            nodeProvenance,
            `Proof simplifier limit '${name}' must be a nonnegative safe ` +
                `integer; received ${String(value)}`
        );
    }
    return Object.freeze(limits);
};

type PatternSubstitution = Map<number, KernelExpression>;

const matchPattern = (
    pattern: KernelExpression,
    candidate: KernelExpression,
    binderCount: number,
    substitution: PatternSubstitution
): boolean => {
    if (pattern.tag === 'bound') {
        if (pattern.index >= binderCount) return false;
        const existing = substitution.get(pattern.index);
        if (existing) return kernelExpressionEquals(existing, candidate);
        substitution.set(pattern.index, candidate);
        return true;
    }
    if (pattern.tag !== candidate.tag) return false;

    switch (pattern.tag) {
        case 'universe':
            return true;
        case 'reference':
            return pattern.name ===
                (candidate as KernelReference).name;
        case 'meta':
            return false;
        case 'application': {
            const other = candidate as Extract<
                KernelExpression,
                { tag: 'application' }
            >;
            return pattern.owner === other.owner &&
                pattern.arguments.length === other.arguments.length &&
                pattern.arguments.every((argument, index) =>
                    argument.plicity === other.arguments[index].plicity &&
                    matchPattern(
                        argument.value,
                        other.arguments[index].value,
                        binderCount,
                        substitution
                    )
                );
        }
        case 'call': {
            const other = candidate as Extract<
                KernelExpression,
                { tag: 'call' }
            >;
            return matchPattern(
                pattern.callee,
                other.callee,
                binderCount,
                substitution
            ) &&
                pattern.arguments.length === other.arguments.length &&
                pattern.arguments.every((argument, index) =>
                    argument.plicity === other.arguments[index].plicity &&
                    matchPattern(
                        argument.value,
                        other.arguments[index].value,
                        binderCount,
                        substitution
                    )
                );
        }
        case 'pi':
        case 'lambda':
            return false;
        default: {
            const exhaustive: never = pattern;
            return exhaustive;
        }
    }
};

interface RuleApplication {
    readonly after: KernelExpression;
    readonly elementClassifier: KernelExpression;
    readonly equalityProof: KernelExpression;
}

const tryRule = (
    environment: CoreLfDeclarationEnvironment,
    candidate: KernelExpression,
    rule: ValidatedRule
): RuleApplication | undefined => {
    const substitution: PatternSubstitution = new Map();
    if (!matchPattern(
        rule.left,
        candidate,
        rule.binders.length,
        substitution
    )) {
        return undefined;
    }

    try {
        const checker = createCoreProofChecker(environment);
        const candidateInference = checker.infer(
            checker.rootContext,
            candidate
        );
        if (isCoreKind(candidateInference.type)) return undefined;
        const elementClassifier = decodedClassifier(
            candidateInference.type
        );
        if (
            !elementClassifier ||
            !matchPattern(
                rule.elementClassifier,
                elementClassifier,
                rule.binders.length,
                substitution
            )
        ) {
            return undefined;
        }
        if (substitution.size !== rule.binders.length) return undefined;

        const spine = Object.freeze(Array.from(
            { length: rule.binders.length },
            (_, index) => substitution.get(index)!
        ));
        const instantiatedLeft = kernelInstantiateSpine(rule.left, spine);
        if (!kernelExpressionEquals(instantiatedLeft, candidate)) {
            return undefined;
        }
        const after = kernelInstantiateSpine(rule.right, spine);
        const equalityClassifier = kernelInstantiateSpine(
            rule.equalityClassifier,
            spine
        );
        const expectedProofType = kernelApplication(
            'decode',
            [{ value: equalityClassifier }],
            rule.input.theorem.provenance
        );
        const supplied = rule.binders.map((binding, outerIndex) => ({
            plicity: binding.mode.plicity,
            value: substitution.get(
                rule.binders.length - outerIndex - 1
            )!,
            provenance: rule.input.theorem.provenance
        }));
        const rawProof = supplied.length === 0
            ? rule.input.theorem
            : kernelCall(
                rule.input.theorem,
                supplied,
                rule.input.theorem.provenance
            );
        const equalityProof = checker.check(
            checker.rootContext,
            rawProof,
            expectedProofType
        ).term;
        return Object.freeze({
            after,
            elementClassifier,
            equalityProof
        });
    } catch (error: unknown) {
        if (error instanceof CoreCheckerError) return undefined;
        throw error;
    }
};

type OccurrencePathSegment =
    | { readonly tag: 'callee' }
    | { readonly tag: 'argument'; readonly index: number };

interface AcceptedRewrite {
    readonly path: readonly OccurrencePathSegment[];
    readonly entry: CoreProofSimplifierTraceEntry;
}

const occurrencePathText = (
    path: readonly OccurrencePathSegment[]
): string => path.reduce((text, segment) => segment.tag === 'callee'
    ? `${text}.callee`
    : `${text}.arguments[${segment.index}]`, '$');

const replaceAtPath = (
    expression: KernelExpression,
    path: readonly OccurrencePathSegment[],
    replacement: KernelExpression
): KernelExpression => {
    if (path.length === 0) return replacement;
    const [head, ...tail] = path;

    if (head.tag === 'callee') {
        if (expression.tag !== 'call') {
            throw new Error('Internal simplifier callee path mismatch');
        }
        return kernelCall(
            replaceAtPath(expression.callee, tail, replacement),
            expression.arguments.map(argument => ({
                plicity: argument.plicity,
                value: argument.value,
                provenance: argument.provenance
            })),
            expression.provenance
        );
    }

    if (
        expression.tag !== 'application' &&
        expression.tag !== 'call'
    ) {
        throw new Error('Internal simplifier argument path mismatch');
    }
    if (head.index < 0 || head.index >= expression.arguments.length) {
        throw new Error('Internal simplifier argument index mismatch');
    }
    const arguments_ = expression.arguments.map((argument, index) => ({
        plicity: argument.plicity,
        value: index === head.index
            ? replaceAtPath(argument.value, tail, replacement)
            : argument.value,
        provenance: argument.provenance
    }));
    return expression.tag === 'application'
        ? kernelApplication(
            expression.owner,
            arguments_,
            expression.provenance
        )
        : kernelCall(
            expression.callee,
            arguments_,
            expression.provenance
        );
};

interface MutableCounters {
    rewrites: number;
    visits: number;
    attempts: number;
}

interface LocatedRewrite extends RuleApplication {
    readonly rule: ValidatedRule;
    readonly before: KernelExpression;
    readonly path: readonly OccurrencePathSegment[];
}

const chargeVisit = (
    counters: MutableCounters,
    limits: CoreProofSimplifierLimits,
    nodeProvenance: Provenance
): void => {
    if (counters.visits >= limits.maximumVisits) {
        fail(
            'VISIT_LIMIT_EXCEEDED',
            'limits.maximumVisits',
            nodeProvenance,
            `Proof simplifier requires a visit beyond ` +
                `${limits.maximumVisits}`
        );
    }
    counters.visits++;
};

const chargeAttempt = (
    counters: MutableCounters,
    limits: CoreProofSimplifierLimits,
    nodeProvenance: Provenance
): void => {
    if (counters.attempts >= limits.maximumRuleAttempts) {
        fail(
            'RULE_ATTEMPT_LIMIT_EXCEEDED',
            'limits.maximumRuleAttempts',
            nodeProvenance,
            `Proof simplifier requires a rule attempt beyond ` +
                `${limits.maximumRuleAttempts}`
        );
    }
    counters.attempts++;
};

const findFirstRewrite = (
    environment: CoreLfDeclarationEnvironment,
    root: KernelExpression,
    rules: readonly ValidatedRule[],
    counters: MutableCounters,
    limits: CoreProofSimplifierLimits
): LocatedRewrite | undefined => {
    const visit = (
        expression: KernelExpression,
        path: readonly OccurrencePathSegment[]
    ): LocatedRewrite | undefined => {
        if (expression.tag === 'application') {
            for (let index = 0; index < expression.arguments.length; index++) {
                const found = visit(
                    expression.arguments[index].value,
                    [...path, Object.freeze({
                        tag: 'argument' as const,
                        index
                    })]
                );
                if (found) return found;
            }
        } else if (expression.tag === 'call') {
            const atCallee = visit(
                expression.callee,
                [...path, Object.freeze({ tag: 'callee' as const })]
            );
            if (atCallee) return atCallee;
            for (let index = 0; index < expression.arguments.length; index++) {
                const found = visit(
                    expression.arguments[index].value,
                    [...path, Object.freeze({
                        tag: 'argument' as const,
                        index
                    })]
                );
                if (found) return found;
            }
        }

        chargeVisit(counters, limits, expression.provenance);
        for (const rule of rules) {
            chargeAttempt(counters, limits, expression.provenance);
            const application = tryRule(environment, expression, rule);
            if (!application) continue;
            return Object.freeze({
                ...application,
                rule,
                before: expression,
                path: Object.freeze([...path])
            });
        }
        return undefined;
    };

    return visit(root, Object.freeze([]));
};

const decoded = (
    classifier: KernelExpression,
    nodeProvenance: Provenance
): KernelExpression => kernelApplication(
    'decode',
    [{ value: classifier }],
    nodeProvenance
);

const buildTransport = (
    environment: CoreLfDeclarationEnvironment,
    adapter: ValidatedAdapter,
    accepted: readonly AcceptedRewrite[],
    simplifiedTarget: KernelExpression,
    originalTarget: KernelExpression,
    bindingName: string,
    nodeProvenance: Provenance
): {
    readonly binding: KernelBinder;
    readonly term: KernelExpression;
} => {
    const binding = kernelBinder(
        bindingName,
        simplifiedTarget,
        binderMode('explicit', 'functorial'),
        nodeProvenance
    );
    const checker = createCoreProofChecker(environment);
    const context = checker.rootContext.extend(binding);
    let term: KernelExpression = kernelBound(0, nodeProvenance);

    for (let index = accepted.length - 1; index >= 0; index--) {
        const { entry, path } = accepted[index];
        const motiveBody = replaceAtPath(
            entry.beforeClassifier,
            path,
            kernelBound(0, nodeProvenance)
        );
        const motive = kernelLambda(
            kernelBinder(
                `simp_value_${entry.step}`,
                decoded(entry.elementClassifier, nodeProvenance),
                adapter.motiveBinderMode,
                nodeProvenance
            ),
            motiveBody,
            nodeProvenance
        );
        term = kernelCall(
            adapter.input.backwardTransport,
            [
                {
                    plicity: 'explicit',
                    value: entry.equalityProof,
                    provenance: nodeProvenance
                },
                {
                    plicity: 'explicit',
                    value: motive,
                    provenance: nodeProvenance
                },
                {
                    plicity: 'explicit',
                    value: term,
                    provenance: nodeProvenance
                }
            ],
            nodeProvenance
        );
    }

    try {
        const checked = checker.check(context, term, originalTarget).term;
        return Object.freeze({ binding, term: checked });
    } catch (error: unknown) {
        const underlying = error instanceof Error ? error : undefined;
        fail(
            'INVALID_TRANSPORT',
            'transport',
            nodeProvenance,
            'Generated simplifier transport failed final proof checking',
            underlying
        );
    }
};

/**
 * Expand one deterministic simplification request into ordinary proof-plan
 * data plus independently checked equality and transport evidence.
 */
export function simplifyCoreProofPlan(
    input: CoreProofSimplifierInput
): CoreProofSimplifierResult {
    const limits = normalizeLimits(input.limits, input.provenance);
    const classifier = validateTarget(
        input.environment,
        input.target,
        input.provenance
    );
    const adapter = validateAdapter(
        input.environment,
        input.adapter,
        input.provenance
    );
    const rules = validateRules(
        input.environment,
        adapter.input.equality,
        input.rules,
        input.provenance
    );
    try {
        validateCoreProofPlan(input.continuation);
    } catch (error: unknown) {
        const underlying = error instanceof Error ? error : undefined;
        fail(
            'INVALID_CONTINUATION',
            'continuation',
            input.continuation?.provenance ?? input.provenance,
            'Proof simplifier continuation is not a valid base plan',
            underlying
        );
    }

    const bindingName = input.bindingName ?? 'simplified';
    if (!SAFE_BINDER.test(bindingName)) {
        fail(
            'INVALID_CONTINUATION',
            'bindingName',
            input.provenance,
            `Proof simplifier have-binder name '${bindingName}' is not a ` +
                'portable Core identifier'
        );
    }

    const counters: MutableCounters = {
        rewrites: 0,
        visits: 0,
        attempts: 0
    };
    const accepted: AcceptedRewrite[] = [];
    const seen = new Set<string>([serializeCoreExpression(classifier)]);
    let current = classifier;

    while (true) {
        const located = findFirstRewrite(
            input.environment,
            current,
            rules,
            counters,
            limits
        );
        if (!located) break;
        if (counters.rewrites >= limits.maximumRewrites) {
            fail(
                'REWRITE_LIMIT_EXCEEDED',
                'limits.maximumRewrites',
                located.before.provenance,
                `Proof simplifier requires a rewrite beyond ` +
                    `${limits.maximumRewrites}`
            );
        }

        const afterClassifier = replaceAtPath(
            current,
            located.path,
            located.after
        );
        const key = serializeCoreExpression(afterClassifier);
        if (seen.has(key)) {
            fail(
                'CYCLE_DETECTED',
                `trace[${accepted.length}]`,
                located.before.provenance,
                `Simplifier rule '${located.rule.input.id}' revisits an ` +
                    'already accepted classifier'
            );
        }

        counters.rewrites++;
        const entry: CoreProofSimplifierTraceEntry = Object.freeze({
            step: counters.rewrites,
            ruleId: located.rule.input.id,
            orientation: 'forward',
            occurrencePath: occurrencePathText(located.path),
            theoremOrigin: Object.freeze({
                kind: 'global-declaration',
                name: located.rule.input.theorem.name
            }),
            beforeClassifier: current,
            afterClassifier,
            before: located.before,
            after: located.after,
            elementClassifier: located.elementClassifier,
            equalityProof: located.equalityProof
        });
        accepted.push(Object.freeze({
            path: located.path,
            entry
        }));
        seen.add(key);
        current = afterClassifier;
    }

    const trace = Object.freeze(accepted.map(item => item.entry));
    const simplifiedTarget = accepted.length === 0
        ? input.target
        : decoded(current, input.target.provenance);
    if (accepted.length === 0) {
        return Object.freeze({
            revision: CORE_PROOF_SIMPLIFIER_PROFILE.revision,
            target: input.target,
            simplifiedTarget,
            rewriteCount: 0,
            visitCount: counters.visits,
            ruleAttemptCount: counters.attempts,
            limits,
            trace,
            plan: input.continuation
        });
    }

    const transport = buildTransport(
        input.environment,
        adapter,
        accepted,
        simplifiedTarget,
        input.target,
        bindingName,
        input.provenance
    );
    const plan = coreProofPlanHave(
        transport.binding,
        input.continuation,
        coreProofPlanExact(transport.term, {
            provenance: input.provenance
        }),
        { provenance: input.provenance }
    );
    validateCoreProofPlan(plan);

    return Object.freeze({
        revision: CORE_PROOF_SIMPLIFIER_PROFILE.revision,
        target: input.target,
        simplifiedTarget,
        rewriteCount: counters.rewrites,
        visitCount: counters.visits,
        ruleAttemptCount: counters.attempts,
        limits,
        trace,
        transportTerm: transport.term,
        plan
    });
}
