/**
 * Bounded bidirectional checking and implicit insertion for explicit Core.
 *
 * This checker knows Pi formation and elimination, lambdas, declarations,
 * contextual metas, and the declarative owner-signature catalog. TSK-2C adds
 * candidate definitional comparison for exactly the H-03-reviewed runtime
 * program. It still executes no proof-time/conformance rule and makes no
 * H-04 termination, confluence, or subject-reduction claim.
 */

import {
    CoreContext,
    CoreDeclarationEnvironment
} from './context';
import {
    BinderMode,
    KernelArgument,
    KernelCallArgumentInput,
    KernelExpression,
    KernelMetaVariable,
    Provenance,
    formatSourceSpan,
    kernelApplication,
    kernelBinder,
    kernelCall,
    kernelExpressionEquals,
    kernelInstantiate,
    kernelInstantiateSpine,
    kernelLambda,
    kernelPi,
    kernelUniverse,
    provenance
} from './kernel';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId
} from './schema';
import {
    coreOwnerResultType,
    coreOwnerSlotType
} from './signature';
import {
    CoreConstraint,
    CoreElaborationSession,
    CoreSessionError
} from './session';
import {
    coreRuntimeDefinitionalCompare
} from './conversion';

/**
 * `KIND` is the checker-only classification of `TYPE` and kind-level Pi
 * telescopes. It is deliberately not a KernelExpression: no Core term may use
 * it as an ordinary type or serialize it as a runtime expression.
 */
export interface CoreKind {
    readonly tag: 'kind';
    readonly provenance: Provenance;
}

export type CoreInferredType = KernelExpression | CoreKind;

export interface CoreInferenceResult {
    readonly term: KernelExpression;
    readonly type: CoreInferredType;
}

export interface CoreCheckResult {
    readonly term: KernelExpression;
    readonly type: KernelExpression;
}

export type CoreCheckerErrorCode =
    | 'FOREIGN_CONTEXT'
    | 'UNBOUND_FREE_REFERENCE'
    | 'DANGLING_BOUND_VARIABLE'
    | 'CANNOT_INFER_LAMBDA'
    | 'EXPECTED_TYPE'
    | 'EXPECTED_FUNCTION'
    | 'PLICITY_MISMATCH'
    | 'BINDER_MODE_MISMATCH'
    | 'TYPE_MISMATCH'
    | 'MISSING_EXPLICIT_ARGUMENT'
    | 'TOO_MANY_ARGUMENTS'
    | 'EMPTY_GENERIC_CALL'
    | 'CONSTRAINT_REJECTED'
    | 'UNRESOLVED_CONSTRAINTS'
    | 'UNRESOLVED_METAVARIABLE'
    | 'INVALID_DECLARATION_TYPE'
    | 'CONVERSION_STEP_LIMIT';

export class CoreCheckerError extends Error {
    constructor(
        public readonly code: CoreCheckerErrorCode,
        public readonly provenance: Provenance,
        message: string,
        public readonly constraint?: CoreConstraint,
        public readonly sessionError?: CoreSessionError
    ) {
        const location = provenance.span
            ? ` at ${formatSourceSpan(provenance.span)}`
            : '';
        super(`${message}${location}`);
        this.name = 'CoreCheckerError';
    }
}

const coreKind = (nodeProvenance: Provenance): CoreKind =>
    Object.freeze({
        tag: 'kind',
        provenance: nodeProvenance
    });

export const isCoreKind = (
    type: CoreInferredType
): type is CoreKind => type.tag === 'kind';

const derived = (
    detail: string,
    nodeProvenance: Provenance
): Provenance => provenance(
    'derived',
    detail,
    nodeProvenance.span
);

const sameMode = (left: BinderMode, right: BinderMode): boolean =>
    left.plicity === right.plicity &&
    left.variation === right.variation;

export const CORE_CHECKER_RUNTIME_COMPARISON_STEP_LIMIT = 256;

const expressionHead = (expression: KernelExpression): string => {
    switch (expression.tag) {
        case 'universe':
            return 'TYPE';
        case 'reference':
            return `free name '${expression.name}'`;
        case 'bound':
            return `bound index ${expression.index}`;
        case 'meta':
            return `metavariable ?m${expression.identity.index}`;
        case 'application':
            return `owner application ${expression.owner}`;
        case 'call':
            return 'generic call';
        case 'pi':
            return 'Pi type';
        case 'lambda':
            return 'lambda';
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const firstUnsolvedMeta = (
    expression: KernelExpression
): KernelMetaVariable | undefined => {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
        case 'bound':
            return undefined;
        case 'meta':
            return expression;
        case 'application':
            for (const argument of expression.arguments) {
                const meta = firstUnsolvedMeta(argument.value);
                if (meta) return meta;
            }
            return undefined;
        case 'call': {
            const headMeta = firstUnsolvedMeta(expression.callee);
            if (headMeta) return headMeta;
            for (const argument of expression.arguments) {
                const meta = firstUnsolvedMeta(argument.value);
                if (meta) return meta;
            }
            return undefined;
        }
        case 'pi':
        case 'lambda':
            return firstUnsolvedMeta(expression.binder.type) ??
                firstUnsolvedMeta(expression.body);
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

interface MutableInferenceResult {
    term: KernelExpression;
    type: CoreInferredType;
}

interface MutableCheckResult {
    term: KernelExpression;
    type: KernelExpression;
}

/**
 * One checker is bound to one elaboration session. Every public operation is a
 * complete boundary: constraints are revisited, results are zonked, and any
 * remaining ambiguity is reported rather than leaking a raw meta.
 */
export class CoreChecker {
    constructor(public readonly session: CoreElaborationSession) {}

    get rootContext(): CoreContext {
        return this.session.rootContext;
    }

    private fail(
        code: CoreCheckerErrorCode,
        nodeProvenance: Provenance,
        message: string,
        constraint?: CoreConstraint,
        sessionError?: CoreSessionError
    ): never {
        throw new CoreCheckerError(
            code,
            nodeProvenance,
            message,
            constraint,
            sessionError
        );
    }

    private assertContext(
        context: CoreContext,
        nodeProvenance: Provenance
    ): void {
        if (context.environment === this.session.environment) return;
        this.fail(
            'FOREIGN_CONTEXT',
            nodeProvenance,
            'Core checker context belongs to a different declaration environment'
        );
    }

    private zonkType(type: CoreInferredType): CoreInferredType {
        return isCoreKind(type) ? type : this.session.zonk(type);
    }

    private addMetaConstraint(
        context: CoreContext,
        left: KernelExpression,
        right: KernelExpression,
        nodeProvenance: Provenance
    ): void {
        const constraint = this.session.addConstraint(
            context,
            left,
            right,
            nodeProvenance
        );
        const step = this.session.stepConstraint(constraint.id);
        if (step.outcome !== 'rejected') return;
        this.fail(
            'CONSTRAINT_REJECTED',
            step.error?.provenance ?? nodeProvenance,
            `Core type constraint ${constraint.id} was rejected: ` +
            `${step.reason}`,
            this.session.constraints.find(item => item.id === constraint.id),
            step.error
        );
    }

    /**
     * Structurally decompose a type equality. Only a meta-vs-term leaf is
     * delegated to the session, preserving its occurs/scope/session checks.
     */
    private constrain(
        context: CoreContext,
        leftInput: KernelExpression,
        rightInput: KernelExpression,
        nodeProvenance: Provenance
    ): void {
        const left = this.session.zonk(leftInput);
        const right = this.session.zonk(rightInput);
        if (kernelExpressionEquals(left, right)) return;

        const comparison = coreRuntimeDefinitionalCompare(
            left,
            right,
            CORE_CHECKER_RUNTIME_COMPARISON_STEP_LIMIT
        );
        if (comparison.status === 'equal') return;
        if (comparison.status === 'step-limit-exceeded') {
            this.fail(
                'CONVERSION_STEP_LIMIT',
                nodeProvenance,
                `Core runtime conversion exceeded ` +
                `${CORE_CHECKER_RUNTIME_COMPARISON_STEP_LIMIT} steps at ` +
                `${comparison.path.join(' / ')} before rule ` +
                `'${comparison.nextRuleId}'`
            );
        }

        if (left.tag === 'meta' || right.tag === 'meta') {
            this.addMetaConstraint(
                context,
                left,
                right,
                nodeProvenance
            );
            return;
        }

        if (left.tag !== right.tag) {
            this.fail(
                'TYPE_MISMATCH',
                nodeProvenance,
                `Core type mismatch: ${expressionHead(left)} is not ` +
                expressionHead(right)
            );
        }

        switch (left.tag) {
            case 'universe':
                return;
            case 'reference': {
                const other = right as typeof left;
                if (
                    left.namespace === other.namespace &&
                    left.name === other.name
                ) {
                    return;
                }
                break;
            }
            case 'bound': {
                const other = right as typeof left;
                if (left.index === other.index) return;
                break;
            }
            case 'application': {
                const other = right as typeof left;
                if (
                    left.owner !== other.owner ||
                    left.arguments.length !== other.arguments.length
                ) {
                    break;
                }
                for (let index = 0; index < left.arguments.length; index++) {
                    const leftArgument = left.arguments[index];
                    const rightArgument = other.arguments[index];
                    if (leftArgument.plicity !== rightArgument.plicity) {
                        this.fail(
                            'PLICITY_MISMATCH',
                            nodeProvenance,
                            `Core owner ${left.owner} type argument ${index} ` +
                            `is ${leftArgument.plicity}, expected ` +
                            rightArgument.plicity
                        );
                    }
                    this.constrain(
                        context,
                        leftArgument.value,
                        rightArgument.value,
                        nodeProvenance
                    );
                }
                return;
            }
            case 'call': {
                const other = right as typeof left;
                if (left.arguments.length !== other.arguments.length) break;
                this.constrain(
                    context,
                    left.callee,
                    other.callee,
                    nodeProvenance
                );
                for (let index = 0; index < left.arguments.length; index++) {
                    const leftArgument = left.arguments[index];
                    const rightArgument = other.arguments[index];
                    if (leftArgument.plicity !== rightArgument.plicity) {
                        this.fail(
                            'PLICITY_MISMATCH',
                            nodeProvenance,
                            `Core generic type argument ${index} is ` +
                            `${leftArgument.plicity}, expected ` +
                            rightArgument.plicity
                        );
                    }
                    this.constrain(
                        context,
                        leftArgument.value,
                        rightArgument.value,
                        nodeProvenance
                    );
                }
                return;
            }
            case 'pi':
            case 'lambda': {
                const other = right as typeof left;
                if (!sameMode(left.binder.mode, other.binder.mode)) {
                    this.fail(
                        left.binder.mode.plicity ===
                            other.binder.mode.plicity
                            ? 'BINDER_MODE_MISMATCH'
                            : 'PLICITY_MISMATCH',
                        nodeProvenance,
                        `Core ${left.tag} binder mode ` +
                        `${left.binder.mode.plicity}/` +
                        `${left.binder.mode.variation} does not match ` +
                        `${other.binder.mode.plicity}/` +
                        other.binder.mode.variation
                    );
                }
                this.constrain(
                    context,
                    left.binder.type,
                    other.binder.type,
                    nodeProvenance
                );
                const binderType = this.session.zonk(left.binder.type);
                const bodyContext = context.extend({
                    name: `comparison${context.depth}`,
                    type: binderType,
                    mode: left.binder.mode,
                    provenance: nodeProvenance
                });
                this.constrain(
                    bodyContext,
                    left.body,
                    other.body,
                    nodeProvenance
                );
                return;
            }
            default: {
                const exhaustive: never = left;
                return exhaustive;
            }
        }

        this.fail(
            'TYPE_MISMATCH',
            nodeProvenance,
            `Core type mismatch: ${expressionHead(left)} differs from ` +
            expressionHead(right)
        );
    }

    private inferMeta(
        context: CoreContext,
        meta: KernelMetaVariable
    ): MutableInferenceResult {
        const zonked = this.session.zonk(meta);
        if (zonked.tag !== 'meta') {
            return this.inferAt(context, zonked);
        }
        const entry = this.session.metavariable(zonked);
        return {
            term: zonked,
            type: this.session.zonk(
                kernelInstantiateSpine(entry.type, zonked.spine)
            )
        };
    }

    private requireType(
        context: CoreContext,
        expression: KernelExpression,
        role: string
    ): KernelExpression {
        const inferred = this.inferAt(context, expression);
        if (isCoreKind(inferred.type)) {
            this.fail(
                'EXPECTED_TYPE',
                expression.provenance,
                `${role} has checker sort KIND, not TYPE`
            );
        }
        this.constrain(
            context,
            inferred.type,
            kernelUniverse(derived(`${role} must inhabit TYPE`, expression.provenance)),
            expression.provenance
        );
        return inferred.term;
    }

    private inferPi(
        context: CoreContext,
        expression: Extract<KernelExpression, { tag: 'pi' }>
    ): MutableInferenceResult {
        const binderType = this.requireType(
            context,
            expression.binder.type,
            `Pi binder '${expression.binder.name}' type`
        );
        const bodyContext = context.extend({
            name: expression.binder.name,
            type: binderType,
            mode: expression.binder.mode,
            provenance: expression.binder.provenance
        });
        const body = this.inferAt(bodyContext, expression.body);
        const term = kernelPi(
            kernelBinder(
                expression.binder.name,
                binderType,
                expression.binder.mode,
                expression.binder.provenance
            ),
            body.term,
            expression.provenance
        );
        if (isCoreKind(body.type)) {
            return {
                term,
                type: coreKind(expression.provenance)
            };
        }
        this.constrain(
            bodyContext,
            body.type,
            kernelUniverse(derived(
                `Pi body '${expression.binder.name}' must inhabit TYPE`,
                expression.body.provenance
            )),
            expression.body.provenance
        );
        return {
            term,
            type: kernelUniverse(derived(
                'type of a term-level Pi',
                expression.provenance
            ))
        };
    }

    private inferOwnerAt(
        context: CoreContext,
        owner: CoreOwnerId,
        supplied: readonly KernelCallArgumentInput[],
        nodeProvenance: Provenance
    ): MutableInferenceResult {
        const schema = CORE_OWNER_SCHEMAS[owner];
        const checked: KernelArgument[] = [];
        let suppliedIndex = 0;

        for (let slotIndex = 0;
            slotIndex < schema.slots.length;
            slotIndex++
        ) {
            const slot = schema.slots[slotIndex];
            const next = supplied[suppliedIndex];
            const slotType = this.session.zonk(coreOwnerSlotType(
                owner,
                slotIndex,
                checked.map(argument => argument.value),
                next?.provenance ?? nodeProvenance
            ));

            if (
                slot.plicity === 'implicit' &&
                (!next || next.plicity === 'explicit')
            ) {
                const insertedProvenance = derived(
                    `inserted implicit ${owner}.${slot.name}`,
                    next?.provenance ?? nodeProvenance
                );
                checked.push({
                    plicity: 'implicit',
                    value: this.session.freshMeta(
                        context,
                        slotType,
                        insertedProvenance
                    ),
                    provenance: insertedProvenance
                });
                continue;
            }

            if (!next) {
                this.fail(
                    'MISSING_EXPLICIT_ARGUMENT',
                    nodeProvenance,
                    `Core owner ${owner} is missing explicit argument ` +
                    `'${slot.name}' at slot ${slotIndex}`
                );
            }
            if (next.plicity !== slot.plicity) {
                this.fail(
                    'PLICITY_MISMATCH',
                    next.provenance ?? next.value.provenance,
                    `Core owner ${owner} slot '${slot.name}' expects a ` +
                    `${slot.plicity} argument, received ${next.plicity}`
                );
            }

            const argument = this.checkAt(context, next.value, slotType);
            checked.push({
                plicity: slot.plicity,
                value: argument.term,
                provenance: next.provenance ?? next.value.provenance
            });
            suppliedIndex++;
        }

        if (suppliedIndex !== supplied.length) {
            const extra = supplied[suppliedIndex];
            this.fail(
                'TOO_MANY_ARGUMENTS',
                extra.provenance ?? extra.value.provenance,
                `Core owner ${owner} received ${supplied.length} supplied ` +
                `arguments but has ${schema.slots.length} slots`
            );
        }

        const term = kernelApplication(
            owner,
            checked.map(argument => ({
                value: argument.value,
                provenance: argument.provenance
            })),
            nodeProvenance
        );
        return {
            term,
            type: coreOwnerResultType(
                owner,
                checked.map(argument => argument.value),
                nodeProvenance
            )
        };
    }

    private insertGenericImplicit(
        context: CoreContext,
        pi: Extract<KernelExpression, { tag: 'pi' }>,
        nodeProvenance: Provenance
    ): {
        argument: KernelArgument;
        type: KernelExpression;
    } {
        const insertedProvenance = derived(
            `inserted implicit generic argument '${pi.binder.name}'`,
            nodeProvenance
        );
        const value = this.session.freshMeta(
            context,
            pi.binder.type,
            insertedProvenance
        );
        return {
            argument: {
                plicity: 'implicit',
                value,
                provenance: insertedProvenance
            },
            type: kernelInstantiate(pi.body, value)
        };
    }

    private inferCallAt(
        context: CoreContext,
        callee: KernelExpression,
        supplied: readonly KernelCallArgumentInput[],
        nodeProvenance: Provenance
    ): MutableInferenceResult {
        const inferredCallee = this.inferAt(context, callee);
        if (isCoreKind(inferredCallee.type)) {
            this.fail(
                'EXPECTED_FUNCTION',
                callee.provenance,
                'Cannot call a Core expression whose checker type is KIND'
            );
        }

        let currentType = this.session.zonk(inferredCallee.type);
        const checked: KernelArgument[] = [];

        for (const next of supplied) {
            while (
                currentType.tag === 'pi' &&
                currentType.binder.mode.plicity === 'implicit' &&
                next.plicity === 'explicit'
            ) {
                const inserted = this.insertGenericImplicit(
                    context,
                    currentType,
                    next.provenance ?? next.value.provenance
                );
                checked.push(inserted.argument);
                currentType = this.session.zonk(inserted.type);
            }

            if (currentType.tag !== 'pi') {
                this.fail(
                    'EXPECTED_FUNCTION',
                    next.provenance ?? next.value.provenance,
                    `Cannot apply ${expressionHead(inferredCallee.term)}: ` +
                    `${expressionHead(currentType)} is not a Pi type`
                );
            }
            if (currentType.binder.mode.plicity !== next.plicity) {
                this.fail(
                    'PLICITY_MISMATCH',
                    next.provenance ?? next.value.provenance,
                    `Generic call binder '${currentType.binder.name}' ` +
                    `expects ${currentType.binder.mode.plicity}, received ` +
                    next.plicity
                );
            }

            const argument = this.checkAt(
                context,
                next.value,
                currentType.binder.type
            );
            checked.push({
                plicity: next.plicity,
                value: argument.term,
                provenance: next.provenance ?? next.value.provenance
            });
            currentType = this.session.zonk(
                kernelInstantiate(currentType.body, argument.term)
            );
        }

        if (checked.length === 0) {
            this.fail(
                'EMPTY_GENERIC_CALL',
                nodeProvenance,
                'A Core generic call must supply or insert at least one argument'
            );
        }

        return {
            term: kernelCall(
                inferredCallee.term,
                checked.map(argument => ({
                    plicity: argument.plicity,
                    value: argument.value,
                    provenance: argument.provenance
                })),
                nodeProvenance
            ),
            type: currentType
        };
    }

    private inferAt(
        context: CoreContext,
        expression: KernelExpression
    ): MutableInferenceResult {
        switch (expression.tag) {
            case 'universe':
                return {
                    term: expression,
                    type: coreKind(expression.provenance)
                };
            case 'reference': {
                const declaration = context.lookupDeclaration(
                    expression.name,
                    expression.provenance
                );
                if (!declaration) {
                    this.fail(
                        'UNBOUND_FREE_REFERENCE',
                        expression.provenance,
                        `Unbound Core free declaration '${expression.name}'`
                    );
                }
                return {
                    term: expression,
                    type: declaration.type
                };
            }
            case 'bound': {
                const local = context.lookupIndex(
                    expression.index,
                    expression.provenance
                );
                if (!local) {
                    this.fail(
                        'DANGLING_BOUND_VARIABLE',
                        expression.provenance,
                        `Core bound index ${expression.index} is not in a ` +
                        `context of depth ${context.depth}`
                    );
                }
                return {
                    term: expression,
                    type: local.type
                };
            }
            case 'meta':
                return this.inferMeta(context, expression);
            case 'application':
                return this.inferOwnerAt(
                    context,
                    expression.owner,
                    expression.arguments.map(argument => ({
                        plicity: argument.plicity,
                        value: argument.value,
                        provenance: argument.provenance
                    })),
                    expression.provenance
                );
            case 'call':
                return this.inferCallAt(
                    context,
                    expression.callee,
                    expression.arguments.map(argument => ({
                        plicity: argument.plicity,
                        value: argument.value,
                        provenance: argument.provenance
                    })),
                    expression.provenance
                );
            case 'pi':
                return this.inferPi(context, expression);
            case 'lambda':
                this.fail(
                    'CANNOT_INFER_LAMBDA',
                    expression.provenance,
                    'Bidirectional Core checking requires an expected Pi type ' +
                    'for a lambda'
                );
            default: {
                const exhaustive: never = expression;
                return exhaustive;
            }
        }
    }

    private checkLambdaAt(
        context: CoreContext,
        expression: Extract<KernelExpression, { tag: 'lambda' }>,
        expected: Extract<KernelExpression, { tag: 'pi' }>
    ): MutableCheckResult {
        if (expression.binder.mode.plicity !== expected.binder.mode.plicity) {
            this.fail(
                'PLICITY_MISMATCH',
                expression.binder.provenance,
                `Lambda binder '${expression.binder.name}' is ` +
                `${expression.binder.mode.plicity}, expected ` +
                expected.binder.mode.plicity
            );
        }
        if (
            expression.binder.mode.variation !==
            expected.binder.mode.variation
        ) {
            this.fail(
                'BINDER_MODE_MISMATCH',
                expression.binder.provenance,
                `Lambda binder '${expression.binder.name}' has variation ` +
                `${expression.binder.mode.variation}, expected ` +
                expected.binder.mode.variation
            );
        }

        const annotatedType = this.requireType(
            context,
            expression.binder.type,
            `Lambda binder '${expression.binder.name}' annotation`
        );
        this.constrain(
            context,
            annotatedType,
            expected.binder.type,
            expression.binder.provenance
        );
        const binderType = this.session.zonk(expected.binder.type);
        const bodyContext = context.extend({
            name: expression.binder.name,
            type: binderType,
            mode: expected.binder.mode,
            provenance: expression.binder.provenance
        });
        const body = this.checkAt(
            bodyContext,
            expression.body,
            expected.body
        );
        return {
            term: kernelLambda(
                kernelBinder(
                    expression.binder.name,
                    binderType,
                    expected.binder.mode,
                    expression.binder.provenance
                ),
                body.term,
                expression.provenance
            ),
            type: expected
        };
    }

    private checkAt(
        context: CoreContext,
        expression: KernelExpression,
        expectedInput: KernelExpression
    ): MutableCheckResult {
        const expected = this.session.zonk(expectedInput);
        if (expression.tag === 'lambda') {
            if (expected.tag !== 'pi') {
                this.fail(
                    'TYPE_MISMATCH',
                    expression.provenance,
                    `Cannot check a lambda against ` +
                    expressionHead(expected)
                );
            }
            return this.checkLambdaAt(context, expression, expected);
        }

        const inferred = this.inferAt(context, expression);
        if (isCoreKind(inferred.type)) {
            this.fail(
                'TYPE_MISMATCH',
                expression.provenance,
                `${expressionHead(inferred.term)} has checker sort KIND and ` +
                `cannot inhabit ${expressionHead(expected)}`
            );
        }
        this.constrain(
            context,
            inferred.type,
            expected,
            expression.provenance
        );
        return {
            term: inferred.term,
            type: expected
        };
    }

    private finishConstraints(): void {
        const report = this.session.solveConstraints();
        if (report.outcome === 'rejected') {
            const rejected = report.constraints.find(
                constraint => constraint.outcome === 'rejected'
            )!;
            this.fail(
                'CONSTRAINT_REJECTED',
                rejected.error?.provenance ?? rejected.provenance,
                `Core type constraint ${rejected.id} was rejected: ` +
                `${rejected.reason}`,
                rejected,
                rejected.error
            );
        }
        if (report.outcome === 'stuck') {
            const stuck = report.constraints.find(
                constraint => constraint.outcome === 'stuck'
            )!;
            this.fail(
                'UNRESOLVED_CONSTRAINTS',
                stuck.provenance,
                `Core type constraint ${stuck.id} remains unresolved: ` +
                stuck.reason,
                stuck
            );
        }
    }

    private assertNoMeta(
        expression: KernelExpression,
        role: string
    ): void {
        const meta = firstUnsolvedMeta(expression);
        if (!meta) return;
        this.fail(
            'UNRESOLVED_METAVARIABLE',
            meta.provenance,
            `${role} contains unresolved metavariable ` +
            `?m${meta.identity.index}`
        );
    }

    private finishInference(
        context: CoreContext,
        result: MutableInferenceResult
    ): CoreInferenceResult {
        this.finishConstraints();
        const term = this.session.zonk(result.term);
        const type = this.zonkType(result.type);
        this.assertNoMeta(term, 'Checked Core term');
        if (!isCoreKind(type)) {
            this.assertNoMeta(type, 'Inferred Core type');
            context.assertScoped(type);
        }
        context.assertScoped(term);
        return Object.freeze({ term, type });
    }

    private finishCheck(
        context: CoreContext,
        result: MutableCheckResult
    ): CoreCheckResult {
        this.finishConstraints();
        const term = this.session.zonk(result.term);
        const type = this.session.zonk(result.type);
        this.assertNoMeta(term, 'Checked Core term');
        this.assertNoMeta(type, 'Checked Core type');
        context.assertScoped(term);
        context.assertScoped(type);
        return Object.freeze({ term, type });
    }

    infer(
        context: CoreContext,
        expression: KernelExpression
    ): CoreInferenceResult {
        this.assertContext(context, expression.provenance);
        context.assertScoped(expression);
        return this.finishInference(
            context,
            this.inferAt(context, expression)
        );
    }

    check(
        context: CoreContext,
        expression: KernelExpression,
        expected: KernelExpression
    ): CoreCheckResult {
        this.assertContext(context, expression.provenance);
        context.assertScoped(expression);
        context.assertScoped(expected);
        return this.finishCheck(
            context,
            this.checkAt(context, expression, expected)
        );
    }

    /**
     * Check a refinement that may contain session-owned unsolved subgoals.
     *
     * Constraints must still close or reject deterministically. Unlike the
     * ordinary public `check` boundary, this result may retain metas in the
     * checked term or type so a proof refiner can make them reachable before
     * returning control to the caller.
     */
    checkRefinement(
        context: CoreContext,
        expression: KernelExpression,
        expected: KernelExpression
    ): CoreCheckResult {
        this.assertContext(context, expression.provenance);
        context.assertScoped(expression);
        context.assertScoped(expected);
        const result = this.checkAt(context, expression, expected);
        this.finishConstraints();
        const term = this.session.zonk(result.term);
        const type = this.session.zonk(result.type);
        context.assertScoped(term);
        context.assertScoped(type);
        return Object.freeze({ term, type });
    }

    inferOwnerApplication(
        context: CoreContext,
        owner: CoreOwnerId,
        supplied: readonly KernelCallArgumentInput[],
        nodeProvenance: Provenance
    ): CoreInferenceResult {
        this.assertContext(context, nodeProvenance);
        supplied.forEach(argument => context.assertScoped(argument.value));
        return this.finishInference(
            context,
            this.inferOwnerAt(
                context,
                owner,
                supplied,
                nodeProvenance
            )
        );
    }

    inferGenericCall(
        context: CoreContext,
        callee: KernelExpression,
        supplied: readonly KernelCallArgumentInput[],
        nodeProvenance: Provenance
    ): CoreInferenceResult {
        this.assertContext(context, nodeProvenance);
        context.assertScoped(callee);
        supplied.forEach(argument => context.assertScoped(argument.value));
        return this.finishInference(
            context,
            this.inferCallAt(
                context,
                callee,
                supplied,
                nodeProvenance
            )
        );
    }

    /**
     * Check that every declaration type is a valid TYPE- or KIND-level
     * expression. Scope/ordering was already enforced by environment
     * construction.
     */
    validateEnvironment(
        environment: CoreDeclarationEnvironment = this.session.environment
    ): void {
        if (environment !== this.session.environment) {
            const fallback = environment.declarations[0]?.provenance ??
                provenance('derived', 'foreign declaration environment');
            this.fail(
                'FOREIGN_CONTEXT',
                fallback,
                'Core checker cannot validate a foreign declaration environment'
            );
        }
        const inferredDeclarations: {
            declarationName: string;
            provenance: Provenance;
            result: MutableInferenceResult;
        }[] = [];
        for (const declaration of environment.declarations) {
            const inferred = this.inferAt(
                this.rootContext,
                declaration.type
            );
            inferredDeclarations.push({
                declarationName: declaration.name,
                provenance: declaration.provenance,
                result: inferred
            });
            if (!isCoreKind(inferred.type)) {
                try {
                    this.constrain(
                        this.rootContext,
                        inferred.type,
                        kernelUniverse(derived(
                            `declaration '${declaration.name}' type`,
                            declaration.provenance
                        )),
                        declaration.provenance
                    );
                } catch (error: unknown) {
                    if (!(error instanceof CoreCheckerError)) throw error;
                    this.fail(
                        'INVALID_DECLARATION_TYPE',
                        declaration.provenance,
                        `Type of Core declaration '${declaration.name}' is ` +
                        `not a TYPE- or KIND-level expression: ` +
                        error.message
                    );
                }
            }
        }
        this.finishConstraints();
        for (const item of inferredDeclarations) {
            const term = this.session.zonk(item.result.term);
            const type = this.zonkType(item.result.type);
            const meta = firstUnsolvedMeta(term) ??
                (isCoreKind(type)
                    ? undefined
                    : firstUnsolvedMeta(type));
            if (meta) {
                this.fail(
                    'INVALID_DECLARATION_TYPE',
                    meta.provenance,
                    `Type of Core declaration '${item.declarationName}' ` +
                    `leaves metavariable ?m${meta.identity.index} unresolved`
                );
            }
            this.rootContext.assertScoped(term);
            if (!isCoreKind(type)) {
                this.rootContext.assertScoped(type);
            }
        }
    }
}
