/**
 * Session-local metavariables and ordered constraints for emdash Core.
 *
 * This is elaboration state, not the trusted checker. It deliberately solves
 * direct canonical flex-rigid equations and the Miller-pattern fragment over
 * distinct contextual variables. The bounded Core checker owns structural
 * decomposition and implicit insertion; conversion and non-pattern
 * higher-order solving remain outside this session.
 */

import {
    CoreContext,
    CoreContextError,
    CoreDeclarationEnvironment
} from './context';
import {
    KernelExpression,
    KernelMetaIdentity,
    KernelMetaVariable,
    Provenance,
    formatSourceSpan,
    kernelBound,
    kernelExpressionEquals,
    kernelInstantiateSpine,
    kernelMeta,
    provenance
} from './kernel';
import {
    CorePatternStuckReason,
    invertCoreMetaPattern
} from './pattern';

export type CoreSessionErrorCode =
    | 'FOREIGN_CONTEXT'
    | 'FOREIGN_METAVARIABLE'
    | 'UNKNOWN_METAVARIABLE'
    | 'INVALID_METAVARIABLE_SPINE'
    | 'INVALID_META_TYPE_SCOPE'
    | 'NONCANONICAL_META_OCCURRENCE'
    | 'META_OCCURS_CHECK'
    | 'PATTERN_SCOPE_ESCAPE'
    | 'INVALID_META_SOLUTION_SCOPE'
    | 'METAVARIABLE_ALREADY_SOLVED'
    | 'CYCLIC_META_SOLUTION'
    | 'UNKNOWN_CONSTRAINT'
    | 'INVALID_CONSTRAINT_SCOPE';

export class CoreSessionError extends Error {
    constructor(
        public readonly code: CoreSessionErrorCode,
        public readonly provenance: Provenance,
        message: string,
        public readonly contextError?: CoreContextError
    ) {
        const location = provenance.span
            ? ` at ${formatSourceSpan(provenance.span)}`
            : '';
        super(`${message}${location}`);
        this.name = 'CoreSessionError';
    }
}

interface MutableMetaEntry {
    readonly identity: KernelMetaIdentity;
    readonly type: KernelExpression;
    readonly creationDepth: number;
    readonly provenance: Provenance;
    readonly context: CoreContext;
    solution?: KernelExpression;
}

export interface CoreMetaEntry {
    readonly identity: KernelMetaIdentity;
    readonly type: KernelExpression;
    readonly creationDepth: number;
    readonly provenance: Provenance;
    readonly solution?: KernelExpression;
}

export type CoreMetaSolveResult = 'solved' | 'already-solved';

export type CoreConstraintOutcome =
    | 'pending'
    | 'solved'
    | 'stuck'
    | 'rejected';

export type CoreConstraintReason =
    | 'STRUCTURAL_EQUALITY'
    | 'ASSIGNED_LEFT_META'
    | 'ASSIGNED_RIGHT_META'
    | 'ASSIGNED_LEFT_PATTERN_META'
    | 'ASSIGNED_RIGHT_PATTERN_META'
    | 'AMBIGUOUS_FLEX_FLEX'
    | 'NONCANONICAL_META_OCCURRENCE'
    | 'REQUIRES_DECOMPOSITION_OR_CONVERSION'
    | CorePatternStuckReason
    | CoreSessionErrorCode;

interface CorePatternAssignment {
    readonly outcome: 'assigned';
}

interface CorePatternAssignmentStuck {
    readonly outcome: 'stuck';
    readonly reason:
        | CorePatternStuckReason
        | 'NONCANONICAL_META_OCCURRENCE';
}

type CorePatternAssignmentResult =
    | CorePatternAssignment
    | CorePatternAssignmentStuck;

interface MutableConstraintEntry {
    readonly id: number;
    readonly context: CoreContext;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
    readonly provenance: Provenance;
    outcome: CoreConstraintOutcome;
    reason?: CoreConstraintReason;
    error?: CoreSessionError;
}

export interface CoreConstraint {
    readonly id: number;
    readonly contextDepth: number;
    readonly left: KernelExpression;
    readonly right: KernelExpression;
    readonly provenance: Provenance;
    readonly outcome: CoreConstraintOutcome;
    readonly reason?: CoreConstraintReason;
    readonly error?: CoreSessionError;
}

export interface CoreConstraintStep {
    readonly id: number;
    readonly outcome: Exclude<CoreConstraintOutcome, 'pending'>;
    readonly reason: CoreConstraintReason;
    readonly error?: CoreSessionError;
}

export interface CoreConstraintReport {
    readonly outcome: 'solved' | 'stuck' | 'rejected';
    readonly constraints: readonly CoreConstraint[];
    /**
     * Constraint ids in the deterministic order in which they became solved.
     */
    readonly resolutionOrder: readonly number[];
}

const frozenMetaEntry = (entry: MutableMetaEntry): CoreMetaEntry =>
    Object.freeze({
        identity: entry.identity,
        type: entry.type,
        creationDepth: entry.creationDepth,
        provenance: entry.provenance,
        solution: entry.solution
    });

const frozenConstraint = (
    entry: MutableConstraintEntry
): CoreConstraint => Object.freeze({
    id: entry.id,
    contextDepth: entry.context.depth,
    left: entry.left,
    right: entry.right,
    provenance: entry.provenance,
    outcome: entry.outcome,
    reason: entry.reason,
    error: entry.error
});

/**
 * Mutable solving state with no process-global counters or registries.
 */
export class CoreElaborationSession {
    private readonly sessionIdentity = Symbol('emdash Core meta session');
    private readonly metaEntries = new Map<number, MutableMetaEntry>();
    private readonly constraintEntries: MutableConstraintEntry[] = [];
    private nextMetaIndex = 0;
    private nextConstraintId = 0;

    public readonly rootContext: CoreContext;

    constructor(
        public readonly environment = CoreDeclarationEnvironment.empty()
    ) {
        this.rootContext = CoreContext.empty(environment);
    }

    private failFromContext(
        code: 'INVALID_META_TYPE_SCOPE' |
            'INVALID_META_SOLUTION_SCOPE' |
            'INVALID_CONSTRAINT_SCOPE',
        error: CoreContextError,
        role: string
    ): never {
        throw new CoreSessionError(
            code,
            error.provenance,
            `${role}: ${error.message}`,
            error
        );
    }

    private assertContext(
        context: CoreContext,
        nodeProvenance: Provenance
    ): void {
        if (context.environment === this.environment) return;
        throw new CoreSessionError(
            'FOREIGN_CONTEXT',
            nodeProvenance,
            'Core context belongs to a different declaration environment'
        );
    }

    private entryForIdentity(
        identity: KernelMetaIdentity,
        nodeProvenance: Provenance
    ): MutableMetaEntry {
        if (identity.session !== this.sessionIdentity) {
            throw new CoreSessionError(
                'FOREIGN_METAVARIABLE',
                nodeProvenance,
                `Metavariable ?m${identity.index} belongs to another session`
            );
        }
        const entry = this.metaEntries.get(identity.index);
        if (!entry) {
            throw new CoreSessionError(
                'UNKNOWN_METAVARIABLE',
                nodeProvenance,
                `Metavariable ?m${identity.index} is not registered in ` +
                'this session'
            );
        }
        return entry;
    }

    private entryForMeta(meta: KernelMetaVariable): MutableMetaEntry {
        const entry = this.entryForIdentity(
            meta.identity,
            meta.provenance
        );
        if (meta.spine.length !== entry.creationDepth) {
            throw new CoreSessionError(
                'INVALID_METAVARIABLE_SPINE',
                meta.provenance,
                `Metavariable ?m${meta.identity.index} expects a contextual ` +
                `spine of length ${entry.creationDepth}, received ` +
                `${meta.spine.length}`
            );
        }
        return entry;
    }

    private visitMetas(
        expression: KernelExpression,
        visit: (meta: KernelMetaVariable) => void
    ): void {
        switch (expression.tag) {
            case 'universe':
            case 'reference':
            case 'bound':
                return;
            case 'meta':
                visit(expression);
                expression.spine.forEach(item =>
                    this.visitMetas(item, visit)
                );
                return;
            case 'application':
                expression.arguments.forEach(argument =>
                    this.visitMetas(argument.value, visit)
                );
                return;
            case 'call':
                this.visitMetas(expression.callee, visit);
                expression.arguments.forEach(argument =>
                    this.visitMetas(argument.value, visit)
                );
                return;
            case 'pi':
            case 'lambda':
                this.visitMetas(expression.binder.type, visit);
                this.visitMetas(expression.body, visit);
                return;
            default: {
                const exhaustive: never = expression;
                return exhaustive;
            }
        }
    }

    private assertOwnedMetas(expression: KernelExpression): void {
        this.visitMetas(expression, meta => {
            this.entryForMeta(meta);
        });
    }

    private validateAtContext(
        context: CoreContext,
        expression: KernelExpression,
        code: 'INVALID_META_TYPE_SCOPE' |
            'INVALID_META_SOLUTION_SCOPE' |
            'INVALID_CONSTRAINT_SCOPE',
        role: string
    ): void {
        try {
            context.assertScoped(expression);
        } catch (error: unknown) {
            if (!(error instanceof CoreContextError)) throw error;
            this.failFromContext(code, error, role);
        }
        this.assertOwnedMetas(expression);
    }

    freshMeta(
        context: CoreContext,
        type: KernelExpression,
        nodeProvenance: Provenance
    ): KernelMetaVariable {
        this.assertContext(context, nodeProvenance);
        this.validateAtContext(
            context,
            type,
            'INVALID_META_TYPE_SCOPE',
            'Invalid Core metavariable type'
        );

        const identity: KernelMetaIdentity = Object.freeze({
            session: this.sessionIdentity,
            index: this.nextMetaIndex++
        });
        const entry: MutableMetaEntry = {
            identity,
            type,
            creationDepth: context.depth,
            provenance: nodeProvenance,
            context
        };
        this.metaEntries.set(identity.index, entry);

        const identitySpine = Array.from(
            { length: context.depth },
            (_, index) => kernelBound(index, nodeProvenance)
        );
        return kernelMeta(identity, identitySpine, nodeProvenance);
    }

    get metavariables(): readonly CoreMetaEntry[] {
        return Object.freeze(
            [...this.metaEntries.values()].map(frozenMetaEntry)
        );
    }

    metavariable(meta: KernelMetaVariable): CoreMetaEntry {
        return frozenMetaEntry(this.entryForMeta(meta));
    }

    private isCanonicalOccurrence(
        meta: KernelMetaVariable,
        entry: MutableMetaEntry
    ): boolean {
        return meta.spine.length === entry.creationDepth &&
            meta.spine.every((item, index) =>
                item.tag === 'bound' && item.index === index
            );
    }

    private contextExtends(
        context: CoreContext,
        ancestor: CoreContext
    ): boolean {
        return context.environment === ancestor.environment &&
            context.depth >= ancestor.depth &&
            ancestor.telescope.every(
                (binding, index) => context.telescope[index] === binding
            );
    }

    private solvePatternOccurrence(
        context: CoreContext,
        meta: KernelMetaVariable,
        rigid: KernelExpression
    ): CorePatternAssignmentResult {
        const entry = this.entryForMeta(meta);
        if (!this.contextExtends(context, entry.context)) {
            return Object.freeze({
                outcome: 'stuck',
                reason: 'NONCANONICAL_META_OCCURRENCE'
            });
        }

        const inversion = invertCoreMetaPattern(
            meta,
            entry.creationDepth,
            context.depth,
            rigid
        );
        if (inversion.outcome === 'stuck') {
            return Object.freeze({
                outcome: 'stuck',
                reason: inversion.reason
            });
        }
        if (inversion.outcome === 'scope-escape') {
            throw new CoreSessionError(
                'PATTERN_SCOPE_ESCAPE',
                inversion.error.provenance,
                `Rigid side of pattern ?m${meta.identity.index} depends on ` +
                'a local variable absent from its distinct-variable spine'
            );
        }

        const canonical = kernelMeta(
            entry.identity,
            Array.from(
                { length: entry.creationDepth },
                (_, index) => kernelBound(index, meta.provenance)
            ),
            meta.provenance
        );
        this.solve(canonical, inversion.solution);
        return Object.freeze({ outcome: 'assigned' });
    }

    private containsMeta(
        expression: KernelExpression,
        targetIndex: number,
        followedSolutions = new Set<number>()
    ): boolean {
        switch (expression.tag) {
            case 'universe':
            case 'reference':
            case 'bound':
                return false;
            case 'meta': {
                const entry = this.entryForMeta(expression);
                if (entry.identity.index === targetIndex) return true;
                if (expression.spine.some(item =>
                    this.containsMeta(
                        item,
                        targetIndex,
                        followedSolutions
                    )
                )) {
                    return true;
                }
                if (
                    !entry.solution ||
                    followedSolutions.has(entry.identity.index)
                ) {
                    return false;
                }
                followedSolutions.add(entry.identity.index);
                const occurs = this.containsMeta(
                    entry.solution,
                    targetIndex,
                    followedSolutions
                );
                followedSolutions.delete(entry.identity.index);
                return occurs;
            }
            case 'application':
                return expression.arguments.some(argument =>
                    this.containsMeta(
                        argument.value,
                        targetIndex,
                        followedSolutions
                    )
                );
            case 'call':
                return this.containsMeta(
                    expression.callee,
                    targetIndex,
                    followedSolutions
                ) || expression.arguments.some(argument =>
                    this.containsMeta(
                        argument.value,
                        targetIndex,
                        followedSolutions
                    )
                );
            case 'pi':
            case 'lambda':
                return this.containsMeta(
                    expression.binder.type,
                    targetIndex,
                    followedSolutions
                ) || this.containsMeta(
                    expression.body,
                    targetIndex,
                    followedSolutions
                );
            default: {
                const exhaustive: never = expression;
                return exhaustive;
            }
        }
    }

    private zonkAt(
        expression: KernelExpression,
        resolving: Set<number>
    ): KernelExpression {
        switch (expression.tag) {
            case 'universe':
            case 'reference':
            case 'bound':
                return expression;
            case 'meta': {
                const entry = this.entryForMeta(expression);
                const spine = expression.spine.map(item =>
                    this.zonkAt(item, resolving)
                );
                if (!entry.solution) {
                    return kernelMeta(
                        expression.identity,
                        spine,
                        expression.provenance
                    );
                }
                if (resolving.has(entry.identity.index)) {
                    throw new CoreSessionError(
                        'CYCLIC_META_SOLUTION',
                        expression.provenance,
                        `Cycle detected while zonking metavariable ` +
                        `?m${entry.identity.index}`
                    );
                }
                resolving.add(entry.identity.index);
                const instantiated = kernelInstantiateSpine(
                    entry.solution,
                    spine
                );
                const result = this.zonkAt(instantiated, resolving);
                resolving.delete(entry.identity.index);
                return result;
            }
            case 'application':
                return {
                    ...expression,
                    arguments: expression.arguments.map(argument => ({
                        ...argument,
                        value: this.zonkAt(argument.value, resolving)
                    }))
                };
            case 'call':
                return {
                    ...expression,
                    callee: this.zonkAt(expression.callee, resolving),
                    arguments: expression.arguments.map(argument => ({
                        ...argument,
                        value: this.zonkAt(argument.value, resolving)
                    }))
                };
            case 'pi':
            case 'lambda':
                return {
                    ...expression,
                    binder: {
                        ...expression.binder,
                        type: this.zonkAt(
                            expression.binder.type,
                            resolving
                        )
                    },
                    body: this.zonkAt(expression.body, resolving)
                };
            default: {
                const exhaustive: never = expression;
                return exhaustive;
            }
        }
    }

    zonk(expression: KernelExpression): KernelExpression {
        this.assertOwnedMetas(expression);
        return this.zonkAt(expression, new Set());
    }

    solve(
        meta: KernelMetaVariable,
        solution: KernelExpression
    ): CoreMetaSolveResult {
        const entry = this.entryForMeta(meta);
        if (!this.isCanonicalOccurrence(meta, entry)) {
            throw new CoreSessionError(
                'NONCANONICAL_META_OCCURRENCE',
                meta.provenance,
                `Direct solving requires the identity occurrence of ` +
                `?m${meta.identity.index}`
            );
        }

        this.validateAtContext(
            entry.context,
            solution,
            'INVALID_META_SOLUTION_SCOPE',
            `Invalid solution for ?m${meta.identity.index}`
        );
        if (this.containsMeta(solution, entry.identity.index)) {
            throw new CoreSessionError(
                'META_OCCURS_CHECK',
                solution.provenance,
                `Metavariable ?m${meta.identity.index} occurs in its ` +
                'proposed solution'
            );
        }

        const zonkedSolution = this.zonk(solution);
        this.validateAtContext(
            entry.context,
            zonkedSolution,
            'INVALID_META_SOLUTION_SCOPE',
            `Invalid zonked solution for ?m${meta.identity.index}`
        );

        if (entry.solution) {
            const previous = this.zonk(entry.solution);
            if (kernelExpressionEquals(previous, zonkedSolution)) {
                return 'already-solved';
            }
            throw new CoreSessionError(
                'METAVARIABLE_ALREADY_SOLVED',
                meta.provenance,
                `Metavariable ?m${meta.identity.index} already has a ` +
                'different solution'
            );
        }

        entry.solution = zonkedSolution;
        return 'solved';
    }

    addConstraint(
        context: CoreContext,
        left: KernelExpression,
        right: KernelExpression,
        nodeProvenance: Provenance
    ): CoreConstraint {
        this.assertContext(context, nodeProvenance);
        this.validateAtContext(
            context,
            left,
            'INVALID_CONSTRAINT_SCOPE',
            'Invalid left constraint term'
        );
        this.validateAtContext(
            context,
            right,
            'INVALID_CONSTRAINT_SCOPE',
            'Invalid right constraint term'
        );

        const entry: MutableConstraintEntry = {
            id: this.nextConstraintId++,
            context,
            left,
            right,
            provenance: nodeProvenance,
            outcome: 'pending'
        };
        this.constraintEntries.push(entry);
        return frozenConstraint(entry);
    }

    get constraints(): readonly CoreConstraint[] {
        return Object.freeze(this.constraintEntries.map(frozenConstraint));
    }

    private constraintEntry(
        id: number,
        nodeProvenance?: Provenance
    ): MutableConstraintEntry {
        const entry = this.constraintEntries.find(item => item.id === id);
        if (entry) return entry;
        const fallback = nodeProvenance ??
            this.constraintEntries[0]?.provenance ??
            this.metaEntries.values().next().value?.provenance ??
            provenance(
                'derived',
                `unknown Core constraint ${id}`
            );
        throw new CoreSessionError(
            'UNKNOWN_CONSTRAINT',
            fallback,
            `Unknown Core constraint ${id}`
        );
    }

    private stuck(
        entry: MutableConstraintEntry,
        reason: CoreConstraintReason
    ): CoreConstraintStep {
        entry.outcome = 'stuck';
        entry.reason = reason;
        entry.error = undefined;
        return Object.freeze({
            id: entry.id,
            outcome: 'stuck',
            reason
        });
    }

    private solved(
        entry: MutableConstraintEntry,
        reason: CoreConstraintReason
    ): CoreConstraintStep {
        entry.outcome = 'solved';
        entry.reason = reason;
        entry.error = undefined;
        return Object.freeze({
            id: entry.id,
            outcome: 'solved',
            reason
        });
    }

    private rejected(
        entry: MutableConstraintEntry,
        error: CoreSessionError
    ): CoreConstraintStep {
        entry.outcome = 'rejected';
        entry.reason = error.code;
        entry.error = error;
        return Object.freeze({
            id: entry.id,
            outcome: 'rejected',
            reason: error.code,
            error
        });
    }

    stepConstraint(id: number): CoreConstraintStep {
        const entry = this.constraintEntry(id);
        if (entry.outcome === 'solved' || entry.outcome === 'rejected') {
            return Object.freeze({
                id,
                outcome: entry.outcome,
                reason: entry.reason!,
                error: entry.error
            });
        }

        try {
            const left = this.zonk(entry.left);
            const right = this.zonk(entry.right);
            if (kernelExpressionEquals(left, right)) {
                return this.solved(entry, 'STRUCTURAL_EQUALITY');
            }

            if (left.tag === 'meta' && right.tag === 'meta') {
                return this.stuck(entry, 'AMBIGUOUS_FLEX_FLEX');
            }

            if (left.tag === 'meta') {
                const metaEntry = this.entryForMeta(left);
                if (
                    entry.context === metaEntry.context &&
                    this.isCanonicalOccurrence(left, metaEntry)
                ) {
                    this.solve(left, right);
                    return this.solved(entry, 'ASSIGNED_LEFT_META');
                }

                const assignment = this.solvePatternOccurrence(
                    entry.context,
                    left,
                    right
                );
                return assignment.outcome === 'stuck'
                    ? this.stuck(entry, assignment.reason)
                    : this.solved(entry, 'ASSIGNED_LEFT_PATTERN_META');
            }

            if (right.tag === 'meta') {
                const metaEntry = this.entryForMeta(right);
                if (
                    entry.context === metaEntry.context &&
                    this.isCanonicalOccurrence(right, metaEntry)
                ) {
                    this.solve(right, left);
                    return this.solved(entry, 'ASSIGNED_RIGHT_META');
                }

                const assignment = this.solvePatternOccurrence(
                    entry.context,
                    right,
                    left
                );
                return assignment.outcome === 'stuck'
                    ? this.stuck(entry, assignment.reason)
                    : this.solved(entry, 'ASSIGNED_RIGHT_PATTERN_META');
            }

            return this.stuck(
                entry,
                'REQUIRES_DECOMPOSITION_OR_CONVERSION'
            );
        } catch (error: unknown) {
            if (!(error instanceof CoreSessionError)) throw error;
            return this.rejected(entry, error);
        }
    }

    solveConstraints(): CoreConstraintReport {
        const resolutionOrder: number[] = [];
        let madeProgress: boolean;

        do {
            madeProgress = false;
            for (const entry of this.constraintEntries) {
                if (
                    entry.outcome === 'solved' ||
                    entry.outcome === 'rejected'
                ) {
                    continue;
                }
                const step = this.stepConstraint(entry.id);
                if (step.outcome === 'solved') {
                    madeProgress = true;
                    resolutionOrder.push(entry.id);
                }
            }
        } while (madeProgress);

        const constraints = this.constraints;
        const outcome = constraints.some(
            constraint => constraint.outcome === 'rejected'
        )
            ? 'rejected'
            : constraints.every(
                constraint => constraint.outcome === 'solved'
            )
                ? 'solved'
                : 'stuck';
        return Object.freeze({
            outcome,
            constraints,
            resolutionOrder: Object.freeze(resolutionOrder)
        });
    }
}
