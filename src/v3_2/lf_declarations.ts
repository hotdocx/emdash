/**
 * Immutable checked declarations and bounded delta for the candidate λΠ LF.
 *
 * Definitions are layered over the existing declaration/checker environment
 * instead of changing the frozen MVP declaration representation. A body is
 * checked in the preceding environment, so every free dependency has a
 * strictly smaller declaration ordinal. Transparent equations for intrinsic
 * owners additionally pass an explicit dependency-graph cycle check because
 * transfer slices may discover a source-prior owner equation after already
 * checked declarations that mentioned the then-opaque owner.
 */

import {
    CoreBindingInput,
    CoreContextError,
    CoreDeclarationEnvironment
} from './context';
import {
    CoreChecker
} from './checker';
import {
    KernelArgument,
    KernelExpression,
    KernelReference,
    Provenance,
    kernelCall,
    provenance
} from './kernel';
import {
    CoreLfEvaluationError
} from './lf';
import {
    CoreOwnerId
} from './schema';
import {
    CoreElaborationSession
} from './session';
import {
    coreOwnerSignatureType
} from './signature';

export type CoreLfTransparency = 'opaque' | 'transparent';

export interface CoreLfDeclarationInput extends CoreBindingInput {
    readonly body?: KernelExpression;
    /**
     * Omitting transparency is the conservative `opaque` default.
     * Unfolding therefore always requires an explicit `transparent` request.
     */
    readonly transparency?: CoreLfTransparency;
}

export interface CoreLfDeclaration extends CoreBindingInput {
    readonly reference: KernelReference;
    readonly body?: KernelExpression;
    readonly transparency: CoreLfTransparency;
    readonly ordinal: number;
    /**
     * Distinct free names in first-occurrence order across the checked body.
     */
    readonly bodyDependencies: readonly string[];
    /**
     * Distinct semantic owners in first-occurrence order across the body.
     *
     * These are recorded even while an owner remains opaque. If that owner is
     * later given a transparent intrinsic definition, the completed
     * transparent dependency graph is checked for cycles.
     */
    readonly bodyOwnerDependencies: readonly CoreOwnerId[];
}

export interface CoreLfIntrinsicDefinitionInput {
    readonly owner: CoreOwnerId;
    readonly body: KernelExpression;
    readonly provenance: Provenance;
    /**
     * Stable source-facing name used only in delta traces and diagnostics.
     */
    readonly declarationName?: string;
}

/**
 * A checked transparent equation for an existing semantic Core owner.
 *
 * The owner keeps its backend-neutral identity and built-in signature. This
 * parallel entry supplies only the candidate LF delta body; it never shadows
 * the owner with a free declaration.
 */
export interface CoreLfIntrinsicDefinition {
    readonly owner: CoreOwnerId;
    readonly declarationName: string;
    readonly type: KernelExpression;
    readonly body: KernelExpression;
    readonly transparency: 'transparent';
    readonly provenance: Provenance;
    readonly ordinal: number;
    readonly bodyDependencies: readonly string[];
    readonly ownerDependencies: readonly CoreOwnerId[];
}

/**
 * Candidate declaration validation may opt into a reviewed checker while the
 * default remains the frozen Core checker. The factory is supplied an exact
 * persistent declaration environment and the earlier LF delta environment
 * for each validation phase.
 */
export interface CoreLfDeclarationCheckerContext {
    readonly phase: 'declaration-type' | 'definition-body';
    readonly lfEnvironment: CoreLfDeclarationEnvironment;
}

export type CoreLfDeclarationCheckerFactory = (
    environment: CoreDeclarationEnvironment,
    context: CoreLfDeclarationCheckerContext
) => CoreChecker;

const defaultCoreLfDeclarationCheckerFactory:
CoreLfDeclarationCheckerFactory =
    environment => new CoreChecker(
        new CoreElaborationSession(environment)
    );

export type CoreLfDeclarationErrorCode =
    | 'INVALID_DECLARATION'
    | 'DUPLICATE_DECLARATION'
    | 'INVALID_TRANSPARENCY'
    | 'TRANSPARENT_ASSUMPTION'
    | 'INVALID_DECLARATION_TYPE'
    | 'SELF_REFERENCE'
    | 'UNBOUND_BODY_REFERENCE'
    | 'DUPLICATE_INTRINSIC_DEFINITION'
    | 'CYCLIC_INTRINSIC_DEFINITION'
    | 'INVALID_DEFINITION_BODY';

export class CoreLfDeclarationError extends Error {
    constructor(
        public readonly code: CoreLfDeclarationErrorCode,
        public readonly provenance: Provenance,
        message: string,
        public readonly underlying?: Error
    ) {
        super(message);
        this.name = 'CoreLfDeclarationError';
    }
}

const collectFreeReferences = (
    expression: KernelExpression
): readonly KernelReference[] => {
    const references: KernelReference[] = [];
    const seen = new Set<string>();

    const visit = (current: KernelExpression): void => {
        switch (current.tag) {
            case 'universe':
            case 'bound':
                return;
            case 'reference':
                if (!seen.has(current.name)) {
                    seen.add(current.name);
                    references.push(current);
                }
                return;
            case 'meta':
                current.spine.forEach(visit);
                return;
            case 'application':
                current.arguments.forEach(argument => visit(argument.value));
                return;
            case 'call':
                visit(current.callee);
                current.arguments.forEach(argument => visit(argument.value));
                return;
            case 'pi':
            case 'lambda':
                visit(current.binder.type);
                visit(current.body);
                return;
            default: {
                const exhaustive: never = current;
                return exhaustive;
            }
        }
    };

    visit(expression);
    return Object.freeze(references);
};

const collectOwnerDependencies = (
    expression: KernelExpression
): readonly CoreOwnerId[] => {
    const owners: CoreOwnerId[] = [];
    const seen = new Set<CoreOwnerId>();

    const visit = (current: KernelExpression): void => {
        switch (current.tag) {
            case 'universe':
            case 'reference':
            case 'bound':
                return;
            case 'meta':
                current.spine.forEach(visit);
                return;
            case 'application':
                if (!seen.has(current.owner)) {
                    seen.add(current.owner);
                    owners.push(current.owner);
                }
                current.arguments.forEach(argument => visit(argument.value));
                return;
            case 'call':
                visit(current.callee);
                current.arguments.forEach(argument => visit(argument.value));
                return;
            case 'pi':
            case 'lambda':
                visit(current.binder.type);
                visit(current.body);
                return;
            default: {
                const exhaustive: never = current;
                return exhaustive;
            }
        }
    };

    visit(expression);
    return Object.freeze(owners);
};

const errorText = (error: unknown): string =>
    error instanceof Error ? error.message : String(error);

interface CoreLfDeltaDependencyNode {
    readonly id: string;
    readonly label: string;
    readonly freeDependencies: readonly string[];
    readonly ownerDependencies: readonly CoreOwnerId[];
}

const freeDeltaNodeId = (name: string): string => `free:${name}`;
const ownerDeltaNodeId = (owner: CoreOwnerId): string => `owner:${owner}`;

/**
 * Return the first deterministic transparent-delta cycle, if any.
 */
const coreLfDeltaDependencyCycle = (
    declarations: readonly CoreLfDeclaration[],
    intrinsicDefinitions: readonly CoreLfIntrinsicDefinition[]
): readonly string[] | undefined => {
    const transparentFree = declarations.filter(declaration =>
        declaration.transparency === 'transparent' &&
        declaration.body !== undefined
    );
    const freeIds = new Set(
        transparentFree.map(declaration =>
            freeDeltaNodeId(declaration.name)
        )
    );
    const ownerIds = new Set(
        intrinsicDefinitions.map(definition =>
            ownerDeltaNodeId(definition.owner)
        )
    );
    const nodes = new Map<string, CoreLfDeltaDependencyNode>();

    transparentFree.forEach(declaration => {
        const id = freeDeltaNodeId(declaration.name);
        nodes.set(id, {
            id,
            label: declaration.name,
            freeDependencies: declaration.bodyDependencies,
            ownerDependencies: declaration.bodyOwnerDependencies
        });
    });
    intrinsicDefinitions.forEach(definition => {
        const id = ownerDeltaNodeId(definition.owner);
        nodes.set(id, {
            id,
            label: definition.declarationName,
            freeDependencies: definition.bodyDependencies,
            ownerDependencies: definition.ownerDependencies
        });
    });

    const edges = (
        node: CoreLfDeltaDependencyNode
    ): readonly string[] => [
        ...node.freeDependencies
            .map(freeDeltaNodeId)
            .filter(id => freeIds.has(id)),
        ...node.ownerDependencies
            .map(ownerDeltaNodeId)
            .filter(id => ownerIds.has(id))
    ];
    const active = new Set<string>();
    const complete = new Set<string>();
    const stack: string[] = [];

    const visit = (id: string): readonly string[] | undefined => {
        if (complete.has(id)) return undefined;
        if (active.has(id)) {
            const start = stack.indexOf(id);
            return Object.freeze([
                ...stack.slice(start),
                id
            ].map(item => nodes.get(item)?.label ?? item));
        }
        const node = nodes.get(id);
        if (node === undefined) return undefined;
        active.add(id);
        stack.push(id);
        for (const dependency of edges(node)) {
            const cycle = visit(dependency);
            if (cycle !== undefined) return cycle;
        }
        stack.pop();
        active.delete(id);
        complete.add(id);
        return undefined;
    };

    for (const id of nodes.keys()) {
        const cycle = visit(id);
        if (cycle !== undefined) return cycle;
    }
    return undefined;
};

/**
 * Persistent candidate definition environment.
 *
 * `coreEnvironment` contains the same declarations without bodies so the
 * existing checker can validate types and bodies without learning delta yet.
 * The parallel declaration array owns candidate-only body/transparency data.
 */
export class CoreLfDeclarationEnvironment {
    private readonly declarationMap:
        ReadonlyMap<string, CoreLfDeclaration>;
    private readonly intrinsicDefinitionMap:
        ReadonlyMap<CoreOwnerId, CoreLfIntrinsicDefinition>;

    private constructor(
        public readonly coreEnvironment: CoreDeclarationEnvironment,
        public readonly declarations: readonly CoreLfDeclaration[],
        public readonly intrinsicDefinitions:
            readonly CoreLfIntrinsicDefinition[],
        private readonly checkerFactory:
            CoreLfDeclarationCheckerFactory
    ) {
        this.declarations = Object.freeze([...declarations]);
        this.intrinsicDefinitions = Object.freeze([
            ...intrinsicDefinitions
        ]);
        this.declarationMap = new Map(
            this.declarations.map(declaration => [
                declaration.name,
                declaration
            ])
        );
        this.intrinsicDefinitionMap = new Map(
            this.intrinsicDefinitions.map(definition => [
                definition.owner,
                definition
            ])
        );
        Object.freeze(this);
    }

    static empty(): CoreLfDeclarationEnvironment {
        return new CoreLfDeclarationEnvironment(
            CoreDeclarationEnvironment.empty(),
            [],
            [],
            defaultCoreLfDeclarationCheckerFactory
        );
    }

    lookup(name: string): CoreLfDeclaration | undefined {
        return this.declarationMap.get(name);
    }

    lookupIntrinsicDefinition(
        owner: CoreOwnerId
    ): CoreLfIntrinsicDefinition | undefined {
        return this.intrinsicDefinitionMap.get(owner);
    }

    extend(
        input: CoreLfDeclarationInput,
        checkerFactory: CoreLfDeclarationCheckerFactory =
            this.checkerFactory
    ): CoreLfDeclarationEnvironment {
        const transparency = input.transparency ?? 'opaque';
        if (
            transparency !== 'opaque' &&
            transparency !== 'transparent'
        ) {
            throw new CoreLfDeclarationError(
                'INVALID_TRANSPARENCY',
                input.provenance,
                `Core LF declaration '${input.name}' has invalid ` +
                `transparency '${String(transparency)}'`
            );
        }
        if (this.declarationMap.has(input.name)) {
            throw new CoreLfDeclarationError(
                'DUPLICATE_DECLARATION',
                input.provenance,
                `Duplicate Core LF declaration '${input.name}'`
            );
        }
        if (transparency === 'transparent' && input.body === undefined) {
            throw new CoreLfDeclarationError(
                'TRANSPARENT_ASSUMPTION',
                input.provenance,
                `Core LF declaration '${input.name}' cannot be transparent ` +
                'without a checked body'
            );
        }

        let nextCoreEnvironment: CoreDeclarationEnvironment;
        try {
            nextCoreEnvironment = this.coreEnvironment.extend({
                name: input.name,
                type: input.type,
                mode: input.mode,
                provenance: input.provenance
            });
            const typeChecker = checkerFactory(nextCoreEnvironment, {
                phase: 'declaration-type',
                lfEnvironment: this
            });
            if (
                typeChecker.rootContext.environment !==
                nextCoreEnvironment
            ) {
                throw new CoreLfDeclarationError(
                    'INVALID_DECLARATION_TYPE',
                    input.provenance,
                    `Checker factory for Core LF declaration ` +
                    `'${input.name}' returned a checker for a foreign ` +
                    'declaration environment'
                );
            }
            typeChecker.validateEnvironment();
        } catch (error: unknown) {
            const underlying = error instanceof Error ? error : undefined;
            const code = error instanceof CoreContextError &&
                error.code === 'DUPLICATE_DECLARATION'
                ? 'DUPLICATE_DECLARATION'
                : 'INVALID_DECLARATION_TYPE';
            throw new CoreLfDeclarationError(
                code,
                input.provenance,
                `Invalid type for Core LF declaration '${input.name}': ` +
                errorText(error),
                underlying
            );
        }

        let checkedBody: KernelExpression | undefined;
        let bodyDependencies: readonly string[] = Object.freeze([]);
        let bodyOwnerDependencies: readonly CoreOwnerId[] =
            Object.freeze([]);
        if (input.body !== undefined) {
            const references = collectFreeReferences(input.body);
            for (const reference of references) {
                if (reference.name === input.name) {
                    throw new CoreLfDeclarationError(
                        'SELF_REFERENCE',
                        reference.provenance,
                        `Core LF definition '${input.name}' refers to itself; ` +
                        'definition bodies may mention only earlier declarations'
                    );
                }
                if (!this.declarationMap.has(reference.name)) {
                    throw new CoreLfDeclarationError(
                        'UNBOUND_BODY_REFERENCE',
                        reference.provenance,
                        `Core LF definition '${input.name}' refers to ` +
                        `non-earlier declaration '${reference.name}'`
                    );
                }
            }
            bodyDependencies = Object.freeze(
                references.map(reference => reference.name)
            );
            bodyOwnerDependencies = collectOwnerDependencies(input.body);

            try {
                const bodyChecker = checkerFactory(
                    this.coreEnvironment,
                    {
                        phase: 'definition-body',
                        lfEnvironment: this
                    }
                );
                if (
                    bodyChecker.rootContext.environment !==
                    this.coreEnvironment
                ) {
                    throw new CoreLfDeclarationError(
                        'INVALID_DEFINITION_BODY',
                        input.body.provenance,
                        `Checker factory for Core LF definition ` +
                        `'${input.name}' returned a checker for a foreign ` +
                        'declaration environment'
                    );
                }
                checkedBody = bodyChecker.check(
                    bodyChecker.rootContext,
                    input.body,
                    input.type
                ).term;
            } catch (error: unknown) {
                const underlying = error instanceof Error ? error : undefined;
                throw new CoreLfDeclarationError(
                    'INVALID_DEFINITION_BODY',
                    input.body.provenance,
                    `Invalid body for Core LF definition '${input.name}': ` +
                    errorText(error),
                    underlying
                );
            }
        }

        const coreDeclaration = nextCoreEnvironment.lookup(input.name);
        if (!coreDeclaration) {
            throw new CoreLfDeclarationError(
                'INVALID_DECLARATION',
                input.provenance,
                `Core LF declaration '${input.name}' was not retained by ` +
                'the checked declaration environment'
            );
        }

        const declaration: CoreLfDeclaration = Object.freeze({
            name: input.name,
            type: coreDeclaration.type,
            mode: coreDeclaration.mode,
            provenance: coreDeclaration.provenance,
            reference: coreDeclaration.reference,
            body: checkedBody,
            transparency,
            ordinal:
                this.declarations.length +
                this.intrinsicDefinitions.length,
            bodyDependencies,
            bodyOwnerDependencies
        });
        return new CoreLfDeclarationEnvironment(
            nextCoreEnvironment,
            [...this.declarations, declaration],
            this.intrinsicDefinitions,
            checkerFactory
        );
    }

    /**
     * Install a checked transparent body for an existing semantic owner.
     *
     * Free references must already exist. Owner references may have been
     * checked while this owner was opaque, so installation validates the
     * complete transparent dependency graph and rejects any resulting cycle.
     */
    extendIntrinsicDefinition(
        input: CoreLfIntrinsicDefinitionInput,
        checkerFactory: CoreLfDeclarationCheckerFactory =
            this.checkerFactory
    ): CoreLfDeclarationEnvironment {
        if (this.intrinsicDefinitionMap.has(input.owner)) {
            throw new CoreLfDeclarationError(
                'DUPLICATE_INTRINSIC_DEFINITION',
                input.provenance,
                `Core LF owner '${input.owner}' already has a transparent ` +
                    'intrinsic definition'
            );
        }

        const references = collectFreeReferences(input.body);
        for (const reference of references) {
            if (!this.declarationMap.has(reference.name)) {
                throw new CoreLfDeclarationError(
                    'UNBOUND_BODY_REFERENCE',
                    reference.provenance,
                    `Core LF intrinsic definition '${input.owner}' refers ` +
                        `to non-earlier declaration '${reference.name}'`
                );
            }
        }
        const ownerDependencies =
            collectOwnerDependencies(input.body);
        if (ownerDependencies.includes(input.owner)) {
            throw new CoreLfDeclarationError(
                'SELF_REFERENCE',
                input.body.provenance,
                `Core LF intrinsic definition '${input.owner}' refers to ` +
                    'its own semantic owner'
            );
        }

        const type = coreOwnerSignatureType(
            input.owner,
            input.provenance
        );
        let checkedBody: KernelExpression;
        try {
            const bodyChecker = checkerFactory(
                this.coreEnvironment,
                {
                    phase: 'definition-body',
                    lfEnvironment: this
                }
            );
            if (
                bodyChecker.rootContext.environment !==
                this.coreEnvironment
            ) {
                throw new CoreLfDeclarationError(
                    'INVALID_DEFINITION_BODY',
                    input.body.provenance,
                    `Checker factory for intrinsic Core LF definition ` +
                        `'${input.owner}' returned a checker for a foreign ` +
                        'declaration environment'
                );
            }
            checkedBody = bodyChecker.check(
                bodyChecker.rootContext,
                input.body,
                type
            ).term;
        } catch (error: unknown) {
            const underlying = error instanceof Error ? error : undefined;
            throw new CoreLfDeclarationError(
                'INVALID_DEFINITION_BODY',
                input.body.provenance,
                `Invalid body for intrinsic Core LF definition ` +
                    `'${input.owner}': ${errorText(error)}`,
                underlying
            );
        }

        const checkedReferences = collectFreeReferences(checkedBody);
        const definition: CoreLfIntrinsicDefinition = Object.freeze({
            owner: input.owner,
            declarationName:
                input.declarationName ?? `@core-owner:${input.owner}`,
            type,
            body: checkedBody,
            transparency: 'transparent',
            provenance: input.provenance,
            ordinal:
                this.declarations.length +
                this.intrinsicDefinitions.length,
            bodyDependencies: Object.freeze(
                checkedReferences.map(reference => reference.name)
            ),
            ownerDependencies: collectOwnerDependencies(checkedBody)
        });
        const cycle = coreLfDeltaDependencyCycle(
            this.declarations,
            [...this.intrinsicDefinitions, definition]
        );
        if (cycle !== undefined) {
            throw new CoreLfDeclarationError(
                'CYCLIC_INTRINSIC_DEFINITION',
                input.provenance,
                `Core LF intrinsic definition '${input.owner}' creates ` +
                    `transparent delta cycle ${cycle.join(' -> ')}`
            );
        }
        return new CoreLfDeclarationEnvironment(
            this.coreEnvironment,
            this.declarations,
            [...this.intrinsicDefinitions, definition],
            checkerFactory
        );
    }
}

export type CoreLfDeltaIrreducibleReason =
    | 'not-a-reference-head'
    | 'empty-call'
    | 'declaration-not-found'
    | 'declaration-without-body'
    | 'declaration-opaque';

export interface CoreLfDeltaHeadUnfold {
    readonly status: 'unfolded';
    readonly before: KernelExpression;
    readonly after: KernelExpression;
    readonly declarationName: string;
    readonly declarationOrdinal: number;
}

export interface CoreLfDeltaHeadIrreducible {
    readonly status: 'irreducible';
    readonly expression: KernelExpression;
    readonly head: KernelExpression;
    readonly reason: CoreLfDeltaIrreducibleReason;
    readonly declarationName?: string;
}

export type CoreLfDeltaHeadResult =
    | CoreLfDeltaHeadUnfold
    | CoreLfDeltaHeadIrreducible;

export interface CoreLfDeltaTraceEntry {
    readonly step: number;
    readonly kind: 'delta';
    readonly declarationName: string;
    readonly declarationOrdinal: number;
    readonly before: KernelExpression;
    readonly after: KernelExpression;
}

export interface CoreLfDeltaRedexSummary {
    readonly declarationName: string;
    readonly declarationOrdinal: number;
}

interface CoreLfDeltaWeakHeadBase {
    readonly expression: KernelExpression;
    readonly steps: number;
    readonly trace: readonly CoreLfDeltaTraceEntry[];
}

export interface CoreLfDeltaWeakHeadNormal
    extends CoreLfDeltaWeakHeadBase {
    readonly status: 'weak-head-normal';
    readonly reason: CoreLfDeltaIrreducibleReason;
}

export interface CoreLfDeltaWeakHeadStepLimit
    extends CoreLfDeltaWeakHeadBase {
    readonly status: 'step-limit-exceeded';
    readonly next: CoreLfDeltaRedexSummary;
}

export type CoreLfDeltaWeakHeadResult =
    | CoreLfDeltaWeakHeadNormal
    | CoreLfDeltaWeakHeadStepLimit;

interface CoreLfDeltaSpine {
    readonly head: KernelExpression;
    readonly arguments: readonly KernelArgument[];
    readonly hasEmptyCall: boolean;
}

const decomposeDeltaSpine = (
    expression: KernelExpression
): CoreLfDeltaSpine => {
    let current = expression;
    const segments: (readonly KernelArgument[])[] = [];
    let hasEmptyCall = false;

    while (current.tag === 'call') {
        if (current.arguments.length === 0) hasEmptyCall = true;
        segments.unshift(current.arguments);
        current = current.callee;
    }
    return {
        head: current,
        arguments: Object.freeze(segments.flat()),
        hasEmptyCall
    };
};

const deltaCallProvenance = (
    expression: KernelExpression,
    declaration: CoreLfDeclaration
): Provenance => provenance(
    'derived',
    `outer LF delta unfolding ${declaration.name}`,
    expression.provenance.span
);

/**
 * Unfold one transparent definition at the weak head.
 */
export function coreLfDeltaReduceHead(
    environment: CoreLfDeclarationEnvironment,
    expression: KernelExpression
): CoreLfDeltaHeadResult {
    const spine = decomposeDeltaSpine(expression);
    if (spine.hasEmptyCall) {
        return Object.freeze({
            status: 'irreducible',
            expression,
            head: spine.head,
            reason: 'empty-call'
        });
    }
    if (spine.head.tag === 'application') {
        const definition = environment.lookupIntrinsicDefinition(
            spine.head.owner
        );
        if (definition === undefined) {
            return Object.freeze({
                status: 'irreducible',
                expression,
                head: spine.head,
                reason: 'not-a-reference-head'
            });
        }
        const arguments_ = [
            ...spine.head.arguments,
            ...spine.arguments
        ];
        const after = arguments_.length === 0
            ? definition.body
            : kernelCall(
                definition.body,
                arguments_.map(argument => ({
                    plicity: argument.plicity,
                    value: argument.value,
                    provenance: argument.provenance
                })),
                provenance(
                    'derived',
                    `outer LF delta unfolding ` +
                        `${definition.declarationName}`,
                    expression.provenance.span
                )
            );
        return Object.freeze({
            status: 'unfolded',
            before: expression,
            after,
            declarationName: definition.declarationName,
            declarationOrdinal: definition.ordinal
        });
    }
    if (spine.head.tag !== 'reference') {
        return Object.freeze({
            status: 'irreducible',
            expression,
            head: spine.head,
            reason: 'not-a-reference-head'
        });
    }

    const declaration = environment.lookup(spine.head.name);
    if (!declaration) {
        return Object.freeze({
            status: 'irreducible',
            expression,
            head: spine.head,
            reason: 'declaration-not-found',
            declarationName: spine.head.name
        });
    }
    if (declaration.body === undefined) {
        return Object.freeze({
            status: 'irreducible',
            expression,
            head: spine.head,
            reason: 'declaration-without-body',
            declarationName: declaration.name
        });
    }
    if (declaration.transparency !== 'transparent') {
        return Object.freeze({
            status: 'irreducible',
            expression,
            head: spine.head,
            reason: 'declaration-opaque',
            declarationName: declaration.name
        });
    }

    const after = spine.arguments.length === 0
        ? declaration.body
        : kernelCall(
            declaration.body,
            spine.arguments.map(argument => ({
                plicity: argument.plicity,
                value: argument.value,
                provenance: argument.provenance
            })),
            deltaCallProvenance(expression, declaration)
        );
    return Object.freeze({
        status: 'unfolded',
        before: expression,
        after,
        declarationName: declaration.name,
        declarationOrdinal: declaration.ordinal
    });
}

const frozenDeltaTrace = (
    trace: readonly CoreLfDeltaTraceEntry[]
): readonly CoreLfDeltaTraceEntry[] =>
    Object.freeze(trace.map(entry => Object.freeze({ ...entry })));

/**
 * Repeatedly unfold only transparent weak-head definitions under a finite
 * step bound. Free-only chains decrease declaration ordinals, while
 * intrinsic-owner equations are admitted only after a transparent dependency
 * graph cycle check. The explicit global bound remains part of the API.
 */
export function coreLfDeltaWeakHead(
    environment: CoreLfDeclarationEnvironment,
    expression: KernelExpression,
    stepLimit: number
): CoreLfDeltaWeakHeadResult {
    if (!Number.isSafeInteger(stepLimit) || stepLimit < 0) {
        throw new CoreLfEvaluationError(
            'INVALID_STEP_LIMIT',
            expression.provenance,
            `Outer LF delta step limit must be a nonnegative safe integer; ` +
            `received ${stepLimit}`
        );
    }

    let current = expression;
    const trace: CoreLfDeltaTraceEntry[] = [];

    while (true) {
        const unfolding = coreLfDeltaReduceHead(environment, current);
        if (unfolding.status === 'irreducible') {
            return Object.freeze({
                status: 'weak-head-normal',
                expression: current,
                steps: trace.length,
                trace: frozenDeltaTrace(trace),
                reason: unfolding.reason
            });
        }
        if (trace.length === stepLimit) {
            return Object.freeze({
                status: 'step-limit-exceeded',
                expression: current,
                steps: trace.length,
                trace: frozenDeltaTrace(trace),
                next: Object.freeze({
                    declarationName: unfolding.declarationName,
                    declarationOrdinal: unfolding.declarationOrdinal
                })
            });
        }

        trace.push(Object.freeze({
            step: trace.length,
            kind: 'delta',
            declarationName: unfolding.declarationName,
            declarationOrdinal: unfolding.declarationOrdinal,
            before: unfolding.before,
            after: unfolding.after
        }));
        current = unfolding.after;
    }
}
