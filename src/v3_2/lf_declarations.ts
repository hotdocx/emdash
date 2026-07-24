/**
 * Immutable checked declarations and bounded delta for the candidate λΠ LF.
 *
 * Definitions are layered over the existing declaration/checker environment
 * instead of changing the frozen MVP declaration representation. A body is
 * checked in the preceding environment, so every free dependency has a
 * strictly smaller declaration ordinal and the initial delta fragment is
 * acyclic by construction.
 */

import {
    CoreBindingInput,
    CoreContextError,
    CoreDeclarationEnvironment
} from './context';
import {
    CoreChecker,
    CoreCheckerError
} from './checker';
import {
    KernelArgument,
    KernelCall,
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
    CoreElaborationSession
} from './session';

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
}

/**
 * Candidate declaration validation may opt into a reviewed checker while the
 * default remains the frozen Core checker. The factory is supplied an exact
 * persistent declaration environment for each validation phase.
 */
export type CoreLfDeclarationCheckerFactory = (
    environment: CoreDeclarationEnvironment
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

const errorText = (error: unknown): string =>
    error instanceof Error ? error.message : String(error);

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

    private constructor(
        public readonly coreEnvironment: CoreDeclarationEnvironment,
        public readonly declarations: readonly CoreLfDeclaration[],
        private readonly checkerFactory:
            CoreLfDeclarationCheckerFactory
    ) {
        this.declarations = Object.freeze([...declarations]);
        this.declarationMap = new Map(
            this.declarations.map(declaration => [
                declaration.name,
                declaration
            ])
        );
        Object.freeze(this);
    }

    static empty(): CoreLfDeclarationEnvironment {
        return new CoreLfDeclarationEnvironment(
            CoreDeclarationEnvironment.empty(),
            [],
            defaultCoreLfDeclarationCheckerFactory
        );
    }

    lookup(name: string): CoreLfDeclaration | undefined {
        return this.declarationMap.get(name);
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
            const typeChecker = checkerFactory(nextCoreEnvironment);
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

            try {
                const bodyChecker = checkerFactory(
                    this.coreEnvironment
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
            ordinal: this.declarations.length,
            bodyDependencies
        });
        return new CoreLfDeclarationEnvironment(
            nextCoreEnvironment,
            [...this.declarations, declaration],
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
 * step bound. Earlier-only body dependencies give delta-only chains a strict
 * ordinal decrease; the explicit bound remains part of the candidate API.
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
