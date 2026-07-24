/**
 * Scoped HOAS-style construction for the candidate outer λΠ LF.
 *
 * Binder callbacks execute immediately and exactly once. The temporary
 * builder tree stores only branded token identities, never callbacks.
 * Lowering resolves those identities to De Bruijn indices and returns the
 * existing explicit Core representation.
 */

import {
    BinderMode,
    CoreOwnerId,
    KernelExpression,
    Plicity,
    Provenance,
    assertSafeIdentifier,
    binderMode,
    kernelApplication,
    kernelAssertScoped,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelFree,
    kernelLambda,
    kernelPi,
    kernelUniverse,
    provenance
} from './kernel';
import {
    CORE_OWNER_SCHEMAS
} from './schema';

const CORE_LF_BUILDER_TERM = Symbol('CoreLfBuilderTerm');
const CORE_LF_BINDER_TOKEN = Symbol('CoreLfBinderToken');

/**
 * Opaque candidate surface term. Values can only be constructed by their
 * owning `CoreLfScopedBuilder`.
 */
export interface CoreLfBuilderTerm {
    readonly [CORE_LF_BUILDER_TERM]: true;
}

/**
 * A builder-local binder occurrence supplied to one callback.
 */
export interface CoreLfBinderToken extends CoreLfBuilderTerm {
    readonly [CORE_LF_BINDER_TOKEN]: true;
}

export interface CoreLfBuilderCallArgument {
    readonly plicity: Plicity;
    readonly value: CoreLfBuilderTerm;
    readonly provenance?: Provenance;
}

export type CoreLfBuilderErrorCode =
    | 'INVALID_TERM'
    | 'FOREIGN_TERM'
    | 'ESCAPED_BINDER_TOKEN'
    | 'OPEN_EMBEDDED_CORE'
    | 'INVALID_OWNER_ARITY';

export class CoreLfBuilderError extends Error {
    constructor(
        public readonly code: CoreLfBuilderErrorCode,
        public readonly provenance: Provenance,
        message: string,
        public readonly underlying?: Error
    ) {
        super(message);
        this.name = 'CoreLfBuilderError';
    }
}

type CoreLfBuilderNode =
    | {
        readonly tag: 'core';
        readonly expression: KernelExpression;
    }
    | {
        readonly tag: 'token';
        readonly ordinal: number;
        readonly hint: string;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'application';
        readonly owner: CoreOwnerId;
        readonly arguments: readonly InternalCoreLfBuilderTerm[];
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'call';
        readonly callee: InternalCoreLfBuilderTerm;
        readonly arguments: readonly {
            readonly plicity: Plicity;
            readonly value: InternalCoreLfBuilderTerm;
            readonly provenance?: Provenance;
        }[];
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'pi' | 'lambda';
        readonly name: string;
        readonly type: InternalCoreLfBuilderTerm;
        readonly mode: BinderMode;
        readonly token: InternalCoreLfBuilderTerm;
        readonly body: InternalCoreLfBuilderTerm;
        readonly provenance: Provenance;
    }
    | {
        readonly tag: 'let';
        readonly name: string;
        readonly type: InternalCoreLfBuilderTerm;
        readonly value: InternalCoreLfBuilderTerm;
        readonly mode: BinderMode;
        readonly token: InternalCoreLfBuilderTerm;
        readonly body: InternalCoreLfBuilderTerm;
        readonly provenance: Provenance;
    };

interface InternalCoreLfBuilderTerm extends CoreLfBuilderTerm {
    readonly builderIdentity: symbol;
    readonly node: CoreLfBuilderNode;
    readonly [CORE_LF_BINDER_TOKEN]?: true;
}

const freezeMode = (mode: BinderMode): BinderMode => Object.freeze({
    plicity: mode.plicity,
    variation: mode.variation
});

/**
 * Session-local scoped builder. It has no global token counter or registry.
 */
export class CoreLfScopedBuilder {
    private readonly builderIdentity = Symbol('CoreLfScopedBuilder');
    private nextTokenOrdinal = 0;

    constructor(
        private readonly defaultProvenance: Provenance = provenance(
            'derived',
            'scoped Core LF builder'
        )
    ) {}

    private nodeProvenance(
        detail: string,
        supplied?: Provenance
    ): Provenance {
        if (supplied) return supplied;
        return provenance(
            'derived',
            detail,
            this.defaultProvenance.span
        );
    }

    private makeTerm(
        node: CoreLfBuilderNode,
        binderToken = false
    ): InternalCoreLfBuilderTerm {
        const term = {
            [CORE_LF_BUILDER_TERM]: true as const,
            ...(binderToken
                ? { [CORE_LF_BINDER_TOKEN]: true as const }
                : {}),
            builderIdentity: this.builderIdentity,
            node: Object.freeze(node)
        };
        return Object.freeze(term);
    }

    private requireTerm(
        value: CoreLfBuilderTerm,
        nodeProvenance: Provenance
    ): InternalCoreLfBuilderTerm {
        if (
            typeof value !== 'object' ||
            value === null ||
            (value as InternalCoreLfBuilderTerm)[CORE_LF_BUILDER_TERM] !== true
        ) {
            throw new CoreLfBuilderError(
                'INVALID_TERM',
                nodeProvenance,
                'Scoped Core LF builder callback or constructor received an ' +
                'invalid term'
            );
        }
        const term = value as InternalCoreLfBuilderTerm;
        if (term.builderIdentity !== this.builderIdentity) {
            throw new CoreLfBuilderError(
                'FOREIGN_TERM',
                nodeProvenance,
                'Scoped Core LF builder term belongs to another builder'
            );
        }
        return term;
    }

    private token(
        hint: string,
        nodeProvenance: Provenance
    ): InternalCoreLfBuilderTerm {
        return this.makeTerm({
            tag: 'token',
            ordinal: this.nextTokenOrdinal++,
            hint,
            provenance: nodeProvenance
        }, true);
    }

    private bind(
        tag: 'pi' | 'lambda',
        name: string,
        type: CoreLfBuilderTerm,
        body: (token: CoreLfBinderToken) => CoreLfBuilderTerm,
        mode: BinderMode,
        suppliedProvenance?: Provenance
    ): CoreLfBuilderTerm {
        assertSafeIdentifier(name, 'Scoped Core LF binder hint');
        const nodeProvenance = this.nodeProvenance(
            `scoped Core LF ${tag} ${name}`,
            suppliedProvenance
        );
        const checkedType = this.requireTerm(type, nodeProvenance);
        const token = this.token(name, nodeProvenance);
        // The callback is deliberately evaluated here once and never stored.
        const checkedBody = this.requireTerm(
            body(token as CoreLfBinderToken),
            nodeProvenance
        );
        return this.makeTerm({
            tag,
            name,
            type: checkedType,
            mode: freezeMode(mode),
            token,
            body: checkedBody,
            provenance: nodeProvenance
        });
    }

    universe(nodeProvenance?: Provenance): CoreLfBuilderTerm {
        const resolved = this.nodeProvenance(
            'scoped Core LF universe',
            nodeProvenance
        );
        return this.makeTerm({
            tag: 'core',
            expression: kernelUniverse(resolved)
        });
    }

    free(
        name: string,
        nodeProvenance?: Provenance
    ): CoreLfBuilderTerm {
        const resolved = this.nodeProvenance(
            `scoped Core LF free name ${name}`,
            nodeProvenance
        );
        return this.makeTerm({
            tag: 'core',
            expression: kernelFree(name, resolved)
        });
    }

    /**
     * Embed only a closed explicit Core subtree. Scoped dependencies must use
     * callback tokens so lowering, not a caller-supplied index, owns binding.
     */
    embed(expression: KernelExpression): CoreLfBuilderTerm {
        try {
            kernelAssertScoped(expression);
        } catch (error: unknown) {
            const underlying = error instanceof Error ? error : undefined;
            throw new CoreLfBuilderError(
                'OPEN_EMBEDDED_CORE',
                expression.provenance,
                'Scoped Core LF builder can embed only closed Core terms',
                underlying
            );
        }
        return this.makeTerm({
            tag: 'core',
            expression
        });
    }

    application(
        owner: CoreOwnerId,
        arguments_: readonly CoreLfBuilderTerm[],
        suppliedProvenance?: Provenance
    ): CoreLfBuilderTerm {
        const nodeProvenance = this.nodeProvenance(
            `scoped Core LF owner application ${owner}`,
            suppliedProvenance
        );
        const expected = CORE_OWNER_SCHEMAS[owner].slots.length;
        if (arguments_.length !== expected) {
            throw new CoreLfBuilderError(
                'INVALID_OWNER_ARITY',
                nodeProvenance,
                `Scoped Core LF owner ${owner} expects ${expected} ` +
                `arguments, received ${arguments_.length}`
            );
        }
        return this.makeTerm({
            tag: 'application',
            owner,
            arguments: Object.freeze(arguments_.map(argument =>
                this.requireTerm(argument, nodeProvenance)
            )),
            provenance: nodeProvenance
        });
    }

    call(
        callee: CoreLfBuilderTerm,
        arguments_: readonly CoreLfBuilderCallArgument[],
        suppliedProvenance?: Provenance
    ): CoreLfBuilderTerm {
        const nodeProvenance = this.nodeProvenance(
            'scoped Core LF generic call',
            suppliedProvenance
        );
        return this.makeTerm({
            tag: 'call',
            callee: this.requireTerm(callee, nodeProvenance),
            arguments: Object.freeze(arguments_.map(argument =>
                Object.freeze({
                    plicity: argument.plicity,
                    value: this.requireTerm(
                        argument.value,
                        argument.provenance ?? nodeProvenance
                    ),
                    provenance: argument.provenance
                })
            )),
            provenance: nodeProvenance
        });
    }

    apply(
        callee: CoreLfBuilderTerm,
        value: CoreLfBuilderTerm,
        plicity: Plicity = 'explicit',
        nodeProvenance?: Provenance
    ): CoreLfBuilderTerm {
        return this.call(
            callee,
            [{ plicity, value, provenance: nodeProvenance }],
            nodeProvenance
        );
    }

    pi(
        name: string,
        type: CoreLfBuilderTerm,
        body: (token: CoreLfBinderToken) => CoreLfBuilderTerm,
        mode: BinderMode = binderMode('explicit', 'functorial'),
        nodeProvenance?: Provenance
    ): CoreLfBuilderTerm {
        return this.bind(
            'pi',
            name,
            type,
            body,
            mode,
            nodeProvenance
        );
    }

    lam(
        name: string,
        type: CoreLfBuilderTerm,
        body: (token: CoreLfBinderToken) => CoreLfBuilderTerm,
        mode: BinderMode = binderMode('explicit', 'functorial'),
        nodeProvenance?: Provenance
    ): CoreLfBuilderTerm {
        return this.bind(
            'lambda',
            name,
            type,
            body,
            mode,
            nodeProvenance
        );
    }

    /**
     * Surface let. Lowering produces `(λ x : type, body) value`; Core gains no
     * let node and candidate beta supplies ζ computation.
     */
    let_(
        name: string,
        type: CoreLfBuilderTerm,
        value: CoreLfBuilderTerm,
        body: (token: CoreLfBinderToken) => CoreLfBuilderTerm,
        mode: BinderMode = binderMode('explicit', 'functorial'),
        suppliedProvenance?: Provenance
    ): CoreLfBuilderTerm {
        assertSafeIdentifier(name, 'Scoped Core LF let binder hint');
        const nodeProvenance = this.nodeProvenance(
            `scoped Core LF let ${name}`,
            suppliedProvenance
        );
        const checkedType = this.requireTerm(type, nodeProvenance);
        const checkedValue = this.requireTerm(value, nodeProvenance);
        const token = this.token(name, nodeProvenance);
        const checkedBody = this.requireTerm(
            body(token as CoreLfBinderToken),
            nodeProvenance
        );
        return this.makeTerm({
            tag: 'let',
            name,
            type: checkedType,
            value: checkedValue,
            mode: freezeMode(mode),
            token,
            body: checkedBody,
            provenance: nodeProvenance
        });
    }

    private lowerAt(
        term: InternalCoreLfBuilderTerm,
        scope: readonly InternalCoreLfBuilderTerm[]
    ): KernelExpression {
        switch (term.node.tag) {
            case 'core':
                return term.node.expression;
            case 'token': {
                const index = scope.indexOf(term);
                if (index < 0) {
                    throw new CoreLfBuilderError(
                        'ESCAPED_BINDER_TOKEN',
                        term.node.provenance,
                        `Scoped Core LF binder token '${term.node.hint}' ` +
                        `#${term.node.ordinal} escaped its callback body`
                    );
                }
                return kernelBound(index, term.node.provenance);
            }
            case 'application':
                return kernelApplication(
                    term.node.owner,
                    term.node.arguments.map(argument => ({
                        value: this.lowerAt(argument, scope)
                    })),
                    term.node.provenance
                );
            case 'call':
                return kernelCall(
                    this.lowerAt(term.node.callee, scope),
                    term.node.arguments.map(argument => ({
                        plicity: argument.plicity,
                        value: this.lowerAt(argument.value, scope),
                        provenance: argument.provenance
                    })),
                    term.node.provenance
                );
            case 'pi':
            case 'lambda': {
                const type = this.lowerAt(term.node.type, scope);
                const body = this.lowerAt(
                    term.node.body,
                    [term.node.token, ...scope]
                );
                const binder = kernelBinder(
                    term.node.name,
                    type,
                    term.node.mode,
                    term.node.provenance
                );
                return term.node.tag === 'pi'
                    ? kernelPi(binder, body, term.node.provenance)
                    : kernelLambda(binder, body, term.node.provenance);
            }
            case 'let': {
                const type = this.lowerAt(term.node.type, scope);
                const value = this.lowerAt(term.node.value, scope);
                const body = this.lowerAt(
                    term.node.body,
                    [term.node.token, ...scope]
                );
                const lambda = kernelLambda(
                    kernelBinder(
                        term.node.name,
                        type,
                        term.node.mode,
                        term.node.provenance
                    ),
                    body,
                    term.node.provenance
                );
                return kernelCall(
                    lambda,
                    [{
                        plicity: term.node.mode.plicity,
                        value,
                        provenance: value.provenance
                    }],
                    provenance(
                        'derived',
                        `lowered Core LF let ${term.node.name}`,
                        term.node.provenance.span
                    )
                );
            }
            default: {
                const exhaustive: never = term.node;
                return exhaustive;
            }
        }
    }

    lower(term: CoreLfBuilderTerm): KernelExpression {
        const checked = this.requireTerm(
            term,
            this.defaultProvenance
        );
        const lowered = this.lowerAt(checked, []);
        kernelAssertScoped(lowered);
        return lowered;
    }
}
