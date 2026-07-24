/**
 * Persistent declaration and local-scope contexts for explicit emdash Core.
 *
 * Free declarations are ordered and session-owned: there is no ambient
 * registry. Local binders form a telescope in outermost-to-innermost order.
 * A local binding type is stored in the scope that owns it (before that
 * binding is introduced), then lifted deterministically when looked up from
 * a deeper scope.
 */

import {
    BinderMode,
    KernelBoundVariable,
    KernelExpression,
    KernelReference,
    KernelScopeError,
    Provenance,
    assertSafeIdentifier,
    formatSourceSpan,
    kernelAssertScoped,
    kernelBinder,
    kernelBound,
    kernelFree,
    kernelLambda,
    kernelPi,
    kernelShift
} from './kernel';

export interface CoreBindingInput {
    readonly name: string;
    readonly type: KernelExpression;
    readonly mode: BinderMode;
    readonly provenance: Provenance;
}

export interface CoreDeclaration extends CoreBindingInput {
    readonly reference: KernelReference;
}

export interface CoreLocalBinding extends CoreBindingInput {
    /**
     * Number of local binders in scope while this binding's type was formed.
     */
    readonly ownerDepth: number;
}

export type CoreContextErrorCode =
    | 'DUPLICATE_DECLARATION'
    | 'UNBOUND_NAME'
    | 'UNBOUND_FREE_REFERENCE'
    | 'ILL_SCOPED_DECLARATION_TYPE'
    | 'ILL_SCOPED_LOCAL_TYPE'
    | 'ILL_SCOPED_EXPRESSION';

export class CoreContextError extends Error {
    constructor(
        public readonly code: CoreContextErrorCode,
        public readonly provenance: Provenance,
        message: string,
        public readonly scopeError?: KernelScopeError
    ) {
        const location = provenance.span
            ? ` at ${formatSourceSpan(provenance.span)}`
            : '';
        super(`${message}${location}`);
        this.name = 'CoreContextError';
    }
}

type ScopeErrorCode =
    | 'ILL_SCOPED_DECLARATION_TYPE'
    | 'ILL_SCOPED_LOCAL_TYPE'
    | 'ILL_SCOPED_EXPRESSION';

function visitFreeReferences(
    expression: KernelExpression,
    visit: (reference: KernelReference) => void
): void {
    switch (expression.tag) {
        case 'reference':
            visit(expression);
            return;
        case 'bound':
            return;
        case 'meta':
            expression.spine.forEach(item =>
                visitFreeReferences(item, visit)
            );
            return;
        case 'application':
            expression.arguments.forEach(argument =>
                visitFreeReferences(argument.value, visit)
            );
            return;
        case 'pi':
        case 'lambda':
            visitFreeReferences(expression.binder.type, visit);
            visitFreeReferences(expression.body, visit);
            return;
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
}

function validateExpressionScope(
    expression: KernelExpression,
    ambientDepth: number,
    declarations: CoreDeclarationEnvironment,
    scopeCode: ScopeErrorCode,
    role: string
): void {
    try {
        kernelAssertScoped(expression, ambientDepth);
    } catch (error: unknown) {
        if (!(error instanceof KernelScopeError)) throw error;
        throw new CoreContextError(
            scopeCode,
            error.provenance,
            `${role} is not valid at Core binder depth ${ambientDepth}: ` +
            error.message,
            error
        );
    }

    visitFreeReferences(expression, reference => {
        if (declarations.lookup(reference.name)) return;
        throw new CoreContextError(
            'UNBOUND_FREE_REFERENCE',
            reference.provenance,
            `${role} refers to undeclared free name '${reference.name}'`
        );
    });
}

/**
 * An immutable, ordered environment of free Core declarations.
 *
 * Extension validates a declaration against the previous environment, so a
 * type may mention earlier declarations but not itself or a later name.
 */
export class CoreDeclarationEnvironment {
    private readonly declarationMap: ReadonlyMap<string, CoreDeclaration>;
    public readonly declarations: readonly CoreDeclaration[];

    private constructor(declarations: readonly CoreDeclaration[]) {
        this.declarations = Object.freeze([...declarations]);
        this.declarationMap = new Map(
            this.declarations.map(declaration => [
                declaration.name,
                declaration
            ])
        );
        Object.freeze(this);
    }

    static empty(): CoreDeclarationEnvironment {
        return new CoreDeclarationEnvironment([]);
    }

    lookup(name: string): CoreDeclaration | undefined {
        return this.declarationMap.get(name);
    }

    extend(input: CoreBindingInput): CoreDeclarationEnvironment {
        assertSafeIdentifier(input.name, 'Core declaration');
        if (this.declarationMap.has(input.name)) {
            throw new CoreContextError(
                'DUPLICATE_DECLARATION',
                input.provenance,
                `Duplicate Core declaration '${input.name}'`
            );
        }

        validateExpressionScope(
            input.type,
            0,
            this,
            'ILL_SCOPED_DECLARATION_TYPE',
            `Type of Core declaration '${input.name}'`
        );

        const declaration: CoreDeclaration = Object.freeze({
            ...input,
            reference: kernelFree(input.name, input.provenance)
        });
        return new CoreDeclarationEnvironment([
            ...this.declarations,
            declaration
        ]);
    }
}

export interface CoreFreeLookup {
    readonly kind: 'free';
    readonly name: string;
    readonly term: KernelReference;
    readonly type: KernelExpression;
    readonly mode: BinderMode;
    readonly declaration: CoreDeclaration;
}

export interface CoreLocalLookup {
    readonly kind: 'local';
    readonly name: string;
    readonly term: KernelBoundVariable;
    readonly type: KernelExpression;
    readonly mode: BinderMode;
    readonly index: number;
    readonly binding: CoreLocalBinding;
}

export type CoreContextLookup = CoreFreeLookup | CoreLocalLookup;

/**
 * A persistent locally nameless telescope over one declaration environment.
 */
export class CoreContext {
    public readonly telescope: readonly CoreLocalBinding[];

    private constructor(
        public readonly environment: CoreDeclarationEnvironment,
        telescope: readonly CoreLocalBinding[]
    ) {
        this.telescope = Object.freeze([...telescope]);
        Object.freeze(this);
    }

    static empty(
        declarations = CoreDeclarationEnvironment.empty()
    ): CoreContext {
        return new CoreContext(declarations, []);
    }

    get depth(): number {
        return this.telescope.length;
    }

    extend(input: CoreBindingInput): CoreContext {
        assertSafeIdentifier(input.name, 'Core local binder');
        validateExpressionScope(
            input.type,
            this.depth,
            this.environment,
            'ILL_SCOPED_LOCAL_TYPE',
            `Type of Core local binder '${input.name}'`
        );

        const binding: CoreLocalBinding = Object.freeze({
            ...input,
            ownerDepth: this.depth
        });
        return new CoreContext(
            this.environment,
            [...this.telescope, binding]
        );
    }

    /**
     * Look up a free declaration even when a local binder shadows its name.
     */
    lookupDeclaration(
        name: string,
        occurrenceProvenance?: Provenance
    ): CoreFreeLookup | undefined {
        const declaration = this.environment.lookup(name);
        if (!declaration) return undefined;
        return Object.freeze({
            kind: 'free',
            name,
            term: kernelFree(
                name,
                occurrenceProvenance ?? declaration.provenance
            ),
            type: declaration.type,
            mode: declaration.mode,
            declaration
        });
    }

    /**
     * Resolve the nearest local binder first, then the free environment.
     *
     * A local type is weakened beneath the binding itself and every newer
     * local binder. For a lookup at De Bruijn index `i`, this is exactly a
     * shift by `i + 1`.
     */
    lookup(
        name: string,
        occurrenceProvenance?: Provenance
    ): CoreContextLookup | undefined {
        for (let position = this.telescope.length - 1;
            position >= 0;
            position--
        ) {
            const binding = this.telescope[position];
            if (binding.name !== name) continue;

            const index = this.telescope.length - position - 1;
            return Object.freeze({
                kind: 'local',
                name,
                term: kernelBound(
                    index,
                    occurrenceProvenance ?? binding.provenance
                ),
                type: kernelShift(binding.type, index + 1),
                mode: binding.mode,
                index,
                binding
            });
        }

        return this.lookupDeclaration(name, occurrenceProvenance);
    }

    resolve(
        name: string,
        occurrenceProvenance: Provenance
    ): CoreContextLookup {
        const result = this.lookup(name, occurrenceProvenance);
        if (result) return result;
        throw new CoreContextError(
            'UNBOUND_NAME',
            occurrenceProvenance,
            `Unbound Core name '${name}'`
        );
    }

    assertScoped(expression: KernelExpression): void {
        validateExpressionScope(
            expression,
            this.depth,
            this.environment,
            'ILL_SCOPED_EXPRESSION',
            'Core expression'
        );
    }

    /**
     * Abstract this telescope over a body currently valid at `depth`.
     */
    abstractPi(body: KernelExpression): KernelExpression {
        this.assertScoped(body);
        let result: KernelExpression = body;
        for (let index = this.telescope.length - 1; index >= 0; index--) {
            const binding = this.telescope[index];
            result = kernelPi(
                kernelBinder(
                    binding.name,
                    binding.type,
                    binding.mode,
                    binding.provenance
                ),
                result,
                binding.provenance
            );
        }
        return result;
    }

    /**
     * Abstract this telescope as nested lambdas over a scoped body.
     */
    abstractLambda(body: KernelExpression): KernelExpression {
        this.assertScoped(body);
        let result: KernelExpression = body;
        for (let index = this.telescope.length - 1; index >= 0; index--) {
            const binding = this.telescope[index];
            result = kernelLambda(
                kernelBinder(
                    binding.name,
                    binding.type,
                    binding.mode,
                    binding.provenance
                ),
                result,
                binding.provenance
            );
        }
        return result;
    }
}
