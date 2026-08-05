/**
 * Direct-TypeScript outer-LF adjunction declaration macro.
 *
 * The macro is deliberately outside explicit Core and CoreLfModuleSpec. It
 * validates resolved earlier globals, then expands one trusted host command
 * to an ordinary declaration and two ordinary proof-time rules.
 */

import {
    CoreLfQualifiedSymbol,
    CoreLfTransferDeclaration,
    CoreLfTransferExpression,
    CoreLfTransferProofRule,
    CoreLfTransferProvenance,
    CoreLfTransferExternalAvailability,
    coreLfTransferAbsentBody
} from './lf_transfer';

const RESOLVED_GLOBAL = Symbol('CoreLfAdjunctionResolvedGlobal');

const MODULE_ID =
    /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u;
const OUTPUT_NAME = /^[A-Za-z_][A-Za-z0-9_]*$/u;

export type CoreLfAdjunctionMacroErrorCode =
    | 'INVALID_SCOPE'
    | 'INVALID_OWNER_BINDINGS'
    | 'UNAVAILABLE_GLOBAL'
    | 'FOREIGN_GLOBAL'
    | 'FORWARD_GLOBAL'
    | 'DUPLICATE_SYMBOL'
    | 'INVALID_COMMAND'
    | 'TYPE_MISMATCH'
    | 'UNSUPPORTED_EMISSION';

export class CoreLfAdjunctionMacroError extends Error {
    constructor(
        public readonly code: CoreLfAdjunctionMacroErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfAdjunctionMacroError';
    }
}

export interface CoreLfAdjunctionAvailableGlobalInput {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly type: CoreLfTransferExpression;
    readonly availability: CoreLfTransferExternalAvailability;
    /** Required for same-module earlier-fragment globals. */
    readonly order?: number;
}

export interface CoreLfAdjunctionOwnerBindingsInput {
    readonly decode: CoreLfQualifiedSymbol;
    readonly category: CoreLfQualifiedSymbol;
    readonly functor: CoreLfQualifiedSymbol;
    readonly transformation: CoreLfQualifiedSymbol;
    readonly identityFunctor: CoreLfQualifiedSymbol;
    readonly composeFunctors: CoreLfQualifiedSymbol;
    readonly adjunction: CoreLfQualifiedSymbol;
    readonly unitObservation: CoreLfQualifiedSymbol;
    readonly counitObservation: CoreLfQualifiedSymbol;
    readonly trivialConstraint: CoreLfQualifiedSymbol;
}

/** Optional owners needed only by the coherent counit/transpose facade. */
export interface CoreLfAdjunctionTransposeOwnerBindingsInput {
    readonly profunctorCategory: CoreLfQualifiedSymbol;
    readonly profunctorMap: CoreLfQualifiedSymbol;
    readonly homProfunctorAlong: CoreLfQualifiedSymbol;
    readonly defisoForward: CoreLfQualifiedSymbol;
    readonly adjunctionHomComparison: CoreLfQualifiedSymbol;
}

export interface CoreLfResolvedAdjunctionGlobal {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly type: CoreLfTransferExpression;
    readonly availability: CoreLfTransferExternalAvailability;
    readonly order?: number;
    readonly [RESOLVED_GLOBAL]: true;
}

interface InternalResolvedGlobal extends CoreLfResolvedAdjunctionGlobal {
    readonly scopeIdentity: symbol;
}

export interface CoreLfAdjunctionDeclarationCommand {
    readonly kind: 'adjunction-declaration';
    /** First source order occupied by the three-command expansion. */
    readonly order: number;
    readonly name: string;
    readonly sourceCategory: CoreLfResolvedAdjunctionGlobal;
    readonly targetCategory: CoreLfResolvedAdjunctionGlobal;
    readonly leftAdjoint: CoreLfResolvedAdjunctionGlobal;
    readonly rightAdjoint: CoreLfResolvedAdjunctionGlobal;
    readonly unit: CoreLfResolvedAdjunctionGlobal;
    readonly counit: CoreLfResolvedAdjunctionGlobal;
    readonly provenance: CoreLfTransferProvenance;
}

export interface CoreLfCounitTransposeAdjunctionDeclarationCommand {
    readonly kind: 'adjunction-counit-transpose-declaration';
    /** First source order occupied by the three-command expansion. */
    readonly order: number;
    readonly name: string;
    readonly sourceCategory: CoreLfResolvedAdjunctionGlobal;
    readonly targetCategory: CoreLfResolvedAdjunctionGlobal;
    readonly leftAdjoint: CoreLfResolvedAdjunctionGlobal;
    readonly rightAdjoint: CoreLfResolvedAdjunctionGlobal;
    readonly counit: CoreLfResolvedAdjunctionGlobal;
    /** Coherent forward mate Hom_L(F-,-) -> Hom_R(-,G-) as a ProfMap. */
    readonly transpose: CoreLfResolvedAdjunctionGlobal;
    readonly provenance: CoreLfTransferProvenance;
}

/**
 * Direct-TypeScript facade for the outer `adjunction-declaration` entry.
 *
 * This deliberately omits the macro discriminator. Callers supply already
 * resolved globals; `assumeAdjunction` constructs and expands the outer
 * command before anything reaches explicit Core.
 */
export type CoreLfAssumeAdjunctionInput = Omit<
    CoreLfAdjunctionDeclarationCommand,
    'kind'
>;

export type CoreLfAssumeAdjunctionFromCounitTransposeInput = Omit<
    CoreLfCounitTransposeAdjunctionDeclarationCommand,
    'kind'
>;

export interface CoreLfAdjunctionHandle {
    readonly witness: CoreLfQualifiedSymbol;
    readonly witnessTerm: CoreLfTransferExpression;
    readonly unit: CoreLfTransferExpression;
    readonly counit: CoreLfTransferExpression;
    readonly declaredUnit: CoreLfQualifiedSymbol;
    readonly declaredCounit: CoreLfQualifiedSymbol;
    readonly unitAgreementRuleId: string;
    readonly counitAgreementRuleId: string;
}

export interface CoreLfAdjunctionDeclarationExpansion {
    readonly kind: 'expanded-adjunction-declaration';
    readonly sourceOrders: readonly [number, number, number];
    readonly declaration: CoreLfTransferDeclaration;
    readonly proofRules: readonly [
        CoreLfTransferProofRule,
        CoreLfTransferProofRule
    ];
    readonly handle: CoreLfAdjunctionHandle;
    readonly nextOrder: number;
}

export interface CoreLfCounitTransposeAdjunctionHandle {
    readonly witness: CoreLfQualifiedSymbol;
    readonly witnessTerm: CoreLfTransferExpression;
    readonly counit: CoreLfTransferExpression;
    /** Canonical selected `to` map of Adjunction_hom_prof_comparison. */
    readonly transpose: CoreLfTransferExpression;
    readonly declaredCounit: CoreLfQualifiedSymbol;
    readonly declaredTranspose: CoreLfQualifiedSymbol;
    readonly counitAgreementRuleId: string;
    readonly transposeAgreementRuleId: string;
}

export interface CoreLfCounitTransposeAdjunctionDeclarationExpansion {
    readonly kind: 'expanded-adjunction-counit-transpose-declaration';
    readonly sourceOrders: readonly [number, number, number];
    readonly declaration: CoreLfTransferDeclaration;
    readonly proofRules: readonly [
        CoreLfTransferProofRule,
        CoreLfTransferProofRule
    ];
    readonly handle: CoreLfCounitTransposeAdjunctionHandle;
    readonly nextOrder: number;
}

export type CoreLfAnyAdjunctionDeclarationExpansion =
    | CoreLfAdjunctionDeclarationExpansion
    | CoreLfCounitTransposeAdjunctionDeclarationExpansion;

export interface CoreLfAdjunctionLambdapiEmissionOptions {
    readonly backendName: (symbol: CoreLfQualifiedSymbol) => string;
}

const fail = (
    code: CoreLfAdjunctionMacroErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfAdjunctionMacroError(code, path, message);
};

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        Object.freeze(value);
    }
    return value;
};

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const displaySymbol = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}.${symbol.name}`;

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId && left.name === right.name;

const validateSymbol = (
    symbol: CoreLfQualifiedSymbol,
    path: string
): void => {
    if (
        typeof symbol !== 'object' ||
        symbol === null ||
        !MODULE_ID.test(symbol.moduleId) ||
        symbol.name.length === 0 ||
        symbol.name.trim() !== symbol.name ||
        /[\s\u0000-\u001f\u007f]/u.test(symbol.name)
    ) {
        fail(
            'INVALID_SCOPE',
            path,
            'Adjunction macro scope contains an invalid qualified symbol'
        );
    }
};

const cloneSymbol = (
    symbol: CoreLfQualifiedSymbol
): CoreLfQualifiedSymbol => Object.freeze({ ...symbol });

const cloneExpression = (
    expression: CoreLfTransferExpression,
    path: string,
    depth = 0
): CoreLfTransferExpression => {
    switch (expression.tag) {
        case 'type':
            return { tag: 'type' };
        case 'global':
            validateSymbol(expression.symbol, `${path}.symbol`);
            return {
                tag: 'global',
                symbol: { ...expression.symbol }
            };
        case 'bound':
            if (
                !Number.isSafeInteger(expression.index) ||
                expression.index < 0 ||
                expression.index >= depth
            ) {
                return fail(
                    'INVALID_SCOPE',
                    path,
                    'Available global type contains a dangling bound index'
                );
            }
            return { tag: 'bound', index: expression.index };
        case 'call':
            if (expression.arguments.length === 0) {
                return fail(
                    'INVALID_SCOPE',
                    `${path}.arguments`,
                    'Available global type contains an empty call'
                );
            }
            return {
                tag: 'call',
                callee: cloneExpression(
                    expression.callee,
                    `${path}.callee`,
                    depth
                ),
                arguments: expression.arguments.map((argument, index) => {
                    if (
                        argument.plicity !== 'explicit' &&
                        argument.plicity !== 'implicit'
                    ) {
                        return fail(
                            'INVALID_SCOPE',
                            `${path}.arguments[${index}].plicity`,
                            'Available global type has invalid plicity'
                        );
                    }
                    return {
                        plicity: argument.plicity,
                        value: cloneExpression(
                            argument.value,
                            `${path}.arguments[${index}].value`,
                            depth
                        )
                    };
                })
            };
        case 'pi':
        case 'lambda':
            return {
                tag: expression.tag,
                binder: {
                    hint: expression.binder.hint,
                    mode: { ...expression.binder.mode },
                    type: cloneExpression(
                        expression.binder.type,
                        `${path}.binder.type`,
                        depth
                    )
                },
                body: cloneExpression(
                    expression.body,
                    `${path}.body`,
                    depth + 1
                )
            };
        case 'capture':
        case 'wildcard':
            return fail(
                'INVALID_SCOPE',
                path,
                'Available global type cannot contain rule syntax'
            );
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const expressionEquals = (
    left: CoreLfTransferExpression,
    right: CoreLfTransferExpression
): boolean => {
    if (left.tag !== right.tag) return false;
    switch (left.tag) {
        case 'type':
            return true;
        case 'global':
            return right.tag === 'global' &&
                sameSymbol(left.symbol, right.symbol);
        case 'bound':
            return right.tag === 'bound' && left.index === right.index;
        case 'call':
            return right.tag === 'call' &&
                expressionEquals(left.callee, right.callee) &&
                left.arguments.length === right.arguments.length &&
                left.arguments.every((argument, index) =>
                    argument.plicity === right.arguments[index].plicity &&
                    expressionEquals(
                        argument.value,
                        right.arguments[index].value
                    )
                );
        case 'pi':
        case 'lambda':
            return right.tag === left.tag &&
                left.binder.hint === right.binder.hint &&
                left.binder.mode.plicity ===
                    right.binder.mode.plicity &&
                left.binder.mode.variation ===
                    right.binder.mode.variation &&
                expressionEquals(left.binder.type, right.binder.type) &&
                expressionEquals(left.body, right.body);
        case 'capture':
            return right.tag === 'capture' &&
                left.name === right.name &&
                JSON.stringify(left.allowedBoundIndices) ===
                    JSON.stringify(right.allowedBoundIndices);
        case 'wildcard':
            return right.tag === 'wildcard' &&
                (
                    left.checking === undefined
                        ? right.checking === undefined
                        : right.checking !== undefined &&
                            expressionEquals(left.checking, right.checking)
                );
        default: {
            const exhaustive: never = left;
            return exhaustive;
        }
    }
};

const globalExpression = (
    symbol: CoreLfQualifiedSymbol
): CoreLfTransferExpression => ({
    tag: 'global',
    symbol: { ...symbol }
});

const callExpression = (
    symbol: CoreLfQualifiedSymbol,
    arguments_: readonly {
        readonly plicity: 'explicit' | 'implicit';
        readonly value: CoreLfTransferExpression;
    }[]
): CoreLfTransferExpression => ({
    tag: 'call',
    callee: globalExpression(symbol),
    arguments: arguments_.map(argument => ({
        plicity: argument.plicity,
        value: argument.value
    }))
});

const explicit = (value: CoreLfTransferExpression) => ({
    plicity: 'explicit' as const,
    value
});

const implicit = (value: CoreLfTransferExpression) => ({
    plicity: 'implicit' as const,
    value
});

const validateOrder = (order: number, path: string): void => {
    if (!Number.isSafeInteger(order) || order < 0 || order > MAX_ORDER - 2) {
        fail(
            'INVALID_COMMAND',
            path,
            'Adjunction macro order must reserve three safe source ordinals'
        );
    }
};

const MAX_ORDER = Number.MAX_SAFE_INTEGER;

/**
 * Immutable resolution scope for one source position in an outer LF module.
 */
export class CoreLfAdjunctionMacroScope {
    private readonly scopeIdentity = Symbol('CoreLfAdjunctionMacroScope');
    private readonly available = new Map<string, InternalResolvedGlobal>();
    private readonly owners: {
        readonly [Name in keyof CoreLfAdjunctionOwnerBindingsInput]:
            InternalResolvedGlobal;
    };
    private readonly transposeOwners?: {
        readonly [Name in keyof
        CoreLfAdjunctionTransposeOwnerBindingsInput]: InternalResolvedGlobal;
    };

    constructor(
        public readonly moduleId: string,
        availableGlobals: readonly CoreLfAdjunctionAvailableGlobalInput[],
        ownerBindings: CoreLfAdjunctionOwnerBindingsInput,
        transposeOwnerBindings?:
            CoreLfAdjunctionTransposeOwnerBindingsInput
    ) {
        if (!MODULE_ID.test(moduleId)) {
            fail(
                'INVALID_SCOPE',
                'scope.moduleId',
                `Invalid outer module ID '${moduleId}'`
            );
        }
        availableGlobals.forEach((entry, index) => {
            const path = `scope.availableGlobals[${index}]`;
            validateSymbol(entry.symbol, `${path}.symbol`);
            if (
                entry.availability !== 'dependency-module' &&
                entry.availability !== 'existing-core' &&
                entry.availability !== 'earlier-fragment'
            ) {
                fail(
                    'INVALID_SCOPE',
                    `${path}.availability`,
                    'Available global has invalid availability'
                );
            }
            if (
                entry.availability === 'earlier-fragment' &&
                (
                    entry.symbol.moduleId !== moduleId ||
                    entry.order === undefined ||
                    !Number.isSafeInteger(entry.order) ||
                    entry.order < 0
                )
            ) {
                fail(
                    'INVALID_SCOPE',
                    path,
                    'Earlier-fragment global needs a same-module source order'
                );
            }
            if (
                entry.availability !== 'earlier-fragment' &&
                entry.order !== undefined
            ) {
                fail(
                    'INVALID_SCOPE',
                    `${path}.order`,
                    'Only earlier-fragment globals carry source order'
                );
            }
            const key = symbolKey(entry.symbol);
            if (this.available.has(key)) {
                fail(
                    'DUPLICATE_SYMBOL',
                    `${path}.symbol`,
                    `Duplicate available global '${displaySymbol(entry.symbol)}'`
                );
            }
            const resolved: InternalResolvedGlobal = deepFreeze({
                [RESOLVED_GLOBAL]: true as const,
                scopeIdentity: this.scopeIdentity,
                symbol: { ...entry.symbol },
                type: cloneExpression(entry.type, `${path}.type`),
                availability: entry.availability,
                ...(entry.order === undefined ? {} : { order: entry.order })
            });
            this.available.set(key, resolved);
        });

        const resolveOwner = <Name extends keyof
        CoreLfAdjunctionOwnerBindingsInput>(
            name: Name
        ): InternalResolvedGlobal => {
            const symbol = ownerBindings[name];
            validateSymbol(symbol, `scope.ownerBindings.${name}`);
            const resolved = this.available.get(symbolKey(symbol));
            if (resolved === undefined) {
                return fail(
                    'INVALID_OWNER_BINDINGS',
                    `scope.ownerBindings.${name}`,
                    `Owner '${displaySymbol(symbol)}' is not available`
                );
            }
            return resolved;
        };

        this.owners = deepFreeze({
            decode: resolveOwner('decode'),
            category: resolveOwner('category'),
            functor: resolveOwner('functor'),
            transformation: resolveOwner('transformation'),
            identityFunctor: resolveOwner('identityFunctor'),
            composeFunctors: resolveOwner('composeFunctors'),
            adjunction: resolveOwner('adjunction'),
            unitObservation: resolveOwner('unitObservation'),
            counitObservation: resolveOwner('counitObservation'),
            trivialConstraint: resolveOwner('trivialConstraint')
        });
        if (
            transposeOwnerBindings !== undefined &&
            (
                typeof transposeOwnerBindings !== 'object' ||
                transposeOwnerBindings === null
            )
        ) {
            fail(
                'INVALID_OWNER_BINDINGS',
                'scope.transposeOwnerBindings',
                'Transpose owner bindings must be an object'
            );
        }
        if (transposeOwnerBindings !== undefined) {
            const resolveTransposeOwner = <Name extends keyof
            CoreLfAdjunctionTransposeOwnerBindingsInput>(
                name: Name
            ): InternalResolvedGlobal => {
                const symbol = transposeOwnerBindings[name];
                validateSymbol(
                    symbol,
                    `scope.transposeOwnerBindings.${name}`
                );
                const resolved = this.available.get(symbolKey(symbol));
                if (resolved === undefined) {
                    return fail(
                        'INVALID_OWNER_BINDINGS',
                        `scope.transposeOwnerBindings.${name}`,
                        `Owner '${displaySymbol(symbol)}' is not available`
                    );
                }
                return resolved;
            };
            this.transposeOwners = deepFreeze({
                profunctorCategory:
                    resolveTransposeOwner('profunctorCategory'),
                profunctorMap: resolveTransposeOwner('profunctorMap'),
                homProfunctorAlong:
                    resolveTransposeOwner('homProfunctorAlong'),
                defisoForward: resolveTransposeOwner('defisoForward'),
                adjunctionHomComparison:
                    resolveTransposeOwner('adjunctionHomComparison')
            });
        }
        Object.freeze(this);
    }

    resolve(
        symbol: CoreLfQualifiedSymbol
    ): CoreLfResolvedAdjunctionGlobal {
        validateSymbol(symbol, 'resolve.symbol');
        const resolved = this.available.get(symbolKey(symbol));
        if (resolved === undefined) {
            return fail(
                'UNAVAILABLE_GLOBAL',
                'resolve.symbol',
                `Global '${displaySymbol(symbol)}' is not available`
            );
        }
        return resolved;
    }

    private requireHandle(
        value: CoreLfResolvedAdjunctionGlobal,
        path: string,
        commandOrder: number
    ): InternalResolvedGlobal {
        if (
            typeof value !== 'object' ||
            value === null ||
            (value as InternalResolvedGlobal)[RESOLVED_GLOBAL] !== true ||
            (value as InternalResolvedGlobal).scopeIdentity !==
                this.scopeIdentity
        ) {
            return fail(
                'FOREIGN_GLOBAL',
                path,
                'Adjunction input is not a global resolved in this scope'
            );
        }
        const resolved = value as InternalResolvedGlobal;
        if (
            resolved.availability === 'earlier-fragment' &&
            resolved.order !== undefined &&
            resolved.order >= commandOrder
        ) {
            return fail(
                'FORWARD_GLOBAL',
                path,
                `Global '${displaySymbol(resolved.symbol)}' occurs at ` +
                    `source order ${resolved.order}, not before ` +
                    commandOrder
            );
        }
        return resolved;
    }

    private callOwner(
        owner: keyof CoreLfAdjunctionOwnerBindingsInput,
        arguments_: readonly {
            readonly plicity: 'explicit' | 'implicit';
            readonly value: CoreLfTransferExpression;
        }[]
    ): CoreLfTransferExpression {
        return callExpression(this.owners[owner].symbol, arguments_);
    }

    private requireTransposeOwners(): NonNullable<
    CoreLfAdjunctionMacroScope['transposeOwners']> {
        if (this.transposeOwners === undefined) {
            return fail(
                'INVALID_OWNER_BINDINGS',
                'scope.transposeOwnerBindings',
                'Counit/transpose declarations require profunctor owners'
            );
        }
        return this.transposeOwners;
    }

    private callTransposeOwner(
        owner: keyof CoreLfAdjunctionTransposeOwnerBindingsInput,
        arguments_: readonly {
            readonly plicity: 'explicit' | 'implicit';
            readonly value: CoreLfTransferExpression;
        }[]
    ): CoreLfTransferExpression {
        const owners = this.requireTransposeOwners();
        return callExpression(owners[owner].symbol, arguments_);
    }

    private decoded(classifier: CoreLfTransferExpression):
    CoreLfTransferExpression {
        return this.callOwner('decode', [explicit(classifier)]);
    }

    private functorType(
        source: CoreLfTransferExpression,
        target: CoreLfTransferExpression
    ): CoreLfTransferExpression {
        return this.decoded(this.callOwner('functor', [
            explicit(source),
            explicit(target)
        ]));
    }

    private identityFunctor(
        category: CoreLfTransferExpression
    ): CoreLfTransferExpression {
        return this.callOwner('identityFunctor', [implicit(category)]);
    }

    private composeFunctors(
        source: CoreLfTransferExpression,
        middle: CoreLfTransferExpression,
        target: CoreLfTransferExpression,
        outer: CoreLfTransferExpression,
        inner: CoreLfTransferExpression
    ): CoreLfTransferExpression {
        return this.callOwner('composeFunctors', [
            implicit(source),
            implicit(middle),
            implicit(target),
            explicit(outer),
            explicit(inner)
        ]);
    }

    private transformationType(
        sourceCategory: CoreLfTransferExpression,
        targetCategory: CoreLfTransferExpression,
        sourceFunctor: CoreLfTransferExpression,
        targetFunctor: CoreLfTransferExpression
    ): CoreLfTransferExpression {
        return this.decoded(this.callOwner('transformation', [
            implicit(sourceCategory),
            implicit(targetCategory),
            explicit(sourceFunctor),
            explicit(targetFunctor)
        ]));
    }

    private homProfunctorAlong(
        leftBase: CoreLfTransferExpression,
        rightBase: CoreLfTransferExpression,
        ambient: CoreLfTransferExpression,
        leftEndpoint: CoreLfTransferExpression,
        rightEndpoint: CoreLfTransferExpression
    ): CoreLfTransferExpression {
        return this.callTransposeOwner('homProfunctorAlong', [
            implicit(leftBase),
            implicit(rightBase),
            implicit(ambient),
            explicit(leftEndpoint),
            explicit(rightEndpoint)
        ]);
    }

    private profunctorMapType(
        leftBase: CoreLfTransferExpression,
        rightBase: CoreLfTransferExpression,
        source: CoreLfTransferExpression,
        target: CoreLfTransferExpression
    ): CoreLfTransferExpression {
        return this.decoded(this.callTransposeOwner('profunctorMap', [
            implicit(leftBase),
            implicit(rightBase),
            explicit(source),
            explicit(target)
        ]));
    }

    private assertType(
        actual: InternalResolvedGlobal,
        expected: CoreLfTransferExpression,
        path: string,
        description: string
    ): void {
        if (!expressionEquals(actual.type, expected)) {
            fail(
                'TYPE_MISMATCH',
                path,
                `${description} '${displaySymbol(actual.symbol)}' has the ` +
                    'wrong canonical explicit type'
            );
        }
    }

    /**
     * Assume a rectangular adjunction and return its atomic explicit-LF
     * expansion. This is the intended host API; `expand` remains the generic
     * outer-command dispatch point.
     */
    assumeAdjunction(
        input: CoreLfAssumeAdjunctionInput
    ): CoreLfAdjunctionDeclarationExpansion {
        return this.expand({
            ...input,
            kind: 'adjunction-declaration'
        });
    }

    /**
     * Assume the same ordinary adjunction from a whole counit and a coherent
     * forward mate. The supplied transpose is required to be a ProfMap, so
     * its naturality/higher action is part of the already declared input.
     */
    assumeAdjunctionFromCounitTranspose(
        input: CoreLfAssumeAdjunctionFromCounitTransposeInput
    ): CoreLfCounitTransposeAdjunctionDeclarationExpansion {
        return this.expandCounitTranspose({
            ...input,
            kind: 'adjunction-counit-transpose-declaration'
        });
    }

    expand(
        command: CoreLfAdjunctionDeclarationCommand
    ): CoreLfAdjunctionDeclarationExpansion {
        if (
            typeof command !== 'object' ||
            command === null ||
            command.kind !== 'adjunction-declaration'
        ) {
            return fail(
                'INVALID_COMMAND',
                'command.kind',
                'Expected an adjunction-declaration command'
            );
        }
        validateOrder(command.order, 'command.order');
        if (
            typeof command.name !== 'string' ||
            !OUTPUT_NAME.test(command.name)
        ) {
            fail(
                'INVALID_COMMAND',
                'command.name',
                `Invalid generated adjunction name '${command.name}'`
            );
        }
        if (
            typeof command.provenance !== 'object' ||
            command.provenance === null ||
            typeof command.provenance.authorityPath !== 'string' ||
            typeof command.provenance.sourceFragment !== 'string' ||
            command.provenance.authorityPath.length === 0 ||
            command.provenance.sourceFragment.length === 0 ||
            (
                command.provenance.canonicalCommandOrdinal !== undefined &&
                (
                    !Number.isSafeInteger(
                        command.provenance.canonicalCommandOrdinal
                    ) ||
                    command.provenance.canonicalCommandOrdinal < 0
                )
            )
        ) {
            fail(
                'INVALID_COMMAND',
                'command.provenance',
                'Adjunction command provenance cannot be empty'
            );
        }
        const witness: CoreLfQualifiedSymbol = {
            moduleId: this.moduleId,
            name: command.name
        };
        if (this.available.has(symbolKey(witness))) {
            fail(
                'DUPLICATE_SYMBOL',
                'command.name',
                `Global '${displaySymbol(witness)}' already exists`
            );
        }

        const sourceCategory = this.requireHandle(
            command.sourceCategory,
            'command.sourceCategory',
            command.order
        );
        const targetCategory = this.requireHandle(
            command.targetCategory,
            'command.targetCategory',
            command.order
        );
        const leftAdjoint = this.requireHandle(
            command.leftAdjoint,
            'command.leftAdjoint',
            command.order
        );
        const rightAdjoint = this.requireHandle(
            command.rightAdjoint,
            'command.rightAdjoint',
            command.order
        );
        const unit = this.requireHandle(
            command.unit,
            'command.unit',
            command.order
        );
        const counit = this.requireHandle(
            command.counit,
            'command.counit',
            command.order
        );

        const source = globalExpression(sourceCategory.symbol);
        const target = globalExpression(targetCategory.symbol);
        const left = globalExpression(leftAdjoint.symbol);
        const right = globalExpression(rightAdjoint.symbol);
        const unitTerm = globalExpression(unit.symbol);
        const counitTerm = globalExpression(counit.symbol);
        const categoryType = globalExpression(this.owners.category.symbol);

        this.assertType(
            sourceCategory,
            categoryType,
            'command.sourceCategory',
            'Source category'
        );
        this.assertType(
            targetCategory,
            categoryType,
            'command.targetCategory',
            'Target category'
        );
        this.assertType(
            leftAdjoint,
            this.functorType(source, target),
            'command.leftAdjoint',
            'Left adjoint'
        );
        this.assertType(
            rightAdjoint,
            this.functorType(target, source),
            'command.rightAdjoint',
            'Right adjoint'
        );

        const rightAfterLeft = this.composeFunctors(
            source,
            target,
            source,
            right,
            left
        );
        const leftAfterRight = this.composeFunctors(
            target,
            source,
            target,
            left,
            right
        );
        this.assertType(
            unit,
            this.transformationType(
                source,
                source,
                this.identityFunctor(source),
                rightAfterLeft
            ),
            'command.unit',
            'Unit'
        );
        this.assertType(
            counit,
            this.transformationType(
                target,
                target,
                leftAfterRight,
                this.identityFunctor(target)
            ),
            'command.counit',
            'Counit'
        );

        const witnessTerm = globalExpression(witness);
        const adjunctionClassifier = this.callOwner('adjunction', [
            implicit(source),
            implicit(target),
            explicit(left),
            explicit(right)
        ]);
        const witnessType = this.decoded(adjunctionClassifier);
        const canonicalUnit = this.callOwner('unitObservation', [
            implicit(source),
            implicit(target),
            implicit(left),
            implicit(right),
            explicit(witnessTerm)
        ]);
        const canonicalCounit = this.callOwner('counitObservation', [
            implicit(source),
            implicit(target),
            implicit(left),
            implicit(right),
            explicit(witnessTerm)
        ]);
        const trivial = globalExpression(
            this.owners.trivialConstraint.symbol
        );
        const unitAgreementRuleId =
            `adjunction.${command.name}.unit-agreement`;
        const counitAgreementRuleId =
            `adjunction.${command.name}.counit-agreement`;
        const provenance: CoreLfTransferProvenance = {
            ...command.provenance
        };

        const declaration: CoreLfTransferDeclaration = {
            order: command.order,
            symbol: witness,
            type: witnessType,
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public',
                rigidity: 'constant',
                sourceOpacity: 'opaque'
            },
            provenance
        };
        const proofRules: readonly [
            CoreLfTransferProofRule,
            CoreLfTransferProofRule
        ] = [
            {
                order: command.order + 1,
                id: unitAgreementRuleId,
                sourceOwner: this.owners.unitObservation.symbol,
                variables: [],
                problem: {
                    left: canonicalUnit,
                    right: unitTerm
                },
                generatedConstraints: [{
                    left: trivial,
                    right: trivial
                }],
                provenance
            },
            {
                order: command.order + 2,
                id: counitAgreementRuleId,
                sourceOwner: this.owners.counitObservation.symbol,
                variables: [],
                problem: {
                    left: canonicalCounit,
                    right: counitTerm
                },
                generatedConstraints: [{
                    left: trivial,
                    right: trivial
                }],
                provenance
            }
        ];

        return deepFreeze({
            kind: 'expanded-adjunction-declaration' as const,
            sourceOrders: [
                command.order,
                command.order + 1,
                command.order + 2
            ] as const,
            declaration,
            proofRules,
            handle: {
                witness,
                witnessTerm,
                unit: canonicalUnit,
                counit: canonicalCounit,
                declaredUnit: unit.symbol,
                declaredCounit: counit.symbol,
                unitAgreementRuleId,
                counitAgreementRuleId
            },
            nextOrder: command.order + 3
        });
    }

    expandCounitTranspose(
        command: CoreLfCounitTransposeAdjunctionDeclarationCommand
    ): CoreLfCounitTransposeAdjunctionDeclarationExpansion {
        if (
            typeof command !== 'object' ||
            command === null ||
            command.kind !== 'adjunction-counit-transpose-declaration'
        ) {
            return fail(
                'INVALID_COMMAND',
                'command.kind',
                'Expected an adjunction-counit-transpose-declaration command'
            );
        }
        const transposeOwners = this.requireTransposeOwners();
        validateOrder(command.order, 'command.order');
        if (
            typeof command.name !== 'string' ||
            !OUTPUT_NAME.test(command.name)
        ) {
            fail(
                'INVALID_COMMAND',
                'command.name',
                `Invalid generated adjunction name '${command.name}'`
            );
        }
        if (
            typeof command.provenance !== 'object' ||
            command.provenance === null ||
            typeof command.provenance.authorityPath !== 'string' ||
            typeof command.provenance.sourceFragment !== 'string' ||
            command.provenance.authorityPath.length === 0 ||
            command.provenance.sourceFragment.length === 0 ||
            (
                command.provenance.canonicalCommandOrdinal !== undefined &&
                (
                    !Number.isSafeInteger(
                        command.provenance.canonicalCommandOrdinal
                    ) ||
                    command.provenance.canonicalCommandOrdinal < 0
                )
            )
        ) {
            fail(
                'INVALID_COMMAND',
                'command.provenance',
                'Adjunction command provenance cannot be empty'
            );
        }
        const witness: CoreLfQualifiedSymbol = {
            moduleId: this.moduleId,
            name: command.name
        };
        if (this.available.has(symbolKey(witness))) {
            fail(
                'DUPLICATE_SYMBOL',
                'command.name',
                `Global '${displaySymbol(witness)}' already exists`
            );
        }

        const sourceCategory = this.requireHandle(
            command.sourceCategory,
            'command.sourceCategory',
            command.order
        );
        const targetCategory = this.requireHandle(
            command.targetCategory,
            'command.targetCategory',
            command.order
        );
        const leftAdjoint = this.requireHandle(
            command.leftAdjoint,
            'command.leftAdjoint',
            command.order
        );
        const rightAdjoint = this.requireHandle(
            command.rightAdjoint,
            'command.rightAdjoint',
            command.order
        );
        const counit = this.requireHandle(
            command.counit,
            'command.counit',
            command.order
        );
        const transpose = this.requireHandle(
            command.transpose,
            'command.transpose',
            command.order
        );

        const source = globalExpression(sourceCategory.symbol);
        const target = globalExpression(targetCategory.symbol);
        const left = globalExpression(leftAdjoint.symbol);
        const right = globalExpression(rightAdjoint.symbol);
        const counitTerm = globalExpression(counit.symbol);
        const transposeTerm = globalExpression(transpose.symbol);
        const categoryType = globalExpression(this.owners.category.symbol);

        this.assertType(
            sourceCategory,
            categoryType,
            'command.sourceCategory',
            'Source category'
        );
        this.assertType(
            targetCategory,
            categoryType,
            'command.targetCategory',
            'Target category'
        );
        this.assertType(
            leftAdjoint,
            this.functorType(source, target),
            'command.leftAdjoint',
            'Left adjoint'
        );
        this.assertType(
            rightAdjoint,
            this.functorType(target, source),
            'command.rightAdjoint',
            'Right adjoint'
        );

        const leftAfterRight = this.composeFunctors(
            target,
            source,
            target,
            left,
            right
        );
        this.assertType(
            counit,
            this.transformationType(
                target,
                target,
                leftAfterRight,
                this.identityFunctor(target)
            ),
            'command.counit',
            'Counit'
        );

        const sourceHom = this.homProfunctorAlong(
            source,
            target,
            target,
            left,
            this.identityFunctor(target)
        );
        const targetHom = this.homProfunctorAlong(
            source,
            target,
            source,
            this.identityFunctor(source),
            right
        );
        this.assertType(
            transpose,
            this.profunctorMapType(source, target, sourceHom, targetHom),
            'command.transpose',
            'Forward transpose'
        );

        const witnessTerm = globalExpression(witness);
        const adjunctionClassifier = this.callOwner('adjunction', [
            implicit(source),
            implicit(target),
            explicit(left),
            explicit(right)
        ]);
        const witnessType = this.decoded(adjunctionClassifier);
        const canonicalCounit = this.callOwner('counitObservation', [
            implicit(source),
            implicit(target),
            implicit(left),
            implicit(right),
            explicit(witnessTerm)
        ]);
        const comparison = this.callTransposeOwner(
            'adjunctionHomComparison',
            [
                implicit(source),
                implicit(target),
                implicit(left),
                implicit(right),
                explicit(witnessTerm)
            ]
        );
        const profunctorCategory = this.callTransposeOwner(
            'profunctorCategory',
            [explicit(source), explicit(target)]
        );
        // Explicit Core retains all arguments. The narrow Lambdapi lowering
        // deliberately re-infers these first three implicit slots because
        // exact endpoint syntax is too rigid for this unification-rule head.
        const canonicalTranspose = this.callTransposeOwner(
            'defisoForward',
            [
                implicit(profunctorCategory),
                implicit(sourceHom),
                implicit(targetHom),
                explicit(comparison)
            ]
        );
        const trivial = globalExpression(
            this.owners.trivialConstraint.symbol
        );
        const counitAgreementRuleId =
            `adjunction.${command.name}.counit-agreement`;
        const transposeAgreementRuleId =
            `adjunction.${command.name}.transpose-agreement`;
        const provenance: CoreLfTransferProvenance = {
            ...command.provenance
        };

        const declaration: CoreLfTransferDeclaration = {
            order: command.order,
            symbol: witness,
            type: witnessType,
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public',
                rigidity: 'constant',
                sourceOpacity: 'opaque'
            },
            provenance
        };
        const proofRules: readonly [
            CoreLfTransferProofRule,
            CoreLfTransferProofRule
        ] = [
            {
                order: command.order + 1,
                id: counitAgreementRuleId,
                sourceOwner: this.owners.counitObservation.symbol,
                variables: [],
                problem: {
                    left: canonicalCounit,
                    right: counitTerm
                },
                generatedConstraints: [{
                    left: trivial,
                    right: trivial
                }],
                provenance
            },
            {
                order: command.order + 2,
                id: transposeAgreementRuleId,
                sourceOwner: transposeOwners.defisoForward.symbol,
                variables: [],
                problem: {
                    left: canonicalTranspose,
                    right: transposeTerm
                },
                generatedConstraints: [{
                    left: trivial,
                    right: trivial
                }],
                provenance
            }
        ];

        return deepFreeze({
            kind: 'expanded-adjunction-counit-transpose-declaration' as const,
            sourceOrders: [
                command.order,
                command.order + 1,
                command.order + 2
            ] as const,
            declaration,
            proofRules,
            handle: {
                witness,
                witnessTerm,
                counit: canonicalCounit,
                transpose: canonicalTranspose,
                declaredCounit: counit.symbol,
                declaredTranspose: transpose.symbol,
                counitAgreementRuleId,
                transposeAgreementRuleId
            },
            nextOrder: command.order + 3
        });
    }
}

const serializeExpression = (
    expression: CoreLfTransferExpression,
    options: CoreLfAdjunctionLambdapiEmissionOptions,
    asArgument = false
): string => {
    switch (expression.tag) {
        case 'type':
            return 'TYPE';
        case 'global': {
            const name = options.backendName(expression.symbol);
            if (
                name.length === 0 ||
                name.trim() !== name ||
                /[\s\u0000-\u001f\u007f]/u.test(name)
            ) {
                return fail(
                    'UNSUPPORTED_EMISSION',
                    `backendName(${displaySymbol(expression.symbol)})`,
                    'Lambdapi backend name is empty or contains whitespace'
                );
            }
            return name;
        }
        case 'call': {
            if (expression.callee.tag !== 'global') {
                return fail(
                    'UNSUPPORTED_EMISSION',
                    'expression.callee',
                    'Adjunction emission requires a global call head'
                );
            }
            const head = serializeExpression(
                expression.callee,
                options
            );
            const explicitHead = expression.arguments.some(
                argument => argument.plicity === 'implicit'
            ) ? `@${head}` : head;
            const body = [
                explicitHead,
                ...expression.arguments.map(argument =>
                    serializeExpression(argument.value, options, true)
                )
            ].join(' ');
            return asArgument ? `(${body})` : body;
        }
        case 'bound':
        case 'pi':
        case 'lambda':
        case 'capture':
        case 'wildcard':
            return fail(
                'UNSUPPORTED_EMISSION',
                'expression',
                `Adjunction fragment cannot emit '${expression.tag}'`
            );
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const serializeProofRuleLeft = (
    expansion: CoreLfAnyAdjunctionDeclarationExpansion,
    rule: CoreLfTransferProofRule,
    index: number,
    options: CoreLfAdjunctionLambdapiEmissionOptions
): string => {
    if (
        expansion.kind !==
            'expanded-adjunction-counit-transpose-declaration' ||
        index !== 1
    ) {
        return serializeExpression(rule.problem.left, options);
    }
    const left = rule.problem.left;
    if (
        left.tag !== 'call' ||
        left.callee.tag !== 'global' ||
        !sameSymbol(left.callee.symbol, rule.sourceOwner) ||
        left.arguments.length !== 4 ||
        left.arguments[0].plicity !== 'implicit' ||
        left.arguments[1].plicity !== 'implicit' ||
        left.arguments[2].plicity !== 'implicit' ||
        left.arguments[3].plicity !== 'explicit'
    ) {
        return fail(
            'UNSUPPORTED_EMISSION',
            'expansion.proofRules[1].problem.left',
            'Transpose agreement needs explicit-Core defiso_to shape'
        );
    }
    const head = serializeExpression(left.callee, options);
    const comparison = serializeExpression(
        left.arguments[3].value,
        options,
        true
    );
    return `${head} ${comparison}`;
};

/** Deterministically serialize only the three generated Lambdapi commands. */
export function emitCoreLfAdjunctionLambdapiFragment(
    expansion: CoreLfAnyAdjunctionDeclarationExpansion,
    options: CoreLfAdjunctionLambdapiEmissionOptions
): string {
    if (
        (
            expansion.kind !== 'expanded-adjunction-declaration' &&
            expansion.kind !==
                'expanded-adjunction-counit-transpose-declaration'
        ) ||
        expansion.proofRules.length !== 2
    ) {
        return fail(
            'UNSUPPORTED_EMISSION',
            'expansion',
            'Expected one complete adjunction expansion'
        );
    }
    const declarationName = options.backendName(
        expansion.declaration.symbol
    );
    if (!OUTPUT_NAME.test(declarationName)) {
        return fail(
            'UNSUPPORTED_EMISSION',
            'expansion.declaration.symbol',
            `Invalid generated Lambdapi symbol name '${declarationName}'`
        );
    }
    const lines = [
        `constant symbol ${declarationName} : ` +
            `${serializeExpression(expansion.declaration.type, options)};`,
        '',
        ...expansion.proofRules.flatMap((rule, index) => [
            `unif_rule ${serializeProofRuleLeft(
                expansion,
                rule,
                index,
                options
            )} ` +
                `≡ ${serializeExpression(rule.problem.right, options)} ` +
                `↪ [ ` +
                rule.generatedConstraints.map(constraint =>
                    `${serializeExpression(constraint.left, options)} ≡ ` +
                    serializeExpression(constraint.right, options)
                ).join('; ') +
                ' ];',
            ...(index === expansion.proofRules.length - 1 ? [] : [''])
        ])
    ];
    return `${lines.join('\n')}\n`;
}
