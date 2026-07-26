/**
 * Generic compiled-module exposition boundary for SCALE-MODULE-VISIBILITY-1.
 *
 * A provider keeps its complete checked environment so public transparent
 * definitions may continue reducing through protected implementation
 * dependencies. A consumer receives a separate immutable interface:
 *
 * - public declarations may be referenced in ordinary terms;
 * - protected declarations may only occur inside an external runtime-rule
 *   pattern (the local source owner remains the root); and
 * - private declarations are never externally referenceable.
 *
 * Existing intrinsic Core-owner links do not require a compiled dependency
 * interface. Ordinary free declarations from a dependency module do.
 */

import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferVisibility
} from './lf_transfer';
import type {
    CoreLfCompiledDeclaration,
    CoreLfCompiledDeclarationModule,
    CoreLfTransferDeclarationLink
} from './lf_transfer_compiler';
import {
    KernelExpression,
    kernelExpressionEquals
} from './kernel';

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const displaySymbol = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}.${symbol.name}`;

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId &&
    left.name === right.name;

const sameLink = (
    left: CoreLfTransferDeclarationLink,
    right: CoreLfTransferDeclarationLink
): boolean => {
    if (left.kind !== right.kind) return false;
    if (left.kind === 'core-owner') {
        return right.kind === 'core-owner' &&
            left.owner === right.owner;
    }
    return right.kind === 'free-declaration' &&
        left.coreName === right.coreName &&
        left.backendName === right.backendName;
};

const cloneLink = (
    link: CoreLfTransferDeclarationLink
): CoreLfTransferDeclarationLink =>
    link.kind === 'core-owner'
        ? Object.freeze({
            order: link.order,
            symbol: Object.freeze({ ...link.symbol }),
            kind: link.kind,
            owner: link.owner
        })
        : Object.freeze({
            order: link.order,
            symbol: Object.freeze({ ...link.symbol }),
            kind: link.kind,
            coreName: link.coreName,
            backendName: link.backendName
        });

export interface CoreLfCompiledModuleInterfaceEntry {
    readonly symbol: CoreLfQualifiedSymbol;
    readonly visibility: CoreLfTransferVisibility;
    readonly link: CoreLfTransferDeclarationLink;
    readonly status: CoreLfCompiledDeclaration['status'];
    readonly type: KernelExpression;
}

/**
 * A checked provider artifact plus its immutable source-level exposition map.
 *
 * The full provider environment is intentionally retained behind the
 * interface. Filtering the environment itself would make a public
 * transparent definition unable to reduce through its protected closure.
 */
export class CoreLfCompiledModuleInterface {
    readonly moduleId: string;
    readonly providerRevisions: readonly string[];
    readonly fragmentIds: readonly string[];
    readonly entries: readonly CoreLfCompiledModuleInterfaceEntry[];

    private constructor(
        public readonly providers:
            readonly CoreLfCompiledDeclarationModule[],
        entries: readonly CoreLfCompiledModuleInterfaceEntry[]
    ) {
        this.moduleId = providers[0].module.moduleId;
        this.providerRevisions = Object.freeze(
            providers.map(provider => provider.module.revision)
        );
        this.fragmentIds = Object.freeze(
            providers.map(provider => provider.module.fragmentId)
        );
        this.entries = Object.freeze(entries.map(entry => Object.freeze({
            symbol: Object.freeze({ ...entry.symbol }),
            visibility: entry.visibility,
            link: cloneLink(entry.link),
            status: entry.status,
            type: entry.type
        })));
        Object.freeze(this);
    }

    static fromCompiled(
        providerOrProviders:
            CoreLfCompiledDeclarationModule |
            readonly CoreLfCompiledDeclarationModule[]
    ): CoreLfCompiledModuleInterface {
        const providers: readonly CoreLfCompiledDeclarationModule[] =
            Array.isArray(providerOrProviders)
                ? [
                    ...providerOrProviders as
                        readonly CoreLfCompiledDeclarationModule[]
                ]
                : [
                    providerOrProviders as
                        CoreLfCompiledDeclarationModule
                ];
        if (providers.length === 0) {
            throw new CoreLfModuleVisibilityError(
                'INVALID_MODULE_INTERFACE',
                'providers',
                'A compiled module interface requires at least one provider'
            );
        }
        const moduleId = providers[0].module.moduleId;
        const seen = new Set<string>();
        const entries = providers.flatMap((provider, providerIndex) => {
            if (provider.module.moduleId !== moduleId) {
                throw new CoreLfModuleVisibilityError(
                    'INVALID_MODULE_INTERFACE',
                    `providers[${providerIndex}]`,
                    'One compiled module interface cannot combine different ' +
                        'source modules'
                );
            }
            const sourceBySymbol = new Map(
                provider.module.declarations.map(declaration => [
                    symbolKey(declaration.symbol),
                    declaration
                ] as const)
            );
            return provider.declarations.map(declaration => {
                const key = symbolKey(declaration.symbol);
                const source = sourceBySymbol.get(key);
                if (source === undefined) {
                    throw new CoreLfModuleVisibilityError(
                        'INVALID_MODULE_INTERFACE',
                        `providers[${providerIndex}].declarations`,
                        `Compiled provider has no source declaration for ` +
                            `'${displaySymbol(declaration.symbol)}'`
                    );
                }
                if (seen.has(key)) {
                    throw new CoreLfModuleVisibilityError(
                        'INVALID_MODULE_INTERFACE',
                        `providers[${providerIndex}].declarations`,
                        `Compiled module interface duplicates ` +
                            `'${displaySymbol(declaration.symbol)}'`
                    );
                }
                seen.add(key);
                return {
                    symbol: declaration.symbol,
                    visibility: source.modifiers.visibility,
                    link: declaration.link,
                    status: declaration.status,
                    type: declaration.type
                };
            });
        });
        return new CoreLfCompiledModuleInterface(
            Object.freeze(providers),
            entries
        );
    }

    declaration(
        symbol: CoreLfQualifiedSymbol
    ): CoreLfCompiledModuleInterfaceEntry | undefined {
        return this.entries.find(entry =>
            sameSymbol(entry.symbol, symbol)
        );
    }

    assertEnvironment(
        environment: CoreLfDeclarationEnvironment
    ): void {
        this.providers.forEach(provider =>
            provider.assertEnvironment(environment)
        );
    }
}

export const createCoreLfCompiledModuleInterface = (
    providerOrProviders:
        CoreLfCompiledDeclarationModule |
        readonly CoreLfCompiledDeclarationModule[]
): CoreLfCompiledModuleInterface =>
    CoreLfCompiledModuleInterface.fromCompiled(providerOrProviders);

export type CoreLfDependencySymbolUse =
    | 'general-term'
    | 'external-runtime-pattern';

export type CoreLfModuleVisibilityErrorCode =
    | 'INVALID_MODULE_INTERFACE'
    | 'MISSING_MODULE_INTERFACE'
    | 'INACCESSIBLE_EXTERNAL_SYMBOL'
    | 'DEPENDENCY_LINK_MISMATCH';

export class CoreLfModuleVisibilityError extends Error {
    constructor(
        public readonly code: CoreLfModuleVisibilityErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfModuleVisibilityError';
    }
}

/**
 * Resolve exact compiled dependency interfaces once, then check every
 * external use through the same source-level exposition policy.
 */
export class CoreLfDependencyAccess {
    private readonly byModule:
        ReadonlyMap<string, CoreLfCompiledModuleInterface>;

    constructor(
        private readonly module: CoreLfModuleSpec,
        interfaces: readonly CoreLfCompiledModuleInterface[]
    ) {
        const byModule = new Map<
            string,
            CoreLfCompiledModuleInterface
        >();
        interfaces.forEach((dependency, index) => {
            if (!module.dependencies.includes(dependency.moduleId)) {
                throw new CoreLfModuleVisibilityError(
                    'INVALID_MODULE_INTERFACE',
                    `dependencyInterfaces[${index}]`,
                    `Compiled interface '${dependency.moduleId}' is not an ` +
                        `import of '${module.moduleId}'`
                );
            }
            if (byModule.has(dependency.moduleId)) {
                throw new CoreLfModuleVisibilityError(
                    'INVALID_MODULE_INTERFACE',
                    `dependencyInterfaces[${index}]`,
                    `Compiled dependency interface '${dependency.moduleId}' ` +
                        `is duplicated`
                );
            }
            byModule.set(dependency.moduleId, dependency);
        });
        this.byModule = byModule;
        Object.freeze(this);
    }

    assertExternal(
        symbol: CoreLfQualifiedSymbol,
        link: CoreLfTransferDeclarationLink,
        environment: CoreLfDeclarationEnvironment,
        use: CoreLfDependencySymbolUse,
        path: string,
        type?: KernelExpression
    ): void {
        const external = this.module.externalSymbols.find(candidate =>
            sameSymbol(candidate.symbol, symbol)
        );
        if (
            external === undefined ||
            external.availability !== 'dependency-module'
        ) {
            return;
        }

        // Intrinsic schemas form the pre-existing Core boundary. They are not
        // free exports of a separately compiled transfer module.
        if (link.kind === 'core-owner') return;

        const dependency = this.byModule.get(symbol.moduleId);
        if (dependency === undefined) {
            throw new CoreLfModuleVisibilityError(
                'MISSING_MODULE_INTERFACE',
                path,
                `Free dependency declaration '${displaySymbol(symbol)}' ` +
                    `requires an exact compiled module interface`
            );
        }
        dependency.assertEnvironment(environment);
        const entry = dependency.declaration(symbol);
        if (
            entry === undefined ||
            entry.status === 'excluded'
        ) {
            throw new CoreLfModuleVisibilityError(
                'INACCESSIBLE_EXTERNAL_SYMBOL',
                path,
                `Dependency module '${symbol.moduleId}' does not expose a ` +
                    `compiled declaration '${symbol.name}'`
            );
        }
        if (
            !sameLink(entry.link, link) ||
            (
                type !== undefined &&
                !kernelExpressionEquals(entry.type, type)
            )
        ) {
            throw new CoreLfModuleVisibilityError(
                'DEPENDENCY_LINK_MISMATCH',
                path,
                `Dependency declaration '${displaySymbol(symbol)}' differs ` +
                    `from its compiled provider interface`
            );
        }

        const permitted =
            entry.visibility === 'public' ||
            (
                entry.visibility === 'protected' &&
                use === 'external-runtime-pattern'
            );
        if (!permitted) {
            throw new CoreLfModuleVisibilityError(
                'INACCESSIBLE_EXTERNAL_SYMBOL',
                path,
                `${entry.visibility[0].toUpperCase()}` +
                    `${entry.visibility.slice(1)} dependency declaration ` +
                    `'${displaySymbol(symbol)}' cannot be used as a ` +
                    (use === 'general-term'
                        ? 'general external term'
                        : 'runtime pattern dependency')
            );
        }
    }
}
