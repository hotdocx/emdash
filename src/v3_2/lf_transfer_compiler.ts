/**
 * Generic declaration compiler for the shared SCALE transfer IR.
 *
 * Semantic policy and symbol linkage are explicit inputs. The compiler has
 * no knowledge of emdash owner names: intrinsic Core owners are validated
 * against their existing schemas, while ordinary declarations are installed
 * in one persistent LF environment.
 */

import {
    CoreChecker,
    CoreCheckerConversionResult
} from './checker';
import {
    CoreDeclarationEnvironment
} from './context';
import {
    CoreLfChecker,
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    createCoreLfChecker
} from './lf_checker';
import {
    CoreLfCatalogRuntime,
    CoreLfCombinedNextStep,
    coreLfDefinitionalCompare
} from './lf_conversion';
import {
    CoreLfDeclarationCheckerContext,
    CoreLfDeclarationCheckerFactory,
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferDeclaration,
    CoreLfTransferExpression,
    CoreLfTransferPolicyClass,
    CoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    KernelExpression,
    Provenance,
    assertSafeIdentifier,
    kernelApplication,
    kernelAssertScoped,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    kernelPi,
    kernelUniverse,
    provenance
} from './kernel';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    Plicity
} from './schema';
import {
    coreOwnerSignatureType
} from './signature';
import {
    CoreElaborationSession
} from './session';

export interface CoreLfTransferCoreOwnerLink {
    readonly order: number;
    readonly symbol: CoreLfQualifiedSymbol;
    readonly kind: 'core-owner';
    readonly owner: CoreOwnerId;
}

export interface CoreLfTransferFreeDeclarationLink {
    readonly order: number;
    readonly symbol: CoreLfQualifiedSymbol;
    readonly kind: 'free-declaration';
    readonly coreName: string;
    readonly backendName: string;
}

export type CoreLfTransferDeclarationLink =
    | CoreLfTransferCoreOwnerLink
    | CoreLfTransferFreeDeclarationLink;

export interface CoreLfTransferDeclarationLinkageInput {
    readonly revision: string;
    readonly moduleRevision: string;
    /**
     * Exactly one entry for every local declaration and declared external.
     */
    readonly entries: readonly CoreLfTransferDeclarationLink[];
}

export interface CoreLfTransferDeclarationLinkage
    extends CoreLfTransferDeclarationLinkageInput {
    readonly moduleId: string;
    readonly fragmentId: string;
}

export type CoreLfDeclarationCompilerErrorCode =
    | 'INVALID_LINKAGE'
    | 'INCOMPLETE_LINKAGE'
    | 'INCOMPLETE_POLICY'
    | 'UNSUPPORTED_MODULE_CONTENT'
    | 'UNSUPPORTED_DECLARATION_BODY'
    | 'INCOMPATIBLE_POLICY'
    | 'UNAVAILABLE_SYMBOL'
    | 'INVALID_APPLICATION'
    | 'INTRINSIC_SIGNATURE_MISMATCH'
    | 'DECLARATION_CHECK_FAILED'
    | 'FOREIGN_DECLARATION_ENVIRONMENT';

export class CoreLfDeclarationCompilerError extends Error {
    constructor(
        public readonly code: CoreLfDeclarationCompilerErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(message);
        this.name = 'CoreLfDeclarationCompilerError';
    }
}

export type CoreLfCompiledDeclarationStatus =
    | 'intrinsic-conformance'
    | 'intrinsic-transparent'
    | 'installed-opaque'
    | 'installed-transparent'
    | 'installed-theorem'
    | 'excluded';

export interface CoreLfCompiledDeclaration {
    readonly order: number;
    readonly symbol: CoreLfQualifiedSymbol;
    readonly policy: CoreLfTransferPolicyClass;
    readonly link: CoreLfTransferDeclarationLink;
    readonly status: CoreLfCompiledDeclarationStatus;
    readonly type: KernelExpression;
    readonly body?: KernelExpression;
    readonly provenance: Provenance;
}

export interface CoreLfDeclarationCompilerOptions {
    readonly initialEnvironment?: CoreLfDeclarationEnvironment;
    /**
     * Optional closed runtime used only while checking declaration types and
     * explicit bodies. Rule compilation remains a separate SCALE slice.
     */
    readonly runtimeProgram?: CoreLfCatalogRuntime;
    readonly comparisonStepLimit?: number;
}

const REVISION_ID = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const displaySymbol = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}.${symbol.name}`;

const fail = (
    code: CoreLfDeclarationCompilerErrorCode,
    path: string,
    message: string,
    underlying?: Error
): never => {
    throw new CoreLfDeclarationCompilerError(
        code,
        path,
        message,
        underlying
    );
};

const errorText = (error: unknown): string =>
    error instanceof Error ? error.message : String(error);

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

const cloneSymbol = (
    symbol: CoreLfQualifiedSymbol
): CoreLfQualifiedSymbol => Object.freeze({ ...symbol });

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId &&
    left.name === right.name;

const validateSymbol = (
    symbol: CoreLfQualifiedSymbol,
    path: string
): void => {
    if (
        typeof symbol !== 'object' ||
        symbol === null ||
        !/^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/u
            .test(symbol.moduleId) ||
        symbol.name.length === 0 ||
        symbol.name.trim() !== symbol.name ||
        /[\s\u0000-\u001f\u007f]/u.test(symbol.name)
    ) {
        fail(
            'INVALID_LINKAGE',
            path,
            'Declaration linkage contains an invalid qualified symbol'
        );
    }
};

const validateBackendName = (
    backendName: string,
    path: string
): void => {
    if (
        backendName.length === 0 ||
        backendName.trim() !== backendName ||
        /[\s\u0000-\u001f\u007f]/u.test(backendName)
    ) {
        fail(
            'INVALID_LINKAGE',
            path,
            `Invalid backend declaration name '${backendName}'`
        );
    }
};

/**
 * Validate, clone, and deeply freeze the non-semantic symbol linkage.
 */
export function createCoreLfTransferDeclarationLinkage(
    module: CoreLfModuleSpec,
    input: CoreLfTransferDeclarationLinkageInput
): CoreLfTransferDeclarationLinkage {
    if (!REVISION_ID.test(input.revision)) {
        fail(
            'INVALID_LINKAGE',
            'linkage.revision',
            `Invalid declaration-linkage revision '${input.revision}'`
        );
    }
    if (input.moduleRevision !== module.revision) {
        fail(
            'INVALID_LINKAGE',
            'linkage.moduleRevision',
            'Declaration linkage targets a different module revision'
        );
    }

    const targets = new Map<string, CoreLfQualifiedSymbol>([
        ...module.declarations.map(declaration => [
            symbolKey(declaration.symbol),
            declaration.symbol
        ] as const),
        ...module.externalSymbols.map(external => [
            symbolKey(external.symbol),
            external.symbol
        ] as const)
    ]);
    const seenSymbols = new Set<string>();
    const seenCoreNames = new Set<string>();
    const seenOwners = new Set<CoreOwnerId>();
    let previousOrder = -1;

    const entries = input.entries.map((entry, index) => {
        const path = `linkage.entries[${index}]`;
        if (
            !Number.isSafeInteger(entry.order) ||
            entry.order < 0 ||
            entry.order <= previousOrder
        ) {
            fail(
                'INVALID_LINKAGE',
                `${path}.order`,
                'Declaration linkage entries must be strictly ordered'
            );
        }
        previousOrder = entry.order;
        validateSymbol(entry.symbol, `${path}.symbol`);
        const key = symbolKey(entry.symbol);
        const target = targets.get(key);
        if (target === undefined || !sameSymbol(target, entry.symbol)) {
            fail(
                'INVALID_LINKAGE',
                `${path}.symbol`,
                `Declaration linkage targets unknown symbol ` +
                    `'${displaySymbol(entry.symbol)}'`
            );
        }
        if (seenSymbols.has(key)) {
            fail(
                'INVALID_LINKAGE',
                `${path}.symbol`,
                `Duplicate declaration linkage for ` +
                    `'${displaySymbol(entry.symbol)}'`
            );
        }
        seenSymbols.add(key);

        if (entry.kind === 'core-owner') {
            if (
                !Object.prototype.hasOwnProperty.call(
                    CORE_OWNER_SCHEMAS,
                    entry.owner
                )
            ) {
                fail(
                    'INVALID_LINKAGE',
                    `${path}.owner`,
                    `Unknown intrinsic Core owner '${String(entry.owner)}'`
                );
            }
            if (seenOwners.has(entry.owner)) {
                fail(
                    'INVALID_LINKAGE',
                    `${path}.owner`,
                    `Intrinsic Core owner '${entry.owner}' is linked twice`
                );
            }
            seenOwners.add(entry.owner);
            return Object.freeze({
                order: entry.order,
                symbol: cloneSymbol(entry.symbol),
                kind: entry.kind,
                owner: entry.owner
            });
        }

        if (entry.kind !== 'free-declaration') {
            fail(
                'INVALID_LINKAGE',
                `${path}.kind`,
                `Unsupported declaration linkage kind ` +
                    `'${String(
                        (entry as { readonly kind?: unknown }).kind
                    )}'`
            );
        }
        try {
            assertSafeIdentifier(
                entry.coreName,
                'Linked Core declaration name'
            );
        } catch (error: unknown) {
            fail(
                'INVALID_LINKAGE',
                `${path}.coreName`,
                errorText(error),
                error instanceof Error ? error : undefined
            );
        }
        validateBackendName(entry.backendName, `${path}.backendName`);
        if (seenCoreNames.has(entry.coreName)) {
            fail(
                'INVALID_LINKAGE',
                `${path}.coreName`,
                `Core declaration name '${entry.coreName}' is linked twice`
            );
        }
        seenCoreNames.add(entry.coreName);
        return Object.freeze({
            order: entry.order,
            symbol: cloneSymbol(entry.symbol),
            kind: entry.kind,
            coreName: entry.coreName,
            backendName: entry.backendName
        });
    });

    const missing = [...targets.values()].filter(
        symbol => !seenSymbols.has(symbolKey(symbol))
    );
    if (missing.length > 0) {
        fail(
            'INCOMPLETE_LINKAGE',
            'linkage.entries',
            'Declaration linkage is missing: ' +
                missing.map(displaySymbol).join(', ')
        );
    }
    if (entries.length !== targets.size) {
        fail(
            'INCOMPLETE_LINKAGE',
            'linkage.entries',
            `Declaration linkage contains ${entries.length} entries for ` +
                `${targets.size} symbols`
        );
    }

    return deepFreeze({
        revision: input.revision,
        moduleRevision: input.moduleRevision,
        moduleId: module.moduleId,
        fragmentId: module.fragmentId,
        entries
    });
}

const formatNextStep = (next: CoreLfCombinedNextStep): string => {
    switch (next.kind) {
        case 'zonk':
            return 'transfer declaration zonk step';
        case 'beta':
            return `transfer declaration beta step ` +
                `(${next.argumentPlicity})`;
        case 'delta':
            return `transfer declaration delta step ` +
                `'${next.declarationName}'`;
        case 'runtime':
            return `transfer declaration runtime rule '${next.ruleId}'`;
        default: {
            const exhaustive: never = next;
            return exhaustive;
        }
    }
};

/**
 * Generic checker for directly transferred declarations. It deliberately
 * receives a closed runtime component rather than a registration surface.
 */
class CoreLfTransferDeclarationChecker extends CoreChecker {
    constructor(
        environment: CoreDeclarationEnvironment,
        private readonly deltaEnvironment:
            CoreLfDeclarationEnvironment,
        private readonly runtimeProgram?: CoreLfCatalogRuntime
    ) {
        super(new CoreElaborationSession(environment));
    }

    protected permitsAnnotatedLambdaInference(): boolean {
        return true;
    }

    protected conversionDiagnosticName(): string {
        return 'Transferred Core LF declaration conversion';
    }

    protected compareDefinitions(
        left: KernelExpression,
        right: KernelExpression,
        stepLimit: number
    ): CoreCheckerConversionResult {
        const result = coreLfDefinitionalCompare(
            this.deltaEnvironment,
            left,
            right,
            stepLimit,
            undefined,
            this.runtimeProgram
        );
        if (result.status === 'step-limit-exceeded') {
            return {
                status: 'step-limit-exceeded',
                path: result.path,
                nextStep: formatNextStep(result.next)
            };
        }
        return { status: result.status };
    }
}

export const createCoreLfTransferDeclarationCheckerFactory = (
    runtimeProgram?: CoreLfCatalogRuntime
): CoreLfDeclarationCheckerFactory =>
    (
        environment: CoreDeclarationEnvironment,
        context: CoreLfDeclarationCheckerContext
    ) => new CoreLfTransferDeclarationChecker(
        environment,
        context.lfEnvironment,
        runtimeProgram
    );

interface CompilationState {
    readonly links: ReadonlyMap<string, CoreLfTransferDeclarationLink>;
    readonly availableSymbols: ReadonlySet<string>;
    readonly compiledBySymbol:
        ReadonlyMap<string, CoreLfCompiledDeclaration>;
}

const expressionProvenance = (
    declaration: CoreLfTransferDeclaration,
    path: string
): Provenance => deepFreeze(provenance(
    'recovered',
    `transfer ${displaySymbol(declaration.symbol)} ${path} from ` +
        `${declaration.provenance.authorityPath}: ` +
        declaration.provenance.sourceFragment
));

const leadingPiPlicities = (
    type: KernelExpression
): readonly Plicity[] => {
    const result: Plicity[] = [];
    let current = type;
    while (current.tag === 'pi') {
        result.push(current.binder.mode.plicity);
        current = current.body;
    }
    return result;
};

const compileExpression = (
    expression: CoreLfTransferExpression,
    declaration: CoreLfTransferDeclaration,
    path: string,
    state: CompilationState
): KernelExpression => {
    const nodeProvenance = expressionProvenance(declaration, path);
    const compile = (
        child: CoreLfTransferExpression,
        childPath: string
    ): KernelExpression => compileExpression(
        child,
        declaration,
        childPath,
        state
    );

    switch (expression.tag) {
        case 'type':
            return deepFreeze(kernelUniverse(nodeProvenance));
        case 'bound':
            return deepFreeze(kernelBound(
                expression.index,
                nodeProvenance
            ));
        case 'capture':
        case 'wildcard':
            return fail(
                'UNSUPPORTED_DECLARATION_BODY',
                path,
                `Declaration compilation cannot lower '${expression.tag}'`
            );
        case 'global': {
            const key = symbolKey(expression.symbol);
            const link = state.links.get(key);
            if (
                link === undefined ||
                !state.availableSymbols.has(key)
            ) {
                return fail(
                    'UNAVAILABLE_SYMBOL',
                    path,
                    `Declaration expression refers to unavailable symbol ` +
                        `'${displaySymbol(expression.symbol)}'`
                );
            }
            if (link.kind === 'free-declaration') {
                return deepFreeze(kernelFree(
                    link.coreName,
                    nodeProvenance
                ));
            }
            const schema = CORE_OWNER_SCHEMAS[link.owner];
            if (schema.slots.length !== 0) {
                return fail(
                    'INVALID_APPLICATION',
                    path,
                    `Intrinsic owner '${link.owner}' requires ` +
                        `${schema.slots.length} arguments`
                );
            }
            return deepFreeze(kernelApplication(
                link.owner,
                [],
                nodeProvenance
            ));
        }
        case 'call': {
            if (expression.callee.tag === 'global') {
                const key = symbolKey(expression.callee.symbol);
                const link = state.links.get(key);
                if (
                    link === undefined ||
                    !state.availableSymbols.has(key)
                ) {
                    return fail(
                        'UNAVAILABLE_SYMBOL',
                        `${path}.callee`,
                        `Declaration call refers to unavailable symbol ` +
                            `'${displaySymbol(
                                expression.callee.symbol
                            )}'`
                    );
                }
                const arguments_ = expression.arguments.map(
                    (argument, index) => ({
                        plicity: argument.plicity,
                        value: compile(
                            argument.value,
                            `${path}.arguments[${index}].value`
                        )
                    })
                );
                if (link.kind === 'core-owner') {
                    const schema = CORE_OWNER_SCHEMAS[link.owner];
                    if (arguments_.length !== schema.slots.length) {
                        return fail(
                            'INVALID_APPLICATION',
                            path,
                            `Intrinsic owner '${link.owner}' expects ` +
                                `${schema.slots.length} arguments, received ` +
                                arguments_.length
                        );
                    }
                    arguments_.forEach((argument, index) => {
                        if (
                            argument.plicity !==
                            schema.slots[index].plicity
                        ) {
                            fail(
                                'INVALID_APPLICATION',
                                `${path}.arguments[${index}].plicity`,
                                `Intrinsic owner '${link.owner}' argument ` +
                                    `${index} must be ` +
                                    schema.slots[index].plicity
                            );
                        }
                    });
                    return deepFreeze(kernelApplication(
                        link.owner,
                        arguments_.map(argument => ({
                            value: argument.value
                        })),
                        nodeProvenance
                    ));
                }

                const earlier = state.compiledBySymbol.get(key);
                const declarationType = earlier?.type;
                if (declarationType !== undefined) {
                    const plicities =
                        leadingPiPlicities(declarationType);
                    if (arguments_.length > plicities.length) {
                        return fail(
                            'INVALID_APPLICATION',
                            path,
                            `Free declaration '${link.coreName}' receives ` +
                                `${arguments_.length} arguments but its ` +
                                `signature exposes ${plicities.length}`
                        );
                    }
                    arguments_.forEach((argument, index) => {
                        if (argument.plicity !== plicities[index]) {
                            fail(
                                'INVALID_APPLICATION',
                                `${path}.arguments[${index}].plicity`,
                                `Free declaration '${link.coreName}' ` +
                                    `argument ${index} must be ` +
                                    plicities[index]
                            );
                        }
                    });
                }
                return deepFreeze(kernelCall(
                    kernelFree(link.coreName, nodeProvenance),
                    arguments_,
                    nodeProvenance
                ));
            }

            return deepFreeze(kernelCall(
                compile(expression.callee, `${path}.callee`),
                expression.arguments.map((argument, index) => ({
                    plicity: argument.plicity,
                    value: compile(
                        argument.value,
                        `${path}.arguments[${index}].value`
                    )
                })),
                nodeProvenance
            ));
        }
        case 'pi':
        case 'lambda': {
            const binderType = compile(
                expression.binder.type,
                `${path}.binder.type`
            );
            const binder = deepFreeze(kernelBinder(
                expression.binder.hint,
                binderType,
                expression.binder.mode,
                nodeProvenance
            ));
            const body = compile(expression.body, `${path}.body`);
            return deepFreeze(
                expression.tag === 'pi'
                    ? kernelPi(binder, body, nodeProvenance)
                    : kernelLambda(binder, body, nodeProvenance)
            );
        }
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const policyKey = (symbol: CoreLfQualifiedSymbol): string =>
    `declaration:${symbolKey(symbol)}`;

const policyMap = (
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay
): ReadonlyMap<string, CoreLfTransferPolicyClass> => {
    if (
        policy.moduleRevision !== module.revision ||
        policy.moduleId !== module.moduleId ||
        policy.fragmentId !== module.fragmentId
    ) {
        return fail(
            'INCOMPLETE_POLICY',
            'policy',
            'Declaration policy targets a foreign transfer module'
        );
    }
    const result = new Map<string, CoreLfTransferPolicyClass>();
    policy.entries.forEach((entry, index) => {
        if (entry.target.kind !== 'declaration') {
            return fail(
                'INCOMPLETE_POLICY',
                `policy.entries[${index}].target`,
                'Declaration compiler accepts declaration policies only'
            );
        }
        const key = policyKey(entry.target.symbol);
        if (result.has(key)) {
            fail(
                'INCOMPLETE_POLICY',
                `policy.entries[${index}].target`,
                `Duplicate declaration policy for ` +
                    `'${displaySymbol(entry.target.symbol)}'`
            );
        }
        result.set(key, entry.policy);
    });
    const missing = module.declarations.filter(
        declaration => !result.has(policyKey(declaration.symbol))
    );
    if (
        missing.length > 0 ||
        result.size !== module.declarations.length
    ) {
        return fail(
            'INCOMPLETE_POLICY',
            'policy.entries',
            'Declaration policy must cover every declaration exactly once' +
                (missing.length === 0
                    ? ''
                    : `; missing ${missing.map(declaration =>
                        displaySymbol(declaration.symbol)
                    ).join(', ')}`)
        );
    }
    return result;
};

const compilerStatus = (
    policy: CoreLfTransferPolicyClass,
    link: CoreLfTransferDeclarationLink
): CoreLfCompiledDeclarationStatus => {
    switch (policy) {
        case 'conformance-only':
            return 'intrinsic-conformance';
        case 'opaque-signature':
            return 'installed-opaque';
        case 'checked-transparent-definition':
            return link.kind === 'core-owner'
                ? 'intrinsic-transparent'
                : 'installed-transparent';
        case 'theorem-body':
            return 'installed-theorem';
        case 'excluded':
            return 'excluded';
        case 'runtime-rewrite':
        case 'proof-unification':
            return fail(
                'INCOMPATIBLE_POLICY',
                'policy',
                `Policy '${policy}' cannot target a declaration`
            );
        default: {
            const exhaustive: never = policy;
            return exhaustive;
        }
    }
};

const assertPolicyBody = (
    declaration: CoreLfTransferDeclaration,
    policy: CoreLfTransferPolicyClass,
    link: CoreLfTransferDeclarationLink,
    path: string
): void => {
    switch (policy) {
        case 'conformance-only':
            if (
                link.kind !== 'core-owner' ||
                declaration.body.kind !== 'absent'
            ) {
                fail(
                    'INCOMPATIBLE_POLICY',
                    path,
                    'Conformance-only declarations must be body-free ' +
                        'intrinsic Core-owner links'
                );
            }
            return;
        case 'opaque-signature':
            if (
                link.kind !== 'free-declaration' ||
                declaration.body.kind !== 'absent'
            ) {
                fail(
                    'INCOMPATIBLE_POLICY',
                    path,
                    'Opaque signatures must be body-free free declarations'
                );
            }
            return;
        case 'checked-transparent-definition':
            if (
                declaration.body.kind !== 'explicit-term' ||
                declaration.modifiers.sourceOpacity !== 'transparent'
            ) {
                fail(
                    'INCOMPATIBLE_POLICY',
                    path,
                    'Checked transparent definitions require a transparent ' +
                        'explicit term and a Core-owner or free-declaration ' +
                        'link'
                );
            }
            return;
        case 'theorem-body':
            if (
                link.kind !== 'free-declaration' ||
                declaration.body.kind !== 'explicit-term'
            ) {
                fail(
                    'INCOMPATIBLE_POLICY',
                    path,
                    'Theorem bodies require an explicit term and a ' +
                        'free-declaration link'
                );
            }
            return;
        case 'excluded':
            return;
        case 'runtime-rewrite':
        case 'proof-unification':
            return fail(
                'INCOMPATIBLE_POLICY',
                path,
                `Policy '${policy}' cannot target a declaration`
            );
        default: {
            const exhaustive: never = policy;
            return exhaustive;
        }
    }
};

const freezeCompiledDeclaration = (
    declaration: CoreLfCompiledDeclaration
): CoreLfCompiledDeclaration => deepFreeze({
    ...declaration,
    symbol: { ...declaration.symbol },
    link: {
        ...declaration.link,
        symbol: { ...declaration.link.symbol }
    }
});

/**
 * Immutable result of one generic declaration compilation.
 */
export class CoreLfCompiledDeclarationModule {
    constructor(
        public readonly module: CoreLfModuleSpec,
        public readonly policy: CoreLfTransferPolicyOverlay,
        public readonly linkage: CoreLfTransferDeclarationLinkage,
        public readonly environment: CoreLfDeclarationEnvironment,
        public readonly declarations: readonly CoreLfCompiledDeclaration[],
        public readonly externalFreeReferences:
            Readonly<Record<string, string>>,
        public readonly externalTransparentDefinitions:
            Readonly<Record<string, string>>,
        public readonly initialDeclarationCount: number,
        private readonly runtimeProgram?: CoreLfCatalogRuntime,
        public readonly comparisonStepLimit =
            CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
    ) {
        this.declarations = Object.freeze(
            declarations.map(freezeCompiledDeclaration)
        );
        this.externalFreeReferences = Object.freeze({
            ...externalFreeReferences
        });
        this.externalTransparentDefinitions = Object.freeze({
            ...externalTransparentDefinitions
        });
        Object.freeze(this);
    }

    declaration(
        symbol: CoreLfQualifiedSymbol
    ): CoreLfCompiledDeclaration | undefined {
        const key = symbolKey(symbol);
        return this.declarations.find(
            declaration => symbolKey(declaration.symbol) === key
        );
    }

    application(
        symbol: CoreLfQualifiedSymbol,
        arguments_: readonly KernelExpression[],
        nodeProvenance: Provenance
    ): KernelExpression {
        const declaration = this.declaration(symbol);
        if (
            declaration === undefined ||
            declaration.status === 'excluded'
        ) {
            return fail(
                'UNAVAILABLE_SYMBOL',
                'application.symbol',
                `Compiled module has no available declaration ` +
                    `'${displaySymbol(symbol)}'`
            );
        }
        const plicities = leadingPiPlicities(declaration.type);
        if (arguments_.length !== plicities.length) {
            return fail(
                'INVALID_APPLICATION',
                'application.arguments',
                `Declaration '${displaySymbol(symbol)}' expects ` +
                    `${plicities.length} arguments, received ` +
                    arguments_.length
            );
        }
        if (declaration.link.kind === 'core-owner') {
            return kernelApplication(
                declaration.link.owner,
                arguments_.map(value => ({ value })),
                nodeProvenance
            );
        }
        return kernelCall(
            kernelFree(declaration.link.coreName, nodeProvenance),
            arguments_.map((value, index) => ({
                plicity: plicities[index],
                value
            })),
            nodeProvenance
        );
    }

    assertEnvironment(
        environment: CoreLfDeclarationEnvironment
    ): void {
        const installed = this.declarations.filter(
            declaration =>
                declaration.status !== 'intrinsic-conformance' &&
                declaration.status !== 'intrinsic-transparent' &&
                declaration.status !== 'excluded'
        );
        if (
            environment.declarations.length <
            this.initialDeclarationCount + installed.length
        ) {
            fail(
                'FOREIGN_DECLARATION_ENVIRONMENT',
                'environment.declarations',
                'Declaration environment is missing compiled declarations'
            );
        }
        installed.forEach(declaration => {
            const link = declaration.link;
            if (link.kind !== 'free-declaration') {
                return fail(
                    'FOREIGN_DECLARATION_ENVIRONMENT',
                    'environment.declarations',
                    'Installed declaration has a non-free linkage'
                );
            }
            const actual = environment.lookup(link.coreName);
            const expectedTransparency =
                declaration.status === 'installed-transparent'
                    ? 'transparent'
                    : 'opaque';
            if (
                actual === undefined ||
                actual.transparency !== expectedTransparency ||
                !kernelExpressionEquals(actual.type, declaration.type) ||
                (
                    declaration.body === undefined
                        ? actual.body !== undefined
                        : actual.body === undefined ||
                            !kernelExpressionEquals(
                                actual.body,
                                declaration.body
                            )
                )
            ) {
                fail(
                    'FOREIGN_DECLARATION_ENVIRONMENT',
                    'environment.declarations',
                    `Environment does not preserve compiled declaration ` +
                        `'${displaySymbol(declaration.symbol)}'`
                );
            }
        });
        this.declarations
            .filter(declaration =>
                declaration.status === 'intrinsic-transparent'
            )
            .forEach(declaration => {
                const link = declaration.link;
                if (link.kind !== 'core-owner') {
                    return fail(
                        'FOREIGN_DECLARATION_ENVIRONMENT',
                        'environment.intrinsicDefinitions',
                        'Intrinsic transparent declaration has a non-owner ' +
                            'linkage'
                    );
                }
                const actual =
                    environment.lookupIntrinsicDefinition(link.owner);
                if (
                    actual === undefined ||
                    !kernelExpressionEquals(
                        actual.type,
                        declaration.type
                    ) ||
                    declaration.body === undefined ||
                    !kernelExpressionEquals(
                        actual.body,
                        declaration.body
                    )
                ) {
                    fail(
                        'FOREIGN_DECLARATION_ENVIRONMENT',
                        'environment.intrinsicDefinitions',
                        `Environment does not preserve intrinsic definition ` +
                            `'${displaySymbol(declaration.symbol)}'`
                    );
                }
            });
    }

    createChecker(
        environment: CoreLfDeclarationEnvironment = this.environment
    ): CoreLfChecker {
        this.assertEnvironment(environment);
        return createCoreLfChecker(
            environment,
            this.comparisonStepLimit,
            this.runtimeProgram
        );
    }
}

/**
 * Compile the declaration-only portion of one transfer module.
 */
export function compileCoreLfDeclarations(
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay,
    linkage: CoreLfTransferDeclarationLinkage,
    options: CoreLfDeclarationCompilerOptions = {}
): CoreLfCompiledDeclarationModule {
    if (
        module.inductives.length > 0 ||
        module.runtimeRules.length > 0 ||
        module.proofRules.length > 0
    ) {
        return fail(
            'UNSUPPORTED_MODULE_CONTENT',
            'module',
            'Declaration compiler refuses inductives, runtime rules, and ' +
                'proof rules; use their separate compiler phases'
        );
    }
    if (
        linkage.moduleRevision !== module.revision ||
        linkage.moduleId !== module.moduleId ||
        linkage.fragmentId !== module.fragmentId
    ) {
        return fail(
            'INVALID_LINKAGE',
            'linkage',
            'Declaration linkage targets a foreign transfer module'
        );
    }

    const policies = policyMap(module, policy);
    const links = new Map(
        linkage.entries.map(link => [symbolKey(link.symbol), link])
    );
    const externalKeys = new Set(
        module.externalSymbols.map(external =>
            symbolKey(external.symbol)
        )
    );
    const availableSymbols = new Set(externalKeys);
    const initialEnvironment =
        options.initialEnvironment ??
        CoreLfDeclarationEnvironment.empty();
    let environment = initialEnvironment;

    for (const external of module.externalSymbols) {
        const link = links.get(symbolKey(external.symbol));
        if (link === undefined) {
            return fail(
                'INCOMPLETE_LINKAGE',
                'linkage.entries',
                `External '${displaySymbol(external.symbol)}' has no link`
            );
        }
        if (
            link.kind === 'free-declaration' &&
            initialEnvironment.lookup(link.coreName) === undefined
        ) {
            return fail(
                'UNAVAILABLE_SYMBOL',
                'module.externalSymbols',
                `External free declaration '${link.coreName}' is absent ` +
                    'from the initial environment'
            );
        }
    }

    const checkerFactory =
        createCoreLfTransferDeclarationCheckerFactory(
            options.runtimeProgram
        );
    const comparisonStepLimit =
        options.comparisonStepLimit ??
        CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT;
    if (
        !Number.isSafeInteger(comparisonStepLimit) ||
        comparisonStepLimit < 0
    ) {
        return fail(
            'DECLARATION_CHECK_FAILED',
            'options.comparisonStepLimit',
            'Declaration comparison budget must be a nonnegative safe integer'
        );
    }

    const compiled: CoreLfCompiledDeclaration[] = [];
    const compiledBySymbol =
        new Map<string, CoreLfCompiledDeclaration>();
    const externalFreeReferences: Record<string, string> = {};
    const externalTransparentDefinitions: Record<string, string> = {};

    for (const declaration of module.declarations) {
        const key = symbolKey(declaration.symbol);
        const path = `module.declarations[${declaration.order}]`;
        const link = links.get(key);
        if (link === undefined) {
            return fail(
                'INCOMPLETE_LINKAGE',
                `${path}.symbol`,
                `Declaration '${displaySymbol(declaration.symbol)}' has no link`
            );
        }
        const selectedPolicy = policies.get(
            policyKey(declaration.symbol)
        );
        if (selectedPolicy === undefined) {
            return fail(
                'INCOMPLETE_POLICY',
                `${path}.symbol`,
                `Declaration '${displaySymbol(declaration.symbol)}' has no ` +
                    'policy'
            );
        }
        assertPolicyBody(
            declaration,
            selectedPolicy,
            link,
            `${path}.body`
        );

        const state: CompilationState = {
            links,
            availableSymbols,
            compiledBySymbol
        };
        const type = compileExpression(
            declaration.type,
            declaration,
            `${path}.type`,
            state
        );
        kernelAssertScoped(type);
        const body = declaration.body.kind === 'explicit-term'
            ? compileExpression(
                declaration.body.term,
                declaration,
                `${path}.body.term`,
                state
            )
            : undefined;
        if (body !== undefined) kernelAssertScoped(body);

        const status = compilerStatus(selectedPolicy, link);
        const nodeProvenance = expressionProvenance(
            declaration,
            'declaration'
        );
        if (
            (
                status === 'intrinsic-conformance' ||
                status === 'intrinsic-transparent'
            ) &&
            link.kind === 'core-owner'
        ) {
            const expected = coreOwnerSignatureType(
                link.owner,
                nodeProvenance
            );
            if (!kernelExpressionEquals(type, expected)) {
                return fail(
                    'INTRINSIC_SIGNATURE_MISMATCH',
                    `${path}.type`,
                    `Transferred signature for intrinsic owner ` +
                        `'${link.owner}' differs from its Core schema`
                );
            }
            if (status === 'intrinsic-transparent') {
                if (body === undefined) {
                    return fail(
                        'DECLARATION_CHECK_FAILED',
                        path,
                        `Intrinsic transparent declaration ` +
                            `'${displaySymbol(declaration.symbol)}' has no body`
                    );
                }
                try {
                    environment = environment.extendIntrinsicDefinition({
                        owner: link.owner,
                        body,
                        provenance: nodeProvenance,
                        declarationName:
                            displaySymbol(declaration.symbol)
                    }, checkerFactory);
                } catch (error: unknown) {
                    return fail(
                        'DECLARATION_CHECK_FAILED',
                        path,
                        `Failed to check transferred intrinsic definition ` +
                            `'${displaySymbol(declaration.symbol)}': ` +
                            errorText(error),
                        error instanceof Error ? error : undefined
                    );
                }
            }
        } else if (
            status !== 'excluded' &&
            link.kind === 'free-declaration'
        ) {
            try {
                environment = environment.extend({
                    name: link.coreName,
                    type,
                    mode: {
                        plicity: 'explicit',
                        variation: 'functorial'
                    },
                    provenance: nodeProvenance,
                    body,
                    transparency:
                        status === 'installed-transparent'
                            ? 'transparent'
                            : 'opaque'
                }, checkerFactory);
            } catch (error: unknown) {
                return fail(
                    'DECLARATION_CHECK_FAILED',
                    path,
                    `Failed to check transferred declaration ` +
                        `'${displaySymbol(declaration.symbol)}': ` +
                        errorText(error),
                    error instanceof Error ? error : undefined
                );
            }
            if (status === 'installed-transparent') {
                externalTransparentDefinitions[link.coreName] =
                    link.backendName;
            } else {
                externalFreeReferences[link.coreName] =
                    link.backendName;
            }
        }

        const result = freezeCompiledDeclaration({
            order: declaration.order,
            symbol: declaration.symbol,
            policy: selectedPolicy,
            link,
            status,
            type,
            body,
            provenance: nodeProvenance
        });
        compiled.push(result);
        compiledBySymbol.set(key, result);
        if (status !== 'excluded') availableSymbols.add(key);
    }

    const result = new CoreLfCompiledDeclarationModule(
        module,
        policy,
        linkage,
        environment,
        compiled,
        externalFreeReferences,
        externalTransparentDefinitions,
        initialEnvironment.declarations.length,
        options.runtimeProgram,
        comparisonStepLimit
    );
    result.assertEnvironment(environment);
    result.createChecker().validateEnvironment();
    return result;
}
