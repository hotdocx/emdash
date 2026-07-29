/**
 * Generic inductive-signature lowering for SCALE-INDUCTIVE-1A.
 *
 * This phase lowers inductive heads and constructors to ordinary LF
 * declarations. Backend-generated eliminators remain explicit withheld
 * identities until their types and computation rules are represented.
 */

import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferExpression,
    CoreLfTransferInductiveBlock,
    CoreLfTransferPolicyClass,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferTelescopeBinder,
    coreLfTransferAbsentBody,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    CoreLfCompiledDeclarationModule,
    CoreLfDeclarationCompilerOptions,
    CoreLfTransferDeclarationLinkage,
    compileCoreLfDeclarations
} from './lf_transfer_compiler';

export type CoreLfInductiveCompilerErrorCode =
    | 'INVALID_INDUCTIVE_INPUT'
    | 'INCOMPLETE_INDUCTIVE_POLICY'
    | 'INVALID_CONSTRUCTOR_RESULT'
    | 'UNTYPED_GENERATED_SYMBOL_REFERENCED'
    | 'FOREIGN_INDUCTIVE_LOWERING';

export class CoreLfInductiveCompilerError extends Error {
    constructor(
        public readonly code: CoreLfInductiveCompilerErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfInductiveCompilerError';
    }
}

export interface CoreLfLoweredInductiveBlock {
    readonly sourceOrder: number;
    readonly symbol: CoreLfQualifiedSymbol;
    readonly headDeclarationOrder: number;
    readonly constructorDeclarationOrders: readonly number[];
    readonly generatedSymbols: readonly CoreLfQualifiedSymbol[];
    readonly referencedUntypedGeneratedSymbols:
        readonly CoreLfQualifiedSymbol[];
}

export interface CoreLfInductiveSignatureLowering {
    readonly revision: string;
    readonly sourceModuleRevision: string;
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
    readonly blocks: readonly CoreLfLoweredInductiveBlock[];
    readonly semanticStatus: 'signature-lowering-only';
    readonly doesNotProvide: readonly [
        'strict-positivity-validation',
        'generated-eliminator-types',
        'generated-computation-rules',
        'induction-semantics',
        'implicit-native-TYPE-parameter-encoding',
        'active-semantic-policy'
    ];
}

const fail = (
    code: CoreLfInductiveCompilerErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfInductiveCompilerError(code, path, message);
};

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean =>
    left.moduleId === right.moduleId && left.name === right.name;

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

const wrapTelescope = (
    binders: readonly CoreLfTransferTelescopeBinder[],
    body: CoreLfTransferExpression
): CoreLfTransferExpression =>
    binders.reduceRight<CoreLfTransferExpression>(
        (currentBody, binder) => ({
            tag: 'pi',
            binder: {
                hint: binder.hint,
                mode: binder.mode,
                type: binder.type
            },
            body: currentBody
        }),
        body
    );

interface ResultApplication {
    readonly head: CoreLfQualifiedSymbol;
    readonly arguments: readonly {
        readonly plicity: 'explicit' | 'implicit';
        readonly value: CoreLfTransferExpression;
    }[];
}

const resultApplication = (
    expression: CoreLfTransferExpression,
    path: string
): ResultApplication => {
    if (expression.tag === 'global') {
        return {
            head: expression.symbol,
            arguments: []
        };
    }
    if (
        expression.tag === 'call' &&
        expression.callee.tag === 'global'
    ) {
        return {
            head: expression.callee.symbol,
            arguments: expression.arguments
        };
    }
    return fail(
        'INVALID_CONSTRUCTOR_RESULT',
        path,
        'Constructor result must have its inductive symbol as a rigid head'
    );
};

const validateConstructorResult = (
    block: CoreLfTransferInductiveBlock,
    constructorIndex: number
): void => {
    const constructor = block.constructors[constructorIndex];
    const path =
        `inductives.${block.symbol.name}.constructors[` +
        `${constructorIndex}].result`;
    const result = resultApplication(constructor.result, path);
    if (!sameSymbol(result.head, block.symbol)) {
        return fail(
            'INVALID_CONSTRUCTOR_RESULT',
            path,
            `Constructor '${constructor.symbol.name}' returns ` +
                `'${result.head.moduleId}.${result.head.name}' instead of ` +
                `'${block.symbol.moduleId}.` +
                `${block.symbol.name}'`
        );
    }

    const expectedBinders = [
        ...block.parameters,
        ...block.indices
    ];
    if (result.arguments.length !== expectedBinders.length) {
        return fail(
            'INVALID_CONSTRUCTOR_RESULT',
            path,
            `Constructor '${constructor.symbol.name}' applies its head to ` +
                `${result.arguments.length} arguments, expected ` +
                expectedBinders.length
        );
    }
    expectedBinders.forEach((binder, index) => {
        if (result.arguments[index].plicity !== binder.mode.plicity) {
            fail(
                'INVALID_CONSTRUCTOR_RESULT',
                `${path}.arguments[${index}].plicity`,
                `Constructor result plicity does not match ` +
                    `'${binder.hint}'`
            );
        }
    });

    block.parameters.forEach((parameter, index) => {
        const value = result.arguments[index].value;
        const expectedIndex =
            constructor.binders.length +
            block.parameters.length -
            index -
            1;
        if (
            value.tag !== 'bound' ||
            value.index !== expectedIndex
        ) {
            fail(
                'INVALID_CONSTRUCTOR_RESULT',
                `${path}.arguments[${index}].value`,
                `Constructor result must pass parameter ` +
                    `'${parameter.hint}' unchanged at bound index ` +
                    expectedIndex
            );
        }
    });
};

const inductivePolicies = (
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay
): ReadonlyMap<string, CoreLfTransferPolicyClass> => {
    if (
        policy.moduleRevision !== module.revision ||
        policy.moduleId !== module.moduleId ||
        policy.fragmentId !== module.fragmentId
    ) {
        return fail(
            'INVALID_INDUCTIVE_INPUT',
            'policy',
            'Inductive policy targets a foreign transfer module'
        );
    }
    const selected = new Map<string, CoreLfTransferPolicyClass>();
    policy.entries.forEach((entry, index) => {
        if (entry.target.kind !== 'inductive') return;
        const key = symbolKey(entry.target.symbol);
        if (selected.has(key)) {
            fail(
                'INCOMPLETE_INDUCTIVE_POLICY',
                `policy.entries[${index}]`,
                'Inductive policy contains a duplicate block target'
            );
        }
        selected.set(key, entry.policy);
    });
    const missing = module.inductives.filter(
        block => !selected.has(symbolKey(block.symbol))
    );
    if (
        missing.length > 0 ||
        selected.size !== module.inductives.length
    ) {
        return fail(
            'INCOMPLETE_INDUCTIVE_POLICY',
            'policy.entries',
            'Inductive lowering requires exactly one policy for every block'
        );
    }
    return selected;
};

/**
 * Lower every inductive block in one mixed or phase-pure module to a
 * declaration-only signature fragment.
 *
 * Generated symbols are retained as withheld evidence, not invented as
 * declarations. The returned ordinary declaration fragment can be compiled
 * by the existing generic declaration compiler.
 */
export function lowerCoreLfInductiveSignatures(
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay
): CoreLfInductiveSignatureLowering {
    if (module.inductives.length === 0) {
        return fail(
            'INVALID_INDUCTIVE_INPUT',
            'module.inductives',
            'Inductive lowering requires at least one block'
        );
    }
    const policies = inductivePolicies(module, policy);
    const generatedKeys = new Set(
        module.inductives.flatMap(block =>
            block.generatedSymbols.map(symbolKey)
        )
    );
    const referencedGenerated = new Set(
        module.referencedSymbols
            .map(symbolKey)
            .filter(key => generatedKeys.has(key))
    );

    let declarationOrder = 0;
    const declarations = [];
    const entries = [];
    const blocks: CoreLfLoweredInductiveBlock[] = [];

    module.inductives.forEach((block, blockIndex) => {
        block.constructors.forEach((_constructor, constructorIndex) =>
            validateConstructorResult(block, constructorIndex)
        );
        const selectedPolicy = policies.get(symbolKey(block.symbol));
        if (selectedPolicy === undefined) {
            return fail(
                'INCOMPLETE_INDUCTIVE_POLICY',
                `module.inductives[${blockIndex}]`,
                'Inductive block has no selected policy'
            );
        }

        const headDeclarationOrder = declarationOrder++;
        declarations.push({
            order: headDeclarationOrder,
            symbol: block.symbol,
            type: wrapTelescope(
                [...block.parameters, ...block.indices],
                block.sort
            ),
            body: coreLfTransferAbsentBody(),
            modifiers: block.modifiers,
            provenance: block.provenance
        });
        entries.push({
            order: entries.length,
            target: {
                kind: 'declaration' as const,
                symbol: block.symbol
            },
            policy: selectedPolicy,
            evidence:
                `Inductive signature head lowered from source order ` +
                block.order
        });

        const constructorDeclarationOrders: number[] = [];
        block.constructors.forEach(constructor => {
            const order = declarationOrder++;
            constructorDeclarationOrders.push(order);
            const constructorParameters = block.parameters.map(
                (parameter, parameterIndex) => ({
                    ...parameter,
                    mode:
                        constructor.parameterModes?.[parameterIndex] ??
                        parameter.mode
                })
            );
            declarations.push({
                order,
                symbol: constructor.symbol,
                type: wrapTelescope(
                    [
                        ...constructorParameters,
                        ...constructor.binders
                    ],
                    constructor.result
                ),
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: block.modifiers.visibility,
                    rigidity: 'injective' as const,
                    sourceOpacity: 'opaque' as const,
                    generatedBy: block.symbol
                },
                provenance: constructor.provenance
            });
            entries.push({
                order: entries.length,
                target: {
                    kind: 'declaration' as const,
                    symbol: constructor.symbol
                },
                policy: selectedPolicy,
                evidence:
                    `Inductive constructor lowered from source order ` +
                    block.order
            });
        });

        blocks.push({
            sourceOrder: block.order,
            symbol: block.symbol,
            headDeclarationOrder,
            constructorDeclarationOrders,
            generatedSymbols: block.generatedSymbols,
            referencedUntypedGeneratedSymbols:
                block.generatedSymbols.filter(symbol =>
                    referencedGenerated.has(symbolKey(symbol))
                )
        });
    });

    const provisionalModule = createCoreLfModuleSpec({
        revision: `${module.revision}+inductive-signatures-1`,
        moduleId: module.moduleId,
        fragmentId: `${module.fragmentId}-inductive-signatures`,
        authorityPath: module.authorityPath,
        sourceSha256: module.sourceSha256,
        canonicalExport: module.canonicalExport,
        dependencies: module.dependencies,
        externalSymbols: module.externalSymbols,
        declarations,
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const referencedKeys = new Set(
        provisionalModule.referencedSymbols.map(symbolKey)
    );
    const externalSymbols = module.externalSymbols.filter(
        external => referencedKeys.has(symbolKey(external.symbol))
    );
    const dependencyModules = new Set(
        externalSymbols
            .filter(
                external =>
                    external.availability === 'dependency-module'
            )
            .map(external => external.symbol.moduleId)
    );
    const loweredModule = createCoreLfModuleSpec({
        ...provisionalModule,
        dependencies: module.dependencies.filter(
            dependency => dependencyModules.has(dependency)
        ),
        externalSymbols
    });
    const loweredPolicy = createCoreLfTransferPolicyOverlay(
        loweredModule,
        {
            revision: `${policy.revision}+inductive-signatures-1`,
            moduleRevision: loweredModule.revision,
            entries
        }
    );
    return deepFreeze({
        revision: `${module.revision}+${policy.revision}` +
            '+inductive-signatures-1',
        sourceModuleRevision: module.revision,
        module: loweredModule,
        policy: loweredPolicy,
        blocks,
        semanticStatus: 'signature-lowering-only',
        doesNotProvide: [
            'strict-positivity-validation',
            'generated-eliminator-types',
            'generated-computation-rules',
            'induction-semantics',
            'implicit-native-TYPE-parameter-encoding',
            'active-semantic-policy'
        ]
    });
}

/**
 * Compile one previously validated lowering through the existing generic
 * declaration engine.
 */
export function compileCoreLfInductiveSignatures(
    lowering: CoreLfInductiveSignatureLowering,
    linkage: CoreLfTransferDeclarationLinkage,
    options: CoreLfDeclarationCompilerOptions = {}
): CoreLfCompiledDeclarationModule {
    if (
        lowering.sourceModuleRevision.length === 0 ||
        linkage.moduleRevision !== lowering.module.revision ||
        linkage.moduleId !== lowering.module.moduleId ||
        linkage.fragmentId !== lowering.module.fragmentId
    ) {
        return fail(
            'FOREIGN_INDUCTIVE_LOWERING',
            'linkage',
            'Inductive linkage targets a foreign lowered fragment'
        );
    }
    const referenced = lowering.blocks.flatMap(
        block => block.referencedUntypedGeneratedSymbols
    );
    if (referenced.length > 0) {
        return fail(
            'UNTYPED_GENERATED_SYMBOL_REFERENCED',
            'lowering.blocks',
            'Inductive fragment references backend-generated symbols ' +
                'without explicit LF types: ' +
                referenced.map(symbol => symbol.name).join(', ')
        );
    }
    return compileCoreLfDeclarations(
        lowering.module,
        lowering.policy,
        linkage,
        options
    );
}
