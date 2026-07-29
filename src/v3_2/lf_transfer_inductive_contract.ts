/**
 * Generic explicit generated-owner contracts for inductive transfer.
 *
 * The transfer boundary does not trust a backend-generated name. A reviewed
 * contract explicitly supplies the generated declaration and computation
 * rules, associates them with one represented inductive block, and then
 * delegates checking to the ordinary mixed declaration/runtime compilers.
 *
 * The first reviewed mode is intentionally limited to indexed,
 * nonrecursive blocks. Recursive occurrences and nontrivial strict
 * positivity remain SCALE-INDUCTIVE-1B2.
 */

import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferExpression,
    CoreLfTransferInductiveBlock
} from './lf_transfer';
import {
    CoreLfCompiledMixedModule,
    CoreLfMixedCompileOptions,
    CoreLfMixedDeclarationLinkage,
    CoreLfMixedPhasePlan,
    compileCoreLfMixedPhases
} from './lf_transfer_mixed';

export type CoreLfGeneratedInductiveContractErrorCode =
    | 'INVALID_GENERATED_CONTRACT_INPUT'
    | 'GENERATED_OWNER_NOT_UNIQUE'
    | 'INVALID_GENERATED_DECLARATION'
    | 'INVALID_GENERATED_RULE_OWNERSHIP'
    | 'GENERATED_CLASSIFICATION_DRIFT'
    | 'UNSUPPORTED_GENERATED_RECURSION'
    | 'GENERATED_CONTRACT_COMPILE_DRIFT';

export class CoreLfGeneratedInductiveContractError extends Error {
    constructor(
        public readonly code:
            CoreLfGeneratedInductiveContractErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfGeneratedInductiveContractError';
    }
}

export interface CoreLfGeneratedInductiveContractSpec {
    readonly revision: string;
    readonly sourceModuleRevision: string;
    readonly contractModuleRevision: string;
    readonly block: CoreLfQualifiedSymbol;
    readonly generatedOwner: CoreLfQualifiedSymbol;
    readonly runtimeRuleIds: readonly string[];
    readonly classification: {
        readonly kind: 'nonrecursive-indexed';
        readonly expectedParameterCount: number;
        readonly expectedIndexCount: number;
        readonly expectedConstructorCount: number;
    };
}

export interface CoreLfGeneratedInductiveContractAssociation {
    readonly revision: string;
    readonly sourceModuleRevision: string;
    readonly contractModuleRevision: string;
    readonly contractModuleId: string;
    readonly contractFragmentId: string;
    readonly block: CoreLfQualifiedSymbol;
    readonly generatedOwner: CoreLfQualifiedSymbol;
    readonly generatedDeclarationOrder: number;
    readonly runtimeRuleIds: readonly string[];
    readonly classification: {
        readonly kind: 'nonrecursive-indexed';
        readonly parameterCount: number;
        readonly indexCount: number;
        readonly constructorCount: number;
        readonly recursiveOccurrencePaths: readonly string[];
        readonly strictPositivity: 'trivial-nonrecursive';
    };
    readonly semanticStatus:
        'explicit-generated-owner-contract-associated';
    readonly doesNotProvide: readonly [
        'recursive-inductive-validation',
        'general-strict-positivity',
        'automatic-eliminator-synthesis',
        'end-user-inductive-declaration-facade',
        'active-semantic-policy',
        'browser-api'
    ];
}

export interface CoreLfCompiledGeneratedInductiveContract {
    readonly association: CoreLfGeneratedInductiveContractAssociation;
    readonly compiled: CoreLfCompiledMixedModule;
}

const fail = (
    code: CoreLfGeneratedInductiveContractErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfGeneratedInductiveContractError(
        code,
        path,
        message
    );
};

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const sameSymbol = (
    left: CoreLfQualifiedSymbol,
    right: CoreLfQualifiedSymbol
): boolean => symbolKey(left) === symbolKey(right);

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Reflect.ownKeys(value as object).forEach(key =>
            deepFreeze((value as Record<PropertyKey, unknown>)[key])
        );
        Object.freeze(value);
    }
    return value;
};

const occurrencePaths = (
    expression: CoreLfTransferExpression,
    symbol: CoreLfQualifiedSymbol,
    path: string
): readonly string[] => {
    switch (expression.tag) {
        case 'type':
        case 'bound':
        case 'capture':
            return [];
        case 'global':
            return sameSymbol(expression.symbol, symbol) ? [path] : [];
        case 'call':
            return [
                ...occurrencePaths(
                    expression.callee,
                    symbol,
                    `${path}.callee`
                ),
                ...expression.arguments.flatMap((argument, index) =>
                    occurrencePaths(
                        argument.value,
                        symbol,
                        `${path}.arguments[${index}].value`
                    )
                )
            ];
        case 'pi':
        case 'lambda':
            return [
                ...occurrencePaths(
                    expression.binder.type,
                    symbol,
                    `${path}.binder.type`
                ),
                ...occurrencePaths(
                    expression.body,
                    symbol,
                    `${path}.body`
                )
            ];
        case 'wildcard':
            return expression.checking === undefined
                ? []
                : occurrencePaths(
                    expression.checking,
                    symbol,
                    `${path}.checking`
                );
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const resultOccurrencePaths = (
    block: CoreLfTransferInductiveBlock,
    constructorIndex: number
): readonly string[] => {
    const result = block.constructors[constructorIndex].result;
    const path =
        `sourceModule.inductives.${block.symbol.name}.constructors[` +
        `${constructorIndex}].result`;
    if (
        result.tag === 'call' &&
        result.callee.tag === 'global' &&
        sameSymbol(result.callee.symbol, block.symbol)
    ) {
        return result.arguments.flatMap((argument, index) =>
            occurrencePaths(
                argument.value,
                block.symbol,
                `${path}.arguments[${index}].value`
            )
        );
    }
    if (
        result.tag === 'global' &&
        sameSymbol(result.symbol, block.symbol)
    ) {
        return [];
    }
    return occurrencePaths(result, block.symbol, path);
};

const recursiveOccurrencePaths = (
    block: CoreLfTransferInductiveBlock
): readonly string[] => [
    ...block.parameters.flatMap((binder, index) =>
        occurrencePaths(
            binder.type,
            block.symbol,
            `sourceModule.inductives.${block.symbol.name}.` +
                `parameters[${index}].type`
        )
    ),
    ...block.indices.flatMap((binder, index) =>
        occurrencePaths(
            binder.type,
            block.symbol,
            `sourceModule.inductives.${block.symbol.name}.` +
                `indices[${index}].type`
        )
    ),
    ...block.constructors.flatMap((constructor, constructorIndex) => [
        ...constructor.binders.flatMap((binder, binderIndex) =>
            occurrencePaths(
                binder.type,
                block.symbol,
                `sourceModule.inductives.${block.symbol.name}.` +
                    `constructors[${constructorIndex}].` +
                    `binders[${binderIndex}].type`
            )
        ),
        ...resultOccurrencePaths(block, constructorIndex)
    ])
];

const exactStrings = (
    left: readonly string[],
    right: readonly string[]
): boolean =>
    left.length === right.length &&
    left.every((value, index) => value === right[index]);

/**
 * Associate one explicit generated declaration/rule contract with exactly
 * one represented inductive block.
 */
export function associateCoreLfGeneratedInductiveContract(
    sourceModule: CoreLfModuleSpec,
    contractModule: CoreLfModuleSpec,
    spec: CoreLfGeneratedInductiveContractSpec
): CoreLfGeneratedInductiveContractAssociation {
    if (
        spec.revision.length === 0 ||
        spec.sourceModuleRevision !== sourceModule.revision ||
        spec.contractModuleRevision !== contractModule.revision ||
        spec.classification.kind !== 'nonrecursive-indexed' ||
        spec.classification.expectedParameterCount < 0 ||
        spec.classification.expectedIndexCount < 1 ||
        spec.classification.expectedConstructorCount < 1
    ) {
        return fail(
            'INVALID_GENERATED_CONTRACT_INPUT',
            'spec',
            'Generated-owner contract revisions or expected counts drifted'
        );
    }

    const owningBlocks = sourceModule.inductives.filter(block =>
        block.generatedSymbols.some(symbol =>
            sameSymbol(symbol, spec.generatedOwner)
        )
    );
    if (
        owningBlocks.length !== 1 ||
        !sameSymbol(owningBlocks[0].symbol, spec.block)
    ) {
        return fail(
            'GENERATED_OWNER_NOT_UNIQUE',
            'spec.generatedOwner',
            `Generated owner '${spec.generatedOwner.name}' must be listed ` +
                'by exactly the selected inductive block'
        );
    }
    const block = owningBlocks[0];
    const generatedDeclarations = contractModule.declarations.filter(
        declaration => sameSymbol(
            declaration.symbol,
            spec.generatedOwner
        )
    );
    const generated = generatedDeclarations[0];
    if (
        generatedDeclarations.length !== 1 ||
        generated.body.kind !== 'absent' ||
        generated.modifiers.rigidity !== 'ordinary' ||
        generated.modifiers.sourceOpacity !== 'opaque' ||
        generated.modifiers.generatedBy === undefined ||
        !sameSymbol(generated.modifiers.generatedBy, block.symbol)
    ) {
        return fail(
            'INVALID_GENERATED_DECLARATION',
            'contractModule.declarations',
            'The explicit generated declaration must be unique, opaque, ' +
                'and linked to its inductive block with generatedBy'
        );
    }
    const linkedDeclarations = contractModule.declarations.filter(
        declaration =>
            declaration.modifiers.generatedBy !== undefined &&
            sameSymbol(
                declaration.modifiers.generatedBy,
                block.symbol
            )
    );
    if (
        linkedDeclarations.length !== 1 ||
        !sameSymbol(
            linkedDeclarations[0].symbol,
            spec.generatedOwner
        )
    ) {
        return fail(
            'INVALID_GENERATED_DECLARATION',
            'contractModule.declarations.modifiers.generatedBy',
            'The contract must link only its explicit generated owner'
        );
    }

    const ownedRuleIds = contractModule.runtimeRules
        .filter(rule => sameSymbol(
            rule.sourceOwner,
            spec.generatedOwner
        ))
        .map(rule => rule.id);
    const selectedRules = spec.runtimeRuleIds.map(id =>
        contractModule.runtimeRules.find(rule => rule.id === id)
    );
    if (
        new Set(spec.runtimeRuleIds).size !==
            spec.runtimeRuleIds.length ||
        selectedRules.some(rule => rule === undefined) ||
        selectedRules.some(rule => !sameSymbol(
            rule!.sourceOwner,
            spec.generatedOwner
        )) ||
        !exactStrings(ownedRuleIds, spec.runtimeRuleIds)
    ) {
        return fail(
            'INVALID_GENERATED_RULE_OWNERSHIP',
            'spec.runtimeRuleIds',
            'Every selected beta must exist, be owned by the generated ' +
                'declaration, and exhaust its contract-local rules'
        );
    }

    const expected = spec.classification;
    if (
        block.parameters.length !== expected.expectedParameterCount ||
        block.indices.length !== expected.expectedIndexCount ||
        block.constructors.length !==
            expected.expectedConstructorCount
    ) {
        return fail(
            'GENERATED_CLASSIFICATION_DRIFT',
            'spec.classification',
            'The represented parameter/index/constructor counts drifted'
        );
    }
    const recursivePaths = recursiveOccurrencePaths(block);
    if (recursivePaths.length > 0) {
        return fail(
            'UNSUPPORTED_GENERATED_RECURSION',
            recursivePaths[0],
            'The 1B1 contract accepts only a nonrecursive indexed block'
        );
    }

    return deepFreeze({
        revision: `${spec.revision}+associated-1`,
        sourceModuleRevision: sourceModule.revision,
        contractModuleRevision: contractModule.revision,
        contractModuleId: contractModule.moduleId,
        contractFragmentId: contractModule.fragmentId,
        block: { ...block.symbol },
        generatedOwner: { ...spec.generatedOwner },
        generatedDeclarationOrder: generated.order,
        runtimeRuleIds: [...spec.runtimeRuleIds],
        classification: {
            kind: 'nonrecursive-indexed',
            parameterCount: block.parameters.length,
            indexCount: block.indices.length,
            constructorCount: block.constructors.length,
            recursiveOccurrencePaths: recursivePaths,
            strictPositivity: 'trivial-nonrecursive'
        },
        semanticStatus:
            'explicit-generated-owner-contract-associated',
        doesNotProvide: [
            'recursive-inductive-validation',
            'general-strict-positivity',
            'automatic-eliminator-synthesis',
            'end-user-inductive-declaration-facade',
            'active-semantic-policy',
            'browser-api'
        ]
    });
}

/**
 * Compile an associated contract through the existing generic mixed-phase
 * declaration/runtime path and fail closed on orchestration drift.
 */
export function compileCoreLfGeneratedInductiveContract(
    association: CoreLfGeneratedInductiveContractAssociation,
    plan: CoreLfMixedPhasePlan,
    linkage: CoreLfMixedDeclarationLinkage,
    options: CoreLfMixedCompileOptions = {}
): CoreLfCompiledGeneratedInductiveContract {
    if (
        plan.sourceModule.revision !==
            association.contractModuleRevision ||
        plan.sourceModule.moduleId !== association.contractModuleId ||
        plan.sourceModule.fragmentId !==
            association.contractFragmentId
    ) {
        return fail(
            'GENERATED_CONTRACT_COMPILE_DRIFT',
            'plan.sourceModule',
            'Mixed plan does not target the associated contract module'
        );
    }
    const compiled = compileCoreLfMixedPhases(
        plan,
        linkage,
        options
    );
    const localDeclaration = compiled.phases.some(phase =>
        phase.kind === 'declaration' &&
        phase.declarations.declaration(
            association.generatedOwner
        ) !== undefined
    );
    if (
        !localDeclaration ||
        compiled.latestRuntime === undefined ||
        !exactStrings(
            compiled.latestRuntime.localProgram.ruleIds,
            association.runtimeRuleIds
        )
    ) {
        return fail(
            'GENERATED_CONTRACT_COMPILE_DRIFT',
            'compiled',
            'Generated declaration or exact local beta program is missing'
        );
    }
    return Object.freeze({
        association,
        compiled
    });
}
