/**
 * Generic source-ordered mixed-phase planning for
 * SCALE-MIXED-PHASE-1A/1B/1C.
 *
 * The planner partitions one shared transfer module into phase-pure
 * fragments and feeds only already reviewed declaration, inductive
 * signature, runtime, and proof compilers. It owns no semantic owner cases
 * and selects no active policy.
 */

import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreLfCatalogRuntime
} from './lf_conversion';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferDeclaration,
    CoreLfTransferExternalSymbol,
    CoreLfTransferInductiveBlock,
    CoreLfTransferPolicyEntry,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferProofRule,
    CoreLfTransferRuntimeRule,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    CoreLfCompiledDeclaration,
    CoreLfCompiledDeclarationModule,
    CoreLfTransferCoreOwnerLink,
    CoreLfTransferDeclarationLink,
    CoreLfTransferDeclarationLinkage,
    compileCoreLfDeclarations,
    createCoreLfTransferDeclarationLinkage
} from './lf_transfer_compiler';
import {
    CoreLfInductiveSignatureLowering,
    compileCoreLfInductiveSignatures,
    lowerCoreLfInductiveSignatures
} from './lf_transfer_inductive';
import {
    CoreLfComposedProofProgram,
    CoreLfCompiledProofProgram,
    CoreLfProofCompilerOptions,
    composeCoreLfProofPrograms,
    compileCoreLfProofProgram
} from './lf_transfer_proof';
import {
    CoreLfCompiledRuntimeFragment,
    CoreLfRuntimeCompilerOptions,
    CoreLfRuntimeFragmentDependency,
    composeCoreLfRuntimeDependencies,
    compileCoreLfRuntimeFragment
} from './lf_transfer_runtime';
import {
    CoreLfCompiledModuleInterface
} from './lf_transfer_visibility';
import { provenance } from './kernel';
import { coreOwnerSignatureType } from './signature';

export type CoreLfMixedPhaseKind =
    | 'declaration'
    | 'inductive-signature'
    | 'runtime'
    | 'proof';

interface CoreLfMixedPhaseBase {
    readonly index: number;
    readonly kind: CoreLfMixedPhaseKind;
    readonly sourceOrders: readonly number[];
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
}

export interface CoreLfMixedDeclarationPhase
extends CoreLfMixedPhaseBase {
    readonly kind: 'declaration';
}

export interface CoreLfMixedInductivePhase
extends CoreLfMixedPhaseBase {
    readonly kind: 'inductive-signature';
    readonly lowering: CoreLfInductiveSignatureLowering;
}

export interface CoreLfMixedRuntimePhase
extends CoreLfMixedPhaseBase {
    readonly kind: 'runtime';
    readonly groupId: string;
    readonly clauseOrders: readonly number[];
}

export interface CoreLfMixedProofPhase
extends CoreLfMixedPhaseBase {
    readonly kind: 'proof';
}

export type CoreLfMixedPhase =
    | CoreLfMixedDeclarationPhase
    | CoreLfMixedInductivePhase
    | CoreLfMixedRuntimePhase
    | CoreLfMixedProofPhase;

export interface CoreLfMixedPhasePlan {
    readonly revision: string;
    readonly sourceModule: CoreLfModuleSpec;
    readonly sourcePolicy: CoreLfTransferPolicyOverlay;
    readonly phases: readonly CoreLfMixedPhase[];
    readonly semanticStatus: 'phase-plan-only';
    readonly doesNotProvide: readonly [
        'active-policy-selection',
        'generated-induction-semantics',
        'implicit-native-TYPE-parameter-encoding',
        'browser-api'
    ];
}

export type CoreLfMixedCompilerErrorCode =
    | 'INVALID_MIXED_INPUT'
    | 'INCOMPLETE_MIXED_POLICY'
    | 'FORWARD_PHASE_REFERENCE'
    | 'SPLIT_RUNTIME_GROUP'
    | 'UNTYPED_GENERATED_SYMBOL_REFERENCED'
    | 'INVALID_MIXED_LINKAGE'
    | 'INVALID_INITIAL_DECLARATIONS'
    | 'INVALID_INITIAL_RUNTIME'
    | 'INVALID_RUNTIME_DEPENDENCY'
    | 'FOREIGN_MIXED_PLAN';

export class CoreLfMixedCompilerError extends Error {
    constructor(
        public readonly code: CoreLfMixedCompilerErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfMixedCompilerError';
    }
}

type SourceEntry =
    | {
        readonly kind: 'declaration';
        readonly order: number;
        readonly declaration: CoreLfTransferDeclaration;
    }
    | {
        readonly kind: 'inductive-signature';
        readonly order: number;
        readonly inductive: CoreLfTransferInductiveBlock;
    }
    | {
        readonly kind: 'runtime';
        readonly order: number;
        readonly runtimeRule: CoreLfTransferRuntimeRule;
    }
    | {
        readonly kind: 'proof';
        readonly order: number;
        readonly proofRule: CoreLfTransferProofRule;
    };

interface Definition {
    readonly order: number;
    readonly symbol: CoreLfQualifiedSymbol;
    readonly availability: 'typed' | 'generated-untyped';
}

const fail = (
    code: CoreLfMixedCompilerErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfMixedCompilerError(code, path, message);
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

const policyTargetKey = (
    entry: CoreLfTransferPolicyEntry
): string => {
    switch (entry.target.kind) {
        case 'declaration':
        case 'inductive':
            return `${entry.target.kind}:` +
                symbolKey(entry.target.symbol);
        case 'runtime-rule':
        case 'proof-rule':
            return `${entry.target.kind}:${entry.target.id}`;
        default: {
            const exhaustive: never = entry.target;
            return exhaustive;
        }
    }
};

const sourceTargetKey = (entry: SourceEntry): string => {
    switch (entry.kind) {
        case 'declaration':
            return 'declaration:' +
                symbolKey(entry.declaration.symbol);
        case 'inductive-signature':
            return 'inductive:' +
                symbolKey(entry.inductive.symbol);
        case 'runtime':
            return `runtime-rule:${entry.runtimeRule.id}`;
        case 'proof':
            return `proof-rule:${entry.proofRule.id}`;
        default: {
            const exhaustive: never = entry;
            return exhaustive;
        }
    }
};

const sourceEntries = (
    module: CoreLfModuleSpec
): readonly SourceEntry[] => Object.freeze([
    ...module.declarations.map(declaration => ({
        kind: 'declaration' as const,
        order: declaration.order,
        declaration
    })),
    ...module.inductives.map(inductive => ({
        kind: 'inductive-signature' as const,
        order: inductive.order,
        inductive
    })),
    ...module.runtimeRules.map(runtimeRule => ({
        kind: 'runtime' as const,
        order: runtimeRule.order,
        runtimeRule
    })),
    ...module.proofRules.map(proofRule => ({
        kind: 'proof' as const,
        order: proofRule.order,
        proofRule
    }))
].sort((left, right) => left.order - right.order));

const definitions = (
    module: CoreLfModuleSpec
): ReadonlyMap<string, Definition> => {
    const result = new Map<string, Definition>();
    const entries: Definition[] = module.declarations.map(declaration => ({
        order: declaration.order,
        symbol: declaration.symbol,
        availability: 'typed'
    }));
    module.inductives.forEach(block => {
        entries.push({
            order: block.order,
            symbol: block.symbol,
            availability: 'typed'
        });
        block.constructors.forEach(constructor => entries.push({
            order: block.order,
            symbol: constructor.symbol,
            availability: 'typed'
        }));
        block.generatedSymbols.forEach(symbol => entries.push({
            order: block.order,
            symbol,
            availability: 'generated-untyped'
        }));
    });
    entries
        .sort((left, right) => left.order - right.order)
        .forEach(definition =>
            result.set(symbolKey(definition.symbol), definition)
        );
    return result;
};

const phaseLocalKeys = (
    entries: readonly SourceEntry[]
): ReadonlySet<string> => {
    const keys = new Set<string>();
    entries.forEach(entry => {
        if (entry.kind === 'declaration') {
            keys.add(symbolKey(entry.declaration.symbol));
        } else if (entry.kind === 'inductive-signature') {
            keys.add(symbolKey(entry.inductive.symbol));
            entry.inductive.constructors.forEach(constructor =>
                keys.add(symbolKey(constructor.symbol))
            );
            entry.inductive.generatedSymbols.forEach(symbol =>
                keys.add(symbolKey(symbol))
            );
        }
    });
    return keys;
};

const samePhase = (
    left: SourceEntry,
    right: SourceEntry
): boolean => {
    if (left.kind !== right.kind) return false;
    switch (left.kind) {
        case 'declaration':
        case 'inductive-signature':
            return false;
        case 'runtime':
            return right.kind === 'runtime' &&
                left.runtimeRule.groupId ===
                    right.runtimeRule.groupId;
        case 'proof':
            return true;
        default: {
            const exhaustive: never = left;
            return exhaustive;
        }
    }
};

const phaseGroups = (
    entries: readonly SourceEntry[]
): readonly (readonly SourceEntry[])[] => {
    const result: SourceEntry[][] = [];
    entries.forEach(entry => {
        const current = result[result.length - 1];
        if (
            current !== undefined &&
            samePhase(current[current.length - 1], entry)
        ) {
            current.push(entry);
        } else {
            result.push([entry]);
        }
    });

    const runtimeGroups = new Map<string, number>();
    result.forEach((group, phaseIndex) => {
        const first = group[0];
        if (first.kind !== 'runtime') return;
        const prior = runtimeGroups.get(first.runtimeRule.groupId);
        if (prior !== undefined) {
            fail(
                'SPLIT_RUNTIME_GROUP',
                `phases[${phaseIndex}]`,
                `Runtime group '${first.runtimeRule.groupId}' is split ` +
                    `between source phases ${prior} and ${phaseIndex}`
            );
        }
        runtimeGroups.set(first.runtimeRule.groupId, phaseIndex);
    });
    return Object.freeze(
        result.map(group => Object.freeze([...group]))
    );
};

const assertExactPolicy = (
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay,
    entries: readonly SourceEntry[]
): ReadonlyMap<string, CoreLfTransferPolicyEntry> => {
    if (
        policy.moduleRevision !== module.revision ||
        policy.moduleId !== module.moduleId ||
        policy.fragmentId !== module.fragmentId
    ) {
        return fail(
            'INCOMPLETE_MIXED_POLICY',
            'policy',
            'Mixed-phase policy targets a foreign module'
        );
    }
    const expected = new Set(entries.map(sourceTargetKey));
    const selected = new Map(
        policy.entries.map(entry => [
            policyTargetKey(entry),
            entry
        ])
    );
    if (
        selected.size !== expected.size ||
        policy.entries.length !== expected.size ||
        [...expected].some(key => !selected.has(key))
    ) {
        return fail(
            'INCOMPLETE_MIXED_POLICY',
            'policy.entries',
            'Mixed-phase planning requires exactly one policy entry for ' +
                'every source item'
        );
    }
    return selected;
};

const preliminaryExternals = (
    module: CoreLfModuleSpec,
    allDefinitions: ReadonlyMap<string, Definition>,
    localKeys: ReadonlySet<string>
): readonly CoreLfTransferExternalSymbol[] => {
    const result: CoreLfTransferExternalSymbol[] = [];
    const seen = new Set<string>();
    const add = (external: CoreLfTransferExternalSymbol): void => {
        const key = symbolKey(external.symbol);
        if (localKeys.has(key) || seen.has(key)) return;
        seen.add(key);
        result.push(external);
    };
    module.externalSymbols.forEach(add);
    allDefinitions.forEach(definition => add({
        symbol: definition.symbol,
        availability: 'earlier-fragment'
    }));
    return Object.freeze(result);
};

const phaseModule = (
    sourceModule: CoreLfModuleSpec,
    phaseIndex: number,
    entries: readonly SourceEntry[],
    allDefinitions: ReadonlyMap<string, Definition>
): CoreLfModuleSpec => {
    const first = entries[0];
    const kind = first.kind;
    const localKeys = phaseLocalKeys(entries);
    const externals = preliminaryExternals(
        sourceModule,
        allDefinitions,
        localKeys
    );
    const input = {
        revision:
            `${sourceModule.revision}+mixed-phase-${phaseIndex}-${kind}`,
        moduleId: sourceModule.moduleId,
        fragmentId:
            `${sourceModule.fragmentId}-mixed-${phaseIndex}-${kind}`,
        authorityPath: sourceModule.authorityPath,
        sourceSha256: sourceModule.sourceSha256,
        ...(sourceModule.canonicalExport === undefined
            ? {}
            : { canonicalExport: sourceModule.canonicalExport }),
        dependencies: sourceModule.dependencies,
        externalSymbols: externals,
        declarations: entries
            .filter(
                (entry): entry is Extract<
                    SourceEntry,
                    { readonly kind: 'declaration' }
                > => entry.kind === 'declaration'
            )
            .map(entry => entry.declaration),
        inductives: entries
            .filter(
                (entry): entry is Extract<
                    SourceEntry,
                    { readonly kind: 'inductive-signature' }
                > => entry.kind === 'inductive-signature'
            )
            .map(entry => entry.inductive),
        runtimeRules: entries
            .filter(
                (entry): entry is Extract<
                    SourceEntry,
                    { readonly kind: 'runtime' }
                > => entry.kind === 'runtime'
            )
            .map(entry => entry.runtimeRule),
        proofRules: entries
            .filter(
                (entry): entry is Extract<
                    SourceEntry,
                    { readonly kind: 'proof' }
                > => entry.kind === 'proof'
            )
            .map(entry => entry.proofRule)
    };
    const preliminary = createCoreLfModuleSpec(input);
    const firstOrder = entries[0].order;
    const referencedKeys = new Set(
        preliminary.referencedSymbols.map(symbolKey)
    );

    preliminary.referencedSymbols.forEach(symbol => {
        const definition = allDefinitions.get(symbolKey(symbol));
        if (definition?.availability === 'generated-untyped') {
            fail(
                'UNTYPED_GENERATED_SYMBOL_REFERENCED',
                `phases[${phaseIndex}].module.referencedSymbols`,
                `Source phase references generated symbol ` +
                    `'${displaySymbol(symbol)}' without an explicit type`
            );
        }
        if (
            definition !== undefined &&
            !localKeys.has(symbolKey(symbol)) &&
            definition.order >= firstOrder
        ) {
            fail(
                'FORWARD_PHASE_REFERENCE',
                `phases[${phaseIndex}].module.referencedSymbols`,
                `Source phase at order ${firstOrder} refers forward to ` +
                    `'${displaySymbol(symbol)}' at order ` +
                    definition.order
            );
        }
    });

    return createCoreLfModuleSpec({
        ...input,
        externalSymbols: externals.filter(external =>
            referencedKeys.has(symbolKey(external.symbol))
        )
    });
};

const phasePolicy = (
    sourcePolicy: CoreLfTransferPolicyOverlay,
    module: CoreLfModuleSpec,
    phaseIndex: number,
    entries: readonly SourceEntry[],
    policyByTarget:
        ReadonlyMap<string, CoreLfTransferPolicyEntry>
): CoreLfTransferPolicyOverlay => {
    const selected = entries.map(entry => {
        const policy = policyByTarget.get(sourceTargetKey(entry));
        if (policy === undefined) {
            return fail(
                'INCOMPLETE_MIXED_POLICY',
                `phases[${phaseIndex}].policy`,
                'Source phase has no selected policy'
            );
        }
        return policy;
    });
    return createCoreLfTransferPolicyOverlay(module, {
        revision:
            `${sourcePolicy.revision}+mixed-phase-${phaseIndex}`,
        moduleRevision: module.revision,
        entries: selected
    });
};

/**
 * Partition one mixed transfer module into exact source-ordered,
 * phase-pure fragments.
 */
export function planCoreLfMixedPhases(
    module: CoreLfModuleSpec,
    policy: CoreLfTransferPolicyOverlay
): CoreLfMixedPhasePlan {
    const entries = sourceEntries(module);
    if (
        entries.length === 0 ||
        new Set(entries.map(entry => entry.kind)).size < 2
    ) {
        return fail(
            'INVALID_MIXED_INPUT',
            'module',
            'Mixed-phase planning requires at least two source phase kinds'
        );
    }
    const policyByTarget = assertExactPolicy(
        module,
        policy,
        entries
    );
    const allDefinitions = definitions(module);
    const phases = phaseGroups(entries).map(
        (group, phaseIndex): CoreLfMixedPhase => {
            const plannedModule = phaseModule(
                module,
                phaseIndex,
                group,
                allDefinitions
            );
            const plannedPolicy = phasePolicy(
                policy,
                plannedModule,
                phaseIndex,
                group,
                policyByTarget
            );
            const sourceOrders =
                Object.freeze(group.map(entry => entry.order));
            const first = group[0];
            switch (first.kind) {
                case 'declaration':
                    return deepFreeze({
                        index: phaseIndex,
                        kind: first.kind,
                        sourceOrders,
                        module: plannedModule,
                        policy: plannedPolicy
                    });
                case 'inductive-signature':
                    return deepFreeze({
                        index: phaseIndex,
                        kind: first.kind,
                        sourceOrders,
                        module: plannedModule,
                        policy: plannedPolicy,
                        lowering: lowerCoreLfInductiveSignatures(
                            plannedModule,
                            plannedPolicy
                        )
                    });
                case 'runtime':
                    return deepFreeze({
                        index: phaseIndex,
                        kind: first.kind,
                        sourceOrders,
                        module: plannedModule,
                        policy: plannedPolicy,
                        groupId: first.runtimeRule.groupId,
                        clauseOrders: group.map(entry => {
                            if (entry.kind !== 'runtime') {
                                return fail(
                                    'INVALID_MIXED_INPUT',
                                    `phases[${phaseIndex}]`,
                                    'Runtime phase contains a foreign item'
                                );
                            }
                            return entry.runtimeRule.clauseOrder;
                        })
                    });
                case 'proof':
                    return deepFreeze({
                        index: phaseIndex,
                        kind: first.kind,
                        sourceOrders,
                        module: plannedModule,
                        policy: plannedPolicy
                    });
                default: {
                    const exhaustive: never = first;
                    return exhaustive;
                }
            }
        }
    );
    return deepFreeze({
        revision: `${module.revision}+${policy.revision}` +
            '+mixed-phase-plan-1',
        sourceModule: module,
        sourcePolicy: policy,
        phases,
        semanticStatus: 'phase-plan-only',
        doesNotProvide: [
            'active-policy-selection',
            'generated-induction-semantics',
            'implicit-native-TYPE-parameter-encoding',
            'browser-api'
        ]
    });
}

export interface CoreLfMixedDeclarationLinkageInput {
    readonly revision: string;
    readonly moduleRevision: string;
    /**
     * Exactly one entry for each original external, ordinary declaration,
     * inductive head, and constructor. Generated owners are excluded until
     * an explicit typed contract exists.
     */
    readonly entries: readonly CoreLfTransferDeclarationLink[];
}

export interface CoreLfMixedDeclarationLinkage
extends CoreLfMixedDeclarationLinkageInput {
    readonly moduleId: string;
    readonly fragmentId: string;
}

const mixedLinkageValidationModule = (
    plan: CoreLfMixedPhasePlan
): CoreLfModuleSpec => {
    let order = 0;
    const declarations: CoreLfTransferDeclaration[] = [];
    plan.phases.forEach(phase => {
        const sourceDeclarations = phase.kind === 'inductive-signature'
            ? phase.lowering.module.declarations
            : phase.module.declarations;
        sourceDeclarations.forEach(declaration => {
            declarations.push({
                ...declaration,
                order: order++
            });
        });
    });
    const module = plan.sourceModule;
    return createCoreLfModuleSpec({
        revision: `${module.revision}+mixed-linkage-targets-1`,
        moduleId: module.moduleId,
        fragmentId: `${module.fragmentId}-mixed-linkage-targets`,
        authorityPath: module.authorityPath,
        sourceSha256: module.sourceSha256,
        ...(module.canonicalExport === undefined
            ? {}
            : { canonicalExport: module.canonicalExport }),
        dependencies: module.dependencies,
        externalSymbols: module.externalSymbols,
        declarations,
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
};

/**
 * Validate one module-wide linkage once, then mechanically project it to
 * every declaration-producing phase during compilation.
 */
export function createCoreLfMixedDeclarationLinkage(
    plan: CoreLfMixedPhasePlan,
    input: CoreLfMixedDeclarationLinkageInput
): CoreLfMixedDeclarationLinkage {
    if (input.moduleRevision !== plan.sourceModule.revision) {
        return fail(
            'INVALID_MIXED_LINKAGE',
            'linkage.moduleRevision',
            'Mixed linkage targets a foreign source module revision'
        );
    }
    const validationModule = mixedLinkageValidationModule(plan);
    const validated = createCoreLfTransferDeclarationLinkage(
        validationModule,
        {
            revision: input.revision,
            moduleRevision: validationModule.revision,
            entries: input.entries
        }
    );
    return deepFreeze({
        revision: input.revision,
        moduleRevision: input.moduleRevision,
        moduleId: plan.sourceModule.moduleId,
        fragmentId: plan.sourceModule.fragmentId,
        entries: validated.entries
    });
}

const projectedLinkage = (
    module: CoreLfModuleSpec,
    linkage: CoreLfMixedDeclarationLinkage,
    phaseIndex: number
): CoreLfTransferDeclarationLinkage => {
    const targets = new Set([
        ...module.externalSymbols.map(external =>
            symbolKey(external.symbol)
        ),
        ...module.declarations.map(declaration =>
            symbolKey(declaration.symbol)
        )
    ]);
    return createCoreLfTransferDeclarationLinkage(module, {
        revision: `${linkage.revision}+mixed-phase-${phaseIndex}`,
        moduleRevision: module.revision,
        entries: linkage.entries.filter(entry =>
            targets.has(symbolKey(entry.symbol))
        )
    });
};

export interface CoreLfMixedDeclarationBaseContext {
    readonly environment: CoreLfDeclarationEnvironment;
    declaration(
        symbol: CoreLfQualifiedSymbol
    ): CoreLfCompiledDeclaration | undefined;
}

const EMPTY_DECLARATIONS: CoreLfMixedDeclarationBaseContext =
    Object.freeze({
        environment: CoreLfDeclarationEnvironment.empty(),
        declaration: (
            _symbol: CoreLfQualifiedSymbol
        ): undefined => undefined
    });

const sameDeclarationLink = (
    left: CoreLfTransferDeclarationLink,
    right: CoreLfTransferDeclarationLink
): boolean => {
    if (
        left.symbol.moduleId !== right.symbol.moduleId ||
        left.symbol.name !== right.symbol.name ||
        left.kind !== right.kind
    ) {
        return false;
    }
    if (
        left.kind === 'core-owner' &&
        right.kind === 'core-owner'
    ) {
        return left.owner === right.owner;
    }
    if (
        left.kind === 'free-declaration' &&
        right.kind === 'free-declaration'
    ) {
        return (
            left.coreName === right.coreName &&
            left.backendName === right.backendName
        );
    }
    return false;
};

const isIntrinsicDefinitionRefinement = (
    previous: CoreLfCompiledDeclaration,
    next: CoreLfCompiledDeclaration
): boolean =>
    previous.status === 'intrinsic-conformance' &&
    next.status === 'intrinsic-transparent' &&
    previous.link.kind === 'core-owner' &&
    next.link.kind === 'core-owner' &&
    sameDeclarationLink(previous.link, next.link);

/**
 * Preserve module-level external linkage for later runtime/proof phases.
 *
 * Free externals must already be supplied by the immutable initial
 * declaration context. Intrinsic Core owners require no LF environment
 * declaration, so this creates only their checked lookup evidence.
 */
const externalDeclarationContext = (
    plan: CoreLfMixedPhasePlan,
    linkage: CoreLfMixedDeclarationLinkage,
    initial: CoreLfMixedDeclarationBaseContext =
        EMPTY_DECLARATIONS
): CoreLfMixedDeclarationBaseContext => {
    const links = new Map(
        linkage.entries.map(entry => [
            symbolKey(entry.symbol),
            entry
        ])
    );
    const intrinsic = new Map<
        string,
        CoreLfCompiledDeclaration
    >();
    plan.sourceModule.externalSymbols.forEach(
        (external, index) => {
            const key = symbolKey(external.symbol);
            const link = links.get(key);
            if (link === undefined) {
                fail(
                    'INVALID_MIXED_LINKAGE',
                    `sourceModule.externalSymbols[${index}]`,
                    `External '${displaySymbol(external.symbol)}' ` +
                        'has no mixed declaration link'
                );
            }
            const existing = initial.declaration(external.symbol);
            if (existing !== undefined) {
                if (!sameDeclarationLink(existing.link, link)) {
                    fail(
                        'INVALID_INITIAL_DECLARATIONS',
                        `sourceModule.externalSymbols[${index}]`,
                        `Initial declaration for ` +
                            `'${displaySymbol(external.symbol)}' ` +
                            'does not preserve the mixed linkage'
                    );
                }
                return;
            }
            if (link.kind === 'free-declaration') {
                fail(
                    'INVALID_INITIAL_DECLARATIONS',
                    `sourceModule.externalSymbols[${index}]`,
                    `Initial declarations do not resolve external ` +
                        `'${displaySymbol(external.symbol)}'`
                );
            }
            if (link.kind !== 'core-owner') {
                fail(
                    'INVALID_MIXED_LINKAGE',
                    `sourceModule.externalSymbols[${index}]`,
                    'Unsupported external declaration link'
                );
            }
            const intrinsicLink =
                link as CoreLfTransferCoreOwnerLink;
            const nodeProvenance = provenance(
                'recovered',
                `mixed intrinsic external ` +
                    `${displaySymbol(external.symbol)} from ` +
                    plan.sourceModule.authorityPath
            );
            intrinsic.set(key, deepFreeze({
                order: link.order,
                symbol: { ...external.symbol },
                policy: 'conformance-only',
                link: {
                    ...intrinsicLink,
                    symbol: { ...intrinsicLink.symbol }
                },
                status: 'intrinsic-conformance',
                type: coreOwnerSignatureType(
                    intrinsicLink.owner,
                    nodeProvenance
                ),
                provenance: nodeProvenance
            }));
        }
    );
    return Object.freeze({
        environment: initial.environment,
        declaration(
            symbol: CoreLfQualifiedSymbol
        ): CoreLfCompiledDeclaration | undefined {
            return intrinsic.get(symbolKey(symbol)) ??
                initial.declaration(symbol);
        }
    });
};

/**
 * Persistent declaration view over the initial dependency context and every
 * source-prior local declaration phase.
 */
export class CoreLfMixedDeclarationContext
implements CoreLfMixedDeclarationBaseContext {
    readonly environment: CoreLfDeclarationEnvironment;
    readonly modules: readonly CoreLfCompiledDeclarationModule[];
    private readonly base: CoreLfMixedDeclarationBaseContext;
    private readonly bySymbol:
        ReadonlyMap<string, CoreLfCompiledDeclaration>;

    constructor(
        base: CoreLfMixedDeclarationBaseContext =
            EMPTY_DECLARATIONS,
        modules: readonly CoreLfCompiledDeclarationModule[] = []
    ) {
        this.base = base;
        this.modules = Object.freeze([...modules]);
        const bySymbol = new Map<
            string,
            CoreLfCompiledDeclaration
        >();
        this.modules.forEach((module, moduleIndex) => {
            module.declarations.forEach((declaration, declarationIndex) => {
                const key = symbolKey(declaration.symbol);
                const previous =
                    bySymbol.get(key) ??
                    base.declaration(declaration.symbol);
                if (
                    previous !== undefined &&
                    !isIntrinsicDefinitionRefinement(
                        previous,
                        declaration
                    )
                ) {
                    fail(
                        'INVALID_INITIAL_DECLARATIONS',
                        `declarationModules[${moduleIndex}]` +
                            `.declarations[${declarationIndex}]`,
                        `Mixed declaration context duplicates ` +
                            `'${displaySymbol(declaration.symbol)}'`
                    );
                }
                bySymbol.set(key, declaration);
            });
        });
        this.bySymbol = bySymbol;
        this.environment =
            this.modules[this.modules.length - 1]?.environment ??
            base.environment;
        this.modules.forEach(module =>
            module.assertEnvironment(this.environment)
        );
        Object.freeze(this);
    }

    declaration(
        symbol: CoreLfQualifiedSymbol
    ): CoreLfCompiledDeclaration | undefined {
        return this.bySymbol.get(symbolKey(symbol)) ??
            this.base.declaration(symbol);
    }

    extend(
        module: CoreLfCompiledDeclarationModule
    ): CoreLfMixedDeclarationContext {
        return new CoreLfMixedDeclarationContext(
            this.base,
            [...this.modules, module]
        );
    }
}

export interface CoreLfMixedDeclarationPhaseOptions {
    readonly comparisonStepLimit?: number;
}

export interface CoreLfMixedCompileOptions {
    readonly initialDeclarations?:
        CoreLfMixedDeclarationBaseContext;
    /**
     * Exact source-exposition interfaces for ordinary declarations imported
     * from dependency modules. The same interfaces govern declaration,
     * runtime, and proof phases.
     */
    readonly dependencyInterfaces?:
        readonly CoreLfCompiledModuleInterface[];
    /**
     * Runtime conversion used when rechecking an immutable initial
     * declaration context and compiling later declaration/proof-only phases.
     *
     * A raw catalog runtime has no transfer-fragment identity, so it cannot
     * be composed with a local runtime phase. Such a plan fails closed and
     * must instead supply an explicit compiled runtime dependency.
     */
    readonly initialCheckingRuntime?: CoreLfCatalogRuntime;
    /**
     * Explicit dependency-module or source-prior same-module runtime
     * fragments. Runtime phases produced inside this plan are still added
     * mechanically; an `earlier-fragment` entry here represents a distinct
     * already compiled source fragment.
     */
    readonly runtimeDependencies?:
        readonly CoreLfRuntimeFragmentDependency[];
    readonly declarationOptions?: (
        phase: CoreLfMixedDeclarationPhase
    ) => CoreLfMixedDeclarationPhaseOptions;
    readonly inductiveOptions?: (
        phase: CoreLfMixedInductivePhase
    ) => CoreLfMixedDeclarationPhaseOptions;
    readonly runtimeOptions?: (
        phase: CoreLfMixedRuntimePhase
    ) => CoreLfRuntimeCompilerOptions;
    readonly proofOptions?: (
        phase: CoreLfMixedProofPhase
    ) => Omit<CoreLfProofCompilerOptions, 'runtimeProgram'>;
}

interface CoreLfCompiledMixedPhaseBase {
    readonly index: number;
    readonly kind: CoreLfMixedPhaseKind;
    readonly sourceOrders: readonly number[];
}

export interface CoreLfCompiledMixedDeclarationPhase
extends CoreLfCompiledMixedPhaseBase {
    readonly kind: 'declaration';
    readonly source: CoreLfMixedDeclarationPhase;
    readonly declarations: CoreLfCompiledDeclarationModule;
}

export interface CoreLfCompiledMixedInductivePhase
extends CoreLfCompiledMixedPhaseBase {
    readonly kind: 'inductive-signature';
    readonly source: CoreLfMixedInductivePhase;
    readonly declarations: CoreLfCompiledDeclarationModule;
}

export interface CoreLfCompiledMixedRuntimePhase
extends CoreLfCompiledMixedPhaseBase {
    readonly kind: 'runtime';
    readonly source: CoreLfMixedRuntimePhase;
    readonly runtime: CoreLfCompiledRuntimeFragment;
}

export interface CoreLfCompiledMixedProofPhase
extends CoreLfCompiledMixedPhaseBase {
    readonly kind: 'proof';
    readonly source: CoreLfMixedProofPhase;
    readonly proof: CoreLfCompiledProofProgram;
}

export type CoreLfCompiledMixedPhase =
    | CoreLfCompiledMixedDeclarationPhase
    | CoreLfCompiledMixedInductivePhase
    | CoreLfCompiledMixedRuntimePhase
    | CoreLfCompiledMixedProofPhase;

export class CoreLfCompiledMixedModule {
    readonly revision: string;
    readonly phases: readonly CoreLfCompiledMixedPhase[];
    readonly proofPrograms: readonly CoreLfCompiledProofProgram[];
    readonly proofProgram?:
        CoreLfCompiledProofProgram | CoreLfComposedProofProgram;
    readonly semanticStatus = 'compiled-selected-policy' as const;
    readonly doesNotProvide = Object.freeze([
        'active-policy-selection',
        'generated-induction-semantics',
        'implicit-native-TYPE-parameter-encoding',
        'browser-api'
    ] as const);

    constructor(
        public readonly plan: CoreLfMixedPhasePlan,
        public readonly linkage: CoreLfMixedDeclarationLinkage,
        public readonly declarations: CoreLfMixedDeclarationContext,
        phases: readonly CoreLfCompiledMixedPhase[],
        public readonly latestRuntime?: CoreLfCompiledRuntimeFragment,
        proofProgram?:
            CoreLfCompiledProofProgram | CoreLfComposedProofProgram
    ) {
        this.revision =
            `${plan.revision}+${linkage.revision}+compiled-1`;
        this.phases = Object.freeze([...phases]);
        this.proofPrograms = Object.freeze(
            phases
                .filter(
                    (
                        phase
                    ): phase is CoreLfCompiledMixedProofPhase =>
                        phase.kind === 'proof'
                )
                .map(phase => phase.proof)
        );
        this.proofProgram = proofProgram;
        Object.freeze(this);
    }
}

const validateRuntimeDependencies = (
    plan: CoreLfMixedPhasePlan,
    dependencies: readonly CoreLfRuntimeFragmentDependency[]
): void => {
    let priorModuleIndex = -1;
    let sawEarlierFragment = false;
    const identities = new Set<string>();
    dependencies.forEach((dependency, index) => {
        const moduleId = dependency.fragment.module.moduleId;
        if (identities.has(dependency.fragment.identity)) {
            fail(
                'INVALID_RUNTIME_DEPENDENCY',
                `options.runtimeDependencies[${index}]`,
                `Runtime dependency '${moduleId}/` +
                    `${dependency.fragment.module.fragmentId}' is duplicated`
            );
        }
        identities.add(dependency.fragment.identity);

        if (dependency.relation === 'dependency-module') {
            const moduleIndex =
                plan.sourceModule.dependencies.indexOf(moduleId);
            if (
                moduleIndex < 0 ||
                moduleId === plan.sourceModule.moduleId ||
                sawEarlierFragment ||
                moduleIndex < priorModuleIndex
            ) {
                fail(
                    'INVALID_RUNTIME_DEPENDENCY',
                    `options.runtimeDependencies[${index}].relation`,
                    `Runtime dependency '${moduleId}/` +
                        `${dependency.fragment.module.fragmentId}' is ` +
                        'foreign or out of source import order'
                );
            }
            priorModuleIndex = moduleIndex;
            return;
        }

        if (dependency.relation === 'earlier-fragment') {
            if (
                moduleId !== plan.sourceModule.moduleId ||
                dependency.fragment.module.fragmentId ===
                    plan.sourceModule.fragmentId
            ) {
                fail(
                    'INVALID_RUNTIME_DEPENDENCY',
                    `options.runtimeDependencies[${index}].relation`,
                    'An explicit earlier runtime must be a distinct ' +
                        `source-prior fragment of module ` +
                        `'${plan.sourceModule.moduleId}'`
                );
            }
            sawEarlierFragment = true;
            return;
        }

        const exhaustive: never = dependency.relation;
        return exhaustive;
    });
};

/**
 * Execute a planned mixed module strictly in source order. This is
 * orchestration only: each phase delegates to its existing generic compiler.
 */
export function compileCoreLfMixedPhases(
    plan: CoreLfMixedPhasePlan,
    linkage: CoreLfMixedDeclarationLinkage,
    options: CoreLfMixedCompileOptions = {}
): CoreLfCompiledMixedModule {
    if (
        linkage.moduleRevision !== plan.sourceModule.revision ||
        linkage.moduleId !== plan.sourceModule.moduleId ||
        linkage.fragmentId !== plan.sourceModule.fragmentId
    ) {
        return fail(
            'FOREIGN_MIXED_PLAN',
            'linkage',
            'Mixed compilation linkage targets a foreign phase plan'
        );
    }
    if (
        options.initialCheckingRuntime !== undefined &&
        plan.phases.some(phase => phase.kind === 'runtime')
    ) {
        return fail(
            'INVALID_INITIAL_RUNTIME',
            'options.initialCheckingRuntime',
            'A raw initial checking runtime cannot be composed with local ' +
                'runtime phases; supply an explicit compiled runtime ' +
                'fragment dependency'
        );
    }
    const externalRuntimeDependencies =
        options.runtimeDependencies ?? [];
    if (
        options.initialCheckingRuntime !== undefined &&
        externalRuntimeDependencies.length > 0
    ) {
        return fail(
            'INVALID_INITIAL_RUNTIME',
            'options.initialCheckingRuntime',
            'A raw initial checking runtime and explicit runtime-fragment ' +
                'dependencies cannot be combined'
        );
    }
    validateRuntimeDependencies(
        plan,
        externalRuntimeDependencies
    );
    const externalCheckingRuntime =
        composeCoreLfRuntimeDependencies(
            externalRuntimeDependencies
        );
    let declarations = new CoreLfMixedDeclarationContext(
        externalDeclarationContext(
            plan,
            linkage,
            options.initialDeclarations
        )
    );
    let latestRuntime: CoreLfCompiledRuntimeFragment | undefined;
    const compiled: CoreLfCompiledMixedPhase[] = [];

    plan.phases.forEach(phase => {
        switch (phase.kind) {
            case 'declaration': {
                const phaseOptions =
                    options.declarationOptions?.(phase) ?? {};
                const artifact = compileCoreLfDeclarations(
                    phase.module,
                    phase.policy,
                    projectedLinkage(
                        phase.module,
                        linkage,
                        phase.index
                    ),
                    {
                        initialEnvironment: declarations.environment,
                        dependencyInterfaces:
                            options.dependencyInterfaces,
                        runtimeProgram:
                            latestRuntime?.runtime ??
                            externalCheckingRuntime ??
                            options.initialCheckingRuntime,
                        comparisonStepLimit:
                            phaseOptions.comparisonStepLimit
                    }
                );
                declarations = declarations.extend(artifact);
                compiled.push(deepFreeze({
                    index: phase.index,
                    kind: phase.kind,
                    sourceOrders: phase.sourceOrders,
                    source: phase,
                    declarations: artifact
                }));
                return;
            }
            case 'inductive-signature': {
                const phaseOptions =
                    options.inductiveOptions?.(phase) ?? {};
                const target = phase.lowering.module;
                const artifact = compileCoreLfInductiveSignatures(
                    phase.lowering,
                    projectedLinkage(
                        target,
                        linkage,
                        phase.index
                    ),
                    {
                        initialEnvironment: declarations.environment,
                        dependencyInterfaces:
                            options.dependencyInterfaces,
                        runtimeProgram:
                            latestRuntime?.runtime ??
                            externalCheckingRuntime ??
                            options.initialCheckingRuntime,
                        comparisonStepLimit:
                            phaseOptions.comparisonStepLimit
                    }
                );
                declarations = declarations.extend(artifact);
                compiled.push(deepFreeze({
                    index: phase.index,
                    kind: phase.kind,
                    sourceOrders: phase.sourceOrders,
                    source: phase,
                    declarations: artifact
                }));
                return;
            }
            case 'runtime': {
                const dependencies: CoreLfRuntimeFragmentDependency[] = [
                    ...externalRuntimeDependencies,
                    ...(latestRuntime === undefined
                        ? []
                        : [{
                            relation: 'earlier-fragment' as const,
                            fragment: latestRuntime
                        }])
                ];
                const artifact = compileCoreLfRuntimeFragment(
                    phase.module,
                    phase.policy,
                    declarations,
                    {
                        dependencies,
                        ...(options.runtimeOptions?.(phase) ?? {}),
                        dependencyInterfaces:
                            options.dependencyInterfaces
                    }
                );
                latestRuntime = artifact;
                compiled.push(deepFreeze({
                    index: phase.index,
                    kind: phase.kind,
                    sourceOrders: phase.sourceOrders,
                    source: phase,
                    runtime: artifact
                }));
                return;
            }
            case 'proof': {
                const artifact = compileCoreLfProofProgram(
                    phase.module,
                    phase.policy,
                    declarations,
                    {
                        ...(options.proofOptions?.(phase) ?? {}),
                        dependencyInterfaces:
                            options.dependencyInterfaces,
                        runtimeProgram:
                            latestRuntime?.runtime ??
                            externalCheckingRuntime ??
                            options.initialCheckingRuntime
                    }
                );
                compiled.push(deepFreeze({
                    index: phase.index,
                    kind: phase.kind,
                    sourceOrders: phase.sourceOrders,
                    source: phase,
                    proof: artifact
                }));
                return;
            }
            default: {
                const exhaustive: never = phase;
                return exhaustive;
            }
        }
    });

    const proofPrograms = compiled
        .filter(
            (
                phase
            ): phase is CoreLfCompiledMixedProofPhase =>
                phase.kind === 'proof'
        )
        .map(phase => phase.proof);
    const proofProgram = proofPrograms.length === 0
        ? undefined
        : composeCoreLfProofPrograms(
            proofPrograms,
            declarations,
            {
                executionRuntimeProgram:
                    latestRuntime?.runtime ??
                    externalCheckingRuntime ??
                    options.initialCheckingRuntime
            }
        );
    return new CoreLfCompiledMixedModule(
        plan,
        linkage,
        declarations,
        compiled,
        latestRuntime,
        proofProgram
    );
}
