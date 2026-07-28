/**
 * SCALE-0C migration witness for the reviewed 29-signature continuation.
 *
 * The adapter below converts already reviewed typed snapshots into the shared
 * transfer IR. The generic compiler remains owner-agnostic; this module is
 * the immutable data/linkage edge that proves the existing directed catalogs
 * can be reproduced without their three owner-specific materializers.
 */

import {
    CORE_DIRECTED_1A_PRIMITIVE_NAMES
} from './directed_1a';
import {
    LAMBDAPI_V32_DIRECTED_1A_PROPOSAL_BINDINGS
} from './directed_1a_proposal';
import {
    CORE_DIRECTED_1B_PRIMITIVE_NAMES,
    CoreDirected1bRuntimeProgram
} from './directed_1b';
import {
    LAMBDAPI_V32_DIRECTED_1B_OWNER_BINDINGS
} from './directed_1b_proposal';
import {
    CORE_DIRECTED_1C_PRIMITIVE_NAMES,
    CoreDirected1cCatalog
} from './directed_1c';
import {
    LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING
} from './directed_1c_proposal';
import {
    CORE_DIRECTED_CONTINUATION_PROFILE,
    validateCoreDirectedContinuationProfile
} from './directed_graduation';
import {
    CORE_DIRECTED_GRADUATION_MANIFEST,
    CoreDirectedGraduationDeclarationEntry,
    validateCoreDirectedGraduationManifest
} from './directed_graduation_proposal';
import {
    CoreLfCompiledDeclarationModule,
    CoreLfTransferDeclarationLink,
    compileCoreLfDeclarations,
    createCoreLfTransferDeclarationLinkage
} from './lf_transfer_compiler';
import {
    CoreLfCatalogRuntime
} from './lf_conversion';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferBinderToken,
    CoreLfTransferBuilderExpression,
    CoreLfTransferPolicyEntry,
    CoreLfTransferRigidity,
    CoreLfTransferScopedBuilder,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreLfTransferExplicitBody,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    KernelExpression,
    binderMode,
    kernelExpressionEquals
} from './kernel';
import {
    LAMBDAPI_V32_MODULE,
    LAMBDAPI_V32_OWNER_BINDINGS
} from './lambdapi';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId,
    Plicity
} from './schema';

export const CORE_DIRECTED_CONTINUATION_TRANSFER_REVISION =
    'emdash-v3.2-dttlf-directed-1-transfer-1' as const;

export const CORE_DIRECTED_CONTINUATION_TRANSFER_POLICY_REVISION =
    'SCALE-0C-reviewed-29-policy-1' as const;

export const CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE_REVISION =
    'SCALE-0C-reviewed-29-linkage-1' as const;

export type CoreDirectedContinuationTransferErrorCode =
    | 'REVIEWED_TRANSFER_DRIFT'
    | 'UNSUPPORTED_REVIEWED_EXPRESSION'
    | 'LEGACY_EQUIVALENCE_FAILURE';

export class CoreDirectedContinuationTransferError extends Error {
    constructor(
        public readonly code: CoreDirectedContinuationTransferErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreDirectedContinuationTransferError';
    }
}

interface ReviewedBinding {
    readonly owner: string;
    readonly symbol: CoreLfQualifiedSymbol;
    readonly backendName: string;
    readonly sourceFragment: string;
    readonly rigidity: CoreLfTransferRigidity;
    readonly sourceOpacity: 'transparent' | 'opaque';
}

const fail = (
    code: CoreDirectedContinuationTransferErrorCode,
    message: string
): never => {
    throw new CoreDirectedContinuationTransferError(code, message);
};

const isRecord = (
    value: unknown
): value is Readonly<Record<string, unknown>> =>
    typeof value === 'object' && value !== null;

const record = (
    value: unknown,
    detail: string
): Readonly<Record<string, unknown>> => {
    if (!isRecord(value)) {
        return fail(
            'UNSUPPORTED_REVIEWED_EXPRESSION',
            `${detail} is not an object`
        );
    }
    return value;
};

const stringField = (
    value: unknown,
    detail: string
): string => {
    if (typeof value !== 'string' || value.length === 0) {
        return fail(
            'UNSUPPORTED_REVIEWED_EXPRESSION',
            `${detail} is not a nonempty string`
        );
    }
    return value;
};

const arrayField = (
    value: unknown,
    detail: string
): readonly unknown[] => {
    if (!Array.isArray(value)) {
        return fail(
            'UNSUPPORTED_REVIEWED_EXPRESSION',
            `${detail} is not an array`
        );
    }
    return value;
};

const plicityField = (
    value: unknown,
    detail: string
): Plicity => {
    if (value !== 'explicit' && value !== 'implicit') {
        return fail(
            'UNSUPPORTED_REVIEWED_EXPRESSION',
            `${detail} has invalid plicity '${String(value)}'`
        );
    }
    return value;
};

const isCoreOwner = (owner: string): owner is CoreOwnerId =>
    Object.prototype.hasOwnProperty.call(CORE_OWNER_SCHEMAS, owner);

const bindingRigidity = (
    declaration: string
): CoreLfTransferRigidity => {
    if (declaration.startsWith('constant ')) return 'constant';
    if (declaration.startsWith('injective ')) return 'injective';
    return 'ordinary';
};

const reviewedBindings = (): readonly ReviewedBinding[] => {
    const base: ReviewedBinding[] =
        CORE_DIRECTED_GRADUATION_MANIFEST.baseOwnerSignatures.map(entry => {
            if (!isCoreOwner(entry.owner)) {
                return fail(
                    'REVIEWED_TRANSFER_DRIFT',
                    `Reviewed base owner '${entry.owner}' is not intrinsic`
                );
            }
            const binding = LAMBDAPI_V32_OWNER_BINDINGS[entry.owner];
            return {
                owner: entry.owner,
                symbol: coreLfQualifiedSymbol(
                    binding.module,
                    binding.serializedName
                ),
                backendName: binding.serializedName,
                sourceFragment: binding.provenance.declaration,
                rigidity: bindingRigidity(
                    binding.provenance.declaration
                ),
                sourceOpacity: 'opaque'
            };
        });

    const direct1a: ReviewedBinding[] =
        LAMBDAPI_V32_DIRECTED_1A_PROPOSAL_BINDINGS.map(binding => ({
            owner: binding.owner,
            symbol: coreLfQualifiedSymbol(
                binding.module,
                binding.serializedName
            ),
            backendName: binding.serializedName,
            sourceFragment: binding.provenance.declaration,
            rigidity: bindingRigidity(
                binding.provenance.declaration
            ),
            sourceOpacity: 'opaque'
        }));

    const direct1b: ReviewedBinding[] =
        LAMBDAPI_V32_DIRECTED_1B_OWNER_BINDINGS.map(binding => ({
            owner: binding.owner,
            symbol: coreLfQualifiedSymbol(
                binding.module,
                binding.serializedName
            ),
            backendName: binding.serializedName,
            sourceFragment: binding.provenance.sourceFragment,
            rigidity:
                binding.authority === 'injective-symbol' ||
                binding.authority === 'inductive-type' ||
                binding.authority === 'inductive-constructor'
                    ? 'injective'
                    : 'ordinary',
            sourceOpacity:
                binding.authority === 'transparent-definition'
                    ? 'transparent'
                    : 'opaque'
        }));

    const direct1c: ReviewedBinding = {
        owner: LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING.owner,
        symbol: coreLfQualifiedSymbol(
            LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING.module,
            LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING.serializedName
        ),
        backendName:
            LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING.serializedName,
        sourceFragment:
            LAMBDAPI_V32_DIRECTED_1C_OWNER_BINDING
                .provenance.sourceFragment,
        rigidity: 'ordinary',
        sourceOpacity: 'transparent'
    };

    const result = [
        ...base,
        ...direct1a,
        ...direct1b,
        direct1c
    ];
    const expectedOwners =
        CORE_DIRECTED_CONTINUATION_PROFILE.signatureClosure.ownerIds;
    if (
        result.length !== expectedOwners.length ||
        result.some(
            (binding, index) =>
                binding.owner !== expectedOwners[index] ||
                binding.symbol.moduleId !== LAMBDAPI_V32_MODULE
        )
    ) {
        return fail(
            'REVIEWED_TRANSFER_DRIFT',
            'Reviewed owner bindings do not match the 29-signature closure'
        );
    }
    return Object.freeze(result.map(binding =>
        Object.freeze({
            ...binding,
            symbol: Object.freeze({ ...binding.symbol })
        })
    ));
};

const bindings = reviewedBindings();
const bindingByOwner = new Map(
    bindings.map(binding => [binding.owner, binding])
);

const ownerPlicities = new Map<string, readonly Plicity[]>([
    ...CORE_DIRECTED_GRADUATION_MANIFEST.baseOwnerSignatures.map(entry => [
        entry.owner,
        entry.signature.slots.map(slot => slot.plicity)
    ] as const),
    ...CORE_DIRECTED_GRADUATION_MANIFEST.candidateDeclarations.map(entry => [
        entry.owner,
        entry.signatureSnapshot.slots.map(slot => slot.plicity)
    ] as const)
]);

export const CORE_DIRECTED_CONTINUATION_TRANSFER_SYMBOLS:
Readonly<Record<string, CoreLfQualifiedSymbol>> = Object.freeze(
    Object.fromEntries(bindings.map(binding => [
        binding.owner,
        Object.freeze({ ...binding.symbol })
    ]))
);

export const CORE_DIRECTED_CONTINUATION_TRANSFER_PLICITIES:
Readonly<Record<string, readonly Plicity[]>> = Object.freeze(
    Object.fromEntries([...ownerPlicities].map(([owner, plicities]) => [
        owner,
        Object.freeze([...plicities])
    ]))
);

export function coreDirectedContinuationTransferSymbol(
    owner: string
): CoreLfQualifiedSymbol {
    const symbol = CORE_DIRECTED_CONTINUATION_TRANSFER_SYMBOLS[owner];
    if (symbol === undefined) {
        return fail(
            'REVIEWED_TRANSFER_DRIFT',
            `Owner '${owner}' is outside the reviewed transfer closure`
        );
    }
    return symbol;
}

export function coreDirectedContinuationTransferPlicities(
    owner: string
): readonly Plicity[] {
    const plicities =
        CORE_DIRECTED_CONTINUATION_TRANSFER_PLICITIES[owner];
    if (plicities === undefined) {
        return fail(
            'REVIEWED_TRANSFER_DRIFT',
            `Owner '${owner}' has no reviewed transfer telescope`
        );
    }
    return plicities;
}

type BuilderScope = ReadonlyMap<
    string,
    CoreLfTransferBuilderExpression
>;

const reviewedExpression = (
    value: unknown,
    builder: CoreLfTransferScopedBuilder,
    scope: BuilderScope,
    detail: string
): CoreLfTransferBuilderExpression => {
    const expression = record(value, detail);
    const tag = stringField(expression.tag, `${detail}.tag`);
    switch (tag) {
        case 'universe':
        case 'type':
            return builder.type();
        case 'slot':
        case 'variable': {
            const name = stringField(
                expression.name,
                `${detail}.name`
            );
            const token = scope.get(name);
            if (token === undefined) {
                return fail(
                    'UNSUPPORTED_REVIEWED_EXPRESSION',
                    `${detail} refers to unavailable binder '${name}'`
                );
            }
            return token;
        }
        case 'owner-application': {
            const owner = stringField(
                expression.owner,
                `${detail}.owner`
            );
            const binding = bindingByOwner.get(owner);
            const plicities = ownerPlicities.get(owner);
            if (binding === undefined || plicities === undefined) {
                return fail(
                    'UNSUPPORTED_REVIEWED_EXPRESSION',
                    `${detail} refers to owner outside the reviewed closure ` +
                        `'${owner}'`
                );
            }
            const arguments_ = arrayField(
                expression.arguments,
                `${detail}.arguments`
            );
            if (arguments_.length !== plicities.length) {
                return fail(
                    'UNSUPPORTED_REVIEWED_EXPRESSION',
                    `${detail} applies '${owner}' to ${arguments_.length} ` +
                        `arguments, expected ${plicities.length}`
                );
            }
            const callee = builder.global(binding.symbol);
            if (arguments_.length === 0) return callee;
            return builder.call(
                callee,
                arguments_.map((argument, index) => ({
                    plicity: plicities[index],
                    value: reviewedExpression(
                        argument,
                        builder,
                        scope,
                        `${detail}.${owner}[${index}]`
                    )
                }))
            );
        }
        case 'call': {
            const arguments_ = arrayField(
                expression.arguments,
                `${detail}.arguments`
            );
            return builder.call(
                reviewedExpression(
                    expression.callee,
                    builder,
                    scope,
                    `${detail}.callee`
                ),
                arguments_.map((value_, index) => {
                    const argument = record(
                        value_,
                        `${detail}.arguments[${index}]`
                    );
                    return {
                        plicity: plicityField(
                            argument.plicity,
                            `${detail}.arguments[${index}].plicity`
                        ),
                        value: reviewedExpression(
                            argument.value,
                            builder,
                            scope,
                            `${detail}.arguments[${index}].value`
                        )
                    };
                })
            );
        }
        case 'pi':
        case 'lambda': {
            const binder = record(
                expression.binder,
                `${detail}.binder`
            );
            const name = stringField(
                binder.name,
                `${detail}.binder.name`
            );
            const plicity = plicityField(
                binder.plicity,
                `${detail}.binder.plicity`
            );
            const variation = binder.variation;
            if (
                variation !== 'functorial' &&
                variation !== 'natural' &&
                variation !== 'object-only'
            ) {
                return fail(
                    'UNSUPPORTED_REVIEWED_EXPRESSION',
                    `${detail}.binder.variation is invalid`
                );
            }
            const type = reviewedExpression(
                binder.type,
                builder,
                scope,
                `${detail}.binder.type`
            );
            const body = (
                token: CoreLfTransferBinderToken
            ): CoreLfTransferBuilderExpression => {
                const nextScope = new Map(scope);
                nextScope.set(name, token);
                return reviewedExpression(
                    expression.body,
                    builder,
                    nextScope,
                    `${detail}.body`
                );
            };
            const mode = binderMode(plicity, variation);
            return tag === 'pi'
                ? builder.pi(name, type, body, mode)
                : builder.lam(name, type, body, mode);
        }
        default:
            return fail(
                'UNSUPPORTED_REVIEWED_EXPRESSION',
                `${detail} has unsupported tag '${tag}'`
            );
    }
};

const telescopeExpression = (
    builder: CoreLfTransferScopedBuilder,
    tag: 'pi' | 'lambda',
    slotsValue: unknown,
    result: unknown,
    detail: string
): CoreLfTransferBuilderExpression => {
    const slots = arrayField(slotsValue, `${detail}.slots`);
    const build = (
        index: number,
        scope: BuilderScope
    ): CoreLfTransferBuilderExpression => {
        if (index === slots.length) {
            return reviewedExpression(
                result,
                builder,
                scope,
                `${detail}.${tag === 'pi' ? 'result' : 'body'}`
            );
        }
        const slot = record(slots[index], `${detail}.slots[${index}]`);
        const name = stringField(
            slot.name,
            `${detail}.slots[${index}].name`
        );
        const type = reviewedExpression(
            slot.type,
            builder,
            scope,
            `${detail}.slots[${index}].type`
        );
        const mode = binderMode(
            plicityField(
                slot.plicity,
                `${detail}.slots[${index}].plicity`
            ),
            'functorial'
        );
        const body = (
            token: CoreLfTransferBinderToken
        ): CoreLfTransferBuilderExpression => {
            const nextScope = new Map(scope);
            nextScope.set(name, token);
            return build(index + 1, nextScope);
        };
        return tag === 'pi'
            ? builder.pi(name, type, body, mode)
            : builder.lam(name, type, body, mode);
    };
    return build(0, new Map());
};

const candidateSnapshot = (
    entry: CoreDirectedGraduationDeclarationEntry
): Readonly<Record<string, unknown>> =>
    record(
        entry.signatureSnapshot,
        `reviewed candidate ${entry.owner}`
    );

const candidateBody = (
    entry: CoreDirectedGraduationDeclarationEntry
): unknown => {
    const snapshot = candidateSnapshot(entry);
    return snapshot.body;
};

const reviewedDeclarations = () => {
    const base =
        CORE_DIRECTED_GRADUATION_MANIFEST.baseOwnerSignatures.map(entry => {
            const binding = bindingByOwner.get(entry.owner);
            if (binding === undefined) {
                return fail(
                    'REVIEWED_TRANSFER_DRIFT',
                    `Base owner '${entry.owner}' has no reviewed binding`
                );
            }
            const builder = new CoreLfTransferScopedBuilder();
            const type = builder.term(telescopeExpression(
                builder,
                'pi',
                entry.signature.slots,
                entry.signature.result,
                `reviewed base ${entry.owner}`
            ));
            return {
                order: entry.order,
                symbol: binding.symbol,
                type,
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public' as const,
                    rigidity: binding.rigidity,
                    sourceOpacity: binding.sourceOpacity
                },
                provenance: {
                    authorityPath: 'emdash2/emdash3_2.lp',
                    sourceFragment: binding.sourceFragment
                }
            };
        });

    const candidates =
        CORE_DIRECTED_GRADUATION_MANIFEST.candidateDeclarations.map(entry => {
            const binding = bindingByOwner.get(entry.owner);
            if (binding === undefined) {
                return fail(
                    'REVIEWED_TRANSFER_DRIFT',
                    `Candidate owner '${entry.owner}' has no reviewed binding`
                );
            }
            const snapshot = candidateSnapshot(entry);
            const builder = new CoreLfTransferScopedBuilder();
            const type = builder.term(telescopeExpression(
                builder,
                'pi',
                snapshot.slots,
                snapshot.result,
                `reviewed candidate ${entry.owner}`
            ));
            let body = coreLfTransferAbsentBody();
            if (
                entry.candidateDisposition ===
                'transparent-checked-definition'
            ) {
                const bodySnapshot = candidateBody(entry);
                if (bodySnapshot === undefined) {
                    return fail(
                        'REVIEWED_TRANSFER_DRIFT',
                        `Transparent candidate '${entry.owner}' has no body`
                    );
                }
                const bodyBuilder = new CoreLfTransferScopedBuilder();
                body = coreLfTransferExplicitBody(
                    bodyBuilder.term(telescopeExpression(
                        bodyBuilder,
                        'lambda',
                        snapshot.slots,
                        bodySnapshot,
                        `reviewed candidate ${entry.owner}`
                    ))
                );
            }
            return {
                order: entry.order,
                symbol: binding.symbol,
                type,
                body,
                modifiers: {
                    visibility: 'public' as const,
                    rigidity: binding.rigidity,
                    sourceOpacity: binding.sourceOpacity
                },
                provenance: {
                    authorityPath: 'emdash2/emdash3_2.lp',
                    sourceFragment: binding.sourceFragment
                }
            };
        });
    return [...base, ...candidates];
};

validateCoreDirectedGraduationManifest(
    CORE_DIRECTED_GRADUATION_MANIFEST
);
validateCoreDirectedContinuationProfile(
    CORE_DIRECTED_CONTINUATION_PROFILE
);

export const CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_DIRECTED_CONTINUATION_TRANSFER_REVISION,
    moduleId: LAMBDAPI_V32_MODULE,
    fragmentId: 'reviewed-directed-continuation-signatures',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        'sha256:fac748f9fa27a80ca6a1198145db0fb283dc46ed60d513154c31d706646136ed',
    canonicalExport: {
        exporterVersion: '3.0.0-90-gdb4f780',
        sha256:
            'sha256:fb6fbcf4d486f22fa000f16f2deefc4b9bae65a066b8def952a3f1756030cf2f'
    },
    dependencies: [],
    externalSymbols: [],
    declarations: reviewedDeclarations(),
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

const policyEntries: readonly CoreLfTransferPolicyEntry[] = [
    ...CORE_DIRECTED_GRADUATION_MANIFEST.baseOwnerSignatures.map(entry => {
        const binding = bindingByOwner.get(entry.owner);
        if (binding === undefined) {
            return fail(
                'REVIEWED_TRANSFER_DRIFT',
                `Base policy owner '${entry.owner}' has no binding`
            );
        }
        return {
            order: entry.order,
            target: {
                kind: 'declaration' as const,
                symbol: binding.symbol
            },
            policy: 'conformance-only' as const,
            evidence:
                `${entry.source} in approved D-DTTLF-001 manifest`
        };
    }),
    ...CORE_DIRECTED_GRADUATION_MANIFEST.candidateDeclarations.map(entry => {
        const binding = bindingByOwner.get(entry.owner);
        if (binding === undefined) {
            return fail(
                'REVIEWED_TRANSFER_DRIFT',
                `Candidate policy owner '${entry.owner}' has no binding`
            );
        }
        return {
            order: entry.order,
            target: {
                kind: 'declaration' as const,
                symbol: binding.symbol
            },
            policy:
                entry.candidateDisposition ===
                    'transparent-checked-definition'
                    ? 'checked-transparent-definition' as const
                    : 'opaque-signature' as const,
            evidence:
                `${entry.sourceReview} in approved D-DTTLF-001 manifest`
        };
    })
];

export const CORE_DIRECTED_CONTINUATION_TRANSFER_POLICY =
    createCoreLfTransferPolicyOverlay(
        CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE,
        {
            revision:
                CORE_DIRECTED_CONTINUATION_TRANSFER_POLICY_REVISION,
            moduleRevision:
                CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE.revision,
            entries: policyEntries
        }
    );

const candidateCoreNames: Readonly<Record<string, string>> = Object.freeze({
    ...CORE_DIRECTED_1A_PRIMITIVE_NAMES,
    ...CORE_DIRECTED_1B_PRIMITIVE_NAMES,
    ...CORE_DIRECTED_1C_PRIMITIVE_NAMES
});

const linkageEntries: readonly CoreLfTransferDeclarationLink[] =
    bindings.map((binding, order) => {
        if (isCoreOwner(binding.owner)) {
            return {
                order,
                symbol: binding.symbol,
                kind: 'core-owner' as const,
                owner: binding.owner
            };
        }
        const coreName = candidateCoreNames[binding.owner];
        if (coreName === undefined) {
            return fail(
                'REVIEWED_TRANSFER_DRIFT',
                `Candidate owner '${binding.owner}' has no Core name`
            );
        }
        return {
            order,
            symbol: binding.symbol,
            kind: 'free-declaration' as const,
            coreName,
            backendName: binding.backendName
        };
    });

export const CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE =
    createCoreLfTransferDeclarationLinkage(
        CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE,
        {
            revision:
                CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE_REVISION,
            moduleRevision:
                CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE.revision,
            entries: linkageEntries
        }
    );

/**
 * Compile the exact approved continuation using only generic declaration
 * machinery. The runtime is injected solely for definition checking.
 */
export function compileCoreDirectedContinuationTransfer():
CoreLfCompiledDeclarationModule {
    return compileCoreDirectedContinuationTransferWithRuntime(
        CoreDirected1bRuntimeProgram.create()
    );
}

export function compileCoreDirectedContinuationTransferWithRuntime(
    runtimeProgram: CoreLfCatalogRuntime
): CoreLfCompiledDeclarationModule {
    return compileCoreLfDeclarations(
        CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE,
        CORE_DIRECTED_CONTINUATION_TRANSFER_POLICY,
        CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE,
        {
            runtimeProgram,
            comparisonStepLimit:
                CORE_DIRECTED_CONTINUATION_PROFILE.outerLf
                    .comparisonStepLimit
        }
    );
}

const sameRecord = (
    left: Readonly<Record<string, string>>,
    right: Readonly<Record<string, string>>
): boolean =>
    JSON.stringify(left) === JSON.stringify(right);

/**
 * Executable migration proof against the already reviewed 1A/1B/1C catalog.
 */
export function validateCoreDirectedContinuationTransferEquivalence(
    compiled: CoreLfCompiledDeclarationModule =
        compileCoreDirectedContinuationTransfer()
): void {
    const legacy = CoreDirected1cCatalog.create();
    compiled.createChecker().validateEnvironment();
    legacy.createChecker().validateEnvironment();

    if (
        compiled.declarations.length !== 29 ||
        compiled.declarations.filter(
            declaration =>
                declaration.status === 'intrinsic-conformance'
        ).length !== 20 ||
        compiled.environment.declarations.length !== 9 ||
        legacy.environment.declarations.length !== 9
    ) {
        return fail(
            'LEGACY_EQUIVALENCE_FAILURE',
            'Generic transfer does not preserve the reviewed 20 + 9 split'
        );
    }

    for (
        const entry of
        CORE_DIRECTED_GRADUATION_MANIFEST.candidateDeclarations
    ) {
        const binding = bindingByOwner.get(entry.owner);
        if (binding === undefined) {
            return fail(
                'LEGACY_EQUIVALENCE_FAILURE',
                `Candidate '${entry.owner}' has no binding`
            );
        }
        const generic = compiled.declaration(binding.symbol);
        const coreName = candidateCoreNames[entry.owner];
        const previous = legacy.environment.lookup(coreName);
        if (
            generic === undefined ||
            generic.link.kind !== 'free-declaration' ||
            previous === undefined ||
            generic.link.coreName !== coreName ||
            !kernelExpressionEquals(generic.type, previous.type) ||
            (
                generic.body === undefined
                    ? previous.body !== undefined
                    : previous.body === undefined ||
                        !kernelExpressionEquals(
                            generic.body,
                            previous.body
                        )
            ) ||
            (
                generic.status === 'installed-transparent'
                    ? previous.transparency !== 'transparent'
                    : previous.transparency !== 'opaque'
            )
        ) {
            return fail(
                'LEGACY_EQUIVALENCE_FAILURE',
                `Generic transfer differs for reviewed owner '${entry.owner}'`
            );
        }
    }

    if (
        !sameRecord(
            compiled.externalFreeReferences,
            legacy.externalFreeReferences
        ) ||
        !sameRecord(
            compiled.externalTransparentDefinitions,
            legacy.externalTransparentDefinitions
        )
    ) {
        return fail(
            'LEGACY_EQUIVALENCE_FAILURE',
            'Generic transfer changes backend declaration linkage'
        );
    }

    const probeArguments: KernelExpression[] = [];
    const zeroArity = compiled.declarations.find(declaration =>
        declaration.link.kind === 'core-owner' &&
        CORE_OWNER_SCHEMAS[declaration.link.owner].slots.length === 0
    );
    if (zeroArity === undefined) {
        return fail(
            'LEGACY_EQUIVALENCE_FAILURE',
            'Generic transfer contains no zero-arity intrinsic witness'
        );
    }
    compiled.application(
        zeroArity.symbol,
        probeArguments,
        zeroArity.provenance
    );
}
