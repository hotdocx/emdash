/**
 * SCALE-0D typed migration of the reviewed ten-rule continuation runtime.
 *
 * This module is an exact data/acquisition adapter. Runtime compilation and
 * matching remain entirely generic in lf_transfer_runtime.ts.
 */

import {
    CoreDirected1bRuntimeProgram,
    CoreDirected1bCatalog
} from './directed_1b';
import {
    LAMBDAPI_V32_DIRECTED_1B_RULE_BINDINGS
} from './directed_1b_proposal';
import {
    compileCoreDirectedContinuationTransfer,
    compileCoreDirectedContinuationTransferWithRuntime,
    coreDirectedContinuationTransferPlicities,
    coreDirectedContinuationTransferSymbol,
    validateCoreDirectedContinuationTransferEquivalence
} from './directed_continuation_transfer';
import {
    CORE_DIRECTED_GRADUATION_MANIFEST
} from './directed_graduation_proposal';
import {
    LAMBDAPI_V32_DIRECTED_FOUNDATION_2_RULE_BINDING
} from './directed_foundation_2_proposal';
import {
    LAMBDAPI_V32_DIRECTED_FOUNDATION_RULE_BINDINGS
} from './directed_foundation_proposal';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferBinderToken,
    CoreLfTransferBuilderExpression,
    CoreLfTransferPolicyEntry,
    CoreLfTransferRuntimeRule,
    CoreLfTransferScopedBuilder,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    CoreLfCompiledDeclarationModule
} from './lf_transfer_compiler';
import {
    CoreLfCompiledRuntimeProgram,
    compileCoreLfRuntimeProgram
} from './lf_transfer_runtime';
import {
    BinderMode,
    KernelExpression,
    Plicity,
    kernelApplication,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from './kernel';
import {
    LAMBDAPI_V32_MODULE,
    LAMBDAPI_V32_RULE_EVIDENCE_BINDINGS
} from './lambdapi';
import {
    CORE_MVP_MANIFEST,
    CoreManifestRuleInput,
    CoreRulePatternInput
} from './manifest';
import {
    CORE_OWNER_SCHEMAS,
    CoreOwnerId
} from './schema';
import {
    coreOwnerSlotType
} from './signature';
import {
    coreRuntimeRewriteHead
} from './evaluator';

export const CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_REVISION =
    'emdash-v3.2-dttlf-directed-1-runtime-transfer-1' as const;

export const CORE_DIRECTED_CONTINUATION_RUNTIME_POLICY_REVISION =
    'SCALE-0D-reviewed-10-policy-1' as const;

export const CORE_DIRECTED_CONTINUATION_RUNTIME_SUBJECT_ORACLE =
    Object.freeze({
        authorityPath: 'emdash2/emdash3_2.lp',
        ruleIds: Object.freeze([
            'directed.sigma-telescope-fibre.evaluate',
            'projection.functor-hom.evaluate',
            'projection.transfor-component.evaluate',
            'projection.transfor-hom.evaluate'
        ]),
        evidence:
            'H-DTTLF-03/D-DTTLF-001 requires the Lambdapi ' +
            'subject-reduction oracle and withholds standalone TypeScript ' +
            'subject reduction; the directed fibre rule depends on the ' +
            'unpromoted Const_catd fibre reduction and D-028 records the ' +
            'frozen MVP checker limitation'
    });

export type CoreDirectedContinuationRuntimeTransferErrorCode =
    | 'REVIEWED_RUNTIME_TRANSFER_DRIFT'
    | 'UNSUPPORTED_REVIEWED_RUNTIME_EXPRESSION'
    | 'MVP_RUNTIME_TYPE_INFERENCE_FAILURE'
    | 'RUNTIME_EQUIVALENCE_FAILURE';

export class CoreDirectedContinuationRuntimeTransferError extends Error {
    constructor(
        public readonly code:
            CoreDirectedContinuationRuntimeTransferErrorCode,
        message: string
    ) {
        super(message);
        this.name =
            'CoreDirectedContinuationRuntimeTransferError';
    }
}

export interface CoreDirectedContinuationGenericTransfer {
    readonly declarations: CoreLfCompiledDeclarationModule;
    readonly runtime: CoreLfCompiledRuntimeProgram;
}

interface RuntimeEvidence {
    readonly id: string;
    readonly sourceFragment: string;
}

type BuilderScope = ReadonlyMap<
    string,
    CoreLfTransferBuilderExpression
>;

const fail = (
    code: CoreDirectedContinuationRuntimeTransferErrorCode,
    message: string
): never => {
    throw new CoreDirectedContinuationRuntimeTransferError(
        code,
        message
    );
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
            'UNSUPPORTED_REVIEWED_RUNTIME_EXPRESSION',
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
            'UNSUPPORTED_REVIEWED_RUNTIME_EXPRESSION',
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
            'UNSUPPORTED_REVIEWED_RUNTIME_EXPRESSION',
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
            'UNSUPPORTED_REVIEWED_RUNTIME_EXPRESSION',
            `${detail} has invalid plicity '${String(value)}'`
        );
    }
    return value;
};

const reviewedRuntimeExpression = (
    value: unknown,
    builder: CoreLfTransferScopedBuilder,
    scope: BuilderScope,
    detail: string
): CoreLfTransferBuilderExpression => {
    const expression = record(value, detail);
    const tag = stringField(expression.tag, `${detail}.tag`);
    switch (tag) {
        case 'type':
        case 'universe':
            return builder.type();
        case 'variable': {
            const name = stringField(
                expression.name,
                `${detail}.name`
            );
            return scope.get(name) ?? builder.capture(name);
        }
        case 'owner-application': {
            const owner = stringField(
                expression.owner,
                `${detail}.owner`
            );
            const plicities =
                coreDirectedContinuationTransferPlicities(owner);
            const arguments_ = arrayField(
                expression.arguments,
                `${detail}.arguments`
            );
            if (arguments_.length !== plicities.length) {
                return fail(
                    'UNSUPPORTED_REVIEWED_RUNTIME_EXPRESSION',
                    `${detail} applies '${owner}' to ${arguments_.length} ` +
                        `arguments, expected ${plicities.length}`
                );
            }
            const callee = builder.global(
                coreDirectedContinuationTransferSymbol(owner)
            );
            if (arguments_.length === 0) return callee;
            return builder.call(
                callee,
                arguments_.map((argument, index) => ({
                    plicity: plicities[index],
                    value: reviewedRuntimeExpression(
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
                reviewedRuntimeExpression(
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
                        value: reviewedRuntimeExpression(
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
                    'UNSUPPORTED_REVIEWED_RUNTIME_EXPRESSION',
                    `${detail}.binder.variation is invalid`
                );
            }
            const type = reviewedRuntimeExpression(
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
                return reviewedRuntimeExpression(
                    expression.body,
                    builder,
                    nextScope,
                    `${detail}.body`
                );
            };
            const mode: BinderMode = { plicity, variation };
            return tag === 'pi'
                ? builder.pi(name, type, body, mode)
                : builder.lam(name, type, body, mode);
        }
        default:
            return fail(
                'UNSUPPORTED_REVIEWED_RUNTIME_EXPRESSION',
                `${detail} has unsupported tag '${tag}'`
            );
    }
};

const runtimeEvidence = (): ReadonlyMap<string, RuntimeEvidence> => {
    const evidence: RuntimeEvidence[] = [
        ...LAMBDAPI_V32_DIRECTED_FOUNDATION_RULE_BINDINGS.map(
            binding => ({
                id: binding.id,
                sourceFragment: binding.provenance.sourceFragment
            })
        ),
        {
            id: LAMBDAPI_V32_DIRECTED_FOUNDATION_2_RULE_BINDING.id,
            sourceFragment:
                LAMBDAPI_V32_DIRECTED_FOUNDATION_2_RULE_BINDING
                    .provenance.sourceFragment
        },
        ...LAMBDAPI_V32_DIRECTED_1B_RULE_BINDINGS.map(binding => ({
            id: binding.id,
            sourceFragment: binding.provenance.sourceFragment
        })),
        ...CORE_MVP_MANIFEST.rules.map(rule => {
            const binding =
                LAMBDAPI_V32_RULE_EVIDENCE_BINDINGS[
                    rule.id as keyof
                        typeof LAMBDAPI_V32_RULE_EVIDENCE_BINDINGS
                ];
            const source_ = binding?.provenance.sources.find(
                candidate =>
                    candidate.authorityPath ===
                    'emdash2/emdash3_2.lp'
            );
            if (source_ === undefined) {
                return fail(
                    'REVIEWED_RUNTIME_TRANSFER_DRIFT',
                    `MVP runtime rule '${rule.id}' has no active source`
                );
            }
            return {
                id: rule.id,
                sourceFragment: source_.declaration
            };
        })
    ];
    const expected =
        CORE_DIRECTED_GRADUATION_MANIFEST.runtimeRules;
    if (
        evidence.length !== expected.length ||
        evidence.some((entry, index) => entry.id !== expected[index].id)
    ) {
        return fail(
            'REVIEWED_RUNTIME_TRANSFER_DRIFT',
            'Runtime evidence order differs from the reviewed manifest'
        );
    }
    return new Map(evidence.map(entry => [entry.id, entry]));
};

const evidenceById = runtimeEvidence();

const isCoreOwner = (owner: string): owner is CoreOwnerId =>
    Object.prototype.hasOwnProperty.call(CORE_OWNER_SCHEMAS, owner);

interface InferredMvpVariableType {
    readonly name: string;
    readonly type: KernelExpression;
}

const inferMvpVariableTypes = (
    rule: CoreManifestRuleInput
): readonly InferredMvpVariableType[] => {
    const nodeProvenance = provenance(
        'derived',
        `SCALE-0D inferred variable types for ${rule.id}`
    );
    const terms = new Map<string, KernelExpression>();
    const types = new Map<string, KernelExpression>();

    const inferPattern = (
        pattern: CoreRulePatternInput,
        expected?: KernelExpression
    ): KernelExpression => {
        if (pattern.tag === 'variable') {
            if (expected === undefined) {
                return fail(
                    'MVP_RUNTIME_TYPE_INFERENCE_FAILURE',
                    `Rule '${rule.id}' has a variable at an uninferable root`
                );
            }
            const existingType = types.get(pattern.name);
            if (
                existingType !== undefined &&
                !kernelExpressionEquals(existingType, expected)
            ) {
                return fail(
                    'MVP_RUNTIME_TYPE_INFERENCE_FAILURE',
                    `Rule '${rule.id}' gives variable '${pattern.name}' ` +
                        'incompatible expected types'
                );
            }
            if (existingType === undefined) {
                types.set(pattern.name, expected);
            }
            const existingTerm = terms.get(pattern.name);
            if (existingTerm !== undefined) return existingTerm;
            const term = kernelFree(
                `mvp_${pattern.name}`,
                nodeProvenance
            );
            terms.set(pattern.name, term);
            return term;
        }
        if (!isCoreOwner(pattern.owner)) {
            return fail(
                'MVP_RUNTIME_TYPE_INFERENCE_FAILURE',
                `Rule '${rule.id}' refers to non-Core owner ` +
                    `'${pattern.owner}'`
                );
        }
        const owner = pattern.owner;
        const arguments_: KernelExpression[] = [];
        pattern.arguments.forEach((argument, index) => {
            const type = coreOwnerSlotType(
                owner,
                index,
                arguments_,
                nodeProvenance
            );
            arguments_.push(inferPattern(argument, type));
        });
        return kernelApplication(
            owner,
            arguments_.map(value => ({ value })),
            nodeProvenance
        );
    };

    inferPattern(rule.left);
    return rule.variables.map(name => {
        const type = types.get(name);
        if (type === undefined) {
            return fail(
                'MVP_RUNTIME_TYPE_INFERENCE_FAILURE',
                `Rule '${rule.id}' did not infer variable '${name}'`
            );
        }
        return { name, type };
    });
};

const inferredKernelType = (
    expression: KernelExpression,
    builder: CoreLfTransferScopedBuilder,
    variableNames: ReadonlyMap<string, string>,
    detail: string
): CoreLfTransferBuilderExpression => {
    switch (expression.tag) {
        case 'universe':
            return builder.type();
        case 'reference': {
            const variable = variableNames.get(expression.name);
            if (variable === undefined) {
                return fail(
                    'MVP_RUNTIME_TYPE_INFERENCE_FAILURE',
                    `${detail} has unknown inferred free name ` +
                        `'${expression.name}'`
                );
            }
            return builder.capture(variable);
        }
        case 'application': {
            const plicities =
                coreDirectedContinuationTransferPlicities(
                    expression.owner
                );
            const callee = builder.global(
                coreDirectedContinuationTransferSymbol(
                    expression.owner
                )
            );
            if (expression.arguments.length === 0) return callee;
            return builder.call(
                callee,
                expression.arguments.map((argument, index) => ({
                    plicity: plicities[index],
                    value: inferredKernelType(
                        argument.value,
                        builder,
                        variableNames,
                        `${detail}.${expression.owner}[${index}]`
                    )
                }))
            );
        }
        case 'bound':
        case 'meta':
        case 'call':
        case 'pi':
        case 'lambda':
            return fail(
                'MVP_RUNTIME_TYPE_INFERENCE_FAILURE',
                `${detail} inferred unsupported Core tag '${expression.tag}'`
            );
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const typedVariables = (
    source: Readonly<Record<string, unknown>>,
    manifestRule: CoreManifestRuleInput | undefined,
    ruleId: string
) => {
    if (manifestRule !== undefined) {
        const inferred = inferMvpVariableTypes(manifestRule);
        const names = new Map(
            inferred.map(variable => [
                `mvp_${variable.name}`,
                variable.name
            ])
        );
        return inferred.map(variable => {
            const builder = new CoreLfTransferScopedBuilder();
            return {
                name: variable.name,
                type: builder.template(inferredKernelType(
                    variable.type,
                    builder,
                    names,
                    `${ruleId}.${variable.name}`
                ))
            };
        });
    }

    return arrayField(source.variables, `${ruleId}.variables`).map(
        (value, index) => {
            const variable = record(
                value,
                `${ruleId}.variables[${index}]`
            );
            const builder = new CoreLfTransferScopedBuilder();
            return {
                name: stringField(
                    variable.name,
                    `${ruleId}.variables[${index}].name`
                ),
                type: builder.template(reviewedRuntimeExpression(
                    variable.type,
                    builder,
                    new Map(),
                    `${ruleId}.variables[${index}].type`
                ))
            };
        }
    );
};

const runtimeRule = (
    entry: typeof CORE_DIRECTED_GRADUATION_MANIFEST.runtimeRules[number]
): CoreLfTransferRuntimeRule => {
    const source = record(
        entry.ruleSnapshot,
        `reviewed runtime ${entry.id}`
    );
    const mvpRule = entry.source === 'emdash-v3.2-mvp-1'
        ? entry.ruleSnapshot as CoreManifestRuleInput
        : undefined;
    const variables = typedVariables(source, mvpRule, entry.id);
    const patternBuilder = new CoreLfTransferScopedBuilder();
    const left = patternBuilder.pattern(reviewedRuntimeExpression(
        source.left,
        patternBuilder,
        new Map(),
        `${entry.id}.left`
    ));
    const templateBuilder = new CoreLfTransferScopedBuilder();
    const right = templateBuilder.template(reviewedRuntimeExpression(
        source.right,
        templateBuilder,
        new Map(),
        `${entry.id}.right`
    ));
    const rootOwner = (() => {
        const left_ = record(source.left, `${entry.id}.left`);
        if (left_.tag !== 'owner-application') {
            return fail(
                'REVIEWED_RUNTIME_TRANSFER_DRIFT',
                `Rule '${entry.id}' has no owner-application root`
            );
        }
        const owner = stringField(
            left_.owner,
            `${entry.id}.left.owner`
        );
        if (!isCoreOwner(owner)) {
            return fail(
                'REVIEWED_RUNTIME_TRANSFER_DRIFT',
                `Rule '${entry.id}' has non-Core root owner '${owner}'`
            );
        }
        return owner;
    })();
    const evidence = evidenceById.get(entry.id);
    if (evidence === undefined) {
        return fail(
            'REVIEWED_RUNTIME_TRANSFER_DRIFT',
            `Rule '${entry.id}' has no source evidence`
        );
    }
    return {
        order: entry.order,
        id: entry.id,
        groupId: entry.id,
        clauseOrder: 0,
        sourceOwner:
            coreDirectedContinuationTransferSymbol(rootOwner),
        variables,
        left,
        right,
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            sourceFragment: evidence.sourceFragment
        }
    };
};

const runtimeRules =
    CORE_DIRECTED_GRADUATION_MANIFEST.runtimeRules.map(runtimeRule);

const externalSymbols =
    CORE_DIRECTED_GRADUATION_MANIFEST.baseOwnerSignatures
        .map(entry => entry.owner)
        .concat(
            CORE_DIRECTED_GRADUATION_MANIFEST.candidateDeclarations
                .map(entry => entry.owner)
        )
        .map(owner => ({
            symbol: coreDirectedContinuationTransferSymbol(owner),
            availability: 'earlier-fragment' as const
        }));

export const CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_REVISION,
    moduleId: LAMBDAPI_V32_MODULE,
    fragmentId: 'reviewed-directed-continuation-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        'sha256:16b5b1adc5ec462012e03555cfe65db91679983ef370e01adb9948a0bacc61cb',
    canonicalExport: {
        exporterVersion: '3.0.0-90-gdb4f780',
        sha256:
            'sha256:18500d46d4ff3583fef1f25a3c28eff7b849a61d528a6f9e20e89b32db13f1b2'
    },
    dependencies: [],
    externalSymbols,
    declarations: [],
    inductives: [],
    runtimeRules,
    proofRules: []
});

const policyEntries: readonly CoreLfTransferPolicyEntry[] =
    runtimeRules.map(rule => ({
        order: rule.order,
        target: {
            kind: 'runtime-rule' as const,
            id: rule.id
        },
        policy: 'runtime-rewrite' as const,
        evidence:
            `Reviewed ${CORE_DIRECTED_GRADUATION_MANIFEST.runtimeRules[
                rule.order
            ].sourceReview} runtime authority`
    }));

export const CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_POLICY =
    createCoreLfTransferPolicyOverlay(
        CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE,
        {
            revision:
                CORE_DIRECTED_CONTINUATION_RUNTIME_POLICY_REVISION,
            moduleRevision:
                CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE
                    .revision,
            entries: policyEntries
        }
    );

const sameCompiledRuntimeData = (
    left: CoreLfCompiledRuntimeProgram,
    right: CoreLfCompiledRuntimeProgram
): boolean => JSON.stringify(left.rules) === JSON.stringify(right.rules);

/**
 * Bootstrap from the reviewed runtime only as an oracle, then rebuild both
 * declarations and runtime through the generic pair and return that fixed
 * point. The returned artifact contains no legacy runtime object.
 */
export function compileCoreDirectedContinuationRuntimeTransfer():
CoreDirectedContinuationGenericTransfer {
    const seedDeclarations =
        compileCoreDirectedContinuationTransfer();
    const firstRuntime = compileCoreLfRuntimeProgram(
        CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE,
        CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_POLICY,
        seedDeclarations,
        {
            subjectReductionOracle:
                CORE_DIRECTED_CONTINUATION_RUNTIME_SUBJECT_ORACLE
        }
    );
    const declarations =
        compileCoreDirectedContinuationTransferWithRuntime(firstRuntime);
    const runtime = compileCoreLfRuntimeProgram(
        CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE,
        CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_POLICY,
        declarations,
        {
            subjectReductionOracle:
                CORE_DIRECTED_CONTINUATION_RUNTIME_SUBJECT_ORACLE
        }
    );
    if (!sameCompiledRuntimeData(firstRuntime, runtime)) {
        return fail(
            'RUNTIME_EQUIVALENCE_FAILURE',
            'Generic declaration/runtime recompilation did not reach a ' +
                'stable reviewed fixed point'
        );
    }
    return Object.freeze({ declarations, runtime });
}

const legacyRewrite = (
    ruleIndex: number,
    redex: KernelExpression,
    directed: CoreDirected1bRuntimeProgram
) => ruleIndex < directed.ruleIds.length
    ? directed.rewriteHead(redex)
    : coreRuntimeRewriteHead(redex);

const oppositePlicity = (plicity: Plicity): Plicity =>
    plicity === 'explicit' ? 'implicit' : 'explicit';

const corruptFirstPlicity = (
    expression: KernelExpression
): KernelExpression | undefined => {
    switch (expression.tag) {
        case 'application':
            if (expression.arguments.length === 0) return undefined;
            return {
                ...expression,
                arguments: expression.arguments.map((argument, index) =>
                    index === 0
                        ? {
                            ...argument,
                            plicity: oppositePlicity(argument.plicity)
                        }
                        : argument
                )
            };
        case 'call':
            if (expression.arguments.length > 0) {
                return {
                    ...expression,
                    arguments: expression.arguments.map(
                        (argument, index) => index === 0
                            ? {
                                ...argument,
                                plicity:
                                    oppositePlicity(argument.plicity)
                            }
                            : argument
                    )
                };
            }
            return undefined;
        case 'pi':
        case 'lambda': {
            const body = corruptFirstPlicity(expression.body);
            return body === undefined
                ? undefined
                : { ...expression, body };
        }
        case 'universe':
        case 'reference':
        case 'bound':
        case 'meta':
            return undefined;
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

/**
 * Execute all exact migration and legacy-equivalence checks.
 */
export function validateCoreDirectedContinuationRuntimeTransferEquivalence(
    transfer: CoreDirectedContinuationGenericTransfer =
        compileCoreDirectedContinuationRuntimeTransfer()
): void {
    validateCoreDirectedContinuationTransferEquivalence(
        transfer.declarations
    );
    const expectedIds =
        CORE_DIRECTED_GRADUATION_MANIFEST.runtimeRules.map(
            entry => entry.id
        );
    if (
        JSON.stringify(transfer.runtime.ruleIds) !==
        JSON.stringify(expectedIds)
    ) {
        return fail(
            'RUNTIME_EQUIVALENCE_FAILURE',
            'Generic runtime rule order differs from the reviewed manifest'
        );
    }

    const directed = CoreDirected1bRuntimeProgram.create();
    const nodeProvenance = provenance(
        'derived',
        'SCALE-0D runtime equivalence witness'
    );
    transfer.runtime.rules.forEach((rule, ruleIndex) => {
        const bindings = rule.variables.map((variable, slot) =>
            kernelFree(
                `runtimeWitness_${ruleIndex}_${slot}_${variable.name}`,
                nodeProvenance
            )
        );
        const redex = transfer.runtime.instantiateRuleLeft(
            rule,
            bindings,
            nodeProvenance
        );
        const generic = transfer.runtime.rewriteHead(redex);
        const previous = legacyRewrite(ruleIndex, redex, directed);
        if (
            generic.status !== 'rewritten' ||
            previous.status !== 'rewritten' ||
            generic.ruleId !== rule.id ||
            previous.ruleId !== rule.id ||
            !kernelExpressionEquals(generic.after, previous.after) ||
            generic.match.bindings.length !== bindings.length ||
            previous.match.bindings.length !== bindings.length ||
            !generic.match.bindings.every((binding, index) =>
                kernelExpressionEquals(binding, bindings[index])
            ) ||
            !previous.match.bindings.every((binding, index) =>
                kernelExpressionEquals(binding, bindings[index])
            )
        ) {
            return fail(
                'RUNTIME_EQUIVALENCE_FAILURE',
                `Generic runtime differs for reviewed rule '${rule.id}'`
            );
        }

        const nearMiss = corruptFirstPlicity(redex);
        if (
            nearMiss === undefined ||
            transfer.runtime.rewriteHead(nearMiss).status !==
                'irreducible' ||
            legacyRewrite(ruleIndex, nearMiss, directed).status !==
                'irreducible'
        ) {
            return fail(
                'RUNTIME_EQUIVALENCE_FAILURE',
                `Generic runtime near miss differs for '${rule.id}'`
            );
        }
    });

    const first = transfer.runtime.rules[0];
    const firstRedex = transfer.runtime.instantiateRuleLeft(
        first,
        [],
        nodeProvenance
    );
    const bounded = transfer.runtime.weakHead(firstRedex, 0);
    if (
        bounded.status !== 'step-limit-exceeded' ||
        bounded.nextRuleId !== first.id
    ) {
        return fail(
            'RUNTIME_EQUIVALENCE_FAILURE',
            'Generic runtime does not enforce its zero-step boundary'
        );
    }

    /*
     * Revalidate the old catalog only as an oracle. The returned transfer
     * pair above owns independent generic declaration/runtime objects.
     */
    CoreDirected1bCatalog.create().createChecker().validateEnvironment();
}
