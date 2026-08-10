/**
 * Browser-safe canonical source acquisition for proof developments.
 *
 * This module reconstructs inert, portable data. It does not execute a host
 * module, read a path, compute a hash, or parse the emdash term language.
 */

import {
    CoreOwnerId,
    KernelExpression,
    Provenance,
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
    provenance,
    sourceSpan
} from './kernel';
import {
    CoreProofPlan,
    coreProofPlanApply,
    coreProofPlanExact,
    coreProofPlanHole,
    coreProofPlanIntro,
    validateCoreProofPlan
} from './proof_plan';
import {
    CoreProofArtifactFingerprint,
    validateCoreProofArtifactFingerprint
} from './proof_document';
import {
    CoreLfModuleSpecInput,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    createCoreLfTransferDeclarationLinkage
} from './lf_transfer_compiler';
import {
    CORE_LF_DECLARATION_WORKSPACE_PROFILE,
    CoreLfDeclarationWorkspaceSourceSnapshot,
    createCoreLfDeclarationWorkspace,
    createCoreLfDeclarationWorkspaceSourceSnapshot,
    defineCoreLfDeclarationWorkspaceModule,
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';
import {
    CoreLfWorkspaceProofDocumentInput
} from './lf_workspace_proof';
import {
    CORE_LF_PROOF_DEVELOPMENT_PROFILE,
    CoreLfProofDevelopmentPlan,
    createCoreLfProofDevelopment
} from './lf_proof_development';

export const CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE = Object.freeze({
    revision: 'emdash-lf-proof-development-source-v1' as const,
    developmentProfileRevision:
        CORE_LF_PROOF_DEVELOPMENT_PROFILE.revision,
    workspaceProfileRevision:
        CORE_LF_DECLARATION_WORKSPACE_PROFILE.revision,
    envelope: 'exact-canonical-json-explicit-core-data' as const,
    hostExecutionTrusted: false as const,
    parsesDeclarationSyntax: false as const,
    parsesTermSyntax: false as const,
    permitsCoreMetas: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type CoreLfProofDevelopmentSourceErrorCode =
    | 'INVALID_SOURCE_SNAPSHOT'
    | 'INVALID_SOURCE_TEXT'
    | 'NONCANONICAL_SOURCE_SNAPSHOT'
    | 'NONCANONICAL_SOURCE_TEXT';

export class CoreLfProofDevelopmentSourceError extends Error {
    constructor(
        public readonly code: CoreLfProofDevelopmentSourceErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfProofDevelopmentSourceError';
    }
}

const fail = (
    code: CoreLfProofDevelopmentSourceErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfProofDevelopmentSourceError(code, path, message);
};

const errorText = (error: unknown): string => error instanceof Error
    ? error.message
    : String(error);

const assertDataProperties = (
    value: object,
    path: string,
    array: boolean
): void => {
    const keys = Reflect.ownKeys(value);
    const stringKeys: string[] = [];
    for (const key of keys) {
        const stringKey = typeof key === 'string'
            ? key
            : fail(
                'INVALID_SOURCE_SNAPSHOT',
                path,
                'Portable proof-development data cannot have symbol keys'
            );
        if (array && stringKey === 'length') continue;
        const descriptor = Object.getOwnPropertyDescriptor(value, stringKey);
        if (
            descriptor === undefined ||
            !Object.prototype.hasOwnProperty.call(descriptor, 'value') ||
            descriptor.enumerable !== true
        ) {
            fail(
                'INVALID_SOURCE_SNAPSHOT',
                `${path}.${stringKey}`,
                'Portable proof-development fields must be enumerable data ' +
                    'properties'
            );
        }
        stringKeys.push(stringKey);
    }
    if (!array) return;
    const length = (value as readonly unknown[]).length;
    if (
        stringKeys.length !== length ||
        stringKeys.some((key, index) => key !== String(index))
    ) {
        fail(
            'INVALID_SOURCE_SNAPSHOT',
            path,
            'Portable proof-development arrays must be dense and cannot ' +
                'have extra properties'
        );
    }
};

const deepFreeze = <T>(value: T): T => {
    if (value !== null && typeof value === 'object') {
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        if (!Object.isFrozen(value)) Object.freeze(value);
    }
    return value;
};

type PortableValue =
    | null
    | boolean
    | number
    | string
    | readonly PortableValue[]
    | { readonly [key: string]: PortableValue };

/**
 * Clone inert constructor output while omitting only absent optional fields.
 * Undefined array entries and every other non-data value remain errors.
 */
const portableProjection = (
    value: unknown,
    path: string,
    ancestors: ReadonlySet<object> = new Set()
): PortableValue => {
    if (value === null) return null;
    switch (typeof value) {
        case 'boolean':
        case 'string':
            return value;
        case 'number':
            if (Number.isFinite(value)) return value;
            return fail(
                'INVALID_SOURCE_SNAPSHOT',
                path,
                'Portable proof-development data requires a finite number'
            );
        case 'object':
            break;
        case 'bigint':
        case 'function':
        case 'symbol':
        case 'undefined':
            return fail(
                'INVALID_SOURCE_SNAPSHOT',
                path,
                `Portable proof-development data cannot contain ` +
                    typeof value
            );
        default:
            return fail(
                'INVALID_SOURCE_SNAPSHOT',
                path,
                'Portable proof-development data has an unsupported value'
            );
    }
    if (ancestors.has(value)) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            path,
            'Portable proof-development data cannot contain a cycle'
        );
    }
    const nextAncestors = new Set(ancestors);
    nextAncestors.add(value);
    if (Array.isArray(value)) {
        assertDataProperties(value, path, true);
        return value.map((entry, index) => portableProjection(
            entry,
            `${path}[${index}]`,
            nextAncestors
        ));
    }
    const prototype = Object.getPrototypeOf(value);
    if (prototype !== Object.prototype && prototype !== null) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            path,
            'Portable proof-development data requires plain records'
        );
    }
    assertDataProperties(value, path, false);
    const result: Record<string, PortableValue> = {};
    for (const [key, entry] of Object.entries(
        value as Record<string, unknown>
    )) {
        if (entry === undefined) continue;
        result[key] = portableProjection(
            entry,
            `${path}.${key}`,
            nextAncestors
        );
    }
    return result;
};

const plainRecord = (value: unknown): value is Record<string, unknown> => {
    if (
        value === null ||
        typeof value !== 'object' ||
        Array.isArray(value)
    ) return false;
    const prototype = Object.getPrototypeOf(value);
    return prototype === Object.prototype || prototype === null;
};

const recordAt = (
    value: unknown,
    path: string
): Record<string, unknown> => {
    if (!plainRecord(value)) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            path,
            'Proof-development source requires a plain record'
        );
    }
    assertDataProperties(value, path, false);
    return value;
};

const arrayAt = (value: unknown, path: string): readonly unknown[] => {
    if (!Array.isArray(value)) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            path,
            'Proof-development source requires an array'
        );
    }
    assertDataProperties(value, path, true);
    return value;
};

const stringAt = (value: unknown, path: string): string =>
    typeof value === 'string'
        ? value
        : fail(
            'INVALID_SOURCE_SNAPSHOT',
            path,
            'Proof-development source requires a string'
        );

const integerAt = (value: unknown, path: string): number =>
    typeof value === 'number' && Number.isSafeInteger(value)
        ? value
        : fail(
            'INVALID_SOURCE_SNAPSHOT',
            path,
            'Proof-development source requires a safe integer'
        );

const assertKeys = (
    record: Record<string, unknown>,
    required: readonly string[],
    optional: readonly string[],
    path: string
): void => {
    const allowed = new Set([...required, ...optional]);
    const absent = required.filter(key =>
        !Object.prototype.hasOwnProperty.call(record, key)
    );
    const unsupported = Object.keys(record).filter(key => !allowed.has(key));
    if (absent.length === 0 && unsupported.length === 0) return;
    fail(
        'INVALID_SOURCE_SNAPSHOT',
        path,
        'Proof-development source has missing or unsupported fields'
    );
};

const optionalString = (
    record: Record<string, unknown>,
    key: string,
    path: string
): string | undefined => Object.prototype.hasOwnProperty.call(record, key)
    ? stringAt(record[key], `${path}.${key}`)
    : undefined;

const decodePosition = (
    value: unknown,
    path: string
): { readonly line: number; readonly column: number } => {
    const record = recordAt(value, path);
    assertKeys(record, ['line', 'column'], [], path);
    const line = integerAt(record.line, `${path}.line`);
    const column = integerAt(record.column, `${path}.column`);
    if (line < 1 || column < 1) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            path,
            'Source positions must use positive line and column numbers'
        );
    }
    return Object.freeze({ line, column });
};

const decodeProvenance = (
    value: unknown,
    path: string
): Provenance => {
    const record = recordAt(value, path);
    assertKeys(record, ['origin', 'detail'], ['span'], path);
    const origin = stringAt(record.origin, `${path}.origin`);
    if (
        origin !== 'surface' &&
        origin !== 'recovered' &&
        origin !== 'derived'
    ) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            `${path}.origin`,
            `Unsupported provenance origin '${origin}'`
        );
    }
    const detail = stringAt(record.detail, `${path}.detail`);
    if (!Object.prototype.hasOwnProperty.call(record, 'span')) {
        return provenance(origin, detail);
    }
    const spanPath = `${path}.span`;
    const span = recordAt(record.span, spanPath);
    assertKeys(span, ['file', 'start', 'end'], [], spanPath);
    const file = stringAt(span.file, `${spanPath}.file`);
    if (file.length === 0) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            `${spanPath}.file`,
            'Source span file must be nonempty'
        );
    }
    const start = decodePosition(span.start, `${spanPath}.start`);
    const end = decodePosition(span.end, `${spanPath}.end`);
    if (
        end.line < start.line ||
        (end.line === start.line && end.column < start.column)
    ) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            spanPath,
            'Source span end precedes its start'
        );
    }
    return provenance(origin, detail, sourceSpan(
        file,
        start.line,
        start.column,
        end.line,
        end.column
    ));
};

const decodeMode = (
    value: unknown,
    path: string
): ReturnType<typeof binderMode> => {
    const record = recordAt(value, path);
    assertKeys(record, ['plicity', 'variation'], [], path);
    const plicity = stringAt(record.plicity, `${path}.plicity`);
    const variation = stringAt(record.variation, `${path}.variation`);
    if (plicity !== 'explicit' && plicity !== 'implicit') {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            `${path}.plicity`,
            `Unsupported plicity '${plicity}'`
        );
    }
    if (
        variation !== 'functorial' &&
        variation !== 'natural' &&
        variation !== 'object-only'
    ) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            `${path}.variation`,
            `Unsupported variation '${variation}'`
        );
    }
    return binderMode(plicity, variation);
};

const decodeExpression = (
    value: unknown,
    path: string,
    active: Set<object> = new Set()
): KernelExpression => {
    const record = recordAt(value, path);
    if (active.has(record)) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            path,
            'Explicit Core source cannot contain a cycle'
        );
    }
    active.add(record);
    try {
        const tag = stringAt(record.tag, `${path}.tag`);
        const nodeProvenance = decodeProvenance(
            record.provenance,
            `${path}.provenance`
        );
        switch (tag) {
            case 'universe':
                assertKeys(record, ['tag', 'provenance'], [], path);
                return kernelUniverse(nodeProvenance);
            case 'reference': {
                assertKeys(
                    record,
                    ['tag', 'namespace', 'name', 'provenance'],
                    [],
                    path
                );
                if (record.namespace !== 'free') {
                    return fail(
                        'INVALID_SOURCE_SNAPSHOT',
                        `${path}.namespace`,
                        'Explicit Core references must use the free namespace'
                    );
                }
                return kernelFree(
                    stringAt(record.name, `${path}.name`),
                    nodeProvenance
                );
            }
            case 'bound':
                assertKeys(
                    record,
                    ['tag', 'index', 'provenance'],
                    [],
                    path
                );
                return kernelBound(
                    integerAt(record.index, `${path}.index`),
                    nodeProvenance
                );
            case 'meta':
                return fail(
                    'INVALID_SOURCE_SNAPSHOT',
                    path,
                    'Portable proof-development source cannot contain a ' +
                        'process-local Core metavariable'
                );
            case 'application': {
                assertKeys(
                    record,
                    ['tag', 'owner', 'arguments', 'provenance'],
                    [],
                    path
                );
                const arguments_ = arrayAt(
                    record.arguments,
                    `${path}.arguments`
                ).map((argument, index) => {
                    const argumentPath = `${path}.arguments[${index}]`;
                    const item = recordAt(argument, argumentPath);
                    assertKeys(
                        item,
                        ['plicity', 'value', 'provenance'],
                        [],
                        argumentPath
                    );
                    const plicity = stringAt(
                        item.plicity,
                        `${argumentPath}.plicity`
                    );
                    if (plicity !== 'explicit' && plicity !== 'implicit') {
                        return fail(
                            'INVALID_SOURCE_SNAPSHOT',
                            `${argumentPath}.plicity`,
                            `Unsupported plicity '${plicity}'`
                        );
                    }
                    return {
                        value: decodeExpression(
                            item.value,
                            `${argumentPath}.value`,
                            active
                        ),
                        provenance: decodeProvenance(
                            item.provenance,
                            `${argumentPath}.provenance`
                        )
                    };
                });
                return kernelApplication(
                    stringAt(record.owner, `${path}.owner`) as CoreOwnerId,
                    arguments_,
                    nodeProvenance
                );
            }
            case 'call': {
                assertKeys(
                    record,
                    ['tag', 'callee', 'arguments', 'provenance'],
                    [],
                    path
                );
                const arguments_ = arrayAt(
                    record.arguments,
                    `${path}.arguments`
                ).map((argument, index) => {
                    const argumentPath = `${path}.arguments[${index}]`;
                    const item = recordAt(argument, argumentPath);
                    assertKeys(
                        item,
                        ['plicity', 'value', 'provenance'],
                        [],
                        argumentPath
                    );
                    const plicity = stringAt(
                        item.plicity,
                        `${argumentPath}.plicity`
                    );
                    if (plicity !== 'explicit' && plicity !== 'implicit') {
                        return fail(
                            'INVALID_SOURCE_SNAPSHOT',
                            `${argumentPath}.plicity`,
                            `Unsupported plicity '${plicity}'`
                        );
                    }
                    const canonicalPlicity: 'explicit' | 'implicit' =
                        plicity;
                    return {
                        plicity: canonicalPlicity,
                        value: decodeExpression(
                            item.value,
                            `${argumentPath}.value`,
                            active
                        ),
                        provenance: decodeProvenance(
                            item.provenance,
                            `${argumentPath}.provenance`
                        )
                    };
                });
                return kernelCall(
                    decodeExpression(
                        record.callee,
                        `${path}.callee`,
                        active
                    ),
                    arguments_,
                    nodeProvenance
                );
            }
            case 'pi':
            case 'lambda': {
                assertKeys(
                    record,
                    ['tag', 'binder', 'body', 'provenance'],
                    [],
                    path
                );
                const binderPath = `${path}.binder`;
                const binder = recordAt(record.binder, binderPath);
                assertKeys(
                    binder,
                    ['name', 'type', 'mode', 'provenance'],
                    [],
                    binderPath
                );
                const rebuiltBinder = kernelBinder(
                    stringAt(binder.name, `${binderPath}.name`),
                    decodeExpression(
                        binder.type,
                        `${binderPath}.type`,
                        active
                    ),
                    decodeMode(binder.mode, `${binderPath}.mode`),
                    decodeProvenance(
                        binder.provenance,
                        `${binderPath}.provenance`
                    )
                );
                const body = decodeExpression(
                    record.body,
                    `${path}.body`,
                    active
                );
                return tag === 'pi'
                    ? kernelPi(rebuiltBinder, body, nodeProvenance)
                    : kernelLambda(rebuiltBinder, body, nodeProvenance);
            }
            default:
                return fail(
                    'INVALID_SOURCE_SNAPSHOT',
                    `${path}.tag`,
                    `Unsupported explicit Core tag '${tag}'`
                );
        }
    } finally {
        active.delete(record);
    }
};

const decodePlan = (
    value: unknown,
    path: string,
    active: Set<object> = new Set()
): CoreProofPlan => {
    const record = recordAt(value, path);
    if (active.has(record)) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            path,
            'Proof plan source cannot contain a cycle'
        );
    }
    active.add(record);
    try {
        const tag = stringAt(record.tag, `${path}.tag`);
        const id = optionalString(record, 'id', path);
        const nodeProvenance = decodeProvenance(
            record.provenance,
            `${path}.provenance`
        );
        switch (tag) {
            case 'exact':
                assertKeys(
                    record,
                    ['tag', 'provenance', 'solution'],
                    ['id'],
                    path
                );
                return coreProofPlanExact(
                    decodeExpression(record.solution, `${path}.solution`),
                    { id, provenance: nodeProvenance }
                );
            case 'intro':
                assertKeys(
                    record,
                    ['tag', 'provenance', 'body'],
                    ['id', 'name'],
                    path
                );
                return coreProofPlanIntro(
                    decodePlan(record.body, `${path}.body`, active),
                    {
                        id,
                        name: optionalString(record, 'name', path),
                        provenance: nodeProvenance
                    }
                );
            case 'apply':
                assertKeys(
                    record,
                    ['tag', 'provenance', 'callee', 'premises'],
                    ['id'],
                    path
                );
                return coreProofPlanApply(
                    decodeExpression(record.callee, `${path}.callee`),
                    arrayAt(record.premises, `${path}.premises`).map(
                        (premise, index) => decodePlan(
                            premise,
                            `${path}.premises[${index}]`,
                            active
                        )
                    ),
                    { id, provenance: nodeProvenance }
                );
            case 'hole': {
                assertKeys(
                    record,
                    ['tag', 'provenance', 'goalId'],
                    ['id', 'expectation'],
                    path
                );
                let expectation;
                if (
                    Object.prototype.hasOwnProperty.call(
                        record,
                        'expectation'
                    )
                ) {
                    const expectationPath = `${path}.expectation`;
                    const source = recordAt(
                        record.expectation,
                        expectationPath
                    );
                    assertKeys(
                        source,
                        [],
                        ['contextDepth', 'target'],
                        expectationPath
                    );
                    expectation = Object.freeze({
                        ...(Object.prototype.hasOwnProperty.call(
                            source,
                            'contextDepth'
                        )
                            ? {
                                contextDepth: integerAt(
                                    source.contextDepth,
                                    `${expectationPath}.contextDepth`
                                )
                            }
                            : {}),
                        ...(Object.prototype.hasOwnProperty.call(
                            source,
                            'target'
                        )
                            ? {
                                target: decodeExpression(
                                    source.target,
                                    `${expectationPath}.target`
                                )
                            }
                            : {})
                    });
                }
                return coreProofPlanHole(
                    stringAt(record.goalId, `${path}.goalId`),
                    { id, provenance: nodeProvenance, expectation }
                );
            }
            default:
                return fail(
                    'INVALID_SOURCE_SNAPSHOT',
                    `${path}.tag`,
                    `Unsupported proof-plan tag '${tag}'`
                );
        }
    } finally {
        active.delete(record);
    }
};

const decodeProof = (
    value: unknown,
    path: string
): CoreLfWorkspaceProofDocumentInput => {
    const record = recordAt(value, path);
    assertKeys(record, [
        'moduleId',
        'declarationId',
        'type',
        'plan',
        'provenance',
        'fingerprint'
    ], [], path);
    const plan = decodePlan(record.plan, `${path}.plan`);
    validateCoreProofPlan(plan);
    const assertPlanScoped = (
        node: CoreProofPlan,
        depth: number
    ): void => {
        switch (node.tag) {
            case 'exact':
                kernelAssertScoped(node.solution, depth);
                return;
            case 'intro':
                assertPlanScoped(node.body, depth + 1);
                return;
            case 'apply':
                kernelAssertScoped(node.callee, depth);
                node.premises.forEach(premise =>
                    assertPlanScoped(premise, depth)
                );
                return;
            case 'hole':
                if (node.expectation?.target !== undefined) {
                    kernelAssertScoped(node.expectation.target, depth);
                }
                return;
            default: {
                const exhaustive: never = node;
                return exhaustive;
            }
        }
    };
    assertPlanScoped(plan, 0);
    const fingerprint = validateCoreProofArtifactFingerprint(
        record.fingerprint as CoreProofArtifactFingerprint
    );
    const type = decodeExpression(record.type, `${path}.type`);
    kernelAssertScoped(type, 0);
    return Object.freeze({
        moduleId: stringAt(record.moduleId, `${path}.moduleId`),
        declarationId: stringAt(
            record.declarationId,
            `${path}.declarationId`
        ),
        type,
        plan,
        provenance: decodeProvenance(
            record.provenance,
            `${path}.provenance`
        ),
        fingerprint
    });
};

const decodeModuleSource = (
    value: unknown,
    path: string
): CoreLfDeclarationWorkspaceSourceSnapshot => {
    const record = recordAt(value, path);
    assertKeys(record, ['revision', 'module', 'policy', 'linkage'], [], path);
    if (
        record.revision !==
            CORE_LF_DECLARATION_WORKSPACE_PROFILE.sourceSnapshotRevision
    ) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            `${path}.revision`,
            'Unsupported declaration-module source revision'
        );
    }

    const modulePath = `${path}.module`;
    const moduleRecord = recordAt(record.module, modulePath);
    assertKeys(moduleRecord, [
        'revision',
        'moduleId',
        'fragmentId',
        'authorityPath',
        'sourceSha256',
        'dependencies',
        'externalSymbols',
        'declarations',
        'inductives',
        'runtimeRules',
        'proofRules',
        'referencedSymbols'
    ], ['canonicalExport'], modulePath);
    const moduleInput: CoreLfModuleSpecInput = {
        revision: stringAt(moduleRecord.revision, `${modulePath}.revision`),
        moduleId: stringAt(moduleRecord.moduleId, `${modulePath}.moduleId`),
        fragmentId: stringAt(
            moduleRecord.fragmentId,
            `${modulePath}.fragmentId`
        ),
        authorityPath: stringAt(
            moduleRecord.authorityPath,
            `${modulePath}.authorityPath`
        ),
        sourceSha256: stringAt(
            moduleRecord.sourceSha256,
            `${modulePath}.sourceSha256`
        ),
        ...(Object.prototype.hasOwnProperty.call(
            moduleRecord,
            'canonicalExport'
        )
            ? {
                canonicalExport: moduleRecord.canonicalExport as
                    CoreLfModuleSpecInput['canonicalExport']
            }
            : {}),
        dependencies: arrayAt(
            moduleRecord.dependencies,
            `${modulePath}.dependencies`
        ) as CoreLfModuleSpecInput['dependencies'],
        externalSymbols: arrayAt(
            moduleRecord.externalSymbols,
            `${modulePath}.externalSymbols`
        ) as CoreLfModuleSpecInput['externalSymbols'],
        declarations: arrayAt(
            moduleRecord.declarations,
            `${modulePath}.declarations`
        ) as CoreLfModuleSpecInput['declarations'],
        inductives: arrayAt(
            moduleRecord.inductives,
            `${modulePath}.inductives`
        ) as CoreLfModuleSpecInput['inductives'],
        runtimeRules: arrayAt(
            moduleRecord.runtimeRules,
            `${modulePath}.runtimeRules`
        ) as CoreLfModuleSpecInput['runtimeRules'],
        proofRules: arrayAt(
            moduleRecord.proofRules,
            `${modulePath}.proofRules`
        ) as CoreLfModuleSpecInput['proofRules']
    };
    const module = createCoreLfModuleSpec(moduleInput);

    const policyPath = `${path}.policy`;
    const policyRecord = recordAt(record.policy, policyPath);
    assertKeys(policyRecord, [
        'revision',
        'moduleRevision',
        'moduleId',
        'fragmentId',
        'entries'
    ], [], policyPath);
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: stringAt(policyRecord.revision, `${policyPath}.revision`),
        moduleRevision: stringAt(
            policyRecord.moduleRevision,
            `${policyPath}.moduleRevision`
        ),
        entries: arrayAt(
            policyRecord.entries,
            `${policyPath}.entries`
        ) as Parameters<typeof createCoreLfTransferPolicyOverlay>[1]['entries']
    });

    const linkagePath = `${path}.linkage`;
    const linkageRecord = recordAt(record.linkage, linkagePath);
    assertKeys(linkageRecord, [
        'revision',
        'moduleRevision',
        'moduleId',
        'fragmentId',
        'entries'
    ], [], linkagePath);
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: stringAt(
            linkageRecord.revision,
            `${linkagePath}.revision`
        ),
        moduleRevision: stringAt(
            linkageRecord.moduleRevision,
            `${linkagePath}.moduleRevision`
        ),
        entries: arrayAt(
            linkageRecord.entries,
            `${linkagePath}.entries`
        ) as Parameters<
            typeof createCoreLfTransferDeclarationLinkage
        >[1]['entries']
    });

    return createCoreLfDeclarationWorkspaceSourceSnapshot(
        defineCoreLfDeclarationWorkspaceModule({ module, policy, linkage })
    );
};

export interface CoreLfProofDevelopmentSourceSnapshot {
    readonly revision:
        typeof CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.revision;
    readonly profileRevision:
        typeof CORE_LF_PROOF_DEVELOPMENT_PROFILE.revision;
    readonly developmentRevision: string;
    readonly workspaceRevision: string;
    readonly modules:
        readonly CoreLfDeclarationWorkspaceSourceSnapshot[];
    readonly proofs: readonly CoreLfWorkspaceProofDocumentInput[];
}

export interface CoreLfProofDevelopmentSourceReconstruction {
    readonly snapshot: CoreLfProofDevelopmentSourceSnapshot;
    readonly plan: CoreLfProofDevelopmentPlan;
    readonly sourceText: string;
}

const snapshotFromPlan = (
    plan: CoreLfProofDevelopmentPlan
): CoreLfProofDevelopmentSourceSnapshot => deepFreeze(
    portableProjection({
        revision: CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.revision,
        profileRevision: CORE_LF_PROOF_DEVELOPMENT_PROFILE.revision,
        developmentRevision: plan.revision,
        workspaceRevision: plan.workspace.revision,
        modules: plan.workspace.modules.map(
            createCoreLfDeclarationWorkspaceSourceSnapshot
        ),
        proofs: [...plan.proofs]
    }, 'proofDevelopmentSourceSnapshot') as unknown as
        CoreLfProofDevelopmentSourceSnapshot
);

const reconstructSnapshot = (
    value: unknown
): CoreLfProofDevelopmentSourceReconstruction => {
    const record = recordAt(value, 'sourceSnapshot');
    assertKeys(record, [
        'revision',
        'profileRevision',
        'developmentRevision',
        'workspaceRevision',
        'modules',
        'proofs'
    ], [], 'sourceSnapshot');
    if (record.revision !== CORE_LF_PROOF_DEVELOPMENT_SOURCE_PROFILE.revision) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            'sourceSnapshot.revision',
            'Unsupported proof-development source revision'
        );
    }
    if (record.profileRevision !== CORE_LF_PROOF_DEVELOPMENT_PROFILE.revision) {
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            'sourceSnapshot.profileRevision',
            'Unsupported proof-development profile revision'
        );
    }
    const modules = arrayAt(
        record.modules,
        'sourceSnapshot.modules'
    ).map((module, index) => decodeModuleSource(
        module,
        `sourceSnapshot.modules[${index}]`
    ));
    const workspace = createCoreLfDeclarationWorkspace({
        revision: stringAt(
            record.workspaceRevision,
            'sourceSnapshot.workspaceRevision'
        ),
        modules: modules.map(source => ({
            module: source.module,
            policy: source.policy,
            linkage: source.linkage
        }))
    });
    const proofs = arrayAt(
        record.proofs,
        'sourceSnapshot.proofs'
    ).map((proof, index) => decodeProof(
        proof,
        `sourceSnapshot.proofs[${index}]`
    ));
    const plan = createCoreLfProofDevelopment({
        revision: stringAt(
            record.developmentRevision,
            'sourceSnapshot.developmentRevision'
        ),
        workspace,
        proofs
    });
    const snapshot = snapshotFromPlan(plan);
    const sourceText = serializeCoreLfWorkspaceCanonicalJson(
        snapshot,
        'proofDevelopmentSourceSnapshot'
    );
    const suppliedText = serializeCoreLfWorkspaceCanonicalJson(
        value,
        'suppliedProofDevelopmentSourceSnapshot'
    );
    if (suppliedText !== sourceText) {
        return fail(
            'NONCANONICAL_SOURCE_SNAPSHOT',
            'sourceSnapshot',
            'Proof-development source differs from canonical reconstruction'
        );
    }
    return deepFreeze({ snapshot, plan, sourceText });
};

/** Validate direct TypeScript data and project it to canonical portable data. */
export function createCoreLfProofDevelopmentSourceSnapshot(
    inputPlan: CoreLfProofDevelopmentPlan
): CoreLfProofDevelopmentSourceSnapshot {
    try {
        const workspace = createCoreLfDeclarationWorkspace({
            revision: inputPlan.workspace.revision,
            modules: inputPlan.workspace.modules
        });
        const plan = createCoreLfProofDevelopment({
            revision: inputPlan.revision,
            workspace,
            proofs: inputPlan.proofs
        });
        const portableText = serializeCoreLfWorkspaceCanonicalJson(
            snapshotFromPlan(plan),
            'proofDevelopmentSourceSnapshot'
        );
        return reconstructSnapshot(JSON.parse(portableText)).snapshot;
    } catch (error: unknown) {
        if (error instanceof CoreLfProofDevelopmentSourceError) throw error;
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            'sourceSnapshot',
            `Proof-development source construction failed: ${errorText(error)}`
        );
    }
}

/** Deterministic exact-byte representation for mounted or transported data. */
export const serializeCoreLfProofDevelopmentSourceSnapshot = (
    snapshot: CoreLfProofDevelopmentSourceSnapshot
): string => serializeCoreLfWorkspaceCanonicalJson(
    snapshot,
    'proofDevelopmentSourceSnapshot'
);

/** Re-run every source constructor from an unknown portable value. */
export function reconstructCoreLfProofDevelopmentSourceSnapshot(
    value: unknown
): CoreLfProofDevelopmentSourceReconstruction {
    try {
        return reconstructSnapshot(value);
    } catch (error: unknown) {
        if (error instanceof CoreLfProofDevelopmentSourceError) throw error;
        return fail(
            'INVALID_SOURCE_SNAPSHOT',
            'sourceSnapshot',
            `Proof-development source reconstruction failed: ` +
                errorText(error)
        );
    }
}

/** Parse only the exact canonical serializer output. */
export function parseCoreLfProofDevelopmentSourceText(
    sourceText: string
): CoreLfProofDevelopmentSourceReconstruction {
    if (typeof sourceText !== 'string' || sourceText.length === 0) {
        return fail(
            'INVALID_SOURCE_TEXT',
            'sourceText',
            'Proof-development source text must be nonempty'
        );
    }
    let value: unknown;
    try {
        value = JSON.parse(sourceText);
    } catch {
        return fail(
            'INVALID_SOURCE_TEXT',
            'sourceText',
            'Proof-development source text is not valid JSON'
        );
    }
    const result = reconstructCoreLfProofDevelopmentSourceSnapshot(value);
    if (result.sourceText !== sourceText) {
        return fail(
            'NONCANONICAL_SOURCE_TEXT',
            'sourceText',
            'Proof-development source must be exact canonical serializer output'
        );
    }
    return result;
}
