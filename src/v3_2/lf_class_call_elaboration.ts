/**
 * Saturated dependent-call elaboration with explicit class-binder metadata.
 *
 * This management layer inserts ordinary implicit metas, delays annotated
 * instance requests until ground, invokes the immutable bounded resolver,
 * and returns only fully explicit checked Core. It owns no parser, registry,
 * workspace mutation, process service, or backend execution.
 */

import {
    CoreCheckerError,
    isCoreKind
} from './checker';
import { CoreContext } from './context';
import { serializeCoreExpressionAtDepth } from './core_serialization';
import {
    CoreLfClassInheritanceLayout,
    validateCoreLfClassInheritanceLayout
} from './lf_class_inheritance';
import { CoreLfClassReference } from './lf_class_schema';
import {
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    createCoreLfChecker
} from './lf_checker';
import {
    CoreLfInstanceRegistrySnapshot,
    CoreLfInstanceScopeError,
    CoreLfInstanceScopeSnapshot,
    createCoreLfInstanceRegistrySnapshot,
    createCoreLfInstanceScopeSnapshot,
    serializeCoreLfInstanceRegistrySnapshot,
    serializeCoreLfInstanceScopeSnapshot
} from './lf_instance_scope';
import {
    CoreLfInstanceSynthesisLimitsInput,
    CoreLfInstanceSynthesisReport,
    CoreLfInstanceSynthesisStatus,
    synthesizeCoreLfInstance
} from './lf_instance_synthesis';
import {
    CoreLfInstanceRoleSynthesisReport,
    CoreLfInstanceRoleTargetArgumentInput,
    synthesizeCoreLfInstanceByRoles
} from './lf_instance_role_synthesis';
import { CoreLfCatalogRuntime } from './lf_conversion';
import { CoreLfMixedDeclarationBaseContext } from './lf_transfer_mixed';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import {
    BinderMode,
    KernelCallArgumentInput,
    KernelExpression,
    KernelMetaVariable,
    Provenance,
    kernelCall,
    kernelInstantiate,
    kernelUniverse,
    provenance
} from './kernel';

export const CORE_LF_CLASS_CALL_ELABORATION_PROFILE = Object.freeze({
    revision: 'emdash-lf-class-call-elaboration-v2' as const,
    callShape: 'saturated-dependent-pi' as const,
    defaultMaxBinders: 128,
    instanceScheduling:
        'binder-order-ground-or-whole-output-meta-after-ordinary-inference' as const,
    expectedOutcomes: Object.freeze([
        'elaborated',
        'missing',
        'stuck',
        'ambiguous',
        'limit-exceeded'
    ] as const),
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type CoreLfClassCallElaborationStatus =
    typeof CORE_LF_CLASS_CALL_ELABORATION_PROFILE.expectedOutcomes[number];

export type CoreLfClassCallElaborationErrorCode =
    | 'INVALID_INPUT'
    | 'INVALID_CONTEXT'
    | 'INVALID_CALLEE'
    | 'INVALID_ARGUMENT'
    | 'MISSING_EXPLICIT_ARGUMENT'
    | 'TOO_MANY_ARGUMENTS'
    | 'INVALID_INSTANCE_BINDER'
    | 'DUPLICATE_INSTANCE_BINDER'
    | 'INVALID_CLASS_HEAD'
    | 'INVALID_EXPECTED_TYPE'
    | 'INVALID_LIMITS'
    | 'INVALID_REGISTRY'
    | 'INVALID_SCOPE'
    | 'INVALID_SYNTHESIS_ARTIFACT'
    | 'RESULT_TYPE_MISMATCH'
    | 'NON_PORTABLE_DATA'
    | 'INTERNAL_INVARIANT';

export class CoreLfClassCallElaborationError extends Error {
    constructor(
        public readonly code: CoreLfClassCallElaborationErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(message);
        this.name = 'CoreLfClassCallElaborationError';
    }
}

export interface CoreLfClassCallInstanceBinderInput {
    readonly binderOrdinal: number;
    readonly requestId: string;
    readonly classLayout: CoreLfClassInheritanceLayout;
}

export interface CoreLfSaturatedClassCallInput {
    readonly declarations: CoreLfMixedDeclarationBaseContext;
    readonly context: CoreContext;
    readonly runtimeProgram?: CoreLfCatalogRuntime;
    readonly callee: KernelExpression;
    readonly arguments: readonly KernelCallArgumentInput[];
    readonly instanceBinders:
        readonly CoreLfClassCallInstanceBinderInput[];
    readonly expectedType?: KernelExpression;
    readonly registry: CoreLfInstanceRegistrySnapshot;
    readonly scope: CoreLfInstanceScopeSnapshot;
    readonly synthesisLimits?: CoreLfInstanceSynthesisLimitsInput;
    readonly maxBinders?: number;
    readonly provenance: Provenance;
}

export type CoreLfClassCallBinderDisposition =
    | 'provided'
    | 'inferred-implicit'
    | 'synthesized'
    | 'pending'
    | 'skipped';

export interface CoreLfClassCallBinderTrace {
    readonly ordinal: number;
    readonly binderName: string;
    readonly mode: BinderMode;
    readonly type: string;
    readonly disposition: CoreLfClassCallBinderDisposition;
    readonly reason: string;
    readonly value?: string;
    readonly requestId?: string;
    readonly class?: CoreLfClassReference;
    readonly synthesis?: CoreLfInstanceSynthesisReport;
    readonly roleSynthesis?: CoreLfInstanceRoleSynthesisReport;
}

export interface CoreLfClassCallRuntimeFingerprintMaterial {
    readonly revision?: string;
    readonly ruleIds: readonly string[];
}

export interface CoreLfClassCallScopeFingerprintMaterial {
    readonly registryCanonicalJson: string;
    readonly scopeCanonicalJson: string;
}

export interface CoreLfClassCallElaborationReport {
    readonly revision:
        typeof CORE_LF_CLASS_CALL_ELABORATION_PROFILE.revision;
    readonly status: CoreLfClassCallElaborationStatus;
    readonly reason: string;
    readonly contextDepth: number;
    readonly maxBinders: number;
    readonly callee: string;
    readonly suppliedArgumentCount: number;
    readonly expectedType?: string;
    readonly registryRevision: string;
    readonly scopeRevision: string;
    readonly scopeFingerprintMaterial:
        CoreLfClassCallScopeFingerprintMaterial;
    readonly runtimeFingerprintMaterial:
        CoreLfClassCallRuntimeFingerprintMaterial;
    readonly binders: readonly CoreLfClassCallBinderTrace[];
    readonly term?: string;
    readonly type?: string;
}

interface CoreLfClassCallOutcomeBase {
    readonly status: CoreLfClassCallElaborationStatus;
    readonly report: CoreLfClassCallElaborationReport;
}

export interface CoreLfClassCallElaborated
extends CoreLfClassCallOutcomeBase {
    readonly status: 'elaborated';
    readonly term: KernelExpression;
    readonly type: KernelExpression;
    readonly expectedType?: KernelExpression;
}

export interface CoreLfClassCallUnsolved
extends CoreLfClassCallOutcomeBase {
    readonly status:
        | 'missing'
        | 'stuck'
        | 'ambiguous'
        | 'limit-exceeded';
}

export type CoreLfClassCallElaborationOutcome =
    | CoreLfClassCallElaborated
    | CoreLfClassCallUnsolved;

interface ValidatedSnapshots {
    readonly registry: CoreLfInstanceRegistrySnapshot;
    readonly scope: CoreLfInstanceScopeSnapshot;
    readonly registryCanonicalJson: string;
    readonly scopeCanonicalJson: string;
}

interface ValidatedInstanceBinder {
    readonly binderOrdinal: number;
    readonly requestId: string;
    readonly layout: CoreLfClassInheritanceLayout;
}

interface MutableBinderTrace {
    ordinal: number;
    binderName: string;
    mode: BinderMode;
    type: KernelExpression;
    disposition: CoreLfClassCallBinderDisposition;
    reason: string;
    value?: KernelExpression;
    requestId?: string;
    class?: CoreLfClassReference;
    synthesis?: CoreLfInstanceSynthesisReport;
    roleSynthesis?: CoreLfInstanceRoleSynthesisReport;
}

interface PlannedBinder {
    readonly trace: MutableBinderTrace;
    readonly supplied?: KernelCallArgumentInput;
    readonly meta?: KernelMetaVariable;
    readonly instance?: ValidatedInstanceBinder;
    checkedValue: KernelExpression;
}

interface PendingInstanceRequest {
    readonly plan: PlannedBinder;
    readonly meta: KernelMetaVariable;
    readonly instance: ValidatedInstanceBinder;
    resolved: boolean;
}

interface ReadyResolution {
    readonly progress: boolean;
    readonly failure?: Exclude<
        CoreLfInstanceSynthesisStatus,
        'solved'
    >;
    readonly reason?: string;
    readonly failedRequest?: PendingInstanceRequest;
}

const fail = (
    code: CoreLfClassCallElaborationErrorCode,
    path: string,
    message: string,
    underlying?: Error
): never => {
    throw new CoreLfClassCallElaborationError(
        code,
        path,
        message,
        underlying
    );
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const objectValue = (value: unknown): boolean =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

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

const cloneData = <T>(value: T): T => {
    if (Array.isArray(value)) return value.map(cloneData) as T;
    if (value !== null && typeof value === 'object') {
        return Object.fromEntries(
            Object.entries(value as Record<string, unknown>)
                .filter(([, entry]) => entry !== undefined)
                .map(([key, entry]) => [key, cloneData(entry)])
        ) as T;
    }
    return value;
};

const freezeData = <T>(value: T): T => deepFreeze(cloneData(value));

const containsMeta = (expression: KernelExpression): boolean => {
    switch (expression.tag) {
        case 'universe':
        case 'reference':
        case 'bound':
            return false;
        case 'meta':
            return true;
        case 'application':
            return expression.arguments.some(argument =>
                containsMeta(argument.value)
            );
        case 'call':
            return containsMeta(expression.callee) ||
                expression.arguments.some(argument =>
                    containsMeta(argument.value)
                );
        case 'pi':
        case 'lambda':
            return containsMeta(expression.binder.type) ||
                containsMeta(expression.body);
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const sameSymbol = (
    left: { readonly moduleId: string; readonly name: string },
    right: { readonly moduleId: string; readonly name: string }
): boolean =>
    left.moduleId === right.moduleId && left.name === right.name;

const cloneClass = (
    value: CoreLfClassReference
): CoreLfClassReference => ({
    classId: { ...value.classId },
    parameterCount: value.parameterCount
});

const checkedLimit = (
    value: unknown,
    path: string
): number => {
    if (!Number.isSafeInteger(value) || (value as number) < 0) {
        return fail(
            'INVALID_LIMITS',
            path,
            'Class-call limits must be nonnegative safe integers'
        );
    }
    return value as number;
};

const validateSynthesisLimits = (
    limits: CoreLfInstanceSynthesisLimitsInput | undefined
): void => {
    if (limits === undefined) return;
    if (!record(limits)) {
        return fail(
            'INVALID_LIMITS',
            'input.synthesisLimits',
            'Synthesis limits must be an object when supplied'
        );
    }
    const fields = [
        'maxDepth',
        'maxTableEntries',
        'maxResultSize',
        'maxFuel',
        'comparisonStepLimit'
    ] as const;
    fields.forEach(field => {
        const value = limits[field];
        if (value !== undefined) {
            checkedLimit(value, `input.synthesisLimits.${field}`);
        }
    });
};

const comparisonStepLimit = (
    limits: CoreLfInstanceSynthesisLimitsInput | undefined
): number => limits?.comparisonStepLimit ??
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT;

const runtimeFingerprint = (
    runtimeProgram: CoreLfCatalogRuntime | undefined
): CoreLfClassCallRuntimeFingerprintMaterial => {
    if (runtimeProgram === undefined) return { ruleIds: [] };
    if (
        !record(runtimeProgram) ||
        typeof runtimeProgram.revision !== 'string' ||
        runtimeProgram.revision.length === 0 ||
        !Array.isArray(runtimeProgram.ruleIds) ||
        runtimeProgram.ruleIds.some(ruleId =>
            typeof ruleId !== 'string' || ruleId.length === 0
        ) ||
        new Set(runtimeProgram.ruleIds).size !== runtimeProgram.ruleIds.length ||
        typeof runtimeProgram.rewriteHead !== 'function'
    ) {
        return fail(
            'INVALID_INPUT',
            'input.runtimeProgram',
            'Class-call runtime must be one reviewed catalog runtime'
        );
    }
    return {
        revision: runtimeProgram.revision,
        ruleIds: [...runtimeProgram.ruleIds]
    };
};

const validateSnapshots = (
    registryInput: CoreLfInstanceRegistrySnapshot,
    scopeInput: CoreLfInstanceScopeSnapshot
): ValidatedSnapshots => {
    let phase: 'registry' | 'scope' = 'registry';
    try {
        if (!record(registryInput)) {
            return fail(
                'INVALID_REGISTRY',
                'input.registry',
                'Class-call elaboration requires one registry snapshot'
            );
        }
        const registry = createCoreLfInstanceRegistrySnapshot({
            revision: registryInput.registryRevision,
            providers: registryInput.providers
        });
        const registryCanonicalJson =
            serializeCoreLfInstanceRegistrySnapshot(registry);
        if (
            serializeCoreLfInstanceRegistrySnapshot(registryInput) !==
            registryCanonicalJson
        ) {
            return fail(
                'INVALID_REGISTRY',
                'input.registry',
                'Class-call registry is not its canonical validated snapshot'
            );
        }
        phase = 'scope';
        if (
            !record(scopeInput) ||
            !Array.isArray(scopeInput.localFrames) ||
            !Array.isArray(scopeInput.openedNamedScopes) ||
            !Array.isArray(scopeInput.imports)
        ) {
            return fail(
                'INVALID_SCOPE',
                'input.scope',
                'Class-call elaboration requires one complete scope snapshot'
            );
        }
        const scope = createCoreLfInstanceScopeSnapshot({
            revision: scopeInput.scopeRevision,
            registry,
            moduleId: scopeInput.moduleId,
            contextDepth: scopeInput.contextDepth,
            localFrames: scopeInput.localFrames.map(frame => ({
                frameId: frame.frameId,
                kind: frame.kind,
                providers: frame.providers
            })),
            openedNamedScopes: scopeInput.openedNamedScopes,
            imports: scopeInput.imports.map(importEntry => ({
                moduleId: importEntry.moduleId,
                moduleRevision: importEntry.moduleRevision,
                interfaceRevision: importEntry.interfaceRevision,
                interfaceSha256: importEntry.interfaceSha256,
                providers: importEntry.providers
            }))
        });
        const scopeCanonicalJson =
            serializeCoreLfInstanceScopeSnapshot(scope);
        if (
            serializeCoreLfInstanceScopeSnapshot(scopeInput) !==
            scopeCanonicalJson
        ) {
            return fail(
                'INVALID_SCOPE',
                'input.scope',
                'Class-call scope is not its canonical validated snapshot'
            );
        }
        return {
            registry,
            scope,
            registryCanonicalJson,
            scopeCanonicalJson
        };
    } catch (error: unknown) {
        if (error instanceof CoreLfClassCallElaborationError) throw error;
        if (!(error instanceof CoreLfInstanceScopeError)) throw error;
        const code = phase === 'registry'
            ? 'INVALID_REGISTRY'
            : 'INVALID_SCOPE';
        return fail(
            code,
            code === 'INVALID_REGISTRY' ? 'input.registry' : 'input.scope',
            `Invalid class-call ${phase} snapshot`,
            error
        );
    }
};

const validateInstanceBinders = (
    values: readonly CoreLfClassCallInstanceBinderInput[]
): ReadonlyMap<number, ValidatedInstanceBinder> => {
    if (!Array.isArray(values)) {
        return fail(
            'INVALID_INSTANCE_BINDER',
            'input.instanceBinders',
            'Instance-binder annotations must be a finite array'
        );
    }
    const byOrdinal = new Map<number, ValidatedInstanceBinder>();
    const requestIds = new Set<string>();
    values.forEach((value, index) => {
        const path = `input.instanceBinders[${index}]`;
        if (
            !record(value) ||
            !Number.isSafeInteger(value.binderOrdinal) ||
            (value.binderOrdinal as number) < 0 ||
            typeof value.requestId !== 'string' ||
            !/^[A-Za-z_][A-Za-z0-9_.-]*$/u.test(value.requestId)
        ) {
            return fail(
                'INVALID_INSTANCE_BINDER',
                path,
                'Instance binder requires an ordinal and stable request ID'
            );
        }
        const ordinal = value.binderOrdinal as number;
        if (byOrdinal.has(ordinal) || requestIds.has(value.requestId)) {
            return fail(
                'DUPLICATE_INSTANCE_BINDER',
                path,
                'Instance binder ordinal and request ID must both be unique'
            );
        }
        let layout: CoreLfClassInheritanceLayout;
        try {
            layout = validateCoreLfClassInheritanceLayout(value.classLayout);
        } catch (error: unknown) {
            return fail(
                'INVALID_INSTANCE_BINDER',
                `${path}.classLayout`,
                'Instance binder requires one completed class layout',
                error instanceof Error ? error : undefined
            );
        }
        const validated = {
            binderOrdinal: ordinal,
            requestId: value.requestId,
            layout
        };
        byOrdinal.set(ordinal, validated);
        requestIds.add(value.requestId);
    });
    return byOrdinal;
};

const validateClassTarget = (
    declarations: CoreLfMixedDeclarationBaseContext,
    instance: ValidatedInstanceBinder,
    mode: BinderMode,
    type: KernelExpression,
    path: string
): CoreLfClassReference => {
    if (mode.plicity !== 'implicit') {
        return fail(
            'INVALID_INSTANCE_BINDER',
            path,
            'An instance annotation must target an implicit Pi binder'
        );
    }
    const classId = instance.layout.classId;
    const declaration = declarations.declaration(classId);
    if (
        declaration === undefined ||
        declaration.link.kind !== 'free-declaration' ||
        !sameSymbol(declaration.symbol, classId) ||
        !sameSymbol(declaration.link.symbol, classId) ||
        !declaration.status.startsWith('installed-')
    ) {
        return fail(
            'INVALID_CLASS_HEAD',
            path,
            'Annotated class is not one exact installed free declaration'
        );
    }
    const callee = type.tag === 'call' ? type.callee : type;
    const arguments_ = type.tag === 'call' ? type.arguments : [];
    const parameters = instance.layout.schema.parameters;
    if (
        callee.tag !== 'reference' ||
        callee.namespace !== 'free' ||
        callee.name !== declaration.link.coreName ||
        arguments_.length !== parameters.length
    ) {
        return fail(
            'INVALID_CLASS_HEAD',
            path,
            'Annotated binder type has a different class head or arity'
        );
    }
    arguments_.forEach((argument, index) => {
        const expected = parameters[index].parameter.modes.carrier.plicity;
        if (argument.plicity !== expected) {
            fail(
                'INVALID_CLASS_HEAD',
                `${path}.arguments[${index}].plicity`,
                `Annotated class argument ${index} must be ${expected}`
            );
        }
    });
    return {
        classId: { ...classId },
        parameterCount: parameters.length
    };
};

const rolePatternFromTarget = (
    target: KernelExpression,
    instance: ValidatedInstanceBinder
): readonly CoreLfInstanceRoleTargetArgumentInput[] | undefined => {
    const arguments_ = target.tag === 'call' ? target.arguments : [];
    const parameters = instance.layout.schema.parameters;
    if (arguments_.length !== parameters.length) return undefined;
    let hasOutputHole = false;
    const outputMetaIndices = new Set<number>();
    const pattern: CoreLfInstanceRoleTargetArgumentInput[] = [];
    for (let ordinal = 0; ordinal < arguments_.length; ordinal++) {
        const value = arguments_[ordinal].value;
        if (!containsMeta(value)) {
            pattern.push({ kind: 'known', value });
            continue;
        }
        if (
            value.tag !== 'meta' ||
            parameters[ordinal].role !== 'output' ||
            outputMetaIndices.has(value.identity.index)
        ) {
            return undefined;
        }
        outputMetaIndices.add(value.identity.index);
        hasOutputHole = true;
        pattern.push({ kind: 'infer-output' });
    }
    return hasOutputHole ? pattern : undefined;
};

const validateProvenance = (value: Provenance): void => {
    if (
        !record(value) ||
        (
            value.origin !== 'surface' &&
            value.origin !== 'recovered' &&
            value.origin !== 'derived'
        ) ||
        typeof value.detail !== 'string'
    ) {
        return fail(
            'INVALID_INPUT',
            'input.provenance',
            'Class-call provenance must be one valid Core provenance record'
        );
    }
};

const statusFromSynthesis = (
    status: Exclude<CoreLfInstanceSynthesisStatus, 'solved'>
): Exclude<CoreLfClassCallElaborationStatus, 'elaborated'> => status;

/** Elaborate one completely saturated class-aware dependent Core call. */
export function elaborateCoreLfSaturatedClassCall(
    input: CoreLfSaturatedClassCallInput
): CoreLfClassCallElaborationOutcome {
    if (!record(input)) {
        return fail(
            'INVALID_INPUT',
            'input',
            'Saturated class-call input must be one object'
        );
    }
    if (
        !record(input.declarations) ||
        typeof input.declarations.declaration !== 'function' ||
        input.declarations.environment === undefined
    ) {
        return fail(
            'INVALID_INPUT',
            'input.declarations',
            'Class-call elaboration requires one checked declaration base'
        );
    }
    if (
        !(input.context instanceof CoreContext) ||
        input.context.environment !==
            input.declarations.environment.coreEnvironment
    ) {
        return fail(
            'INVALID_CONTEXT',
            'input.context',
            'Class-call context belongs to another declaration base'
        );
    }
    if (!Array.isArray(input.arguments)) {
        return fail(
            'INVALID_ARGUMENT',
            'input.arguments',
            'Class-call source arguments must be a finite array'
        );
    }
    validateProvenance(input.provenance);
    validateSynthesisLimits(input.synthesisLimits);
    const maxBinders = checkedLimit(
        input.maxBinders ??
            CORE_LF_CLASS_CALL_ELABORATION_PROFILE.defaultMaxBinders,
        'input.maxBinders'
    );
    const runtimeMaterial = runtimeFingerprint(input.runtimeProgram);
    const snapshots = validateSnapshots(input.registry, input.scope);
    if (snapshots.scope.contextDepth !== input.context.depth) {
        return fail(
            'INVALID_CONTEXT',
            'input.scope.contextDepth',
            'Class-call scope depth differs from the exact Core context depth'
        );
    }
    const annotations = validateInstanceBinders(input.instanceBinders);
    if (!objectValue(input.callee) || containsMeta(input.callee)) {
        return fail(
            'INVALID_CALLEE',
            'input.callee',
            'Class-call callee must be one meta-free Core expression'
        );
    }
    input.arguments.forEach((argument, index) => {
        if (
            !objectValue(argument) ||
            (
                argument.plicity !== 'explicit' &&
                argument.plicity !== 'implicit'
            ) ||
            !objectValue(argument.value) ||
            containsMeta(argument.value)
        ) {
            fail(
                'INVALID_ARGUMENT',
                `input.arguments[${index}]`,
                'Source argument must be one plicity-tagged meta-free Core term'
            );
        }
        try {
            input.context.assertScoped(argument.value);
        } catch (error: unknown) {
            fail(
                'INVALID_ARGUMENT',
                `input.arguments[${index}].value`,
                'Source argument is not scoped in the exact Core context',
                error instanceof Error ? error : undefined
            );
        }
    });
    if (input.expectedType !== undefined && containsMeta(input.expectedType)) {
        return fail(
            'INVALID_EXPECTED_TYPE',
            'input.expectedType',
            'Expected call result type must be meta-free'
        );
    }

    const checker = createCoreLfChecker(
        input.declarations.environment,
        comparisonStepLimit(input.synthesisLimits),
        input.runtimeProgram
    );
    const session = checker.lfSession;
    let inferredCallee: ReturnType<typeof checker.infer>;
    let expectedType: KernelExpression | undefined;
    try {
        inferredCallee = checker.infer(input.context, input.callee);
        if (isCoreKind(inferredCallee.type)) {
            return fail(
                'INVALID_CALLEE',
                'input.callee',
                'Class-call callee has checker type KIND'
            );
        }
        if (input.expectedType !== undefined) {
            expectedType = checker.check(
                input.context,
                input.expectedType,
                kernelUniverse(provenance(
                    'derived',
                    'class-call expected result must inhabit TYPE',
                    input.provenance.span
                ))
            ).term;
        }
    } catch (error: unknown) {
        if (error instanceof CoreLfClassCallElaborationError) throw error;
        return fail(
            input.expectedType === undefined
                ? 'INVALID_CALLEE'
                : 'INVALID_EXPECTED_TYPE',
            input.expectedType === undefined
                ? 'input.callee'
                : 'input.expectedType',
            'Class-call callee or expected type failed ordinary Core checking',
            error instanceof Error ? error : undefined
        );
    }

    let currentType = inferredCallee.type;
    const plans: PlannedBinder[] = [];
    const ordinaryMetas: PlannedBinder[] = [];
    const pending: PendingInstanceRequest[] = [];
    let suppliedIndex = 0;
    let ordinal = 0;

    while (currentType.tag === 'pi') {
        if (ordinal >= maxBinders) {
            return fail(
                'INVALID_LIMITS',
                'input.maxBinders',
                `Class-call telescope exceeds maxBinders ${maxBinders}`
            );
        }
        const binderType = session.zonk(currentType.binder.type);
        const annotation = annotations.get(ordinal);
        const classReference = annotation === undefined
            ? undefined
            : validateClassTarget(
                input.declarations,
                annotation,
                currentType.binder.mode,
                binderType,
                `input.instanceBinders[ordinal=${ordinal}]`
            );
        const next = input.arguments[suppliedIndex];
        let supplied: KernelCallArgumentInput | undefined;
        let meta: KernelMetaVariable | undefined;
        let checkedValue: KernelExpression;
        let disposition: CoreLfClassCallBinderDisposition;
        let reason: string;

        if (
            next !== undefined &&
            next.plicity === currentType.binder.mode.plicity
        ) {
            supplied = next;
            checkedValue = next.value;
            suppliedIndex++;
            disposition = 'provided';
            reason = annotation === undefined
                ? 'source-supplied-argument'
                : 'source-supplied-instance-evidence';
        } else if (currentType.binder.mode.plicity === 'implicit') {
            meta = session.freshMeta(
                input.context,
                binderType,
                provenance(
                    'derived',
                    annotation === undefined
                        ? `class-call ordinary implicit ${ordinal}`
                        : `class-call instance request ${annotation.requestId}`,
                    input.provenance.span
                )
            );
            checkedValue = meta;
            disposition = annotation === undefined
                ? 'inferred-implicit'
                : 'pending';
            reason = annotation === undefined
                ? 'ordinary-implicit-awaits-constraints'
                : 'instance-request-awaits-ground-target';
        } else {
            if (next?.plicity === 'implicit') {
                return fail(
                    'INVALID_ARGUMENT',
                    `input.arguments[${suppliedIndex}].plicity`,
                    `Explicit binder ${ordinal} cannot consume an implicit argument`
                );
            }
            return fail(
                'MISSING_EXPLICIT_ARGUMENT',
                `callee.binders[${ordinal}]`,
                `Saturated class call is missing explicit binder ` +
                    `'${currentType.binder.name}'`
            );
        }

        const trace: MutableBinderTrace = {
            ordinal,
            binderName: currentType.binder.name,
            mode: { ...currentType.binder.mode },
            type: binderType,
            disposition,
            reason,
            ...(annotation === undefined
                ? {}
                : {
                    requestId: annotation.requestId,
                    class: cloneClass(classReference!)
                })
        };
        const plan: PlannedBinder = {
            trace,
            supplied,
            meta,
            instance: annotation,
            checkedValue
        };
        plans.push(plan);
        if (meta !== undefined && annotation === undefined) {
            ordinaryMetas.push(plan);
        }
        if (meta !== undefined && annotation !== undefined) {
            pending.push({
                plan,
                meta,
                instance: annotation,
                resolved: false
            });
        }
        currentType = session.zonk(kernelInstantiate(
            currentType.body,
            checkedValue
        ));
        ordinal++;
    }

    if (plans.length === 0) {
        return fail(
            'INVALID_CALLEE',
            'input.callee',
            'Saturated class-call callee does not expose a Pi telescope'
        );
    }
    if (suppliedIndex !== input.arguments.length) {
        return fail(
            'TOO_MANY_ARGUMENTS',
            `input.arguments[${suppliedIndex}]`,
            'Source argument remains after the complete callee telescope'
        );
    }
    for (const annotation of annotations.values()) {
        if (annotation.binderOrdinal >= plans.length) {
            return fail(
                'INVALID_INSTANCE_BINDER',
                `input.instanceBinders[ordinal=${annotation.binderOrdinal}]`,
                'Instance annotation lies beyond the complete callee telescope'
            );
        }
    }

    const report = (
        status: CoreLfClassCallElaborationStatus,
        reason: string,
        term?: KernelExpression,
        type?: KernelExpression
    ): CoreLfClassCallElaborationReport => freezeData({
        revision: CORE_LF_CLASS_CALL_ELABORATION_PROFILE.revision,
        status,
        reason,
        contextDepth: input.context.depth,
        maxBinders,
        callee: serializeCoreExpressionAtDepth(
            inferredCallee.term,
            input.context.depth
        ),
        suppliedArgumentCount: input.arguments.length,
        ...(expectedType === undefined
            ? {}
            : {
                expectedType: serializeCoreExpressionAtDepth(
                    expectedType,
                    input.context.depth
                )
            }),
        registryRevision: snapshots.registry.registryRevision,
        scopeRevision: snapshots.scope.scopeRevision,
        scopeFingerprintMaterial: {
            registryCanonicalJson: snapshots.registryCanonicalJson,
            scopeCanonicalJson: snapshots.scopeCanonicalJson
        },
        runtimeFingerprintMaterial: runtimeMaterial,
        binders: plans.map(plan => {
            const value = session.zonk(plan.checkedValue);
            return {
                ordinal: plan.trace.ordinal,
                binderName: plan.trace.binderName,
                mode: plan.trace.mode,
                type: serializeCoreExpressionAtDepth(
                    session.zonk(plan.trace.type),
                    input.context.depth
                ),
                disposition: plan.trace.disposition,
                reason: plan.trace.reason,
                ...(!containsMeta(value)
                    ? {
                        value: serializeCoreExpressionAtDepth(
                            value,
                            input.context.depth
                        )
                    }
                    : {}),
                ...(plan.trace.requestId === undefined
                    ? {}
                    : { requestId: plan.trace.requestId }),
                ...(plan.trace.class === undefined
                    ? {}
                    : { class: cloneClass(plan.trace.class) }),
                ...(plan.trace.synthesis === undefined
                    ? {}
                    : { synthesis: plan.trace.synthesis }),
                ...(plan.trace.roleSynthesis === undefined
                    ? {}
                    : { roleSynthesis: plan.trace.roleSynthesis })
            };
        }),
        ...(term === undefined
            ? {}
            : {
                term: serializeCoreExpressionAtDepth(
                    term,
                    input.context.depth
                )
            }),
        ...(type === undefined
            ? {}
            : {
                type: serializeCoreExpressionAtDepth(
                    type,
                    input.context.depth
                )
            })
    });

    const unsolved = (
        status: Exclude<CoreLfClassCallElaborationStatus, 'elaborated'>,
        reason: string
    ): CoreLfClassCallUnsolved => freezeData({
        status,
        report: report(status, reason)
    });

    const resolveReady = (
        throughOrdinal = Number.POSITIVE_INFINITY
    ): ReadyResolution => {
        let progress = false;
        for (const request of pending) {
            if (request.plan.trace.ordinal > throughOrdinal) break;
            if (request.resolved) continue;
            const target = session.zonk(
                session.metavariable(request.meta).type
            );
            request.plan.trace.type = target;
            let evidence: KernelExpression;
            if (containsMeta(target)) {
                const rolePattern = rolePatternFromTarget(
                    target,
                    request.instance
                );
                if (rolePattern === undefined) {
                    request.plan.trace.disposition = 'pending';
                    request.plan.trace.reason =
                        'instance-target-blocked-by-ordinary-meta';
                    return { progress };
                }
                let synthesis: ReturnType<
                    typeof synthesizeCoreLfInstanceByRoles
                >;
                try {
                    synthesis = synthesizeCoreLfInstanceByRoles({
                        declarations: input.declarations,
                        context: input.context,
                        runtimeProgram: input.runtimeProgram,
                        targetClass: request.instance.layout,
                        targetArguments: rolePattern,
                        registry: snapshots.registry,
                        scope: snapshots.scope,
                        limits: input.synthesisLimits
                    });
                } catch (error: unknown) {
                    return fail(
                        'INVALID_SYNTHESIS_ARTIFACT',
                        `instanceRequests.${request.instance.requestId}`,
                        'Role-aware instance synthesis rejected a call artifact',
                        error instanceof Error ? error : undefined
                    );
                }
                request.plan.trace.roleSynthesis = synthesis.report;
                if (synthesis.status !== 'solved') {
                    request.plan.trace.disposition = 'pending';
                    request.plan.trace.reason =
                        `instance-role-synthesis-${synthesis.status}`;
                    let sawFailure = false;
                    pending.forEach(later => {
                        if (later === request) {
                            sawFailure = true;
                        } else if (sawFailure && !later.resolved) {
                            later.plan.trace.disposition = 'skipped';
                            later.plan.trace.reason =
                                'earlier-instance-request-blocked-call';
                        }
                    });
                    return {
                        progress,
                        failure: synthesis.status,
                        reason: request.plan.trace.reason,
                        failedRequest: request
                    };
                }
                request.plan.trace.synthesis = synthesis.synthesis;
                evidence = synthesis.term;
            } else {
                let synthesis: ReturnType<typeof synthesizeCoreLfInstance>;
                try {
                    synthesis = synthesizeCoreLfInstance({
                        declarations: input.declarations,
                        context: input.context,
                        runtimeProgram: input.runtimeProgram,
                        targetClass: request.instance.layout,
                        target,
                        registry: snapshots.registry,
                        scope: snapshots.scope,
                        limits: input.synthesisLimits
                    });
                } catch (error: unknown) {
                    return fail(
                        'INVALID_SYNTHESIS_ARTIFACT',
                        `instanceRequests.${request.instance.requestId}`,
                        'Nested instance synthesis rejected a call artifact',
                        error instanceof Error ? error : undefined
                    );
                }
                request.plan.trace.synthesis = synthesis.report;
                if (synthesis.status !== 'solved') {
                    request.plan.trace.disposition = 'pending';
                    request.plan.trace.reason =
                        `instance-synthesis-${synthesis.status}`;
                    let sawFailure = false;
                    pending.forEach(later => {
                        if (later === request) {
                            sawFailure = true;
                        } else if (sawFailure && !later.resolved) {
                            later.plan.trace.disposition = 'skipped';
                            later.plan.trace.reason =
                                'earlier-instance-request-blocked-call';
                        }
                    });
                    return {
                        progress,
                        failure: synthesis.status,
                        reason: request.plan.trace.reason,
                        failedRequest: request
                    };
                }
                evidence = synthesis.term;
            }
            if (evidence === undefined) {
                return fail(
                    'INTERNAL_INVARIANT',
                    `instanceRequests.${request.instance.requestId}`,
                    'Successful instance synthesis did not return evidence'
                );
            }
            try {
                checker.checkRefinement(
                    input.context,
                    evidence,
                    target
                );
                session.solve(request.meta, evidence);
            } catch (error: unknown) {
                return fail(
                    'INTERNAL_INVARIANT',
                    `instanceRequests.${request.instance.requestId}`,
                    'Checked synthesis evidence could not solve its exact call meta',
                    error instanceof Error ? error : undefined
                );
            }
            request.resolved = true;
            request.plan.checkedValue = evidence;
            request.plan.trace.value = evidence;
            request.plan.trace.disposition = 'synthesized';
            request.plan.trace.reason = request.plan.trace.roleSynthesis === undefined
                ? 'checked-instance-evidence-inserted'
                : 'checked-role-inferred-instance-evidence-inserted';
            progress = true;
        }
        return { progress };
    };

    let checkingType = inferredCallee.type;
    const checkedArguments: KernelCallArgumentInput[] = [];
    for (const plan of plans) {
        const before = resolveReady(plan.trace.ordinal - 1);
        if (before.failure !== undefined) {
            return unsolved(
                statusFromSynthesis(before.failure),
                before.reason!
            );
        }
        checkingType = session.zonk(checkingType);
        if (checkingType.tag !== 'pi') {
            return fail(
                'INTERNAL_INVARIANT',
                `callee.binders[${plan.trace.ordinal}]`,
                'Class-call telescope changed shape while checking arguments'
            );
        }
        plan.trace.type = session.zonk(checkingType.binder.type);
        const tryCheck = (): KernelExpression => checker.checkRefinement(
            input.context,
            plan.checkedValue,
            plan.trace.type
        ).term;
        let checked: KernelExpression;
        try {
            checked = tryCheck();
        } catch (error: unknown) {
            if (
                error instanceof CoreCheckerError &&
                error.code === 'UNRESOLVED_CONSTRAINTS'
            ) {
                const resolution = resolveReady();
                if (resolution.failure !== undefined) {
                    return unsolved(
                        statusFromSynthesis(resolution.failure),
                        resolution.reason!
                    );
                }
                if (resolution.progress) {
                    try {
                        checked = tryCheck();
                    } catch (retryError: unknown) {
                        if (
                            retryError instanceof CoreCheckerError &&
                            retryError.code === 'UNRESOLVED_CONSTRAINTS'
                        ) {
                            plan.trace.reason =
                                'argument-check-remains-instance-blocked';
                            return unsolved('stuck', plan.trace.reason);
                        }
                        return fail(
                            'INVALID_ARGUMENT',
                            `input.arguments[binder=${plan.trace.ordinal}]`,
                            'Source argument failed after instance retry',
                            retryError instanceof Error
                                ? retryError
                                : undefined
                        );
                    }
                } else {
                    plan.trace.reason = 'argument-check-instance-blocked';
                    return unsolved('stuck', plan.trace.reason);
                }
            } else if (
                error instanceof CoreCheckerError &&
                error.code === 'CONVERSION_STEP_LIMIT'
            ) {
                plan.trace.reason = 'argument-check-conversion-limit';
                return unsolved('limit-exceeded', plan.trace.reason);
            } else {
                return fail(
                    'INVALID_ARGUMENT',
                    `input.arguments[binder=${plan.trace.ordinal}]`,
                    'Source argument does not check at its dependent binder',
                    error instanceof Error ? error : undefined
                );
            }
        }
        plan.checkedValue = checked!;
        if (plan.supplied !== undefined) {
            plan.trace.value = checked!;
        }
        const after = resolveReady(plan.trace.ordinal);
        if (after.failure !== undefined) {
            return unsolved(
                statusFromSynthesis(after.failure),
                after.reason!
            );
        }
        checked = session.zonk(plan.checkedValue);
        checkedArguments.push({
            plicity: checkingType.binder.mode.plicity,
            value: checked!,
            provenance: plan.supplied?.provenance ?? input.provenance
        });
        checkingType = session.zonk(kernelInstantiate(
            checkingType.body,
            checked!
        ));
    }

    let application = kernelCall(
        inferredCallee.term,
        checkedArguments,
        input.provenance
    );

    if (expectedType !== undefined) {
        let refined = false;
        for (let attempt = 0; attempt <= pending.length; attempt++) {
            try {
                application = checker.checkRefinement(
                    input.context,
                    application,
                    expectedType
                ).term as typeof application;
                refined = true;
                break;
            } catch (error: unknown) {
                if (
                    error instanceof CoreCheckerError &&
                    error.code === 'CONVERSION_STEP_LIMIT'
                ) {
                    return unsolved(
                        'limit-exceeded',
                        'expected-result-conversion-limit'
                    );
                }
                if (
                    error instanceof CoreCheckerError &&
                    error.code === 'UNRESOLVED_CONSTRAINTS'
                ) {
                    const resolution = resolveReady();
                    if (resolution.failure !== undefined) {
                        return unsolved(
                            statusFromSynthesis(resolution.failure),
                            resolution.reason!
                        );
                    }
                    if (resolution.progress) continue;
                    return unsolved(
                        'stuck',
                        'expected-result-remains-instance-blocked'
                    );
                }
                return fail(
                    'RESULT_TYPE_MISMATCH',
                    'input.expectedType',
                    'Saturated call does not check at its expected result type',
                    error instanceof Error ? error : undefined
                );
            }
        }
        if (!refined) {
            return unsolved(
                'stuck',
                'expected-result-refinement-did-not-converge'
            );
        }
    }

    const resolution = resolveReady();
    if (resolution.failure !== undefined) {
        return unsolved(
            statusFromSynthesis(resolution.failure),
            resolution.reason!
        );
    }
    const unresolvedOrdinary = ordinaryMetas.find(plan =>
        containsMeta(session.zonk(plan.meta!))
    );
    if (unresolvedOrdinary !== undefined) {
        unresolvedOrdinary.trace.reason = 'ordinary-implicit-unresolved';
        return unsolved('stuck', unresolvedOrdinary.trace.reason);
    }
    const unresolvedInstance = pending.find(request => !request.resolved);
    if (unresolvedInstance !== undefined) {
        unresolvedInstance.plan.trace.disposition = 'pending';
        unresolvedInstance.plan.trace.reason = 'instance-target-not-ground';
        return unsolved('stuck', unresolvedInstance.plan.trace.reason);
    }

    application = session.zonk(application) as typeof application;
    if (containsMeta(application)) {
        return fail(
            'INTERNAL_INVARIANT',
            'result.term',
            'Completed class-call application retained a metavariable'
        );
    }
    let finalTerm: KernelExpression;
    let finalType: KernelExpression;
    try {
        const inferred = checker.infer(input.context, application);
        if (isCoreKind(inferred.type)) {
            return fail(
                'INTERNAL_INVARIANT',
                'result.type',
                'Completed class-call application inferred checker KIND'
            );
        }
        finalTerm = inferred.term;
        finalType = inferred.type;
        if (expectedType !== undefined) {
            const checked = checker.check(
                input.context,
                finalTerm,
                expectedType
            );
            finalTerm = checked.term;
            finalType = checked.type;
        }
    } catch (error: unknown) {
        if (
            error instanceof CoreCheckerError &&
            error.code === 'CONVERSION_STEP_LIMIT'
        ) {
            return unsolved('limit-exceeded', 'final-check-conversion-limit');
        }
        return fail(
            'INTERNAL_INVARIANT',
            'result.term',
            'Explicit class-call result failed its ordinary final Core check',
            error instanceof Error ? error : undefined
        );
    }
    return freezeData({
        status: 'elaborated',
        term: finalTerm,
        type: finalType,
        ...(expectedType === undefined ? {} : { expectedType }),
        report: report(
            'elaborated',
            'explicit-meta-free-core-call-checked',
            finalTerm,
            finalType
        )
    });
}

/** Canonical browser-safe JSON for one class-call elaboration report. */
export const serializeCoreLfClassCallElaborationReport = (
    report: CoreLfClassCallElaborationReport
): string => {
    try {
        return serializeCoreLfWorkspaceCanonicalJson(
            report,
            'classCallElaborationReport'
        );
    } catch (error: unknown) {
        return fail(
            'NON_PORTABLE_DATA',
            'report',
            'Class-call report is not canonical portable data',
            error instanceof Error ? error : undefined
        );
    }
};
