/**
 * Fresh source-first proof attachment to one exact mixed-fragment closure.
 *
 * The caller supplies proof data and inert fingerprint metadata only. This
 * owner reconstructs the selected module closure from source plans and
 * derives its executable runtime from those checked fragments. It never
 * accepts a runtime callback, checker, session, or mutable rule registry.
 */

import {
    serializeCoreExpression
} from './core_serialization';
import {
    CoreLfCatalogRuntime
} from './lf_conversion';
import {
    CoreLfChecker,
    CoreLfElaborationSession,
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT
} from './lf_checker';
import {
    CoreLfCompiledFragmentModuleWorkspace,
    CoreLfCompiledFragmentModuleWorkspaceModule,
    CoreLfFragmentModuleWorkspaceModule,
    CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE,
    createCoreLfFragmentModuleWorkspace,
    createCoreLfFragmentModuleWorkspaceSourceSnapshot,
    serializeCoreLfFragmentModuleWorkspaceSourceSnapshot
} from './lf_fragment_module_workspace';
import {
    CoreLfDependencyModuleFragmentChainSnapshot,
    compileCoreLfDependencyModuleFragmentChain,
    createCoreLfDependencyModuleFragmentChainSnapshot
} from './lf_fragment_workspace';
import {
    CoreLfMixedDeclarationContext
} from './lf_transfer_mixed';
import {
    CoreLfRuntimeFragmentDependency,
    composeCoreLfRuntimeDependencies
} from './lf_transfer_runtime';
import {
    CoreProofRefiner
} from './proof';
import {
    CoreProofGoalCouplingGraph
} from './proof_goal_graph';
import {
    CoreProofPlan,
    CoreProofPlanStateSnapshot,
    executeCoreProofPlan
} from './proof_plan';
import {
    KernelExpression,
    Provenance,
    kernelUniverse,
    provenance
} from './kernel';
import {
    createCoreLfDeclarationWorkspaceInterfaceSnapshot,
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';

export const CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE = Object.freeze({
    revision: 'emdash-lf-fragment-workspace-proof-v1' as const,
    compilerRevision:
        'emdash-lf-fragment-workspace-proof-compiler-v1' as const,
    artifactRevision:
        'emdash-lf-fragment-workspace-proof-artifact-v1' as const,
    fingerprintRevision:
        'emdash-lf-fragment-workspace-proof-inputs-v1' as const,
    closureRevision:
        'emdash-lf-fragment-workspace-proof-closure-v1' as const,
    checker: 'CoreLfFragmentWorkspaceProofChecker' as const,
    workspaceProfileRevision:
        CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision,
    closurePolicy: 'recompile-exact-transitive-fragment-closure' as const,
    runtimePolicy: 'derive-exact-recompiled-runtime' as const,
    comparisonStepLimit:
        CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    supportsRuntimeFragments: true as const,
    acceptsRuntimeInput: false as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    executesIncrementally: false as const
});

export const serializeCoreLfFragmentWorkspaceProofProfile = (): string =>
    `${JSON.stringify(CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE, null, 2)}\n`;

export type CoreLfFragmentWorkspaceProofErrorCode =
    | 'INVALID_COMPILED_WORKSPACE'
    | 'UNKNOWN_ROOT_MODULE'
    | 'CLOSURE_DRIFT'
    | 'MISSING_RUNTIME'
    | 'INVALID_ID'
    | 'INVALID_FINGERPRINT'
    | 'DUPLICATE_DEPENDENCY'
    | 'FINGERPRINT_CLOSURE_MISMATCH'
    | 'RUNTIME_FINGERPRINT_MISMATCH';

export class CoreLfFragmentWorkspaceProofError extends Error {
    constructor(
        public readonly code: CoreLfFragmentWorkspaceProofErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfFragmentWorkspaceProofError';
    }
}

const fail = (
    code: CoreLfFragmentWorkspaceProofErrorCode,
    path: string,
    message: string
): never => {
    throw new CoreLfFragmentWorkspaceProofError(code, path, message);
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

const compareText = (left: string, right: string): number =>
    left < right ? -1 : left > right ? 1 : 0;

const sameTextArray = (
    left: readonly string[],
    right: readonly string[]
): boolean => left.length === right.length &&
    left.every((entry, index) => entry === right[index]);

const SAFE_DOCUMENT_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const SHA256 = /^sha256:[0-9a-f]{64}$/u;

const assertDocumentId = (value: string, path: string): void => {
    if (SAFE_DOCUMENT_ID.test(value)) return;
    fail('INVALID_ID', path, `Invalid proof document ID '${value}'`);
};

const assertSourceId = (value: string): void => {
    if (value.length > 0 && !/[\u0000-\u001f\u007f]/u.test(value)) return;
    fail(
        'INVALID_ID',
        'fingerprint.source.id',
        'Proof source identity must be nonempty and contain no controls'
    );
};

const assertSha256 = (value: string, path: string): void => {
    if (SHA256.test(value)) return;
    fail(
        'INVALID_FINGERPRINT',
        path,
        "Expected 'sha256:' followed by 64 lowercase hexadecimal digits"
    );
};

export interface CoreLfFragmentWorkspaceProofRuntimeFingerprint {
    readonly revision: string;
    readonly ruleIds: readonly string[];
}

export interface CoreLfFragmentWorkspaceProofFingerprintInput {
    readonly source: {
        readonly id: string;
        readonly sha256: string;
    };
    readonly profileSha256: string;
    readonly dependencies: readonly {
        readonly moduleId: string;
        readonly interfaceSha256: string;
    }[];
    readonly runtime: CoreLfFragmentWorkspaceProofRuntimeFingerprint;
}

export interface CoreLfFragmentWorkspaceProofFingerprintHashes {
    readonly sourceSha256: string;
    readonly profileSha256: string;
    readonly interfaceSha256ByModuleId: Readonly<Record<string, string>>;
}

export interface CoreLfFragmentWorkspaceProofFingerprint {
    readonly revision:
        typeof CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.fingerprintRevision;
    readonly compilerRevision:
        typeof CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.compilerRevision;
    readonly source: {
        readonly id: string;
        readonly sha256: string;
    };
    readonly profile: {
        readonly id:
            typeof CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.revision;
        readonly sha256: string;
    };
    readonly dependencies: readonly {
        readonly moduleId: string;
        readonly interfaceSha256: string;
    }[];
    readonly runtime: CoreLfFragmentWorkspaceProofRuntimeFingerprint;
}

export const createCoreLfFragmentWorkspaceProofRuntimeFingerprint = (
    runtime: CoreLfCatalogRuntime
): CoreLfFragmentWorkspaceProofRuntimeFingerprint => deepFreeze({
    revision: runtime.revision,
    ruleIds: [...runtime.ruleIds]
});

const validateRuntimeFingerprint = (
    runtime: CoreLfFragmentWorkspaceProofRuntimeFingerprint
): CoreLfFragmentWorkspaceProofRuntimeFingerprint => {
    if (
        runtime === null ||
        typeof runtime !== 'object' ||
        typeof runtime.revision !== 'string' ||
        runtime.revision.length === 0 ||
        !Array.isArray(runtime.ruleIds) ||
        runtime.ruleIds.length === 0 ||
        runtime.ruleIds.some(ruleId =>
            typeof ruleId !== 'string' || ruleId.length === 0
        ) ||
        new Set(runtime.ruleIds).size !== runtime.ruleIds.length
    ) {
        return fail(
            'INVALID_FINGERPRINT',
            'fingerprint.runtime',
            'Runtime fingerprint requires a revision and unique rule IDs'
        );
    }
    return deepFreeze({
        revision: runtime.revision,
        ruleIds: [...runtime.ruleIds]
    });
};

export function createCoreLfFragmentWorkspaceProofFingerprint(
    input: CoreLfFragmentWorkspaceProofFingerprintInput
): CoreLfFragmentWorkspaceProofFingerprint {
    assertSourceId(input.source.id);
    assertSha256(input.source.sha256, 'fingerprint.source.sha256');
    assertSha256(input.profileSha256, 'fingerprint.profile.sha256');
    const dependencies = [...input.dependencies].sort((left, right) =>
        compareText(left.moduleId, right.moduleId)
    );
    const seen = new Set<string>();
    const canonicalDependencies = dependencies.map((dependency, index) => {
        assertDocumentId(
            dependency.moduleId,
            `fingerprint.dependencies[${index}].moduleId`
        );
        assertSha256(
            dependency.interfaceSha256,
            `fingerprint.dependencies[${index}].interfaceSha256`
        );
        if (seen.has(dependency.moduleId)) {
            return fail(
                'DUPLICATE_DEPENDENCY',
                `fingerprint.dependencies[${index}].moduleId`,
                `Duplicate proof dependency '${dependency.moduleId}'`
            );
        }
        seen.add(dependency.moduleId);
        return { ...dependency };
    });
    return deepFreeze({
        revision:
            CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.fingerprintRevision,
        compilerRevision:
            CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.compilerRevision,
        source: { ...input.source },
        profile: {
            id: CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.revision,
            sha256: input.profileSha256
        },
        dependencies: canonicalDependencies,
        runtime: validateRuntimeFingerprint(input.runtime)
    });
}

export function validateCoreLfFragmentWorkspaceProofFingerprint(
    fingerprint: CoreLfFragmentWorkspaceProofFingerprint
): CoreLfFragmentWorkspaceProofFingerprint {
    if (
        fingerprint.revision !==
            CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.fingerprintRevision ||
        fingerprint.compilerRevision !==
            CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.compilerRevision ||
        fingerprint.profile.id !==
            CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.revision
    ) {
        return fail(
            'INVALID_FINGERPRINT',
            'fingerprint.revision',
            'Proof fingerprint targets an unsupported fragment-proof profile'
        );
    }
    return createCoreLfFragmentWorkspaceProofFingerprint({
        source: fingerprint.source,
        profileSha256: fingerprint.profile.sha256,
        dependencies: fingerprint.dependencies,
        runtime: fingerprint.runtime
    });
}

export interface CoreLfFragmentWorkspaceProofDocumentInput {
    readonly moduleId: string;
    readonly declarationId: string;
    readonly type: KernelExpression;
    readonly plan: CoreProofPlan;
    readonly provenance: Provenance;
    readonly fingerprint: CoreLfFragmentWorkspaceProofFingerprint;
}

export interface CoreLfFragmentWorkspaceProofClosureModuleSnapshot {
    readonly identity: CoreLfFragmentModuleWorkspaceModule['identity'];
    readonly dependencyProviders:
        CoreLfFragmentModuleWorkspaceModule['dependencyProviders'];
    readonly runtimeProviders:
        CoreLfFragmentModuleWorkspaceModule['runtimeProviders'];
    readonly chain: CoreLfDependencyModuleFragmentChainSnapshot;
}

export interface CoreLfFragmentWorkspaceProofClosureSnapshot {
    readonly revision:
        typeof CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.closureRevision;
    readonly workspaceProfileRevision:
        typeof CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision;
    readonly workspaceRevision: string;
    readonly rootModuleId: string;
    readonly order: readonly string[];
    readonly modules:
        readonly CoreLfFragmentWorkspaceProofClosureModuleSnapshot[];
}

export interface CoreLfFragmentWorkspaceProofArtifact {
    readonly revision:
        typeof CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.artifactRevision;
    readonly compilerRevision:
        typeof CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.compilerRevision;
    readonly closure: CoreLfFragmentWorkspaceProofClosureSnapshot;
    readonly closureText: string;
    readonly runtime: CoreLfFragmentWorkspaceProofRuntimeFingerprint;
    readonly moduleId: string;
    readonly declarationId: string;
    readonly fingerprint: CoreLfFragmentWorkspaceProofFingerprint;
    readonly state: CoreProofPlanStateSnapshot;
    readonly checkedCore?: string;
}

export interface CoreLfFragmentWorkspaceProofClosureCompilation {
    readonly modules:
        readonly CoreLfCompiledFragmentModuleWorkspaceModule[];
    readonly declarations: CoreLfMixedDeclarationContext;
}

export interface CoreLfFragmentWorkspaceProofCompilation {
    readonly artifact: CoreLfFragmentWorkspaceProofArtifact;
    readonly closureCompilation:
        CoreLfFragmentWorkspaceProofClosureCompilation;
    readonly goalGraph: CoreProofGoalCouplingGraph;
    readonly checkedTerm?: KernelExpression;
}

interface RecompiledClosure {
    readonly snapshot: CoreLfFragmentWorkspaceProofClosureSnapshot;
    readonly text: string;
    readonly compilation: CoreLfFragmentWorkspaceProofClosureCompilation;
    readonly root: CoreLfCompiledFragmentModuleWorkspaceModule;
    readonly runtime: CoreLfCatalogRuntime;
}

const compiledModuleSnapshot = (
    module: CoreLfCompiledFragmentModuleWorkspaceModule
): string => serializeCoreLfWorkspaceCanonicalJson({
    identity: module.source.identity,
    dependencyInterfaceModuleIds:
        module.dependencyInterfaces.map(value => value.moduleId),
    runtimeDependencies: module.runtimeDependencies.map(value => ({
        relation: value.relation,
        compiledIdentity: value.fragment.identity
    })),
    chain: createCoreLfDependencyModuleFragmentChainSnapshot(module.compiled)
}, 'fragmentWorkspaceProofCompiledModule');

const canonicalWorkspacePlan = (
    workspace: CoreLfCompiledFragmentModuleWorkspace
) => {
    const canonical = createCoreLfFragmentModuleWorkspace({
        revision: workspace.plan.revision,
        modules: workspace.plan.modules
    });
    const expected = serializeCoreLfFragmentModuleWorkspaceSourceSnapshot(
        createCoreLfFragmentModuleWorkspaceSourceSnapshot(canonical)
    );
    const actual = serializeCoreLfFragmentModuleWorkspaceSourceSnapshot(
        createCoreLfFragmentModuleWorkspaceSourceSnapshot(workspace.plan)
    );
    if (actual !== expected) {
        return fail(
            'INVALID_COMPILED_WORKSPACE',
            'workspace.plan',
            'Compiled fragment workspace plan is not canonical'
        );
    }
    if (workspace.modules.length !== canonical.modules.length) {
        return fail(
            'INVALID_COMPILED_WORKSPACE',
            'workspace.modules',
            'Compiled fragment workspace module count differs from its plan'
        );
    }
    return canonical;
};

const closureOrder = (
    modules: readonly CoreLfFragmentModuleWorkspaceModule[],
    rootModuleId: string
): readonly string[] => {
    const byId = new Map(modules.map(module => [
        module.identity.moduleId,
        module
    ] as const));
    if (!byId.has(rootModuleId)) {
        return fail(
            'UNKNOWN_ROOT_MODULE',
            'moduleId',
            `Fragment workspace has no root module '${rootModuleId}'`
        );
    }
    const closure = new Set<string>();
    const visit = (moduleId: string): void => {
        if (closure.has(moduleId)) return;
        const module = byId.get(moduleId);
        if (module === undefined) {
            return fail(
                'INVALID_COMPILED_WORKSPACE',
                'workspace.plan.modules',
                `Closure dependency '${moduleId}' disappeared`
            );
        }
        module.identity.dependencies.forEach(visit);
        closure.add(moduleId);
    };
    visit(rootModuleId);
    return modules
        .map(module => module.identity.moduleId)
        .filter(moduleId => closure.has(moduleId));
};

const compileExactClosure = (
    workspace: CoreLfCompiledFragmentModuleWorkspace,
    rootModuleId: string
): RecompiledClosure => {
    const canonical = canonicalWorkspacePlan(workspace);
    const order = closureOrder(canonical.modules, rootModuleId);
    const sourceById = new Map(canonical.modules.map(module => [
        module.identity.moduleId,
        module
    ] as const));
    const originalById = new Map<string,
        CoreLfCompiledFragmentModuleWorkspaceModule>();
    workspace.modules.forEach((module, index) => {
        const moduleId = module.source.identity.moduleId;
        if (originalById.has(moduleId)) {
            fail(
                'INVALID_COMPILED_WORKSPACE',
                `workspace.modules[${index}]`,
                `Compiled module '${moduleId}' is duplicated`
            );
        }
        originalById.set(moduleId, module);
    });

    let declarations = new CoreLfMixedDeclarationContext();
    const compiledById = new Map<string,
        CoreLfCompiledFragmentModuleWorkspaceModule>();
    const modules: CoreLfCompiledFragmentModuleWorkspaceModule[] = [];

    order.forEach((moduleId, moduleIndex) => {
        const source = sourceById.get(moduleId);
        if (source === undefined) {
            return fail(
                'INVALID_COMPILED_WORKSPACE',
                `closure.order[${moduleIndex}]`,
                `Closure source '${moduleId}' disappeared`
            );
        }
        const dependencies = source.dependencyProviders.map(
            (provider, dependencyIndex) => {
                const compiled = compiledById.get(provider.moduleId);
                if (compiled !== undefined) return compiled;
                return fail(
                    'INVALID_COMPILED_WORKSPACE',
                    `closure.modules[${moduleIndex}]` +
                        `.dependencyProviders[${dependencyIndex}]`,
                    `Dependency '${provider.moduleId}' is outside the ` +
                        'reconstructed closure'
                );
            }
        );
        const dependencyInterfaces = dependencies.flatMap(module =>
            module.compiled.moduleInterface === undefined
                ? []
                : [module.compiled.moduleInterface]
        );
        const runtimeDependencies: CoreLfRuntimeFragmentDependency[] =
            source.runtimeProviders.map((provider, runtimeIndex) => {
                const dependency = compiledById.get(provider.moduleId);
                const fragment = dependency?.compiled.fragment(
                    provider.fragment
                );
                if (fragment?.runtime !== undefined) {
                    return {
                        relation: 'dependency-module' as const,
                        fragment: fragment.runtime
                    };
                }
                return fail(
                    'INVALID_COMPILED_WORKSPACE',
                    `closure.modules[${moduleIndex}]` +
                        `.runtimeProviders[${runtimeIndex}]`,
                    `Runtime provider '${provider.moduleId}' did not ` +
                        'recompile in the exact closure'
                );
            });
        const compiled = compileCoreLfDependencyModuleFragmentChain(
            source.chain,
            {
                initialDeclarations: declarations,
                dependencyInterfaces,
                runtimeDependencies
            }
        );
        declarations = compiled.declarations;
        const result: CoreLfCompiledFragmentModuleWorkspaceModule =
            Object.freeze({
                source,
                dependencyInterfaces,
                runtimeDependencies,
                compiled
            });
        const original = originalById.get(moduleId);
        if (original === undefined) {
            return fail(
                'INVALID_COMPILED_WORKSPACE',
                `workspace.modules.${moduleId}`,
                `Compiled workspace has no module '${moduleId}'`
            );
        }
        if (compiledModuleSnapshot(original) !== compiledModuleSnapshot(result)) {
            return fail(
                'CLOSURE_DRIFT',
                `closure.modules[${moduleIndex}]`,
                `Recompiled fragment module '${moduleId}' drifted`
            );
        }
        compiledById.set(moduleId, result);
        modules.push(result);
    });

    const root = compiledById.get(rootModuleId);
    if (root === undefined) {
        return fail(
            'UNKNOWN_ROOT_MODULE',
            'moduleId',
            `Reconstructed closure has no root '${rootModuleId}'`
        );
    }
    const runtime = root.compiled.latestRuntime?.runtime ??
        composeCoreLfRuntimeDependencies(root.runtimeDependencies);
    if (runtime === undefined || runtime.ruleIds.length === 0) {
        return fail(
            'MISSING_RUNTIME',
            'closure.runtime',
            `Root module '${rootModuleId}' has no exact compiled runtime`
        );
    }
    const snapshot: CoreLfFragmentWorkspaceProofClosureSnapshot = deepFreeze({
        revision: CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.closureRevision,
        workspaceProfileRevision:
            CORE_LF_FRAGMENT_MODULE_WORKSPACE_PROFILE.revision,
        workspaceRevision: canonical.revision,
        rootModuleId,
        order: [...order],
        modules: modules.map(module => ({
            identity: module.source.identity,
            dependencyProviders: module.source.dependencyProviders,
            runtimeProviders: module.source.runtimeProviders,
            chain: createCoreLfDependencyModuleFragmentChainSnapshot(
                module.compiled
            )
        }))
    });
    return Object.freeze({
        snapshot,
        text: serializeCoreLfWorkspaceCanonicalJson(
            snapshot,
            'fragmentWorkspaceProofClosure'
        ),
        compilation: Object.freeze({
            modules: Object.freeze([...modules]),
            declarations
        }),
        root,
        runtime
    });
};

/**
 * Bind caller-computed hashes to one selected already checked workspace.
 * The browser-safe owner validates exact interface/runtime ownership but
 * deliberately does not compute cryptographic hashes itself.
 */
export function createCoreLfFragmentWorkspaceProofFingerprintForWorkspace(
    workspace: CoreLfCompiledFragmentModuleWorkspace,
    rootModuleId: string,
    sourceId: string,
    hashes: CoreLfFragmentWorkspaceProofFingerprintHashes
): CoreLfFragmentWorkspaceProofFingerprint {
    const closure = compileExactClosure(workspace, rootModuleId);
    const suppliedModules = Object.keys(hashes.interfaceSha256ByModuleId)
        .sort(compareText);
    const expectedModules = [...closure.snapshot.order].sort(compareText);
    if (!sameTextArray(suppliedModules, expectedModules)) {
        return fail(
            'FINGERPRINT_CLOSURE_MISMATCH',
            'hashes.interfaceSha256ByModuleId',
            `Interface hash modules [${suppliedModules.join(', ')}] do not ` +
                `equal exact closure [${expectedModules.join(', ')}]`
        );
    }
    closure.compilation.modules.forEach((module, moduleIndex) => {
        if (module.compiled.declarationModules.length === 0) {
            return fail(
                'INVALID_COMPILED_WORKSPACE',
                `closure.modules[${moduleIndex}].interfaces`,
                `Module '${module.source.identity.moduleId}' has no ` +
                    'declaration interface to fingerprint'
            );
        }
        module.compiled.declarationModules.forEach(
            createCoreLfDeclarationWorkspaceInterfaceSnapshot
        );
    });
    return createCoreLfFragmentWorkspaceProofFingerprint({
        source: {
            id: sourceId,
            sha256: hashes.sourceSha256
        },
        profileSha256: hashes.profileSha256,
        dependencies: expectedModules.map(moduleId => ({
            moduleId,
            interfaceSha256: hashes.interfaceSha256ByModuleId[moduleId]
        })),
        runtime: createCoreLfFragmentWorkspaceProofRuntimeFingerprint(
            closure.runtime
        )
    });
}

const validateFingerprintClosure = (
    fingerprint: CoreLfFragmentWorkspaceProofFingerprint,
    closure: RecompiledClosure
): CoreLfFragmentWorkspaceProofFingerprint => {
    const canonical = validateCoreLfFragmentWorkspaceProofFingerprint(
        fingerprint
    );
    const expectedModules = [...closure.snapshot.order].sort(compareText);
    const actualModules = canonical.dependencies.map(value => value.moduleId);
    if (!sameTextArray(actualModules, expectedModules)) {
        return fail(
            'FINGERPRINT_CLOSURE_MISMATCH',
            'fingerprint.dependencies',
            `Proof fingerprint modules [${actualModules.join(', ')}] do ` +
                `not equal exact closure [${expectedModules.join(', ')}]`
        );
    }
    if (
        canonical.runtime.revision !== closure.runtime.revision ||
        !sameTextArray(
            canonical.runtime.ruleIds,
            closure.runtime.ruleIds
        )
    ) {
        return fail(
            'RUNTIME_FINGERPRINT_MISMATCH',
            'fingerprint.runtime',
            'Proof runtime fingerprint differs from the exact closure runtime'
        );
    }
    return canonical;
};

class CoreLfFragmentWorkspaceProofChecker extends CoreLfChecker {
    constructor(
        environment: CoreLfMixedDeclarationContext['environment'],
        runtime: CoreLfCatalogRuntime
    ) {
        super(new CoreLfElaborationSession(
            environment,
            CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.comparisonStepLimit,
            runtime
        ));
    }

    protected permitsAnnotatedLambdaInference(): boolean {
        return false;
    }

    protected conversionDiagnosticName(): string {
        return 'Exact fragment-workspace proof conversion';
    }
}

const checkedTargetProvenance = (
    input: CoreLfFragmentWorkspaceProofDocumentInput
): Provenance => provenance(
    'derived',
    `well-formed fragment proof target for ` +
        `${input.moduleId}.${input.declarationId}`,
    input.provenance.span
);

/** Reconstruct one exact mixed closure and replay one proof plan within it. */
export function compileCoreLfFragmentWorkspaceProofDocument(
    workspace: CoreLfCompiledFragmentModuleWorkspace,
    input: CoreLfFragmentWorkspaceProofDocumentInput
): CoreLfFragmentWorkspaceProofCompilation {
    assertDocumentId(input.moduleId, 'moduleId');
    assertDocumentId(input.declarationId, 'declarationId');
    const closure = compileExactClosure(workspace, input.moduleId);
    const fingerprint = validateFingerprintClosure(
        input.fingerprint,
        closure
    );
    const checker = new CoreLfFragmentWorkspaceProofChecker(
        closure.root.compiled.declarations.environment,
        closure.runtime
    );
    checker.validateEnvironment();
    const targetProvenance = checkedTargetProvenance(input);
    const checkedTarget = checker.check(
        checker.rootContext,
        input.type,
        kernelUniverse(targetProvenance)
    ).term;
    const root = checker.lfSession.freshMeta(
        checker.rootContext,
        checkedTarget,
        input.provenance
    );
    const execution = executeCoreProofPlan(
        new CoreProofRefiner(checker, root),
        root.identity,
        input.plan
    );

    let checkedTerm: KernelExpression | undefined;
    let checkedCore: string | undefined;
    if (execution.state.status === 'complete') {
        checkedTerm = checker.check(
            checker.rootContext,
            execution.term,
            checkedTarget
        ).term;
        checkedCore = serializeCoreExpression(checkedTerm);
    }
    const artifact: CoreLfFragmentWorkspaceProofArtifact = deepFreeze({
        revision: CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.artifactRevision,
        compilerRevision:
            CORE_LF_FRAGMENT_WORKSPACE_PROOF_PROFILE.compilerRevision,
        closure: closure.snapshot,
        closureText: closure.text,
        runtime: {
            ...createCoreLfFragmentWorkspaceProofRuntimeFingerprint(
                closure.runtime
            )
        },
        moduleId: input.moduleId,
        declarationId: input.declarationId,
        fingerprint,
        state: execution.snapshot,
        ...(checkedCore === undefined ? {} : { checkedCore })
    });
    return Object.freeze({
        artifact,
        closureCompilation: closure.compilation,
        goalGraph: execution.goalGraph,
        ...(checkedTerm === undefined ? {} : { checkedTerm })
    });
}

export const serializeCoreLfFragmentWorkspaceProofArtifact = (
    artifact: CoreLfFragmentWorkspaceProofArtifact
): string => `${JSON.stringify(artifact, null, 2)}\n`;
