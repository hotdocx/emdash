/**
 * Browser-safe theorem bindings over exact runtime proof developments.
 *
 * Opaque signatures remain assumptions while the underlying proof plans are
 * checked. This additive layer certifies exactly the signatures named by its
 * bindings and rejects circular or not-yet-proved uses among that finite set.
 */

import {
    CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    createCoreLfChecker
} from './lf_checker';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreLfQualifiedSymbol,
    coreLfQualifiedSymbol
} from './lf_transfer';
import {
    CoreLfCompiledDeclaration
} from './lf_transfer_compiler';
import {
    composeCoreLfRuntimeDependencies
} from './lf_transfer_runtime';
import {
    CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE,
    CoreLfCompiledFragmentProofDevelopment,
    CoreLfFragmentProofDevelopmentArtifact,
    CoreLfFragmentProofDevelopmentPlan,
    compileCoreLfFragmentProofDevelopment,
    createCoreLfFragmentProofDevelopment
} from './lf_fragment_proof_development';
import {
    CoreLfFragmentWorkspaceProofCompilation
} from './lf_fragment_workspace_proof';
import {
    CoreProofPlan
} from './proof_plan';
import {
    KernelExpression,
    kernelFree,
    provenance
} from './kernel';

export const CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE = Object.freeze({
    revision: 'emdash-lf-declared-theorem-development-v1' as const,
    artifactRevision:
        'emdash-lf-declared-theorem-development-artifact-v1' as const,
    proofDevelopmentProfileRevision:
        CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision,
    bindingPolicy: 'exact-one-to-one-same-module-opaque-signature' as const,
    dependencyPolicy:
        'transitive-free-reference-acyclic-complete-prerequisites' as const,
    assumptionPolicy:
        'unbound-free-declarations-remain-workspace-assumptions' as const,
    theoremOrder: 'stable-dependency-first-topological' as const,
    comparisonStepLimit: CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    supportsOpenProofs: true as const,
    supportsCrossModuleTheoremBindings: false as const,
    generatesDeclarations: false as const,
    acceptsRuntimeInput: false as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    performsIo: false as const
});

export const serializeCoreLfDeclaredTheoremDevelopmentProfile = (): string =>
    `${JSON.stringify(
        CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE,
        null,
        2
    )}\n`;

export const CORE_LF_MODULE_THEOREM_DEVELOPMENT_PROFILE = Object.freeze({
    revision: 'emdash-lf-module-theorem-development-v1' as const,
    artifactRevision:
        'emdash-lf-module-theorem-development-artifact-v1' as const,
    proofDevelopmentProfileRevision:
        CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision,
    declaredTheoremProfileRevision:
        CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.revision,
    bindingPolicy: 'exact-one-to-one-owning-module-opaque-signature' as const,
    referencePolicy: 'root-local-plus-direct-public-imports' as const,
    dependencyPolicy:
        'closed-workspace-transitive-acyclic-complete-prerequisites' as const,
    theoremOrder: 'stable-dependency-first-topological' as const,
    comparisonStepLimit: CORE_LF_CANDIDATE_COMPARISON_STEP_LIMIT,
    supportsOpenProofs: true as const,
    supportsCrossModuleTheoremBindings: true as const,
    supportsDetachedTheoremImports: false as const,
    generatesDeclarations: false as const,
    acceptsRuntimeInput: false as const,
    productionLambdapiDependency: false as const,
    nodeBuiltinDependency: false as const,
    computesCryptographicHashes: false as const,
    performsIo: false as const
});

export const serializeCoreLfModuleTheoremDevelopmentProfile = (): string =>
    `${JSON.stringify(CORE_LF_MODULE_THEOREM_DEVELOPMENT_PROFILE, null, 2)}\n`;

export type CoreLfDeclaredTheoremDevelopmentErrorCode =
    | 'INVALID_DEVELOPMENT'
    | 'INVALID_BINDING'
    | 'UNKNOWN_PROOF'
    | 'MISSING_BINDING'
    | 'DUPLICATE_PROOF_BINDING'
    | 'DUPLICATE_THEOREM_BINDING'
    | 'THEOREM_MODULE_MISMATCH'
    | 'MULTIPLE_THEOREM_MODULES'
    | 'UNKNOWN_THEOREM_DECLARATION'
    | 'UNSUPPORTED_THEOREM_DECLARATION'
    | 'THEOREM_TARGET_MISMATCH'
    | 'INVALID_COMPILED_DEVELOPMENT'
    | 'INACCESSIBLE_PROOF_REFERENCE'
    | 'SELF_THEOREM_DEPENDENCY'
    | 'CYCLIC_THEOREM_DEPENDENCY'
    | 'OPEN_THEOREM_DEPENDENCY';

export class CoreLfDeclaredTheoremDevelopmentError extends Error {
    constructor(
        public readonly code:
            CoreLfDeclaredTheoremDevelopmentErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfDeclaredTheoremDevelopmentError';
    }
}

const fail = (
    code: CoreLfDeclaredTheoremDevelopmentErrorCode,
    path: string,
    message: string,
    underlying?: Error
): never => {
    throw new CoreLfDeclaredTheoremDevelopmentError(
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

const compareText = (left: string, right: string): number =>
    left < right ? -1 : left > right ? 1 : 0;

const SAFE_REVISION = /^[A-Za-z0-9][A-Za-z0-9._+-]*$/u;

export interface CoreLfDeclaredTheoremProofIdentity {
    readonly moduleId: string;
    readonly declarationId: string;
}

export interface CoreLfDeclaredTheoremBindingInput {
    readonly proof: CoreLfDeclaredTheoremProofIdentity;
    readonly theorem: CoreLfQualifiedSymbol;
}

const proofKey = (proof: CoreLfDeclaredTheoremProofIdentity): string =>
    `${proof.moduleId}\u0000${proof.declarationId}`;

const symbolKey = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}\u0000${symbol.name}`;

const displayProof = (proof: CoreLfDeclaredTheoremProofIdentity): string =>
    `${proof.moduleId}.${proof.declarationId}`;

const displaySymbol = (symbol: CoreLfQualifiedSymbol): string =>
    `${symbol.moduleId}.${symbol.name}`;

const cloneProof = (
    proof: CoreLfDeclaredTheoremProofIdentity
): CoreLfDeclaredTheoremProofIdentity => Object.freeze({
    moduleId: proof.moduleId,
    declarationId: proof.declarationId
});

const cloneSymbol = (
    symbol: CoreLfQualifiedSymbol
): CoreLfQualifiedSymbol => Object.freeze({
    moduleId: symbol.moduleId,
    name: symbol.name
});

export interface CoreLfDeclaredTheoremDevelopmentInput {
    readonly revision: string;
    readonly development: CoreLfFragmentProofDevelopmentPlan;
    readonly bindings: readonly CoreLfDeclaredTheoremBindingInput[];
}

export interface CoreLfDeclaredTheoremDevelopmentPlan {
    readonly revision: string;
    readonly profileRevision:
        typeof CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.revision;
    readonly proofDevelopmentProfileRevision:
        typeof CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision;
    readonly development: CoreLfFragmentProofDevelopmentPlan;
    readonly bindings: readonly CoreLfDeclaredTheoremBindingInput[];
}

export interface CoreLfModuleTheoremDevelopmentInput
extends CoreLfDeclaredTheoremDevelopmentInput {}

export interface CoreLfModuleTheoremDevelopmentPlan {
    readonly revision: string;
    readonly profileRevision:
        typeof CORE_LF_MODULE_THEOREM_DEVELOPMENT_PROFILE.revision;
    readonly proofDevelopmentProfileRevision:
        typeof CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision;
    readonly declaredTheoremProfileRevision:
        typeof CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.revision;
    readonly development: CoreLfFragmentProofDevelopmentPlan;
    readonly bindings: readonly CoreLfDeclaredTheoremBindingInput[];
}

interface CanonicalTheoremBindings {
    readonly development: CoreLfFragmentProofDevelopmentPlan;
    readonly bindings: readonly CoreLfDeclaredTheoremBindingInput[];
}

const canonicalTheoremBindings = (
    input: CoreLfDeclaredTheoremDevelopmentInput,
    requireSingleRoot: boolean
): CanonicalTheoremBindings => {
    if (!SAFE_REVISION.test(input.revision)) {
        return fail(
            'INVALID_DEVELOPMENT',
            'revision',
            `Invalid declared-theorem development revision ` +
                `'${input.revision}'`
        );
    }
    const development = createCoreLfFragmentProofDevelopment({
        revision: input.development.revision,
        workspace: input.development.workspace,
        proofs: input.development.proofs
    });
    const proofs = new Map(development.proofs.map(proof => [
        proofKey(proof),
        proof
    ]));
    const seenProofs = new Set<string>();
    const seenTheorems = new Set<string>();
    const roots = new Set<string>();

    const bindings = input.bindings.map((binding, index) => {
        let theorem: CoreLfQualifiedSymbol;
        try {
            theorem = coreLfQualifiedSymbol(
                binding.theorem.moduleId,
                binding.theorem.name
            );
        } catch (error: unknown) {
            return fail(
                'INVALID_BINDING',
                `bindings[${index}].theorem`,
                `Invalid theorem symbol: ${errorText(error)}`,
                error instanceof Error ? error : undefined
            );
        }
        const key = proofKey(binding.proof);
        const proof = proofs.get(key);
        if (proof === undefined) {
            return fail(
                'UNKNOWN_PROOF',
                `bindings[${index}].proof`,
                `Binding names unknown proof '${displayProof(binding.proof)}'`
            );
        }
        if (seenProofs.has(key)) {
            return fail(
                'DUPLICATE_PROOF_BINDING',
                `bindings[${index}].proof`,
                `Proof '${displayProof(proof)}' is bound more than once`
            );
        }
        seenProofs.add(key);

        const theoremKey = symbolKey(theorem);
        if (seenTheorems.has(theoremKey)) {
            return fail(
                'DUPLICATE_THEOREM_BINDING',
                `bindings[${index}].theorem`,
                `Theorem '${displaySymbol(theorem)}' is bound more than once`
            );
        }
        seenTheorems.add(theoremKey);
        if (theorem.moduleId !== proof.moduleId) {
            return fail(
                'THEOREM_MODULE_MISMATCH',
                `bindings[${index}].theorem.moduleId`,
                `Proof '${displayProof(proof)}' cannot bind theorem ` +
                    `'${displaySymbol(theorem)}' outside its owning module`
            );
        }
        roots.add(proof.moduleId);
        return Object.freeze({
            proof: cloneProof(proof),
            theorem: cloneSymbol(theorem)
        });
    });

    for (const proof of development.proofs) {
        if (!seenProofs.has(proofKey(proof))) {
            return fail(
                'MISSING_BINDING',
                'bindings',
                `Proof '${displayProof(proof)}' has no theorem binding`
            );
        }
    }
    if (requireSingleRoot && roots.size > 1) {
        return fail(
            'MULTIPLE_THEOREM_MODULES',
            'bindings',
            'Declared-theorem profile v1 accepts exactly one proof root module'
        );
    }

    bindings.sort((left, right) =>
        compareText(proofKey(left.proof), proofKey(right.proof))
    );
    return {
        development,
        bindings: Object.freeze(bindings)
    };
};

/** Validate exact binding coverage and canonicalize by proof identity. */
export function createCoreLfDeclaredTheoremDevelopment(
    input: CoreLfDeclaredTheoremDevelopmentInput
): CoreLfDeclaredTheoremDevelopmentPlan {
    const canonical = canonicalTheoremBindings(input, true);
    return Object.freeze({
        revision: input.revision,
        profileRevision:
            CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.revision,
        proofDevelopmentProfileRevision:
            CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision,
        development: canonical.development,
        bindings: canonical.bindings
    });
}

/** Validate a closed multi-module theorem development. */
export function createCoreLfModuleTheoremDevelopment(
    input: CoreLfModuleTheoremDevelopmentInput
): CoreLfModuleTheoremDevelopmentPlan {
    const canonical = canonicalTheoremBindings(input, false);
    return Object.freeze({
        revision: input.revision,
        profileRevision: CORE_LF_MODULE_THEOREM_DEVELOPMENT_PROFILE.revision,
        proofDevelopmentProfileRevision:
            CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision,
        declaredTheoremProfileRevision:
            CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.revision,
        development: canonical.development,
        bindings: canonical.bindings
    });
}

const expressionFreeReferences = (
    expression: KernelExpression
): readonly string[] => {
    const references = new Set<string>();
    const pending: KernelExpression[] = [expression];
    while (pending.length > 0) {
        const current = pending.pop();
        if (current === undefined) break;
        switch (current.tag) {
            case 'universe':
            case 'bound':
                break;
            case 'reference':
                references.add(current.name);
                break;
            case 'meta':
                pending.push(...current.spine);
                break;
            case 'application':
                pending.push(...current.arguments.map(argument =>
                    argument.value
                ));
                break;
            case 'call':
                pending.push(
                    current.callee,
                    ...current.arguments.map(argument => argument.value)
                );
                break;
            case 'pi':
            case 'lambda':
                pending.push(current.binder.type, current.body);
                break;
            default: {
                const exhaustive: never = current;
                return exhaustive;
            }
        }
    }
    return Object.freeze([...references].sort(compareText));
};

const transitiveFreeReferences = (
    direct: readonly string[],
    environment: CoreLfDeclarationEnvironment
): readonly string[] => {
    const seen = new Set<string>();
    const pending = [...direct].sort(compareText).reverse();
    while (pending.length > 0) {
        const name = pending.pop();
        if (name === undefined || seen.has(name)) continue;
        seen.add(name);
        const declaration = environment.lookup(name);
        if (declaration?.body === undefined) continue;
        [...declaration.bodyDependencies]
            .sort(compareText)
            .reverse()
            .forEach(dependency => pending.push(dependency));
    }
    return Object.freeze([...seen].sort(compareText));
};

const proofPlanFreeReferences = (
    plan: CoreProofPlan
): readonly string[] => {
    const references = new Set<string>();
    const addExpression = (expression: KernelExpression): void => {
        expressionFreeReferences(expression).forEach(reference =>
            references.add(reference)
        );
    };
    const pending: CoreProofPlan[] = [plan];
    while (pending.length > 0) {
        const current = pending.pop();
        if (current === undefined) break;
        switch (current.tag) {
            case 'exact':
                addExpression(current.solution);
                break;
            case 'intro':
                pending.push(current.body);
                break;
            case 'apply':
                addExpression(current.callee);
                pending.push(...current.premises);
                break;
            case 'have':
                addExpression(current.binding.type);
                pending.push(current.proof, current.body);
                break;
            case 'hole':
                if (current.expectation?.target !== undefined) {
                    addExpression(current.expectation.target);
                }
                break;
            default: {
                const exhaustive: never = current;
                return exhaustive;
            }
        }
    }
    return Object.freeze([...references].sort(compareText));
};

interface ResolvedBinding {
    readonly binding: CoreLfDeclaredTheoremBindingInput;
    readonly proofInput:
        CoreLfFragmentProofDevelopmentPlan['proofs'][number];
    readonly compilation: CoreLfFragmentWorkspaceProofCompilation;
    readonly declaration: CoreLfCompiledDeclaration;
    readonly coreName: string;
    readonly environment: CoreLfDeclarationEnvironment;
}

const accessibleProofReferences = (
    entry: ResolvedBinding,
    index: number
): readonly string[] => {
    const root = entry.compilation.closureCompilation.modules.find(module =>
        module.source.identity.moduleId === entry.binding.proof.moduleId
    );
    if (root === undefined) {
        return fail(
            'INVALID_COMPILED_DEVELOPMENT',
            `bindings[${index}].proof.moduleId`,
            `Exact proof closure has no root ` +
                `'${entry.binding.proof.moduleId}'`
        );
    }
    const allowed = new Set<string>();
    root.compiled.moduleInterface?.entries.forEach(candidate => {
        if (
            candidate.status !== 'excluded' &&
            candidate.link.kind === 'free-declaration'
        ) {
            allowed.add(candidate.link.coreName);
        }
    });
    root.dependencyInterfaces.forEach(dependency => {
        dependency.entries.forEach(candidate => {
            if (
                candidate.status !== 'excluded' &&
                candidate.visibility === 'public' &&
                candidate.link.kind === 'free-declaration'
            ) {
                allowed.add(candidate.link.coreName);
            }
        });
    });

    const sourceReferences = new Set<string>([
        ...expressionFreeReferences(entry.proofInput.type),
        ...proofPlanFreeReferences(entry.proofInput.plan),
        ...(entry.compilation.checkedTerm === undefined
            ? []
            : expressionFreeReferences(entry.compilation.checkedTerm))
    ]);
    const ordered = [...sourceReferences].sort(compareText);
    const inaccessible = ordered.filter(reference => !allowed.has(reference));
    if (inaccessible.length > 0) {
        return fail(
            'INACCESSIBLE_PROOF_REFERENCE',
            `bindings[${index}].proof`,
            `Proof '${displayProof(entry.binding.proof)}' directly names ` +
                `free declaration(s) outside its local/direct-public ` +
                `source scope: ${inaccessible.join(', ')}`
        );
    }
    return Object.freeze(ordered);
};

export interface CoreLfDeclaredTheoremArtifactBinding {
    readonly proof: CoreLfDeclaredTheoremProofIdentity;
    readonly theorem: CoreLfQualifiedSymbol;
    readonly coreName: string;
    readonly status: 'complete' | 'incomplete';
    readonly directFreeReferences: readonly string[];
    readonly transitiveFreeReferences: readonly string[];
    readonly theoremDependencies:
        readonly CoreLfDeclaredTheoremProofIdentity[];
    readonly workspaceDependencies: readonly string[];
}

export interface CoreLfDeclaredTheoremDevelopmentArtifact {
    readonly revision:
        typeof CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.artifactRevision;
    readonly profileRevision:
        typeof CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.revision;
    readonly developmentRevision: string;
    readonly status: 'complete' | 'incomplete';
    readonly openGoalCount: number;
    readonly development: CoreLfFragmentProofDevelopmentArtifact;
    readonly bindings: readonly CoreLfDeclaredTheoremArtifactBinding[];
    readonly theoremOrder:
        readonly CoreLfDeclaredTheoremProofIdentity[];
}

/** Process-local checked development plus its portable theorem evidence. */
export class CoreLfCompiledDeclaredTheoremDevelopment {
    readonly revision: string;
    readonly bindings: readonly CoreLfDeclaredTheoremArtifactBinding[];

    constructor(
        public readonly plan: CoreLfDeclaredTheoremDevelopmentPlan,
        public readonly development: CoreLfCompiledFragmentProofDevelopment,
        public readonly artifact: CoreLfDeclaredTheoremDevelopmentArtifact
    ) {
        this.revision = `${plan.revision}+compiled-1`;
        this.bindings = artifact.bindings;
        Object.freeze(this);
    }

    binding(
        moduleId: string,
        declarationId: string
    ): CoreLfDeclaredTheoremArtifactBinding | undefined {
        return this.bindings.find(entry =>
            entry.proof.moduleId === moduleId &&
            entry.proof.declarationId === declarationId
        );
    }
}

export interface CoreLfModuleTheoremArtifactBinding
extends CoreLfDeclaredTheoremArtifactBinding {
    /** Free declarations named by target, inert plan, or final checked term. */
    readonly sourceFreeReferences: readonly string[];
}

export interface CoreLfModuleTheoremDevelopmentArtifact {
    readonly revision:
        typeof CORE_LF_MODULE_THEOREM_DEVELOPMENT_PROFILE.artifactRevision;
    readonly profileRevision:
        typeof CORE_LF_MODULE_THEOREM_DEVELOPMENT_PROFILE.revision;
    readonly developmentRevision: string;
    readonly status: 'complete' | 'incomplete';
    readonly openGoalCount: number;
    readonly development: CoreLfFragmentProofDevelopmentArtifact;
    readonly bindings: readonly CoreLfModuleTheoremArtifactBinding[];
    readonly theoremOrder:
        readonly CoreLfDeclaredTheoremProofIdentity[];
}

/** Checked closed-workspace theorem DAG plus its portable evidence. */
export class CoreLfCompiledModuleTheoremDevelopment {
    readonly revision: string;
    readonly bindings: readonly CoreLfModuleTheoremArtifactBinding[];

    constructor(
        public readonly plan: CoreLfModuleTheoremDevelopmentPlan,
        public readonly development: CoreLfCompiledFragmentProofDevelopment,
        public readonly artifact: CoreLfModuleTheoremDevelopmentArtifact
    ) {
        this.revision = `${plan.revision}+compiled-1`;
        this.bindings = artifact.bindings;
        Object.freeze(this);
    }

    binding(
        moduleId: string,
        declarationId: string
    ): CoreLfModuleTheoremArtifactBinding | undefined {
        return this.bindings.find(entry =>
            entry.proof.moduleId === moduleId &&
            entry.proof.declarationId === declarationId
        );
    }
}

const exactResolvedBinding = (
    binding: CoreLfDeclaredTheoremBindingInput,
    developmentPlan: CoreLfFragmentProofDevelopmentPlan,
    development: CoreLfCompiledFragmentProofDevelopment,
    index: number
): ResolvedBinding => {
    const key = proofKey(binding.proof);
    const proofInput = developmentPlan.proofs.find(proof =>
        proofKey(proof) === key
    );
    const compilation = development.proof(
        binding.proof.moduleId,
        binding.proof.declarationId
    );
    if (proofInput === undefined || compilation === undefined) {
        return fail(
            'INVALID_COMPILED_DEVELOPMENT',
            `bindings[${index}].proof`,
            `Compiled development omitted proof '${displayProof(binding.proof)}'`
        );
    }
    const declaration = compilation.closureCompilation.declarations
        .declaration(binding.theorem);
    if (declaration === undefined) {
        return fail(
            'UNKNOWN_THEOREM_DECLARATION',
            `bindings[${index}].theorem`,
            `Exact proof closure has no declaration ` +
                `'${displaySymbol(binding.theorem)}'`
        );
    }
    if (
        declaration.link.kind !== 'free-declaration' ||
        declaration.status !== 'installed-opaque' ||
        declaration.policy !== 'opaque-signature' ||
        declaration.body !== undefined
    ) {
        return fail(
            'UNSUPPORTED_THEOREM_DECLARATION',
            `bindings[${index}].theorem`,
            `Bound theorem '${displaySymbol(binding.theorem)}' must be a ` +
                'body-free opaque-signature free declaration'
        );
    }
    const environment = compilation.closureCompilation.declarations.environment;
    const checkedDeclaration = environment.lookup(declaration.link.coreName);
    if (
        checkedDeclaration === undefined ||
        checkedDeclaration.body !== undefined ||
        checkedDeclaration.transparency !== 'opaque'
    ) {
        return fail(
            'UNSUPPORTED_THEOREM_DECLARATION',
            `bindings[${index}].theorem`,
            `Bound theorem '${displaySymbol(binding.theorem)}' does not ` +
                'preserve an opaque absent-body declaration environment entry'
        );
    }

    const root = compilation.closureCompilation.modules.find(module =>
        module.source.identity.moduleId === binding.proof.moduleId
    );
    if (root === undefined) {
        return fail(
            'INVALID_COMPILED_DEVELOPMENT',
            `bindings[${index}].proof.moduleId`,
            `Exact proof closure has no root '${binding.proof.moduleId}'`
        );
    }
    const runtime = root.compiled.latestRuntime?.runtime ??
        composeCoreLfRuntimeDependencies(root.runtimeDependencies);
    const checker = createCoreLfChecker(
        environment,
        CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.comparisonStepLimit,
        runtime
    );
    try {
        checker.validateEnvironment();
        const nodeProvenance = provenance(
            'derived',
            `declared theorem binding for ${displaySymbol(binding.theorem)}`,
            proofInput.provenance.span
        );
        checker.check(
            checker.rootContext,
            kernelFree(declaration.link.coreName, nodeProvenance),
            proofInput.type
        );
        if (compilation.artifact.state.status === 'complete') {
            if (compilation.checkedTerm === undefined) {
                return fail(
                    'INVALID_COMPILED_DEVELOPMENT',
                    `bindings[${index}].proof`,
                    `Complete proof '${displayProof(binding.proof)}' has no ` +
                        'checked term'
                );
            }
            checker.check(
                checker.rootContext,
                compilation.checkedTerm,
                declaration.type
            );
        }
    } catch (error: unknown) {
        if (error instanceof CoreLfDeclaredTheoremDevelopmentError) {
            throw error;
        }
        return fail(
            'THEOREM_TARGET_MISMATCH',
            `bindings[${index}]`,
            `Proof '${displayProof(binding.proof)}' does not prove bound ` +
                `theorem '${displaySymbol(binding.theorem)}': ` +
                errorText(error),
            error instanceof Error ? error : undefined
        );
    }
    return {
        binding,
        proofInput,
        compilation,
        declaration,
        coreName: declaration.link.coreName,
        environment
    };
};

const theoremDependencyCycle = (
    proofKeys: readonly string[],
    edges: ReadonlyMap<string, readonly string[]>
): readonly string[] | undefined => {
    const active = new Set<string>();
    const complete = new Set<string>();
    const stack: string[] = [];

    const visit = (key: string): readonly string[] | undefined => {
        if (complete.has(key)) return undefined;
        if (active.has(key)) {
            const start = stack.indexOf(key);
            return Object.freeze([...stack.slice(start), key]);
        }
        active.add(key);
        stack.push(key);
        for (const dependency of edges.get(key) ?? []) {
            const cycle = visit(dependency);
            if (cycle !== undefined) return cycle;
        }
        stack.pop();
        active.delete(key);
        complete.add(key);
        return undefined;
    };

    for (const key of proofKeys) {
        const cycle = visit(key);
        if (cycle !== undefined) return cycle;
    }
    return undefined;
};

const dependencyFirstOrder = (
    proofKeys: readonly string[],
    edges: ReadonlyMap<string, readonly string[]>
): readonly string[] => {
    const seen = new Set<string>();
    const order: string[] = [];
    const visit = (key: string): void => {
        if (seen.has(key)) return;
        seen.add(key);
        (edges.get(key) ?? []).forEach(visit);
        order.push(key);
    };
    proofKeys.forEach(visit);
    return Object.freeze(order);
};

interface CoreLfTheoremGraphPlan {
    readonly development: CoreLfFragmentProofDevelopmentPlan;
    readonly bindings: readonly CoreLfDeclaredTheoremBindingInput[];
}

interface CoreLfCompiledTheoremGraph {
    readonly development: CoreLfCompiledFragmentProofDevelopment;
    readonly bindings: readonly CoreLfDeclaredTheoremArtifactBinding[];
    readonly theoremOrder:
        readonly CoreLfDeclaredTheoremProofIdentity[];
    readonly sourceFreeReferencesByProof:
        ReadonlyMap<string, readonly string[]>;
}

const compileCoreLfTheoremGraph = (
    plan: CoreLfTheoremGraphPlan,
    enforceSourceVisibility: boolean
): CoreLfCompiledTheoremGraph => {
    const development = compileCoreLfFragmentProofDevelopment(
        plan.development
    );
    const resolved = plan.bindings.map((binding, index) =>
        exactResolvedBinding(binding, plan.development, development, index)
    );
    const resolvedByProof = new Map(resolved.map(entry => [
        proofKey(entry.binding.proof),
        entry
    ]));
    const proofByCoreName = new Map(resolved.map(entry => [
        entry.coreName,
        proofKey(entry.binding.proof)
    ]));
    const proofKeys = resolved.map(entry => proofKey(entry.binding.proof));
    const edges = new Map<string, readonly string[]>();
    const sourceFreeReferencesByProof = new Map<
        string,
        readonly string[]
    >();

    const bindings = resolved.map((entry, index) => {
        const status = entry.compilation.artifact.state.status;
        const direct = entry.compilation.checkedTerm === undefined
            ? Object.freeze([] as string[])
            : expressionFreeReferences(entry.compilation.checkedTerm);
        const transitive = transitiveFreeReferences(
            direct,
            entry.environment
        );
        const dependencyKeys = Object.freeze(transitive.flatMap(name => {
            const dependency = proofByCoreName.get(name);
            return dependency === undefined ? [] : [dependency];
        }).sort(compareText));
        const key = proofKey(entry.binding.proof);
        if (enforceSourceVisibility) {
            sourceFreeReferencesByProof.set(
                key,
                accessibleProofReferences(entry, index)
            );
        }
        if (dependencyKeys.includes(key)) {
            return fail(
                'SELF_THEOREM_DEPENDENCY',
                `bindings[${index}]`,
                `Proof '${displayProof(entry.binding.proof)}' depends on its ` +
                    'own bound theorem signature'
            );
        }
        for (const dependencyKey of dependencyKeys) {
            const dependency = resolvedByProof.get(dependencyKey);
            if (
                status === 'complete' &&
                dependency?.compilation.artifact.state.status !== 'complete'
            ) {
                return fail(
                    'OPEN_THEOREM_DEPENDENCY',
                    `bindings[${index}]`,
                    `Complete proof '${displayProof(entry.binding.proof)}' ` +
                        `depends on open theorem proof ` +
                        `'${displayProof(dependency!.binding.proof)}'`
                );
            }
        }
        edges.set(key, dependencyKeys);
        const theoremDependencies = dependencyKeys.map(dependency =>
            cloneProof(resolvedByProof.get(dependency)!.binding.proof)
        );
        const workspaceDependencies = transitive.filter(name =>
            !proofByCoreName.has(name)
        );
        return {
            proof: cloneProof(entry.binding.proof),
            theorem: cloneSymbol(entry.binding.theorem),
            coreName: entry.coreName,
            status,
            directFreeReferences: direct,
            transitiveFreeReferences: transitive,
            theoremDependencies,
            workspaceDependencies
        };
    });

    const cycle = theoremDependencyCycle(proofKeys, edges);
    if (cycle !== undefined) {
        return fail(
            'CYCLIC_THEOREM_DEPENDENCY',
            'bindings',
            `Declared theorem dependency cycle: ${cycle.map(key =>
                displayProof(resolvedByProof.get(key)!.binding.proof)
            ).join(' -> ')}`
        );
    }
    const theoremOrder = dependencyFirstOrder(proofKeys, edges).map(key =>
        cloneProof(resolvedByProof.get(key)!.binding.proof)
    );
    return {
        development,
        bindings: deepFreeze(bindings),
        theoremOrder: deepFreeze(theoremOrder),
        sourceFreeReferencesByProof
    };
};

/** Compile exact proofs, bind theorem signatures, and certify their DAG. */
export function compileCoreLfDeclaredTheoremDevelopment(
    plan: CoreLfDeclaredTheoremDevelopmentPlan
): CoreLfCompiledDeclaredTheoremDevelopment {
    if (
        plan.profileRevision !==
            CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.revision ||
        plan.proofDevelopmentProfileRevision !==
            CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision
    ) {
        return fail(
            'INVALID_DEVELOPMENT',
            'profileRevision',
            'Declared-theorem development targets an unsupported profile'
        );
    }
    const canonical = createCoreLfDeclaredTheoremDevelopment({
        revision: plan.revision,
        development: plan.development,
        bindings: plan.bindings
    });
    const graph = compileCoreLfTheoremGraph(canonical, false);
    const artifact: CoreLfDeclaredTheoremDevelopmentArtifact = deepFreeze({
        revision:
            CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.artifactRevision,
        profileRevision:
            CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.revision,
        developmentRevision: canonical.revision,
        status: graph.development.artifact.status,
        openGoalCount: graph.development.artifact.openGoalCount,
        development: graph.development.artifact,
        bindings: graph.bindings,
        theoremOrder: graph.theoremOrder
    });
    return new CoreLfCompiledDeclaredTheoremDevelopment(
        canonical,
        graph.development,
        artifact
    );
}

/** Deterministic, diff-friendly portable theorem-development artifact. */
export const serializeCoreLfDeclaredTheoremDevelopmentArtifact = (
    artifact: CoreLfDeclaredTheoremDevelopmentArtifact
): string => `${JSON.stringify(artifact, null, 2)}\n`;

/** Compile a visibility-safe theorem DAG across one closed workspace. */
export function compileCoreLfModuleTheoremDevelopment(
    plan: CoreLfModuleTheoremDevelopmentPlan
): CoreLfCompiledModuleTheoremDevelopment {
    if (
        plan.profileRevision !==
            CORE_LF_MODULE_THEOREM_DEVELOPMENT_PROFILE.revision ||
        plan.proofDevelopmentProfileRevision !==
            CORE_LF_FRAGMENT_PROOF_DEVELOPMENT_PROFILE.revision ||
        plan.declaredTheoremProfileRevision !==
            CORE_LF_DECLARED_THEOREM_DEVELOPMENT_PROFILE.revision
    ) {
        return fail(
            'INVALID_DEVELOPMENT',
            'profileRevision',
            'Module theorem development targets an unsupported profile'
        );
    }
    const canonical = createCoreLfModuleTheoremDevelopment({
        revision: plan.revision,
        development: plan.development,
        bindings: plan.bindings
    });
    const graph = compileCoreLfTheoremGraph(canonical, true);
    const bindings: readonly CoreLfModuleTheoremArtifactBinding[] =
        graph.bindings.map(binding => ({
            ...binding,
            sourceFreeReferences:
                graph.sourceFreeReferencesByProof.get(
                    proofKey(binding.proof)
                ) ?? Object.freeze([])
        }));
    const artifact: CoreLfModuleTheoremDevelopmentArtifact = deepFreeze({
        revision: CORE_LF_MODULE_THEOREM_DEVELOPMENT_PROFILE.artifactRevision,
        profileRevision: CORE_LF_MODULE_THEOREM_DEVELOPMENT_PROFILE.revision,
        developmentRevision: canonical.revision,
        status: graph.development.artifact.status,
        openGoalCount: graph.development.artifact.openGoalCount,
        development: graph.development.artifact,
        bindings,
        theoremOrder: graph.theoremOrder
    });
    return new CoreLfCompiledModuleTheoremDevelopment(
        canonical,
        graph.development,
        artifact
    );
}

/** Deterministic portable closed-workspace theorem artifact. */
export const serializeCoreLfModuleTheoremDevelopmentArtifact = (
    artifact: CoreLfModuleTheoremDevelopmentArtifact
): string => `${JSON.stringify(artifact, null, 2)}\n`;
