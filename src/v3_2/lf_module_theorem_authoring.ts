/**
 * Direct-TypeScript authoring facade for exact module theorem developments.
 *
 * The caller supplies inert theorem proof entries and cryptographic hash
 * material. This owner derives the repeated workspace facts and lowers to the
 * existing module-theorem plan. Proof checking remains entirely in that
 * downstream compiler.
 */

import {
    CoreLfCompiledModuleTheoremDevelopment,
    CoreLfModuleTheoremDevelopmentPlan,
    compileCoreLfModuleTheoremDevelopment,
    createCoreLfModuleTheoremDevelopment
} from './lf_declared_theorem_development';
import {
    CoreLfFragmentProofDevelopmentPlan,
    createCoreLfFragmentProofDevelopment
} from './lf_fragment_proof_development';
import {
    CoreLfFragmentModuleWorkspacePlan,
    compileCoreLfFragmentModuleWorkspace
} from './lf_fragment_module_workspace';
import {
    CoreLfFragmentWorkspaceProofDocumentInput,
    CoreLfFragmentWorkspaceProofFingerprintHashes,
    createCoreLfFragmentWorkspaceProofFingerprintForWorkspace
} from './lf_fragment_workspace_proof';
import {
    CoreProofPlan
} from './proof_plan';
import {
    CoreLfQualifiedSymbol,
    coreLfQualifiedSymbol
} from './lf_transfer';
import {
    Provenance
} from './kernel';

export const CORE_LF_MODULE_THEOREM_AUTHORING_PROFILE = Object.freeze({
    revision: 'emdash-lf-module-theorem-authoring-v1' as const,
    lowering: 'exact-module-theorem-development-plan' as const,
    theoremIdentity: 'explicit-qualified-symbol' as const,
    proofIdentity: 'explicit-stable-proof-id' as const,
    targetPolicy: 'derive-exact-local-compiled-declaration-type' as const,
    fingerprintPolicy:
        'derive-exact-closure-runtime-from-caller-hashes' as const,
    workspaceCompilationDuringLowering: true as const,
    proofCheckingOwner:
        'emdash-lf-module-theorem-development-v1' as const,
    addsProofCheckingSemantics: false as const,
    generatesDeclarations: false as const,
    acceptsRuntimeInput: false as const,
    acceptsCompilerCallbacks: false as const,
    computesCryptographicHashes: false as const,
    performsIo: false as const,
    nodeBuiltinDependency: false as const,
    productionLambdapiDependency: false as const
});

export const serializeCoreLfModuleTheoremAuthoringProfile = (): string =>
    `${JSON.stringify(CORE_LF_MODULE_THEOREM_AUTHORING_PROFILE, null, 2)}\n`;

export type CoreLfModuleTheoremAuthoringErrorCode =
    | 'INVALID_THEOREM_SYMBOL'
    | 'UNKNOWN_THEOREM_MODULE'
    | 'UNKNOWN_LOCAL_THEOREM_DECLARATION';

export class CoreLfModuleTheoremAuthoringError extends Error {
    constructor(
        public readonly code: CoreLfModuleTheoremAuthoringErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'CoreLfModuleTheoremAuthoringError';
    }
}

const fail = (
    code: CoreLfModuleTheoremAuthoringErrorCode,
    path: string,
    message: string,
    underlying?: Error
): never => {
    throw new CoreLfModuleTheoremAuthoringError(
        code,
        path,
        message,
        underlying
    );
};

const errorText = (error: unknown): string =>
    error instanceof Error ? error.message : String(error);

const cloneData = <T>(value: T): T => {
    if (Array.isArray(value)) {
        return value.map(cloneData) as T;
    }
    if (value !== null && typeof value === 'object') {
        return Object.fromEntries(
            Object.entries(value as Record<string, unknown>).map(
                ([key, entry]) => [key, cloneData(entry)]
            )
        ) as T;
    }
    return value;
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

export interface CoreLfModuleTheoremAuthoringEntry {
    readonly proofId: string;
    readonly theorem: CoreLfQualifiedSymbol;
    readonly plan: CoreProofPlan;
    readonly provenance: Provenance;
    readonly sourceId: string;
    readonly fingerprintHashes:
        CoreLfFragmentWorkspaceProofFingerprintHashes;
}

export interface CoreLfModuleTheoremAuthoringInput {
    /** Shared row-19 and row-21 development revision. */
    readonly revision: string;
    readonly workspace: CoreLfFragmentModuleWorkspacePlan;
    readonly theorems: readonly CoreLfModuleTheoremAuthoringEntry[];
}

const theoremSymbol = (
    theorem: CoreLfQualifiedSymbol,
    index: number
): CoreLfQualifiedSymbol => {
    try {
        return coreLfQualifiedSymbol(theorem.moduleId, theorem.name);
    } catch (error: unknown) {
        return fail(
            'INVALID_THEOREM_SYMBOL',
            `theorems[${index}].theorem`,
            `Invalid theorem symbol: ${errorText(error)}`,
            error instanceof Error ? error : undefined
        );
    }
};

/**
 * Derive exact proof documents and theorem bindings, then erase to row 21.
 */
export function createCoreLfAuthoredModuleTheoremDevelopment(
    input: CoreLfModuleTheoremAuthoringInput
): CoreLfModuleTheoremDevelopmentPlan {
    const workspace = compileCoreLfFragmentModuleWorkspace(input.workspace);
    const bindings: {
        proof: { moduleId: string; declarationId: string };
        theorem: CoreLfQualifiedSymbol;
    }[] = [];
    const proofs: CoreLfFragmentWorkspaceProofDocumentInput[] =
        input.theorems.map((entry, index) => {
            const theorem = theoremSymbol(entry.theorem, index);
            const module = workspace.module(theorem.moduleId);
            if (module === undefined) {
                return fail(
                    'UNKNOWN_THEOREM_MODULE',
                    `theorems[${index}].theorem.moduleId`,
                    `Theorem module '${theorem.moduleId}' is not in the ` +
                        'exact fragment workspace'
                );
            }
            const declaration = module.compiled.moduleInterface
                ?.declaration(theorem);
            if (declaration === undefined) {
                return fail(
                    'UNKNOWN_LOCAL_THEOREM_DECLARATION',
                    `theorems[${index}].theorem`,
                    `Module '${theorem.moduleId}' does not locally declare ` +
                        `'${theorem.name}'`
                );
            }
            bindings.push({
                proof: {
                    moduleId: theorem.moduleId,
                    declarationId: entry.proofId
                },
                theorem
            });
            return {
                moduleId: theorem.moduleId,
                declarationId: entry.proofId,
                type: declaration.type,
                plan: deepFreeze(cloneData(entry.plan)),
                provenance: deepFreeze(cloneData(entry.provenance)),
                fingerprint:
                    createCoreLfFragmentWorkspaceProofFingerprintForWorkspace(
                        workspace,
                        theorem.moduleId,
                        entry.sourceId,
                        entry.fingerprintHashes
                    )
            };
        });
    const development: CoreLfFragmentProofDevelopmentPlan =
        createCoreLfFragmentProofDevelopment({
            revision: input.revision,
            workspace: workspace.plan,
            proofs
        });
    return deepFreeze(createCoreLfModuleTheoremDevelopment({
        revision: input.revision,
        development,
        bindings
    }));
}

/** Lower through the authoring facade and invoke the unchanged row-21 owner. */
export function compileCoreLfAuthoredModuleTheoremDevelopment(
    input: CoreLfModuleTheoremAuthoringInput
): CoreLfCompiledModuleTheoremDevelopment {
    return compileCoreLfModuleTheoremDevelopment(
        createCoreLfAuthoredModuleTheoremDevelopment(input)
    );
}
