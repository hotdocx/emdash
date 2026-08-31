/** Durable source-spanned modules of explicitly adopted computation claims. */

import {
    AlgebraFormalTrustedAdoption,
    AlgebraFormalTrustedAdoptionArtifact,
    assertAlgebraFormalComputationResultCurrent
} from './algebra_formal_adoption';
import {
    AlgebraFormalDelegationError
} from './algebra_formal_delegation';
import {
    serializeCoreExpression
} from './core_serialization';
import {
    CoreLfDeclaration,
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreLfKernelProbe,
    serializeCoreLfKernelProbe
} from './lf_probe';
import {
    KernelExpression,
    binderMode,
    kernelFree,
    provenance,
    sourceSpan
} from './kernel';
import {
    serializeCoreLfWorkspaceCanonicalJson
} from './lf_workspace';
import {
    KernelProbeAssertion,
    SerializedProbe
} from './probe';

export const ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-formal-assumption-source-v1' as const,
    entryRevision: 'emdash-algebra-formal-assumption-entry-v1' as const,
    classifications: Object.freeze([
        'computed-equation',
        'trusted-presentation-semantics'
    ] as const),
    sourceOrder: 'explicit-append-only' as const,
    declarationPolicy: 'checked-type-body-free-opaque' as const,
    decisionPolicy: 'one-existing-explicit-adoption-per-entry' as const,
    mutatesBase: false as const,
    addsCoreOwner: false as const,
    addsProofPlanTag: false as const,
    performsIo: false as const,
    productionLambdapiDependency: false as const
});

export type AlgebraFormalAssumptionClassification =
    typeof ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE.classifications[number];

export type AlgebraFormalAssumptionSourceErrorCode =
    | 'INVALID_SOURCE'
    | 'INVALID_CLASSIFICATION'
    | 'FOREIGN_ENVIRONMENT'
    | 'DUPLICATE_ASSUMPTION'
    | 'STALE_ADOPTION'
    | 'SOURCE_DRIFT';

export class AlgebraFormalAssumptionSourceError extends Error {
    constructor(
        public readonly code: AlgebraFormalAssumptionSourceErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraFormalAssumptionSourceError';
    }
}

const fail = (
    code: AlgebraFormalAssumptionSourceErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraFormalAssumptionSourceError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;
const sourceId = (value: unknown, path: string): string => {
    if (
        typeof value === 'string' &&
        value.length > 0 &&
        value.length <= 4096 &&
        !/[\u0000-\u001f\u007f]/u.test(value)
    ) return value;
    return fail('INVALID_SOURCE', path, 'Source identity must be portable text');
};

const stableId = (value: unknown, path: string): string => {
    if (typeof value === 'string' && SAFE_ID.test(value)) return value;
    return fail('INVALID_SOURCE', path, 'Expected one stable portable ID');
};

const classification = (
    value: unknown,
    path: string
): AlgebraFormalAssumptionClassification => {
    if (
        value === 'computed-equation' ||
        value === 'trusted-presentation-semantics'
    ) return value;
    return fail(
        'INVALID_CLASSIFICATION',
        path,
        'Unsupported computed-assumption classification'
    );
};

export interface AlgebraFormalAssumptionSourceEntry {
    readonly revision:
        typeof ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE.entryRevision;
    readonly index: number;
    readonly classification: AlgebraFormalAssumptionClassification;
    readonly declaration: CoreLfDeclaration;
    readonly reference: KernelExpression;
    readonly adoption: AlgebraFormalTrustedAdoption<unknown, unknown, unknown>;
    readonly adoptionArtifact: AlgebraFormalTrustedAdoptionArtifact;
}

export interface AlgebraFormalAssumptionSource {
    readonly profileRevision:
        typeof ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE.revision;
    readonly moduleId: string;
    readonly sourceId: string;
    readonly baseEnvironment: CoreLfDeclarationEnvironment;
    readonly environment: CoreLfDeclarationEnvironment;
    readonly entries: readonly AlgebraFormalAssumptionSourceEntry[];
}

export function createAlgebraFormalAssumptionSource(input: {
    readonly moduleId: string;
    readonly sourceId: string;
    readonly baseEnvironment: CoreLfDeclarationEnvironment;
}): AlgebraFormalAssumptionSource {
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE.revision,
        moduleId: stableId(input.moduleId, 'assumptionSource.moduleId'),
        sourceId: sourceId(input.sourceId, 'assumptionSource.sourceId'),
        baseEnvironment: input.baseEnvironment,
        environment: input.baseEnvironment,
        entries: Object.freeze([])
    });
}

const erasedAdoption = <R, I, O>(
    adoption: AlgebraFormalTrustedAdoption<R, I, O>
): AlgebraFormalTrustedAdoption<unknown, unknown, unknown> =>
    adoption as unknown as AlgebraFormalTrustedAdoption<unknown, unknown, unknown>;

export function appendAlgebraFormalAssumption<R, I, O>(input: {
    readonly source: AlgebraFormalAssumptionSource;
    readonly adoption: AlgebraFormalTrustedAdoption<R, I, O>;
    readonly classification: AlgebraFormalAssumptionClassification;
}): AlgebraFormalAssumptionSource {
    const source = input.source;
    if (
        source.profileRevision !==
            ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE.revision
    ) {
        return fail(
            'INVALID_SOURCE',
            'assumptionSource.profileRevision',
            'Cannot append to a foreign assumption-source revision'
        );
    }
    const selectedClassification = classification(
        input.classification,
        'assumptionSource.entry.classification'
    );
    if (
        input.adoption.result.request.goal.document.environment !==
            source.environment
    ) {
        return fail(
            'FOREIGN_ENVIRONMENT',
            'assumptionSource.entry.adoption',
            'Adopted goal did not start from the current source environment'
        );
    }
    if (source.environment.lookup(input.adoption.assumption.name) !== undefined) {
        return fail(
            'DUPLICATE_ASSUMPTION',
            'assumptionSource.entry.assumption',
            `Assumption '${input.adoption.assumption.name}' already exists`
        );
    }
    try {
        assertAlgebraFormalComputationResultCurrent(
            input.adoption.result,
            input.adoption.result.request
        );
    } catch (error: unknown) {
        return fail(
            'STALE_ADOPTION',
            'assumptionSource.entry.adoption',
            'Adoption result is no longer current',
            error
        );
    }
    const index = source.entries.length;
    const declarationProvenance = provenance(
        'surface',
        `${selectedClassification}: ${input.adoption.assumption.name}`,
        sourceSpan(source.sourceId, index + 1, 1, index + 1, 2)
    );
    let environment: CoreLfDeclarationEnvironment;
    try {
        environment = source.environment.extend({
            name: input.adoption.assumption.name,
            type: input.adoption.assumption.type,
            mode: binderMode('explicit', 'functorial'),
            provenance: declarationProvenance
        });
    } catch (error: unknown) {
        return fail(
            'SOURCE_DRIFT',
            'assumptionSource.entry.declaration',
            'Source-spanned assumption declaration did not check',
            error
        );
    }
    const declaration = environment.lookup(input.adoption.assumption.name)!;
    const reference = kernelFree(declaration.name, declarationProvenance);
    const entry: AlgebraFormalAssumptionSourceEntry = Object.freeze({
        revision: ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE.entryRevision,
        index,
        classification: selectedClassification,
        declaration,
        reference,
        adoption: erasedAdoption(input.adoption),
        adoptionArtifact: input.adoption.artifact
    });
    return Object.freeze({
        ...source,
        environment,
        entries: Object.freeze([...source.entries, entry])
    });
}

export const serializeAlgebraFormalAssumptionSource = (
    source: AlgebraFormalAssumptionSource
): string => serializeCoreLfWorkspaceCanonicalJson({
    serializationRevision:
        ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE.revision,
    moduleId: source.moduleId,
    sourceId: source.sourceId,
    baseDeclarationCount: source.baseEnvironment.declarations.length,
    entries: source.entries.map(entry => ({
        revision: entry.revision,
        index: entry.index,
        classification: entry.classification,
        name: entry.declaration.name,
        typeCore: serializeCoreExpression(entry.declaration.type),
        adoption: entry.adoptionArtifact
    }))
}, 'algebraFormalAssumptionSource');

export function validateAlgebraFormalAssumptionSource(
    source: AlgebraFormalAssumptionSource
): AlgebraFormalAssumptionSource {
    let environment = source.baseEnvironment;
    source.entries.forEach((entry, index) => {
        if (
            entry.index !== index ||
            entry.revision !==
                ALGEBRA_FORMAL_ASSUMPTION_SOURCE_PROFILE.entryRevision
        ) {
            return fail(
                'SOURCE_DRIFT',
                `assumptionSource.entries[${index}]`,
                'Assumption entry order or revision drifted'
            );
        }
        classification(
            entry.classification,
            `assumptionSource.entries[${index}].classification`
        );
        try {
            assertAlgebraFormalComputationResultCurrent(
                entry.adoption.result,
                entry.adoption.result.request
            );
            environment = environment.extend({
                name: entry.declaration.name,
                type: entry.declaration.type,
                mode: entry.declaration.mode,
                provenance: entry.declaration.provenance
            });
        } catch (error: unknown) {
            return fail(
                'SOURCE_DRIFT',
                `assumptionSource.entries[${index}]`,
                'Assumption source no longer replays',
                error
            );
        }
    });
    if (
        environment.declarations.length !== source.environment.declarations.length ||
        environment.declarations.some((declaration, index) => {
            const expected = source.environment.declarations[index];
            return declaration.name !== expected.name ||
                serializeCoreExpression(declaration.type) !==
                    serializeCoreExpression(expected.type);
        })
    ) {
        return fail(
            'SOURCE_DRIFT',
            'assumptionSource.environment',
            'Replayed assumption environment differs from retained environment'
        );
    }
    return source;
}

export function serializeAlgebraFormalAssumptionKernelProbe(input: {
    readonly source: AlgebraFormalAssumptionSource;
    readonly externalFreeReferences?: CoreLfKernelProbe[
        'externalFreeReferences'
    ];
    readonly assertions: readonly KernelProbeAssertion[];
}): SerializedProbe {
    validateAlgebraFormalAssumptionSource(input.source);
    return serializeCoreLfKernelProbe({
        environment: input.source.environment,
        ...(input.externalFreeReferences === undefined
            ? {}
            : { externalFreeReferences: input.externalFreeReferences }),
        assertions: input.assertions
    });
}
