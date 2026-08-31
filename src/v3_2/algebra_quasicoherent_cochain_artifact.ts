/** Portable artifacts for evaluated affine Cech cochains and differentials. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import { algebraPresentedAlgebraModuleIsZero } from './algebra_presented_module';
import {
    AlgebraAffineQuasiCoherentCochain,
    algebraAffineQuasiCoherentCochainIsZero,
    serializeAlgebraAffineQuasiCoherentCochain
} from './algebra_quasicoherent_cochain';
import {
    AlgebraAffineQuasiCoherentDifferential,
    algebraAffineQuasiCoherentDifferential,
    serializeAlgebraAffineQuasiCoherentDifferential
} from './algebra_quasicoherent_differential';
import {
    AlgebraAffineQuasiCoherentDifferentialSquare,
    algebraAffineQuasiCoherentDifferentialSquare,
    serializeAlgebraAffineQuasiCoherentDifferentialSquare
} from './algebra_quasicoherent_differential_square';

export const ALGEBRA_QUASICOHERENT_COCHAIN_ARTIFACT_PROFILE = Object.freeze({
    revision: 'emdash-quasicoherent-cochain-artifact-v1' as const,
    serializationRevision: 'emdash-quasicoherent-cochain-artifact-json-v1' as const,
    content: 'evaluated-cochain-differential-and-optional-square' as const,
    proofClaim: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraQuasiCoherentCochainArtifactErrorCode =
    'INVALID_ARTIFACT_ID';

export class AlgebraQuasiCoherentCochainArtifactError extends Error {
    constructor(
        public readonly code: AlgebraQuasiCoherentCochainArtifactErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraQuasiCoherentCochainArtifactError';
    }
}

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;

export interface AlgebraAffineQuasiCoherentCochainArtifact<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-affine-quasicoherent-cochain-artifact';
    readonly id: string;
    readonly input: AlgebraAffineQuasiCoherentCochain<P, C, I>;
    readonly differential: AlgebraAffineQuasiCoherentDifferential<P, C, I>;
    readonly square?: AlgebraAffineQuasiCoherentDifferentialSquare<P, C, I>;
    readonly summary: {
        readonly sourceDegree: number;
        readonly targetDegree: number;
        readonly sourceComponentCount: number;
        readonly targetComponentCount: number;
        readonly contributionCount: number;
        readonly zeroSimplexModuleCount: number;
        readonly inputIsZero: boolean;
        readonly differentialIsZero: boolean;
        readonly squareAvailable: boolean;
        readonly cancellationCount: number;
        readonly squareHolds?: true;
    };
}

export function algebraAffineQuasiCoherentCochainArtifact<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    id: string,
    input: AlgebraAffineQuasiCoherentCochain<P, C, I>
): AlgebraAffineQuasiCoherentCochainArtifact<P, C, I> {
    if (!SAFE_ID.test(id)) {
        throw new AlgebraQuasiCoherentCochainArtifactError(
            'INVALID_ARTIFACT_ID',
            'quasicoherentCochainArtifact.id',
            'Artifact ID must be one stable portable identifier'
        );
    }
    const differential = algebraAffineQuasiCoherentDifferential(input);
    const squareAvailable = input.parent.diagram.degrees.some(degree =>
        degree.degree === input.parent.degree + 2
    );
    const square = squareAvailable
        ? algebraAffineQuasiCoherentDifferentialSquare(input)
        : undefined;
    const summary = Object.freeze({
        sourceDegree: input.parent.degree,
        targetDegree: differential.targetDegree.degree,
        sourceComponentCount: input.components.length,
        targetComponentCount: differential.output.components.length,
        contributionCount: differential.targets.reduce(
            (count, target) => count + target.contributions.length,
            0
        ),
        zeroSimplexModuleCount: input.parent.diagram.simplices.filter(simplex =>
            algebraPresentedAlgebraModuleIsZero(simplex.value.module)
        ).length,
        inputIsZero: algebraAffineQuasiCoherentCochainIsZero(input),
        differentialIsZero: algebraAffineQuasiCoherentCochainIsZero(
            differential.output
        ),
        squareAvailable,
        cancellationCount: square?.cancellations.length ?? 0,
        ...(square === undefined ? {} : { squareHolds: true as const })
    });
    return Object.freeze({
        kind: 'algebra-affine-quasicoherent-cochain-artifact',
        id,
        input,
        differential,
        ...(square === undefined ? {} : { square }),
        summary
    });
}

export const serializeAlgebraAffineQuasiCoherentCochainArtifact = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(artifact: AlgebraAffineQuasiCoherentCochainArtifact<P, C, I>): string =>
    `${JSON.stringify({
        revision: ALGEBRA_QUASICOHERENT_COCHAIN_ARTIFACT_PROFILE
            .serializationRevision,
        kind: artifact.kind,
        id: artifact.id,
        input: JSON.parse(serializeAlgebraAffineQuasiCoherentCochain(
            artifact.input
        )),
        differential: JSON.parse(
            serializeAlgebraAffineQuasiCoherentDifferential(
                artifact.differential
            )
        ),
        ...(artifact.square === undefined ? {} : {
            square: JSON.parse(
                serializeAlgebraAffineQuasiCoherentDifferentialSquare(
                    artifact.square
                )
            )
        }),
        summary: artifact.summary
    })}\n`;
