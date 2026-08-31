/** Portable deterministic artifacts for affine presented-module descent. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import { algebraQuotientText } from './algebra_quotient';
import {
    AlgebraAffineCover
} from './algebra_cech';
import {
    algebraPresentedAlgebraModuleIsZero
} from './algebra_presented_module';
import {
    AlgebraAffineQuasiCoherentPresentation
} from './algebra_quasicoherent';
import {
    AlgebraAffineQuasiCoherentCechDiagram,
    algebraAffineQuasiCoherentCechDiagram
} from './algebra_quasicoherent_cech';

export const ALGEBRA_PRESENTED_MODULE_ARTIFACT_PROFILE = Object.freeze({
    revision: 'emdash-presented-module-descent-artifact-v1' as const,
    serializationRevision: 'emdash-presented-module-descent-json-v1' as const,
    content: 'whole-varying-ring-cech-data' as const,
    proofClaim: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraPresentedModuleArtifactErrorCode = 'INVALID_ARTIFACT_ID';

export class AlgebraPresentedModuleArtifactError extends Error {
    constructor(
        public readonly code: AlgebraPresentedModuleArtifactErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPresentedModuleArtifactError';
    }
}

const SAFE_ID = /^[A-Za-z][A-Za-z0-9._/-]*$/u;

export interface AlgebraPresentedModuleDescentArtifact<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-presented-module-descent-artifact';
    readonly id: string;
    readonly presentation: AlgebraAffineQuasiCoherentPresentation<P, C, I>;
    readonly cover: AlgebraAffineCover<P, C, I>;
    readonly diagram: AlgebraAffineQuasiCoherentCechDiagram<P, C, I>;
    readonly summary: {
        readonly simplexCount: number;
        readonly faceCount: number;
        readonly comparisonCount: number;
        readonly zeroSimplexCount: number;
        readonly degreeCounts: readonly {
            readonly degree: number;
            readonly simplices: number;
            readonly incomingFaces: number;
        }[];
    };
}

export function algebraPresentedModuleDescentArtifact<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    id: string,
    presentation: AlgebraAffineQuasiCoherentPresentation<P, C, I>,
    cover: AlgebraAffineCover<P, C, I>
): AlgebraPresentedModuleDescentArtifact<P, C, I> {
    if (!SAFE_ID.test(id)) {
        throw new AlgebraPresentedModuleArtifactError(
            'INVALID_ARTIFACT_ID',
            'presentedModuleArtifact.id',
            'Artifact ID must be one stable portable identifier'
        );
    }
    const diagram = algebraAffineQuasiCoherentCechDiagram(
        presentation,
        cover
    );
    const zeroSimplexCount = diagram.simplices.filter(simplex =>
        algebraPresentedAlgebraModuleIsZero(simplex.value.module)
    ).length;
    return Object.freeze({
        kind: 'algebra-presented-module-descent-artifact',
        id,
        presentation,
        cover,
        diagram,
        summary: Object.freeze({
            simplexCount: diagram.simplices.length,
            faceCount: diagram.faces.length,
            comparisonCount: diagram.comparisons.length,
            zeroSimplexCount,
            degreeCounts: Object.freeze(diagram.degrees.map(degree =>
                Object.freeze({
                    degree: degree.degree,
                    simplices: degree.simplices.length,
                    incomingFaces: degree.incomingFaces.length
                })
            ))
        })
    });
}

export const serializeAlgebraPresentedModuleDescentArtifact = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(artifact: AlgebraPresentedModuleDescentArtifact<P, C, I>): string =>
    `${JSON.stringify({
        revision: ALGEBRA_PRESENTED_MODULE_ARTIFACT_PROFILE.serializationRevision,
        kind: artifact.kind,
        id: artifact.id,
        coordinateAlgebra:
            artifact.presentation.scheme.coordinateAlgebra.quotient.identity,
        module: artifact.presentation.module.identity,
        cover: {
            maximumDegree: artifact.cover.maximumDegree,
            elements: artifact.cover.elements.map(algebraQuotientText)
        },
        simplices: artifact.diagram.simplices.map(simplex => ({
            degree: simplex.simplex.degree,
            indices: simplex.simplex.indices,
            product: algebraQuotientText(simplex.simplex.product),
            scalarAlgebra:
                simplex.value.chart.scheme.coordinateAlgebra.quotient.identity,
            module: simplex.value.module.identity,
            zero: algebraPresentedAlgebraModuleIsZero(simplex.value.module)
        })),
        faces: artifact.diagram.faces.map(face => ({
            domain: face.domain.simplex.indices,
            codomain: face.codomain.simplex.indices,
            removedPosition: face.face.removedPosition,
            removedChart: face.face.removedChart,
            sign: face.face.sign,
            scalarMapImages: face.map.scalarMap.generatorImages.map(
                algebraQuotientText
            ),
            generatorImages: face.map.generatorImages.map(image =>
                image.representative.components.map(algebraQuotientText)
            )
        })),
        comparisons: artifact.diagram.comparisons.map(comparison => ({
            simplex: comparison.simplex.simplex.indices,
            lower: comparison.lower.simplex.indices,
            firstIntermediate: comparison.firstIntermediate.simplex.indices,
            secondIntermediate: comparison.secondIntermediate.simplex.indices,
            removedPositions: comparison.removedPositions,
            holds: comparison.holds
        })),
        summary: artifact.summary
    })}\n`;
