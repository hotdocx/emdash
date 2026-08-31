/** Ordered varying-ring Cech data for affine quasi-coherent presentations. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import {
    AlgebraRuntimeSchema,
    defineAlgebraRuntimeSchema
} from './algebra_engine';
import {
    AlgebraAffineCover,
    AlgebraCechFace,
    AlgebraCechSimplex
} from './algebra_cech';
import {
    algebraAffineSchemeEquals
} from './algebra_affine_scheme';
import {
    AlgebraPresentedAlgebraModuleOptions,
    algebraPresentedAlgebraModuleBasisVector,
    algebraPresentedAlgebraModuleElement
} from './algebra_presented_module';
import {
    AlgebraPresentedAlgebraModuleSemilinearMap,
    algebraPresentedAlgebraModuleSemilinearMap,
    algebraPresentedAlgebraModuleSemilinearMapCompose,
    algebraPresentedAlgebraModuleSemilinearMapEquals
} from './algebra_presented_module_map';
import {
    AlgebraAffineQuasiCoherentChart,
    AlgebraAffineQuasiCoherentPresentation,
    algebraAffineQuasiCoherentOnBasicOpen
} from './algebra_quasicoherent';
import { algebraQuotientText } from './algebra_quotient';

export const ALGEBRA_QUASICOHERENT_CECH_PROFILE = Object.freeze({
    revision: 'emdash-quasicoherent-cech-v1' as const,
    simplexValue: 'direct-product-localization-base-change' as const,
    faceMap: 'relation-checked-semilinear-restriction' as const,
    coherence: 'computed-repeated-face-comparison' as const,
    claimsChainComplex: false as const,
    claimsCohomology: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraQuasiCoherentCechErrorCode =
    | 'FOREIGN_AFFINE_COVER'
    | 'MISSING_FACE_TARGET'
    | 'MISSING_FACE_MAP'
    | 'FACE_COMPOSITION_FAILED';

export class AlgebraQuasiCoherentCechError extends Error {
    constructor(
        public readonly code: AlgebraQuasiCoherentCechErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraQuasiCoherentCechError';
    }
}

const fail = (
    code: AlgebraQuasiCoherentCechErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraQuasiCoherentCechError(code, path, message);
};

const record = (value: unknown): value is Record<string, unknown> =>
    typeof value === 'object' && value !== null && !Array.isArray(value);

const key = (indices: readonly number[]): string => indices.join(',');

export interface AlgebraAffineQuasiCoherentCechSimplex<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly simplex: AlgebraCechSimplex<P, C, I>;
    readonly value: AlgebraAffineQuasiCoherentChart<P, C, I>;
}

export interface AlgebraAffineQuasiCoherentCechFace<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly face: AlgebraCechFace<P, C, I>;
    /** Lower-dimensional coordinate-module source. */
    readonly domain: AlgebraAffineQuasiCoherentCechSimplex<P, C, I>;
    /** Containing product-localization coordinate-module target. */
    readonly codomain: AlgebraAffineQuasiCoherentCechSimplex<P, C, I>;
    readonly map: AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
}

export interface AlgebraAffineQuasiCoherentCechFaceComparison<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly simplex: AlgebraAffineQuasiCoherentCechSimplex<P, C, I>;
    readonly removedPositions: readonly [number, number];
    readonly lower: AlgebraAffineQuasiCoherentCechSimplex<P, C, I>;
    readonly firstIntermediate: AlgebraAffineQuasiCoherentCechSimplex<P, C, I>;
    readonly secondIntermediate: AlgebraAffineQuasiCoherentCechSimplex<P, C, I>;
    readonly firstComposite:
        AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
    readonly secondComposite:
        AlgebraPresentedAlgebraModuleSemilinearMap<P, C, I>;
    readonly holds: true;
}

export interface AlgebraAffineQuasiCoherentCechDegree<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly simplices:
        readonly AlgebraAffineQuasiCoherentCechSimplex<P, C, I>[];
    readonly incomingFaces:
        readonly AlgebraAffineQuasiCoherentCechFace<P, C, I>[];
}

export interface AlgebraAffineQuasiCoherentCechDiagram<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-affine-quasicoherent-cech-diagram';
    readonly presentation: AlgebraAffineQuasiCoherentPresentation<P, C, I>;
    readonly cover: AlgebraAffineCover<P, C, I>;
    readonly simplices:
        readonly AlgebraAffineQuasiCoherentCechSimplex<P, C, I>[];
    readonly faces: readonly AlgebraAffineQuasiCoherentCechFace<P, C, I>[];
    readonly comparisons:
        readonly AlgebraAffineQuasiCoherentCechFaceComparison<P, C, I>[];
    readonly degrees:
        readonly AlgebraAffineQuasiCoherentCechDegree<P, C, I>[];
}

const withoutPositions = (
    indices: readonly number[],
    positions: ReadonlySet<number>
): readonly number[] => Object.freeze(indices.filter(
    (_, position) => !positions.has(position)
));

export function algebraAffineQuasiCoherentCechDiagram<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    presentation: AlgebraAffineQuasiCoherentPresentation<P, C, I>,
    cover: AlgebraAffineCover<P, C, I>,
    moduleOptions: AlgebraPresentedAlgebraModuleOptions = {}
): AlgebraAffineQuasiCoherentCechDiagram<P, C, I> {
    if (!algebraAffineSchemeEquals(presentation.scheme, cover.ambient)) {
        return fail(
            'FOREIGN_AFFINE_COVER',
            'quasicoherentCech.cover',
            'Affine cover belongs to a foreign quasi-coherent presentation'
        );
    }
    const simplices = Object.freeze(cover.simplices.map(simplex =>
        Object.freeze({
            simplex,
            value: algebraAffineQuasiCoherentOnBasicOpen(
                presentation,
                simplex.chart,
                moduleOptions
            )
        })
    ));
    const byIndices = new Map(simplices.map(simplex => [
        key(simplex.simplex.indices),
        simplex
    ]));
    const faces: AlgebraAffineQuasiCoherentCechFace<P, C, I>[] = [];
    simplices.forEach((codomain, simplexIndex) => {
        codomain.simplex.faces.forEach((face, faceIndex) => {
            const domain = byIndices.get(key(face.targetIndices));
            if (domain === undefined) {
                return fail(
                    'MISSING_FACE_TARGET',
                    `quasicoherentCech.simplices[${simplexIndex}].faces[${faceIndex}]`,
                    'No lower-dimensional module value exists for this face'
                );
            }
            const map = algebraPresentedAlgebraModuleSemilinearMap(
                domain.value.module,
                codomain.value.module,
                face.restrictionMap,
                Array.from(
                    { length: domain.value.module.freeModule.rank },
                    (_, position) => algebraPresentedAlgebraModuleElement(
                        codomain.value.module,
                        algebraPresentedAlgebraModuleBasisVector(
                            codomain.value.module.freeModule,
                            position
                        )
                    )
                )
            );
            faces.push(Object.freeze({ face, domain, codomain, map }));
        });
    });
    const faceByEndpoints = new Map(faces.map(face => [
        `${key(face.domain.simplex.indices)}->${key(face.codomain.simplex.indices)}`,
        face
    ]));
    const comparisons: AlgebraAffineQuasiCoherentCechFaceComparison<P, C, I>[] =
        [];
    simplices.filter(simplex => simplex.simplex.indices.length >= 3)
        .forEach((simplex, simplexIndex) => {
            const indices = simplex.simplex.indices;
            for (let first = 0; first < indices.length; first++) {
                for (let second = first + 1; second < indices.length; second++) {
                    const lowerIndices = withoutPositions(
                        indices,
                        new Set([first, second])
                    );
                    const firstIndices = withoutPositions(indices, new Set([first]));
                    const secondIndices = withoutPositions(indices, new Set([second]));
                    const lower = byIndices.get(key(lowerIndices));
                    const firstIntermediate = byIndices.get(key(firstIndices));
                    const secondIntermediate = byIndices.get(key(secondIndices));
                    if (
                        lower === undefined ||
                        firstIntermediate === undefined ||
                        secondIntermediate === undefined
                    ) {
                        return fail(
                            'MISSING_FACE_TARGET',
                            `quasicoherentCech.comparisons[${simplexIndex}]`,
                            'Repeated face has a missing intermediate module value'
                        );
                    }
                    const faceMap = (
                        domain: AlgebraAffineQuasiCoherentCechSimplex<P, C, I>,
                        codomain: AlgebraAffineQuasiCoherentCechSimplex<P, C, I>
                    ): AlgebraAffineQuasiCoherentCechFace<P, C, I> => {
                        const result = faceByEndpoints.get(
                            `${key(domain.simplex.indices)}->` +
                                key(codomain.simplex.indices)
                        );
                        if (result === undefined) {
                            return fail(
                                'MISSING_FACE_MAP',
                                `quasicoherentCech.comparisons[${simplexIndex}]`,
                                'Repeated face has a missing semilinear map'
                            );
                        }
                        return result;
                    };
                    const firstComposite =
                        algebraPresentedAlgebraModuleSemilinearMapCompose(
                            faceMap(firstIntermediate, simplex).map,
                            faceMap(lower, firstIntermediate).map
                        );
                    const secondComposite =
                        algebraPresentedAlgebraModuleSemilinearMapCompose(
                            faceMap(secondIntermediate, simplex).map,
                            faceMap(lower, secondIntermediate).map
                        );
                    if (!algebraPresentedAlgebraModuleSemilinearMapEquals(
                        firstComposite,
                        secondComposite
                    )) {
                        return fail(
                            'FACE_COMPOSITION_FAILED',
                            `quasicoherentCech.comparisons[${simplexIndex}]`,
                            'Two repeated face restrictions do not agree'
                        );
                    }
                    comparisons.push(Object.freeze({
                        simplex,
                        removedPositions: Object.freeze([first, second]) as
                            readonly [number, number],
                        lower,
                        firstIntermediate,
                        secondIntermediate,
                        firstComposite,
                        secondComposite,
                        holds: true
                    }));
                }
            }
        });
    const degrees = Object.freeze(cover.cochainDegrees.map(degree =>
        Object.freeze({
            degree: degree.degree,
            simplices: Object.freeze(simplices.filter(simplex =>
                simplex.simplex.degree === degree.degree
            )),
            incomingFaces: Object.freeze(faces.filter(face =>
                face.domain.simplex.degree === degree.degree
            ))
        })
    ));
    return Object.freeze({
        kind: 'algebra-affine-quasicoherent-cech-diagram',
        presentation,
        cover,
        simplices,
        faces: Object.freeze(faces),
        comparisons: Object.freeze(comparisons),
        degrees
    });
}

export function algebraAffineQuasiCoherentCechDiagramSchema<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    presentation: AlgebraAffineQuasiCoherentPresentation<P, C, I>,
    cover: AlgebraAffineCover<P, C, I>
): AlgebraRuntimeSchema<AlgebraAffineQuasiCoherentCechDiagram<P, C, I>> {
    return defineAlgebraRuntimeSchema({
        id: `algebra.affine-quasicoherent-cech/` +
            `${presentation.module.identity.id}/${cover.elements.length}/` +
            cover.maximumDegree,
        revision: ALGEBRA_QUASICOHERENT_CECH_PROFILE.revision,
        normalize(value: unknown, path: string) {
            if (
                !record(value) ||
                value.kind !== 'algebra-affine-quasicoherent-cech-diagram' ||
                !Array.isArray(value.simplices) ||
                !Array.isArray(value.faces)
            ) throw new Error(`quasi-coherent Cech diagram expected at ${path}`);
            return algebraAffineQuasiCoherentCechDiagram(presentation, cover);
        }
    });
}

export const serializeAlgebraAffineQuasiCoherentCechDiagram = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(diagram: AlgebraAffineQuasiCoherentCechDiagram<P, C, I>): string =>
    `${JSON.stringify({
        revision: ALGEBRA_QUASICOHERENT_CECH_PROFILE.revision,
        kind: diagram.kind,
        presentationModule: diagram.presentation.module.identity,
        simplices: diagram.simplices.map(simplex => ({
            degree: simplex.simplex.degree,
            indices: simplex.simplex.indices,
            product: algebraQuotientText(simplex.simplex.product),
            module: simplex.value.module.identity
        })),
        faces: diagram.faces.map(face => ({
            domain: face.domain.simplex.indices,
            codomain: face.codomain.simplex.indices,
            removedPosition: face.face.removedPosition,
            sign: face.face.sign,
            scalarMapImages: face.map.scalarMap.generatorImages.map(
                algebraQuotientText
            ),
            moduleGeneratorImages: face.map.generatorImages.map(image =>
                image.representative.components.map(algebraQuotientText)
            )
        })),
        comparisons: diagram.comparisons.map(comparison => ({
            simplex: comparison.simplex.simplex.indices,
            removedPositions: comparison.removedPositions,
            lower: comparison.lower.simplex.indices,
            holds: comparison.holds
        })),
        degrees: diagram.degrees.map(degree => ({
            degree: degree.degree,
            simplexCount: degree.simplices.length,
            incomingFaceCount: degree.incomingFaces.length
        }))
    })}\n`;
