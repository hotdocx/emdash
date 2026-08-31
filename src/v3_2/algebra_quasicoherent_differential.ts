/** Whole alternating differentials on heterogeneous affine Cech cochains. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import { algebraQuotientText } from './algebra_quotient';
import {
    AlgebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleElementAdd,
    algebraPresentedAlgebraModuleElementIsZero,
    algebraPresentedAlgebraModuleElementNegate,
    algebraPresentedAlgebraModuleElementZero
} from './algebra_presented_module';
import { algebraPresentedAlgebraModuleSemilinearMapApply } from
    './algebra_presented_module_map';
import {
    AlgebraAffineQuasiCoherentCechFace,
    AlgebraAffineQuasiCoherentCechSimplex
} from './algebra_quasicoherent_cech';
import {
    AlgebraAffineQuasiCoherentCochain,
    AlgebraAffineQuasiCoherentCochainDegree,
    algebraAffineQuasiCoherentCochain,
    algebraAffineQuasiCoherentCochainAdd,
    algebraAffineQuasiCoherentCochainComponentAtIndices,
    algebraAffineQuasiCoherentCochainDegree,
    algebraAffineQuasiCoherentCochainEquals,
    algebraAffineQuasiCoherentCochainNegate,
    algebraAffineQuasiCoherentCochainZero
} from './algebra_quasicoherent_cochain';

export const ALGEBRA_QUASICOHERENT_DIFFERENTIAL_PROFILE = Object.freeze({
    revision: 'emdash-quasicoherent-cech-differential-v1' as const,
    formula: 'alternating-sum-of-stored-semilinear-faces' as const,
    finalTruncationDifferential: false as const,
    wholeContributions: true as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraQuasiCoherentDifferentialErrorCode =
    | 'NO_SUCCESSOR_DEGREE'
    | 'MISSING_TARGET_FACES'
    | 'FACE_ORDER_MISMATCH'
    | 'MISSING_SOURCE_COMPONENT';

export class AlgebraQuasiCoherentDifferentialError extends Error {
    constructor(
        public readonly code: AlgebraQuasiCoherentDifferentialErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraQuasiCoherentDifferentialError';
    }
}

const fail = (
    code: AlgebraQuasiCoherentDifferentialErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraQuasiCoherentDifferentialError(code, path, message);
};

const key = (indices: readonly number[]): string => indices.join(',');

export interface AlgebraAffineQuasiCoherentDifferentialContribution<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly face: AlgebraAffineQuasiCoherentCechFace<P, C, I>;
    readonly sourcePosition: number;
    readonly sourceElement: AlgebraPresentedAlgebraModuleElement<P, C, I>;
    readonly image: AlgebraPresentedAlgebraModuleElement<P, C, I>;
    readonly sign: 1 | -1;
    readonly signedImage: AlgebraPresentedAlgebraModuleElement<P, C, I>;
}

export interface AlgebraAffineQuasiCoherentDifferentialTarget<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly targetPosition: number;
    readonly simplex: AlgebraAffineQuasiCoherentCechSimplex<P, C, I>;
    readonly contributions:
        readonly AlgebraAffineQuasiCoherentDifferentialContribution<P, C, I>[];
    readonly sum: AlgebraPresentedAlgebraModuleElement<P, C, I>;
}

export interface AlgebraAffineQuasiCoherentDifferential<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-affine-quasicoherent-differential';
    readonly sourceDegree: AlgebraAffineQuasiCoherentCochainDegree<P, C, I>;
    readonly targetDegree: AlgebraAffineQuasiCoherentCochainDegree<P, C, I>;
    readonly input: AlgebraAffineQuasiCoherentCochain<P, C, I>;
    readonly targets:
        readonly AlgebraAffineQuasiCoherentDifferentialTarget<P, C, I>[];
    readonly output: AlgebraAffineQuasiCoherentCochain<P, C, I>;
}

export function algebraAffineQuasiCoherentDifferential<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    input: AlgebraAffineQuasiCoherentCochain<P, C, I>
): AlgebraAffineQuasiCoherentDifferential<P, C, I> {
    const sourceDegree = input.parent;
    let targetDegree: AlgebraAffineQuasiCoherentCochainDegree<P, C, I>;
    try {
        targetDegree = algebraAffineQuasiCoherentCochainDegree(
            sourceDegree.diagram,
            sourceDegree.degree + 1
        );
    } catch {
        return fail(
            'NO_SUCCESSOR_DEGREE',
            'quasicoherentDifferential.targetDegree',
            `Retained Cech diagram ends at degree ${sourceDegree.degree}`
        );
    }
    const targets = Object.freeze(targetDegree.data.simplices.map(
        (simplex, targetPosition) => {
            const faces = sourceDegree.diagram.faces.filter(face =>
                face.codomain === simplex
            );
            if (faces.length !== simplex.simplex.indices.length) {
                return fail(
                    'MISSING_TARGET_FACES',
                    `quasicoherentDifferential.targets[${targetPosition}]`,
                    'Target simplex does not retain one face per removed position'
                );
            }
            if (faces.some((face, position) =>
                face.face.removedPosition !== position)) {
                return fail(
                    'FACE_ORDER_MISMATCH',
                    `quasicoherentDifferential.targets[${targetPosition}]`,
                    'Stored target faces are not in removed-position order'
                );
            }
            const contributions = Object.freeze(faces.map((face, faceIndex) => {
                const sourcePosition = sourceDegree.data.simplices.findIndex(
                    source => key(source.simplex.indices) ===
                        key(face.domain.simplex.indices)
                );
                if (sourcePosition < 0) {
                    return fail(
                        'MISSING_SOURCE_COMPONENT',
                        `quasicoherentDifferential.targets[${targetPosition}]` +
                            `.contributions[${faceIndex}]`,
                        'Face domain is absent from the source cochain degree'
                    );
                }
                const sourceElement =
                    algebraAffineQuasiCoherentCochainComponentAtIndices(
                        input,
                        face.domain.simplex.indices
                    );
                const image = algebraPresentedAlgebraModuleSemilinearMapApply(
                    face.map,
                    sourceElement
                );
                return Object.freeze({
                    face,
                    sourcePosition,
                    sourceElement,
                    image,
                    sign: face.face.sign,
                    signedImage: face.face.sign === 1
                        ? image
                        : algebraPresentedAlgebraModuleElementNegate(image)
                });
            }));
            const sum = contributions.reduce(
                (value, contribution) =>
                    algebraPresentedAlgebraModuleElementAdd(
                        value,
                        contribution.signedImage
                    ),
                algebraPresentedAlgebraModuleElementZero(simplex.value.module)
            );
            return Object.freeze({
                targetPosition,
                simplex,
                contributions,
                sum
            });
        }
    ));
    const output = algebraAffineQuasiCoherentCochain(
        targetDegree,
        targets.map(target => target.sum)
    );
    return Object.freeze({
        kind: 'algebra-affine-quasicoherent-differential',
        sourceDegree,
        targetDegree,
        input,
        targets,
        output
    });
}

export interface AlgebraAffineQuasiCoherentDifferentialAdditivity<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly left: AlgebraAffineQuasiCoherentDifferential<P, C, I>;
    readonly right: AlgebraAffineQuasiCoherentDifferential<P, C, I>;
    readonly sum: AlgebraAffineQuasiCoherentDifferential<P, C, I>;
    readonly outputSum: AlgebraAffineQuasiCoherentCochain<P, C, I>;
    readonly holds: true;
}

export function algebraAffineQuasiCoherentDifferentialAdditivity<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    leftInput: AlgebraAffineQuasiCoherentCochain<P, C, I>,
    rightInput: AlgebraAffineQuasiCoherentCochain<P, C, I>
): AlgebraAffineQuasiCoherentDifferentialAdditivity<P, C, I> {
    const left = algebraAffineQuasiCoherentDifferential(leftInput);
    const right = algebraAffineQuasiCoherentDifferential(rightInput);
    const sum = algebraAffineQuasiCoherentDifferential(
        algebraAffineQuasiCoherentCochainAdd(leftInput, rightInput)
    );
    const outputSum = algebraAffineQuasiCoherentCochainAdd(
        left.output,
        right.output
    );
    if (!algebraAffineQuasiCoherentCochainEquals(sum.output, outputSum)) {
        throw new Error('Computed Cech differential is not additive');
    }
    return Object.freeze({ left, right, sum, outputSum, holds: true });
}

export const serializeAlgebraAffineQuasiCoherentDifferential = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(differential: AlgebraAffineQuasiCoherentDifferential<P, C, I>): string =>
    `${JSON.stringify({
        revision: ALGEBRA_QUASICOHERENT_DIFFERENTIAL_PROFILE.revision,
        kind: differential.kind,
        sourceDegree: differential.sourceDegree.degree,
        targetDegree: differential.targetDegree.degree,
        targets: differential.targets.map(target => ({
            indices: target.simplex.simplex.indices,
            contributions: target.contributions.map(contribution => ({
                sourceIndices: contribution.face.domain.simplex.indices,
                removedPosition: contribution.face.face.removedPosition,
                sign: contribution.sign,
                image: contribution.image.representative.components.map(
                    algebraQuotientText
                ),
                signedImage: contribution.signedImage.representative.components.map(
                    algebraQuotientText
                )
            })),
            sum: target.sum.representative.components.map(algebraQuotientText)
        })),
        outputIsZero: differential.output.components.every(
            algebraPresentedAlgebraModuleElementIsZero
        )
    })}\n`;

export const algebraAffineQuasiCoherentDifferentialOfZeroIsZero = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(degree: AlgebraAffineQuasiCoherentCochainDegree<P, C, I>): boolean =>
    algebraAffineQuasiCoherentCochainEquals(
        algebraAffineQuasiCoherentDifferential(
            algebraAffineQuasiCoherentCochainZero(degree)
        ).output,
        algebraAffineQuasiCoherentCochainZero(
            algebraAffineQuasiCoherentCochainDegree(
                degree.diagram,
                degree.degree + 1
            )
        )
    );

export const algebraAffineQuasiCoherentDifferentialOfNegate = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(cochain: AlgebraAffineQuasiCoherentCochain<P, C, I>): boolean =>
    algebraAffineQuasiCoherentCochainEquals(
        algebraAffineQuasiCoherentDifferential(
            algebraAffineQuasiCoherentCochainNegate(cochain)
        ).output,
        algebraAffineQuasiCoherentCochainNegate(
            algebraAffineQuasiCoherentDifferential(cochain).output
        )
    );
