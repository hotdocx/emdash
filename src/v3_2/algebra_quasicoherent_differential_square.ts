/** Structural and evaluated d-squared cancellation for affine Cech cochains. */

import {
    AlgebraElement,
    AlgebraParent
} from './algebra_parent';
import { algebraQuotientText } from './algebra_quotient';
import {
    AlgebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleElementAdd,
    algebraPresentedAlgebraModuleElementEquals,
    algebraPresentedAlgebraModuleElementIsZero,
    algebraPresentedAlgebraModuleElementNegate
} from './algebra_presented_module';
import { algebraPresentedAlgebraModuleSemilinearMapApply } from
    './algebra_presented_module_map';
import {
    AlgebraAffineQuasiCoherentCechFace,
    AlgebraAffineQuasiCoherentCechFaceComparison
} from './algebra_quasicoherent_cech';
import {
    AlgebraAffineQuasiCoherentCochain,
    algebraAffineQuasiCoherentCochainComponentAtIndices,
    algebraAffineQuasiCoherentCochainIsZero
} from './algebra_quasicoherent_cochain';
import {
    AlgebraAffineQuasiCoherentDifferential,
    algebraAffineQuasiCoherentDifferential
} from './algebra_quasicoherent_differential';

export const ALGEBRA_QUASICOHERENT_DIFFERENTIAL_SQUARE_PROFILE = Object.freeze({
    revision: 'emdash-quasicoherent-cech-differential-square-v1' as const,
    structuralOwner: 'stored-repeated-face-comparison-and-opposite-signs' as const,
    evaluatedOwner: 'two-whole-differentials-and-canonical-zero' as const,
    proofClaim: false as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraQuasiCoherentDifferentialSquareErrorCode =
    | 'NO_SECOND_SUCCESSOR_DEGREE'
    | 'MISSING_FACE_MAP'
    | 'SIGN_CANCELLATION_FAILED'
    | 'COMPOSITE_IMAGE_MISMATCH'
    | 'PAIR_CANCELLATION_FAILED'
    | 'CANCELLATION_COUNT_MISMATCH'
    | 'DIFFERENTIAL_SQUARE_NONZERO';

export class AlgebraQuasiCoherentDifferentialSquareError extends Error {
    constructor(
        public readonly code: AlgebraQuasiCoherentDifferentialSquareErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraQuasiCoherentDifferentialSquareError';
    }
}

const fail = (
    code: AlgebraQuasiCoherentDifferentialSquareErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraQuasiCoherentDifferentialSquareError(code, path, message);
};

const key = (indices: readonly number[]): string => indices.join(',');

export interface AlgebraAffineQuasiCoherentCancellationPair<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly comparison: AlgebraAffineQuasiCoherentCechFaceComparison<P, C, I>;
    readonly firstInner: AlgebraAffineQuasiCoherentCechFace<P, C, I>;
    readonly firstOuter: AlgebraAffineQuasiCoherentCechFace<P, C, I>;
    readonly secondInner: AlgebraAffineQuasiCoherentCechFace<P, C, I>;
    readonly secondOuter: AlgebraAffineQuasiCoherentCechFace<P, C, I>;
    readonly sourceElement: AlgebraPresentedAlgebraModuleElement<P, C, I>;
    readonly firstImage: AlgebraPresentedAlgebraModuleElement<P, C, I>;
    readonly secondImage: AlgebraPresentedAlgebraModuleElement<P, C, I>;
    readonly firstSign: 1 | -1;
    readonly secondSign: 1 | -1;
    readonly firstSignedImage: AlgebraPresentedAlgebraModuleElement<P, C, I>;
    readonly secondSignedImage: AlgebraPresentedAlgebraModuleElement<P, C, I>;
    readonly sum: AlgebraPresentedAlgebraModuleElement<P, C, I>;
    readonly unsignedImagesEqual: true;
    readonly signsOpposite: true;
    readonly cancels: true;
}

export interface AlgebraAffineQuasiCoherentDifferentialSquare<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-affine-quasicoherent-differential-square';
    readonly input: AlgebraAffineQuasiCoherentCochain<P, C, I>;
    readonly first: AlgebraAffineQuasiCoherentDifferential<P, C, I>;
    readonly second: AlgebraAffineQuasiCoherentDifferential<P, C, I>;
    readonly cancellations:
        readonly AlgebraAffineQuasiCoherentCancellationPair<P, C, I>[];
    readonly outputIsZero: true;
    readonly holds: true;
}

const signed = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    sign: 1 | -1,
    element: AlgebraPresentedAlgebraModuleElement<P, C, I>
): AlgebraPresentedAlgebraModuleElement<P, C, I> => sign === 1
    ? element
    : algebraPresentedAlgebraModuleElementNegate(element);

export function algebraAffineQuasiCoherentDifferentialSquare<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    input: AlgebraAffineQuasiCoherentCochain<P, C, I>
): AlgebraAffineQuasiCoherentDifferentialSquare<P, C, I> {
    const first = algebraAffineQuasiCoherentDifferential(input);
    let second: AlgebraAffineQuasiCoherentDifferential<P, C, I>;
    try {
        second = algebraAffineQuasiCoherentDifferential(first.output);
    } catch {
        return fail(
            'NO_SECOND_SUCCESSOR_DEGREE',
            'quasicoherentDifferentialSquare.second',
            `Retained Cech diagram has no degree ${input.parent.degree + 2}`
        );
    }
    const diagram = input.parent.diagram;
    const faceByEndpoints = new Map(diagram.faces.map(face => [
        `${key(face.domain.simplex.indices)}->${key(face.codomain.simplex.indices)}`,
        face
    ]));
    const comparisons = diagram.comparisons.filter(comparison =>
        comparison.lower.simplex.degree === input.parent.degree
    );
    const faceMap = (
        domain: readonly number[],
        codomain: readonly number[],
        path: string
    ): AlgebraAffineQuasiCoherentCechFace<P, C, I> => {
        const result = faceByEndpoints.get(`${key(domain)}->${key(codomain)}`);
        if (result === undefined) {
            return fail(
                'MISSING_FACE_MAP',
                path,
                'Differential-square path has a missing stored face map'
            );
        }
        return result;
    };
    const cancellations = Object.freeze(comparisons.map((comparison, index) => {
        const path = `quasicoherentDifferentialSquare.cancellations[${index}]`;
        const lower = comparison.lower.simplex.indices;
        const firstIntermediate = comparison.firstIntermediate.simplex.indices;
        const secondIntermediate = comparison.secondIntermediate.simplex.indices;
        const top = comparison.simplex.simplex.indices;
        const firstInner = faceMap(lower, firstIntermediate, path);
        const firstOuter = faceMap(firstIntermediate, top, path);
        const secondInner = faceMap(lower, secondIntermediate, path);
        const secondOuter = faceMap(secondIntermediate, top, path);
        const firstSign = (firstInner.face.sign * firstOuter.face.sign) as 1 | -1;
        const secondSign = (secondInner.face.sign * secondOuter.face.sign) as 1 | -1;
        if (firstSign !== -secondSign) {
            return fail(
                'SIGN_CANCELLATION_FAILED',
                path,
                'Repeated-face paths do not have opposite total signs'
            );
        }
        const sourceElement =
            algebraAffineQuasiCoherentCochainComponentAtIndices(input, lower);
        const firstImage = algebraPresentedAlgebraModuleSemilinearMapApply(
            comparison.firstComposite,
            sourceElement
        );
        const secondImage = algebraPresentedAlgebraModuleSemilinearMapApply(
            comparison.secondComposite,
            sourceElement
        );
        if (!algebraPresentedAlgebraModuleElementEquals(
            firstImage,
            secondImage
        )) {
            return fail(
                'COMPOSITE_IMAGE_MISMATCH',
                path,
                'Equal repeated-face maps produced different canonical images'
            );
        }
        const firstSignedImage = signed(firstSign, firstImage);
        const secondSignedImage = signed(secondSign, secondImage);
        const sum = algebraPresentedAlgebraModuleElementAdd(
            firstSignedImage,
            secondSignedImage
        );
        if (!algebraPresentedAlgebraModuleElementIsZero(sum)) {
            return fail(
                'PAIR_CANCELLATION_FAILED',
                path,
                'Repeated-face signed images did not cancel'
            );
        }
        return Object.freeze({
            comparison,
            firstInner,
            firstOuter,
            secondInner,
            secondOuter,
            sourceElement,
            firstImage,
            secondImage,
            firstSign,
            secondSign,
            firstSignedImage,
            secondSignedImage,
            sum,
            unsignedImagesEqual: true as const,
            signsOpposite: true as const,
            cancels: true as const
        });
    }));
    const expectedCancellations = second.targetDegree.data.simplices.reduce(
        (count, simplex) => count +
            simplex.simplex.indices.length *
                (simplex.simplex.indices.length - 1) / 2,
        0
    );
    if (cancellations.length !== expectedCancellations) {
        return fail(
            'CANCELLATION_COUNT_MISMATCH',
            'quasicoherentDifferentialSquare.cancellations',
            `Expected ${expectedCancellations} cancellation pairs, received ` +
                cancellations.length
        );
    }
    if (!algebraAffineQuasiCoherentCochainIsZero(second.output)) {
        return fail(
            'DIFFERENTIAL_SQUARE_NONZERO',
            'quasicoherentDifferentialSquare.output',
            'The evaluated second differential is not canonical zero'
        );
    }
    return Object.freeze({
        kind: 'algebra-affine-quasicoherent-differential-square',
        input,
        first,
        second,
        cancellations,
        outputIsZero: true,
        holds: true
    });
}

export const serializeAlgebraAffineQuasiCoherentDifferentialSquare = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(square: AlgebraAffineQuasiCoherentDifferentialSquare<P, C, I>): string =>
    `${JSON.stringify({
        revision: ALGEBRA_QUASICOHERENT_DIFFERENTIAL_SQUARE_PROFILE.revision,
        kind: square.kind,
        sourceDegree: square.input.parent.degree,
        middleDegree: square.first.targetDegree.degree,
        targetDegree: square.second.targetDegree.degree,
        cancellations: square.cancellations.map(cancellation => ({
            top: cancellation.comparison.simplex.simplex.indices,
            lower: cancellation.comparison.lower.simplex.indices,
            removedPositions: cancellation.comparison.removedPositions,
            firstIntermediate:
                cancellation.comparison.firstIntermediate.simplex.indices,
            secondIntermediate:
                cancellation.comparison.secondIntermediate.simplex.indices,
            firstPathPositions: [
                cancellation.firstInner.face.removedPosition,
                cancellation.firstOuter.face.removedPosition
            ],
            secondPathPositions: [
                cancellation.secondInner.face.removedPosition,
                cancellation.secondOuter.face.removedPosition
            ],
            firstSign: cancellation.firstSign,
            secondSign: cancellation.secondSign,
            firstImage: cancellation.firstImage.representative.components.map(
                algebraQuotientText
            ),
            secondImage: cancellation.secondImage.representative.components.map(
                algebraQuotientText
            ),
            cancels: cancellation.cancels
        })),
        outputIsZero: square.outputIsZero,
        holds: square.holds
    })}\n`;
