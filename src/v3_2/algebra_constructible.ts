/** Saturation-normalized locally closed and constructible affine subsets. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraGroebnerOptions,
    AlgebraPolynomialIdeal,
    algebraPolynomialIdeal
} from './algebra_ideal';
import {
    AlgebraIdealRadicalMembership,
    AlgebraIdealSaturation,
    algebraIdealRadicalMembership,
    algebraIdealSaturate,
    algebraIdealSum
} from './algebra_ideal_geometry';
import {
    AlgebraPolynomial,
    AlgebraPolynomialRing,
    algebraPolynomialMultiply,
    algebraPolynomialOne,
    validateAlgebraPolynomial
} from './algebra_polynomial';

export const ALGEBRA_CONSTRUCTIBLE_PROFILE = Object.freeze({
    revision: 'emdash-algebra-constructible-v1' as const,
    piece: 'saturation-normalized-V-I-intersect-D-f' as const,
    representation: 'finite-union-of-locally-closed-pieces' as const,
    equality: 'mutual-difference-emptiness' as const,
    nodeBuiltinDependency: false as const,
    performsIo: false as const
});

export type AlgebraConstructibleErrorCode =
    | 'FOREIGN_RING'
    | 'INVALID_PIECE'
    | 'CONSTRUCTIBLE_LIMIT_EXCEEDED';

export class AlgebraConstructibleError extends Error {
    constructor(
        public readonly code: AlgebraConstructibleErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraConstructibleError';
    }
}

const fail = (
    code: AlgebraConstructibleErrorCode,
    path: string,
    message: string
): never => {
    throw new AlgebraConstructibleError(code, path, message);
};

const sameRing = (
    left: { readonly identity: { readonly id: string; readonly revision: string } },
    right: { readonly identity: { readonly id: string; readonly revision: string } }
): boolean => left.identity.id === right.identity.id &&
    left.identity.revision === right.identity.revision;

export interface AlgebraLocallyClosedPiece<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-locally-closed-piece';
    readonly ring: AlgebraPolynomialRing<P, C, I>;
    readonly sourceIdeal: AlgebraPolynomialIdeal<P, C, I>;
    readonly open: AlgebraPolynomial<P, C, I>;
    readonly saturation: AlgebraIdealSaturation<P, C, I>;
    readonly closedIdeal: AlgebraPolynomialIdeal<P, C, I>;
    readonly emptiness: AlgebraIdealRadicalMembership<P, C, I>;
    readonly empty: boolean;
}

export function algebraLocallyClosedPiece<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ideal: AlgebraPolynomialIdeal<P, C, I>,
    openInput: AlgebraPolynomial<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraLocallyClosedPiece<P, C, I> {
    let open: AlgebraPolynomial<P, C, I>;
    try {
        open = validateAlgebraPolynomial(ideal.ring, openInput, 'locallyClosed.open');
    } catch {
        return fail(
            'FOREIGN_RING',
            'locallyClosed.open',
            'Locally closed data must inhabit one polynomial ring'
        );
    }
    const saturation = algebraIdealSaturate(ideal, open, options);
    const emptiness = algebraIdealRadicalMembership(
        saturation.ideal,
        open,
        options
    );
    return Object.freeze({
        kind: 'algebra-locally-closed-piece',
        ring: ideal.ring,
        sourceIdeal: ideal,
        open,
        saturation,
        closedIdeal: saturation.ideal,
        emptiness,
        empty: emptiness.member
    });
}

export interface AlgebraConstructibleSet<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-constructible-set';
    readonly ring: AlgebraPolynomialRing<P, C, I>;
    readonly pieces: readonly AlgebraLocallyClosedPiece<P, C, I>[];
    readonly empty: boolean;
}

export function algebraConstructibleSet<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    ring: AlgebraPolynomialRing<P, C, I>,
    pieceInput: readonly AlgebraLocallyClosedPiece<P, C, I>[]
): AlgebraConstructibleSet<P, C, I> {
    if (!Array.isArray(pieceInput)) {
        return fail('INVALID_PIECE', 'constructible.pieces', 'Pieces must be an array');
    }
    const pieces = pieceInput.filter((piece, index) => {
        if (piece.kind !== 'algebra-locally-closed-piece' ||
            !sameRing(piece.ring, ring)) {
            return fail(
                'FOREIGN_RING',
                `constructible.pieces[${index}]`,
                'Constructible pieces must inhabit one ring'
            );
        }
        return !piece.empty;
    });
    return Object.freeze({
        kind: 'algebra-constructible-set',
        ring,
        pieces: Object.freeze(pieces),
        empty: pieces.length === 0
    });
}

export const algebraConstructibleEmpty = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>): AlgebraConstructibleSet<P, C, I> =>
    algebraConstructibleSet(ring, []);

export const algebraConstructibleFull = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(ring: AlgebraPolynomialRing<P, C, I>, options: AlgebraGroebnerOptions = {}):
    AlgebraConstructibleSet<P, C, I> => algebraConstructibleSet(ring, [
        algebraLocallyClosedPiece(
            algebraPolynomialIdeal(ring, []),
            algebraPolynomialOne(ring),
            options
        )
    ]);

const assertSetPair = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    left: AlgebraConstructibleSet<P, C, I>,
    right: AlgebraConstructibleSet<P, C, I>
): AlgebraPolynomialRing<P, C, I> => {
    if (!sameRing(left.ring, right.ring)) {
        return fail('FOREIGN_RING', 'constructible.right', 'Set operation requires one ring');
    }
    return left.ring;
};

export function algebraConstructibleUnion<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraConstructibleSet<P, C, I>,
    right: AlgebraConstructibleSet<P, C, I>
): AlgebraConstructibleSet<P, C, I> {
    return algebraConstructibleSet(
        assertSetPair(left, right),
        [...left.pieces, ...right.pieces]
    );
}

export function algebraConstructibleIntersection<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraConstructibleSet<P, C, I>,
    right: AlgebraConstructibleSet<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraConstructibleSet<P, C, I> {
    const ring = assertSetPair(left, right);
    return algebraConstructibleSet(ring, left.pieces.flatMap(first =>
        right.pieces.map(second => algebraLocallyClosedPiece(
            algebraIdealSum(first.closedIdeal, second.closedIdeal),
            algebraPolynomialMultiply(first.open, second.open),
            options
        ))
    ));
}

const differencePiece = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    left: AlgebraLocallyClosedPiece<P, C, I>,
    right: AlgebraLocallyClosedPiece<P, C, I>,
    options: AlgebraGroebnerOptions
): readonly AlgebraLocallyClosedPiece<P, C, I>[] => [
    ...right.closedIdeal.generators.map(generator => algebraLocallyClosedPiece(
        left.closedIdeal,
        algebraPolynomialMultiply(left.open, generator),
        options
    )),
    algebraLocallyClosedPiece(
        algebraIdealSum(
            left.closedIdeal,
            algebraPolynomialIdeal(left.ring, [right.open])
        ),
        left.open,
        options
    )
];

export function algebraConstructibleDifference<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraConstructibleSet<P, C, I>,
    right: AlgebraConstructibleSet<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraConstructibleSet<P, C, I> {
    const ring = assertSetPair(left, right);
    let pieces = [...left.pieces];
    right.pieces.forEach(subtracted => {
        pieces = pieces.flatMap(piece => differencePiece(piece, subtracted, options));
    });
    return algebraConstructibleSet(ring, pieces);
}

export const algebraConstructibleComplement = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    value: AlgebraConstructibleSet<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraConstructibleSet<P, C, I> => algebraConstructibleDifference(
        algebraConstructibleFull(value.ring, options),
        value,
        options
    );

export interface AlgebraConstructibleEquivalence<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-constructible-equivalence';
    readonly left: AlgebraConstructibleSet<P, C, I>;
    readonly right: AlgebraConstructibleSet<P, C, I>;
    readonly leftMinusRight: AlgebraConstructibleSet<P, C, I>;
    readonly rightMinusLeft: AlgebraConstructibleSet<P, C, I>;
    readonly equivalent: boolean;
}

export function algebraConstructibleEquivalence<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraConstructibleSet<P, C, I>,
    right: AlgebraConstructibleSet<P, C, I>,
    options: AlgebraGroebnerOptions = {}
): AlgebraConstructibleEquivalence<P, C, I> {
    assertSetPair(left, right);
    const leftMinusRight = algebraConstructibleDifference(left, right, options);
    const rightMinusLeft = algebraConstructibleDifference(right, left, options);
    return Object.freeze({
        kind: 'algebra-constructible-equivalence',
        left,
        right,
        leftMinusRight,
        rightMinusLeft,
        equivalent: leftMinusRight.empty && rightMinusLeft.empty
    });
}
