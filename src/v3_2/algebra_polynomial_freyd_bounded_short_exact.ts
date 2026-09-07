/** Degreewise short-exact sequences over existing bounded Freyd chain maps. */

import { AlgebraElement, AlgebraParent, sameAlgebraParent } from './algebra_parent';
import { AlgebraPolynomialRing } from './algebra_polynomial';
import { AlgebraPresentedPolynomialModule } from './algebra_polynomial_presentation';
import {
    algebraPolynomialModuleMapEquals
} from './algebra_polynomial_presentation_morphism';
import {
    algebraPresentedPolynomialModuleEquals,
    algebraPolynomialFreydZeroPresentation,
    algebraPolynomialPresentationMorphismZero
} from './algebra_polynomial_freyd_category';
import {
    AlgebraPolynomialFreydBoundedChainMap,
    AlgebraPolynomialFreydBoundedComplex
} from './algebra_polynomial_freyd_bounded_complex';
import {
    AlgebraPolynomialFreydShortExactTriple,
    algebraPolynomialFreydShortExactTriple
} from './algebra_polynomial_freyd_short_exact';
import { AlgebraPolynomialWeakKernelFactorOptions } from './algebra_polynomial_weak_kernel';

export const ALGEBRA_POLYNOMIAL_FREYD_BOUNDED_SHORT_EXACT_PROFILE = Object.freeze({
    revision: 'emdash-algebra-polynomial-freyd-bounded-short-exact-v1' as const,
    grading: 'zero-based-consecutive-chain' as const,
    chainMaps: 'retained-existing-owners' as const,
    rowWitnesses: 'computed-short-exact-triples' as const,
    zeroExtension: 'one-retained-zero-row' as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydBoundedShortExactErrorCode =
    | 'INVALID_COMPLEX'
    | 'FOREIGN_SEQUENCE_RING'
    | 'RANGE_MISMATCH'
    | 'CHAIN_MAP_ENDPOINT_MISMATCH'
    | 'INVALID_CHAIN_MAP'
    | 'ROW_NOT_SHORT_EXACT'
    | 'DEGREE_OUT_OF_RANGE';

export class AlgebraPolynomialFreydBoundedShortExactError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydBoundedShortExactErrorCode,
        public readonly path: string,
        message: string,
        public readonly underlying?: Error
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydBoundedShortExactError';
    }
}

const fail = (
    code: AlgebraPolynomialFreydBoundedShortExactErrorCode,
    path: string,
    message: string,
    underlying?: unknown
): never => {
    throw new AlgebraPolynomialFreydBoundedShortExactError(
        code,
        path,
        message,
        underlying instanceof Error ? underlying : undefined
    );
};

export interface AlgebraPolynomialFreydShortExactDegree<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly degree: number;
    readonly location: 'support' | 'zero-extension';
    readonly triple: AlgebraPolynomialFreydShortExactTriple<P, C, I>;
}

export interface AlgebraPolynomialFreydBoundedShortExactSequence<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
> {
    readonly kind: 'algebra-polynomial-freyd-bounded-short-exact-sequence';
    readonly ring: AlgebraPolynomialRing<P, C, I>;
    readonly length: number;
    readonly subcomplex: AlgebraPolynomialFreydBoundedComplex<P, C, I>;
    readonly middleComplex: AlgebraPolynomialFreydBoundedComplex<P, C, I>;
    readonly quotientComplex: AlgebraPolynomialFreydBoundedComplex<P, C, I>;
    readonly inclusion: AlgebraPolynomialFreydBoundedChainMap<P, C, I>;
    readonly projection: AlgebraPolynomialFreydBoundedChainMap<P, C, I>;
    readonly rows: readonly AlgebraPolynomialFreydShortExactDegree<P, C, I>[];
    readonly zeroObject: AlgebraPresentedPolynomialModule<P, C, I>;
    readonly zeroRow: AlgebraPolynomialFreydShortExactTriple<P, C, I>;
    readonly isShortExact: true;
}

// Keep selected presentations and raw differentials fixed. Merely sharing the
// term objects, or having different but congruent differential representatives,
// is insufficient for reusing the supplied chain-map agreement objects.
const sameComplexPresentation = <
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(
    left: AlgebraPolynomialFreydBoundedComplex<P, C, I>,
    right: AlgebraPolynomialFreydBoundedComplex<P, C, I>
): boolean => sameAlgebraParent(left.ring, right.ring) &&
    left.length === right.length &&
    left.terms.length === right.terms.length &&
    left.differentials.length === right.differentials.length &&
    left.terms.every((term, index) =>
        term.degree === right.terms[index].degree &&
        algebraPresentedPolynomialModuleEquals(term.object, right.terms[index].object)
    ) &&
    left.differentials.every((entry, index) =>
        entry.degree === right.differentials[index].degree &&
        algebraPolynomialModuleMapEquals(entry.morphism.map, right.differentials[index].morphism.map)
    );

/** Compute all row witnesses while retaining the existing chain-map owners. */
export function algebraPolynomialFreydBoundedShortExactSequence<
    P extends AlgebraParent,
    C extends AlgebraElement<P>,
    I
>(input: {
    readonly subcomplex: AlgebraPolynomialFreydBoundedComplex<P, C, I>;
    readonly middleComplex: AlgebraPolynomialFreydBoundedComplex<P, C, I>;
    readonly quotientComplex: AlgebraPolynomialFreydBoundedComplex<P, C, I>;
    readonly inclusion: AlgebraPolynomialFreydBoundedChainMap<P, C, I>;
    readonly projection: AlgebraPolynomialFreydBoundedChainMap<P, C, I>;
}, options: AlgebraPolynomialWeakKernelFactorOptions = {}):
    AlgebraPolynomialFreydBoundedShortExactSequence<P, C, I> {
    const { subcomplex, middleComplex, quotientComplex, inclusion, projection } = input;
    const complexes = [subcomplex, middleComplex, quotientComplex];
    const paths = ['subcomplex', 'middleComplex', 'quotientComplex'];
    complexes.forEach((complex, index) => {
        if (!complex.isComplex || complex.conditions.some(condition => !condition.zero)) {
            fail('INVALID_COMPLEX', paths[index], 'Short exactness requires actual complexes');
        }
    });
    if (complexes.some(complex => !sameAlgebraParent(complex.ring, middleComplex.ring))) {
        return fail('FOREIGN_SEQUENCE_RING', 'shortExactSequence.complexes',
            'All three complexes must use the same polynomial ring');
    }
    if (complexes.some(complex => complex.length !== middleComplex.length)) {
        return fail('RANGE_MISMATCH', 'shortExactSequence.complexes',
            'All three complexes must have the same finite degree range');
    }
    const checkMap = (
        map: AlgebraPolynomialFreydBoundedChainMap<P, C, I>,
        source: AlgebraPolynomialFreydBoundedComplex<P, C, I>,
        target: AlgebraPolynomialFreydBoundedComplex<P, C, I>,
        path: string
    ): void => {
        if (!sameComplexPresentation(map.source, source) || !sameComplexPresentation(map.target, target)) {
            fail('CHAIN_MAP_ENDPOINT_MISMATCH', path,
                'Chain-map endpoints must be the declared complexes, including their differentials');
        }
        if (
            !map.isChainMap ||
            map.components.length !== source.length + 1 ||
            map.squares.length !== source.length ||
            map.components.some((component, degree) => component.degree !== degree) ||
            map.squares.some((square, index) =>
                square.degree !== index + 1 || !square.commutes || !square.agreement.agrees
            )
        ) {
            fail('INVALID_CHAIN_MAP', path,
                'Every existing chain-map square must commute');
        }
    };
    checkMap(inclusion, subcomplex, middleComplex, 'shortExactSequence.inclusion');
    checkMap(projection, middleComplex, quotientComplex, 'shortExactSequence.projection');
    const rows = Object.freeze(inclusion.components.map((component, degree) => {
        let triple: AlgebraPolynomialFreydShortExactTriple<P, C, I>;
        try {
            triple = algebraPolynomialFreydShortExactTriple(
                component.morphism,
                projection.components[degree].morphism,
                options
            );
        } catch (error: unknown) {
            return fail('ROW_NOT_SHORT_EXACT', `shortExactSequence.rows[${degree}]`,
                'The selected degree row is not short exact', error);
        }
        return Object.freeze({ degree, location: 'support' as const, triple });
    }));
    const zeroObject = algebraPolynomialFreydZeroPresentation(middleComplex.ring);
    const zero = algebraPolynomialPresentationMorphismZero(zeroObject, zeroObject);
    const zeroRow = algebraPolynomialFreydShortExactTriple(zero, zero, options);
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-bounded-short-exact-sequence',
        ring: middleComplex.ring,
        length: middleComplex.length,
        subcomplex,
        middleComplex,
        quotientComplex,
        inclusion,
        projection,
        rows,
        zeroObject,
        zeroRow,
        isShortExact: true
    });
}

/** Read an already-computed row inside the declared finite support. */
export function algebraPolynomialFreydBoundedShortExactAt<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(sequence: AlgebraPolynomialFreydBoundedShortExactSequence<P, C, I>, degree: number):
    AlgebraPolynomialFreydShortExactDegree<P, C, I> {
    if (!Number.isSafeInteger(degree) || degree < 0 || degree > sequence.length) {
        return fail('DEGREE_OUT_OF_RANGE', 'shortExactSequence.degree',
            'Requested degree lies outside the finite support');
    }
    return sequence.rows[degree];
}

/** Extend by the one retained zero row; this never reruns short-exact computation. */
export function algebraPolynomialFreydBoundedShortExactExtendedAt<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(sequence: AlgebraPolynomialFreydBoundedShortExactSequence<P, C, I>, degree: number):
    AlgebraPolynomialFreydShortExactDegree<P, C, I> {
    if (!Number.isSafeInteger(degree)) {
        return fail('DEGREE_OUT_OF_RANGE', 'shortExactSequence.degree',
            'An extended degree must be a safe integer');
    }
    return degree >= 0 && degree <= sequence.length
        ? sequence.rows[degree]
        : Object.freeze({ degree, location: 'zero-extension', triple: sequence.zeroRow });
}
