/** Whole bounded long exact homology, with shared degree/map/window owners. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraPolynomialFreydBoundedShortExactSequence } from './algebra_polynomial_freyd_bounded_short_exact';
import {
    AlgebraPolynomialFreydHomologyContextErrorCode,
    AlgebraPolynomialFreydHomologyDegree,
    algebraPolynomialFreydHomologyContext
} from './algebra_polynomial_freyd_homology_context';
import { algebraPolynomialFreydHomologyWindow } from './algebra_polynomial_freyd_homology_window';
import { algebraPresentedPolynomialModuleEquals } from './algebra_polynomial_freyd_category';

export const ALGEBRA_POLYNOMIAL_FREYD_LONG_EXACT_PROFILE = Object.freeze({
    revision: 'emdash-polynomial-freyd-long-exact-v1' as const,
    order: 'descending-degree-A-B-C' as const,
    sharing: 'retained-degree-homology-maps-and-windows' as const,
    endpointZeros: 'actual-outside-support-homology' as const,
    assumesSplitEpimorphisms: false as const,
    claimsGenericFormalExactness: false as const,
    performsIo: false as const
});

export type AlgebraPolynomialFreydHomologyRole = 'A' | 'B' | 'C';
export type AlgebraPolynomialFreydLongExactErrorCode =
    | AlgebraPolynomialFreydHomologyContextErrorCode
    | 'POSITION_OUT_OF_RANGE'
    | 'INVALID_ROLE'
    | 'OWNER_MISMATCH'
    | 'EXACTNESS_MISMATCH';

export class AlgebraPolynomialFreydLongExactError extends Error {
    constructor(
        public readonly code: AlgebraPolynomialFreydLongExactErrorCode,
        public readonly path: string,
        message: string
    ) {
        super(`${message} (${path})`);
        this.name = 'AlgebraPolynomialFreydLongExactError';
    }
}

const fail = (code: AlgebraPolynomialFreydLongExactErrorCode, path: string, message: string): never => {
    throw new AlgebraPolynomialFreydLongExactError(code, path, message);
};

export interface AlgebraPolynomialFreydLongExactTerm<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> {
    readonly position: number;
    readonly degree: number;
    readonly role: AlgebraPolynomialFreydHomologyRole;
    readonly location: 'support' | 'endpoint-zero';
    readonly view: AlgebraPolynomialFreydHomologyDegree<P, C, I>;
}

/**
 * 0 → H_L(A) → H_L(B) → H_L(C) → ... → H_0(A) → H_0(B) → H_0(C) → 0.
 * The two displayed zeros are selected H_(L+1)(C) and H_(-1)(A), with
 * retained identity-equals-zero agreements. No map or exactness is supplied.
 */
export function algebraPolynomialFreydBoundedLongExactHomology<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(sequence: AlgebraPolynomialFreydBoundedShortExactSequence<P, C, I>) {
    const topDegree = sequence.length;
    if (!Number.isSafeInteger(topDegree) || topDegree < 0 ||
        !Number.isSafeInteger(3 * (topDegree + 1) + 2) ||
        sequence.rows.length !== topDegree + 1 ||
        [sequence.subcomplex, sequence.middleComplex, sequence.quotientComplex].some(c => c.length !== topDegree)) {
        return fail('INVALID_SEQUENCE', 'longExact.sequence', 'The sequence must have one finite common degree range');
    }
    const context = algebraPolynomialFreydHomologyContext(sequence, 0, 'longExact', fail);
    // Indexed from degree -1 through L+1. These are the sole homology/map
    // constructions; every window below consumes these retained objects.
    const degrees = Object.freeze(Array.from({ length: topDegree + 3 }, (_, index) => {
        const degree = index - 1;
        const A = context.homologyAt(sequence.subcomplex, degree);
        const B = context.homologyAt(sequence.middleComplex, degree);
        const C = context.homologyAt(sequence.quotientComplex, degree);
        const inclusion = context.induced(sequence.inclusion, degree, A.homology, B.homology);
        const projection = context.induced(sequence.projection, degree, B.homology, C.homology);
        return Object.freeze({ degree, A, B, C, inclusion, projection });
    }));
    const windows = Object.freeze(Array.from({ length: topDegree + 2 }, (_, degree) => {
        const upper = degrees[degree + 1];
        const lower = degrees[degree];
        return algebraPolynomialFreydHomologyWindow(sequence, degree, {
            upperA: upper.A, upperB: upper.B, upperC: upper.C,
            lowerA: lower.A, lowerB: lower.B,
            inclusionUpper: upper.inclusion,
            projectionUpper: upper.projection,
            inclusionLower: lower.inclusion
        });
    }));
    const terms: AlgebraPolynomialFreydLongExactTerm<P, C, I>[] = [];
    const appendTerm = (degree: number, role: AlgebraPolynomialFreydHomologyRole, endpoint = false) => {
        terms.push(Object.freeze({
            position: terms.length, degree, role,
            location: endpoint ? 'endpoint-zero' as const : 'support' as const,
            view: degrees[degree + 1][role]
        }));
    };
    appendTerm(topDegree + 1, 'C', true);
    for (let degree = topDegree; degree >= 0; degree--) {
        appendTerm(degree, 'A');
        appendTerm(degree, 'B');
        appendTerm(degree, 'C');
    }
    appendTerm(-1, 'A', true);

    const arrows = [windows[topDegree + 1].connecting.homologyMap];
    for (let degree = topDegree; degree >= 0; degree--) {
        arrows.push(degrees[degree + 1].inclusion.homologyMap,
            degrees[degree + 1].projection.homologyMap, windows[degree].connecting.homologyMap);
    }
    arrows.forEach((arrow, index) => {
        if (!algebraPresentedPolynomialModuleEquals(arrow.source, terms[index].view.homology.homologyObject) ||
            !algebraPresentedPolynomialModuleEquals(arrow.target, terms[index + 1].view.homology.homologyObject)) {
            fail('OWNER_MISMATCH', `longExact.arrows[${index}]`, 'A displayed arrow must use the retained homology endpoints');
        }
    });
    const interior = Object.freeze(terms.slice(1, -1).map(term => {
        const windowDegree = term.role === 'A' ? term.degree + 1 : term.degree;
        const slot = term.role === 'A' ? 2 as const : term.role === 'B' ? 0 as const : 1 as const;
        const window = windows[windowDegree];
        const pair = window.pairs[slot];
        const exactness = window.exactness[slot];
        if (pair.dNext !== arrows[term.position - 1] || pair.d !== arrows[term.position] ||
            exactness.homology.pair !== pair || !pair.chainAgreement.agrees ||
            !exactness.exact || !exactness.epimorphism) {
            fail('EXACTNESS_MISMATCH', `longExact.interior[${term.position}]`,
                'Exactness must belong to the actual displayed pair, with its epimorphism witness');
        }
        return Object.freeze({ term, windowDegree, slot, window, pair, exactness });
    }));
    const initialZero = terms[0].view.zeroIdentity;
    const finalZero = terms[terms.length - 1].view.zeroIdentity;
    if (!initialZero?.agrees || !finalZero?.agrees) {
        return fail('ENDPOINT_NOT_ZERO', 'longExact.endpoints', 'Both displayed endpoints must be witnessed zero objects');
    }
    return Object.freeze({
        kind: 'algebra-polynomial-freyd-bounded-long-exact-homology' as const,
        sequence, topDegree, degrees, windows,
        terms: Object.freeze(terms), arrows: Object.freeze(arrows), interior,
        endpoints: Object.freeze({ initialZero, finalZero }),
        isExact: true as const, assumesSplitEpimorphisms: false as const
    });
}

export type AlgebraPolynomialFreydBoundedLongExactHomology<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = ReturnType<typeof algebraPolynomialFreydBoundedLongExactHomology<P, C, I>>;

/** Convert the mathematical degree/role label to the retained flat position. */
export function algebraPolynomialFreydLongExactPosition<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydBoundedLongExactHomology<P, C, I>, degree: number, role: AlgebraPolynomialFreydHomologyRole): number {
    if (role !== 'A' && role !== 'B' && role !== 'C') {
        return fail('INVALID_ROLE', 'longExact.position.role', 'Homology role must be A, B, or C');
    }
    if (!Number.isSafeInteger(degree)) {
        return fail('DEGREE_OUT_OF_RANGE', 'longExact.position.degree', 'Degree must be an integer');
    }
    if (degree === value.topDegree + 1 && role === 'C') return 0;
    if (degree === -1 && role === 'A') return value.terms.length - 1;
    if (degree < 0 || degree > value.topDegree) {
        return fail('DEGREE_OUT_OF_RANGE', 'longExact.position.degree', 'The degree/role is not a displayed term');
    }
    return 1 + 3 * (value.topDegree - degree) + (role === 'A' ? 0 : role === 'B' ? 1 : 2);
}

/** Observers return retained values and perform no new CAS construction. */
export function algebraPolynomialFreydLongExactTermAt<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydBoundedLongExactHomology<P, C, I>, position: number) {
    if (!Number.isSafeInteger(position) || position < 0 || position >= value.terms.length) {
        return fail('POSITION_OUT_OF_RANGE', 'longExact.term.position', 'Position is outside the displayed sequence');
    }
    return value.terms[position];
}

export function algebraPolynomialFreydLongExactAt<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydBoundedLongExactHomology<P, C, I>, position: number) {
    if (!Number.isSafeInteger(position) || position <= 0 || position >= value.terms.length - 1) {
        return fail('POSITION_OUT_OF_RANGE', 'longExact.exactness.position', 'Exactness is recorded at interior positions');
    }
    return value.interior[position - 1];
}

export function algebraPolynomialFreydLongExactWindowAt<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydBoundedLongExactHomology<P, C, I>, degree: number) {
    if (!Number.isSafeInteger(degree) || degree < 0 || degree >= value.windows.length) {
        return fail('DEGREE_OUT_OF_RANGE', 'longExact.window.degree', 'Degree is outside the retained windows');
    }
    return value.windows[degree];
}
