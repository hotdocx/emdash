/** Complete bounded result; shared links serialize as checked table references. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import {
    AlgebraPolynomialFreydBoundedLongExactHomology,
    AlgebraPolynomialFreydLongExactError
} from './algebra_polynomial_freyd_long_exact';
import { serializeAlgebraPolynomialFreydBoundedShortExactSequence } from './algebra_polynomial_freyd_bounded_short_exact_serialization';
import {
    algebraPolynomialFreydHomologyDegreeData,
    serializeAlgebraPolynomialFreydHomologyWindow
} from './algebra_polynomial_freyd_homology_window_serialization';
import {
    serializeAlgebraPolynomialFreydInducedHomologyMap as induced,
    serializeAlgebraPolynomialFreydChainPair as pair,
    serializeAlgebraPolynomialFreydExactnessAt as exactness
} from './algebra_polynomial_freyd_homology_reference_operations';
import {
    serializeAlgebraPolynomialPresentationMorphism as morphism,
    serializeAlgebraPolynomialPresentationAgreement as agreement
} from './algebra_polynomial_presentation_morphism_reference_operations';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

export function serializeAlgebraPolynomialFreydBoundedLongExactHomology<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydBoundedLongExactHomology<P, C, I>): string {
    const mismatch = (path: string): never => {
        throw new AlgebraPolynomialFreydLongExactError('OWNER_MISMATCH', path,
            'A serialized reference must designate the actual retained owner');
    };
    const terms = value.terms.map((term, position) => {
        if (term.position !== position || term.view !== value.degrees[term.degree + 1]?.[term.role]) {
            return mismatch('longExact.serialization.terms[' + position + ']');
        }
        return {
            position, degree: term.degree, role: term.role,
            location: term.location, degreeTableIndex: term.degree + 1
        };
    });
    const interior = value.interior.map((point, index) => {
        if (point.term !== value.terms[index + 1] || point.window !== value.windows[point.windowDegree] ||
            point.pair !== point.window.pairs[point.slot] || point.exactness !== point.window.exactness[point.slot] ||
            point.pair.dNext !== value.arrows[index] || point.pair.d !== value.arrows[index + 1] ||
            point.exactness.homology.pair !== point.pair) {
            return mismatch('longExact.serialization.interior[' + index + ']');
        }
        return {
            position: point.term.position, windowDegree: point.windowDegree, slot: point.slot,
            pair: pair(point.pair), exactness: exactness(point.exactness)
        };
    });
    return serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        sequence: serializeAlgebraPolynomialFreydBoundedShortExactSequence(value.sequence),
        topDegree: value.topDegree,
        degrees: value.degrees.map(entry => ({
            degree: entry.degree,
            A: algebraPolynomialFreydHomologyDegreeData(entry.A),
            B: algebraPolynomialFreydHomologyDegreeData(entry.B),
            C: algebraPolynomialFreydHomologyDegreeData(entry.C),
            inclusion: induced(entry.inclusion), projection: induced(entry.projection)
        })),
        windows: value.windows.map(serializeAlgebraPolynomialFreydHomologyWindow),
        terms,
        arrows: value.arrows.map(morphism),
        interior,
        endpoints: {
            initialZero: agreement(value.endpoints.initialZero),
            finalZero: agreement(value.endpoints.finalZero)
        },
        isExact: value.isExact,
        assumesSplitEpimorphisms: value.assumesSplitEpimorphisms
    }, 'polynomialFreydBoundedLongExactHomology');
}
