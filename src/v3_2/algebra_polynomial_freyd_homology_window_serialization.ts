/** Canonical whole-window data, including every retained factor and agreement. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraPolynomialFreydHomologyWindow } from './algebra_polynomial_freyd_homology_window';
import {
    serializeAlgebraPolynomialFreydBoundedComplex,
    serializeAlgebraPolynomialFreydBoundedShortExactSequence
} from './algebra_polynomial_freyd_bounded_short_exact_serialization';
import {
    serializeAlgebraPolynomialPresentationAgreement as agreement,
    serializeAlgebraPolynomialPresentationMorphism as morphism
} from './algebra_polynomial_presentation_morphism_reference_operations';
import {
    serializeAlgebraPolynomialFreydChainPair as pair,
    serializeAlgebraPolynomialFreydHomologyAt as homology,
    serializeAlgebraPolynomialFreydInducedHomologyMap as induced,
    serializeAlgebraPolynomialFreydExactnessAt as exactness
} from './algebra_polynomial_freyd_homology_reference_operations';
import { algebraPolynomialFreydHomologyConnectingData } from './algebra_polynomial_freyd_homology_connecting_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

export function serializeAlgebraPolynomialFreydHomologyWindow<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydHomologyWindow<P, C, I>): string {
    const degreeData = (view: typeof value.upperA) => ({
        complex: serializeAlgebraPolynomialFreydBoundedComplex(view.complex),
        degree: view.degree,
        homology: homology(view.homology),
        bounded: view.bounded === undefined ? null : {
            kind: view.bounded.kind,
            complex: serializeAlgebraPolynomialFreydBoundedComplex(view.bounded.complex),
            degree: view.bounded.degree,
            pair: pair(view.bounded.pair),
            homology: homology(view.bounded.homology),
            lowerEndpoint: view.bounded.lowerEndpoint,
            upperEndpoint: view.bounded.upperEndpoint
        },
        zeroIdentity: view.zeroIdentity === undefined ? null : agreement(view.zeroIdentity),
        location: view.location
    });
    return serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        sequence: serializeAlgebraPolynomialFreydBoundedShortExactSequence(value.sequence),
        degree: value.degree,
        upperA: degreeData(value.upperA),
        upperB: degreeData(value.upperB),
        upperC: degreeData(value.upperC),
        lowerA: degreeData(value.lowerA),
        lowerB: degreeData(value.lowerB),
        inclusionUpper: induced(value.inclusionUpper),
        projectionUpper: induced(value.projectionUpper),
        inclusionLower: induced(value.inclusionLower),
        connecting: algebraPolynomialFreydHomologyConnectingData(value.connecting),
        arrows: value.arrows.map(morphism),
        pairs: value.pairs.map(pair),
        exactness: value.exactness.map(exactness),
        isExact: value.isExact,
        assumesSplitEpimorphisms: value.assumesSplitEpimorphisms
    }, 'polynomialFreydHomologyWindow');
}
