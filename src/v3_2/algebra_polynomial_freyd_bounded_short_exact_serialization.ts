/** Canonical algebraic data for the retained bounded short-exact result. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { algebraPolynomialText } from './algebra_polynomial';
import { AlgebraPresentedPolynomialModule } from './algebra_polynomial_presentation';
import {
    AlgebraPolynomialFreydBoundedChainMap,
    AlgebraPolynomialFreydBoundedComplex
} from './algebra_polynomial_freyd_bounded_complex';
import {
    AlgebraPolynomialFreydBoundedShortExactSequence
} from './algebra_polynomial_freyd_bounded_short_exact';
import {
    serializeAlgebraPolynomialPresentationAgreement,
    serializeAlgebraPolynomialPresentationMorphism
} from './algebra_polynomial_presentation_morphism_reference_operations';
import {
    serializeAlgebraPolynomialFreydChainPair
} from './algebra_polynomial_freyd_homology_reference_operations';
import {
    serializeAlgebraPolynomialFreydShortExactTriple
} from './algebra_polynomial_freyd_snake_reference_operations';
import {
    serializeAlgebraPolynomialBoundedFreeComplex
} from './algebra_polynomial_bounded_complex_reference_operations';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

// Use the existing presentation convention: raw generators describe the
// selected presentation; derived Gröbner caches are implementation data.
const presentationData = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPresentedPolynomialModule<P, C, I>
) => ({
    kind: value.kind,
    ambient: value.ambient.identity,
    rank: value.ambient.rank,
    order: value.ambient.termOrder,
    relations: value.relations.generators.map(relation =>
        relation.components.map(algebraPolynomialText)
    )
});

const complexData = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPolynomialFreydBoundedComplex<P, C, I>
) => ({
    kind: value.kind,
    ring: value.ring.identity,
    length: value.length,
    terms: value.terms.map(term => ({
        degree: term.degree,
        object: presentationData(term.object)
    })),
    differentials: value.differentials.map(entry => ({
        degree: entry.degree,
        morphism: serializeAlgebraPolynomialPresentationMorphism(entry.morphism)
    })),
    conditions: value.conditions.map(condition => ({
        upperDegree: condition.upperDegree,
        pair: serializeAlgebraPolynomialFreydChainPair(condition.pair),
        agreement: serializeAlgebraPolynomialPresentationAgreement(condition.agreement),
        zero: condition.zero
    })),
    isComplex: value.isComplex,
    freeSource: value.freeSource === undefined ? null : {
        kind: value.freeSource.kind,
        complex: serializeAlgebraPolynomialBoundedFreeComplex(value.freeSource.complex)
    }
});

const chainMapData = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPolynomialFreydBoundedChainMap<P, C, I>
) => ({
    kind: value.kind,
    source: complexData(value.source),
    target: complexData(value.target),
    components: value.components.map(component => ({
        degree: component.degree,
        morphism: serializeAlgebraPolynomialPresentationMorphism(component.morphism)
    })),
    squares: value.squares.map(square => ({
        degree: square.degree,
        targetAfterComponent:
            serializeAlgebraPolynomialPresentationMorphism(square.targetAfterComponent),
        componentAfterSource:
            serializeAlgebraPolynomialPresentationMorphism(square.componentAfterSource),
        agreement: serializeAlgebraPolynomialPresentationAgreement(square.agreement),
        commutes: square.commutes
    })),
    isChainMap: value.isChainMap
});

export const serializeAlgebraPolynomialFreydBoundedComplex = <
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydBoundedComplex<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson(complexData(value), 'polynomialFreydBoundedComplex');

export const serializeAlgebraPolynomialFreydBoundedChainMap = <
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydBoundedChainMap<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson(chainMapData(value), 'polynomialFreydBoundedChainMap');

export const serializeAlgebraPolynomialFreydBoundedShortExactSequence = <
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydBoundedShortExactSequence<P, C, I>): string =>
    serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        ring: value.ring.identity,
        length: value.length,
        subcomplex: complexData(value.subcomplex),
        middleComplex: complexData(value.middleComplex),
        quotientComplex: complexData(value.quotientComplex),
        inclusion: chainMapData(value.inclusion),
        projection: chainMapData(value.projection),
        rows: value.rows.map(row => ({
            degree: row.degree,
            location: row.location,
            triple: serializeAlgebraPolynomialFreydShortExactTriple(row.triple)
        })),
        zeroObject: presentationData(value.zeroObject),
        zeroRow: serializeAlgebraPolynomialFreydShortExactTriple(value.zeroRow),
        isShortExact: value.isShortExact
    }, 'polynomialFreydBoundedShortExactSequence');
