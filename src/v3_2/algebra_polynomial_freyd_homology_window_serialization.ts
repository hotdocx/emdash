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
import {
    serializeAlgebraPolynomialFreydKernelLift as kernelLift,
    serializeAlgebraPolynomialFreydCokernel as cokernel,
    serializeAlgebraPolynomialFreydCokernelColift as cokernelColift
} from './algebra_formal_freyd_preabelian';
import {
    serializeAlgebraPolynomialFreydNormalMonoLift as monoLift,
    serializeAlgebraPolynomialFreydNormalEpiColift as epiColift,
    serializeAlgebraPolynomialFreydMonomorphismWitness as monic
} from './algebra_formal_freyd_abelian';
import {
    serializeAlgebraPolynomialFreydShortExactTriple as row,
    serializeAlgebraPolynomialFreydSnakeConnecting as snake
} from './algebra_polynomial_freyd_snake_reference_operations';
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
    const isoData = (iso: typeof value.connecting.upperComparison) => ({
        forward: morphism(iso.forward),
        inverse: morphism(iso.inverse),
        sourceIdentity: morphism(iso.sourceIdentity),
        targetIdentity: morphism(iso.targetIdentity),
        inverseAfterForward: morphism(iso.inverseAfterForward),
        forwardAfterInverse: morphism(iso.forwardAfterInverse),
        sourceAgreement: agreement(iso.sourceAgreement),
        targetAgreement: agreement(iso.targetAgreement),
        isomorphism: iso.isomorphism
    });
    const c = value.connecting;
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
        connecting: {
            snake: snake(c.snake),
            upperRow: { degree: c.upperRow.degree, location: c.upperRow.location, triple: row(c.upperRow.triple) },
            lowerRow: { degree: c.lowerRow.degree, location: c.lowerRow.location, triple: row(c.lowerRow.triple) },
            upperForward: cokernelColift(c.upperForward),
            upperInverse: epiColift(c.upperInverse),
            upperComparison: isoData(c.upperComparison),
            lowerForward: kernelLift(c.lowerForward),
            lowerInverse: monoLift(c.lowerInverse),
            lowerComparison: isoData(c.lowerComparison),
            gammaAfterComparison: morphism(c.gammaAfterComparison),
            alphaAfterComparison: morphism(c.alphaAfterComparison),
            gammaAgreement: agreement(c.gammaAgreement),
            alphaAgreement: agreement(c.alphaAgreement),
            cycleForward: kernelLift(c.cycleForward),
            cycleInverse: kernelLift(c.cycleInverse),
            cycleComparison: isoData(c.cycleComparison),
            differentialCokernel: cokernel(c.differentialCokernel),
            targetForward: cokernelColift(c.targetForward),
            targetInverse: cokernelColift(c.targetInverse),
            targetComparison: isoData(c.targetComparison),
            homologyEmbedding: cokernelColift(c.homologyEmbedding),
            homologyMonomorphism: monic(c.homologyMonomorphism),
            snakeAfterCycles: morphism(c.snakeAfterCycles),
            comparedSnake: morphism(c.comparedSnake),
            targetFactor: monoLift(c.targetFactor),
            descent: cokernelColift(c.descent),
            homologyMap: morphism(c.homologyMap)
        },
        arrows: value.arrows.map(morphism),
        pairs: value.pairs.map(pair),
        exactness: value.exactness.map(exactness),
        isExact: value.isExact,
        assumesSplitEpimorphisms: value.assumesSplitEpimorphisms
    }, 'polynomialFreydHomologyWindow');
}
