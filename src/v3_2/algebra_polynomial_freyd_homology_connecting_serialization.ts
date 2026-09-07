/** Complete homology-connecting result, with a separate method-specific trace. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraPolynomialFreydHomologyConnecting } from './algebra_polynomial_freyd_homology_connecting';
import { serializeAlgebraPolynomialFreydBoundedShortExactSequence } from './algebra_polynomial_freyd_bounded_short_exact_serialization';
import {
    serializeAlgebraPolynomialPresentationAgreement as agreement,
    serializeAlgebraPolynomialPresentationMorphism as morphism
} from './algebra_polynomial_presentation_morphism_reference_operations';
import { serializeAlgebraPolynomialFreydHomologyAt as homology } from './algebra_polynomial_freyd_homology_reference_operations';
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

export function algebraPolynomialFreydHomologyConnectingData<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydHomologyConnecting<P, C, I>) {
    const isoData = (iso: typeof value.trace.upperComparison) => ({
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
    const c = value.trace;
    return {
        kind: value.kind,
        sequence: serializeAlgebraPolynomialFreydBoundedShortExactSequence(value.sequence),
        degree: value.degree,
        source: homology(value.source),
        target: homology(value.target),
        homologyMap: morphism(value.homologyMap),
        reconstruction: {
            sourceProjection: morphism(value.reconstruction.sourceProjection),
            targetInclusion: morphism(value.reconstruction.targetInclusion),
            comparedMap: morphism(value.reconstruction.comparedMap),
            reconstructed: morphism(value.reconstruction.reconstructed),
            agreement: agreement(value.reconstruction.agreement)
        },
        trace: {
            kind: c.kind,
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
        assumesSplitEpimorphisms: value.assumesSplitEpimorphisms
    };
}

export function serializeAlgebraPolynomialFreydHomologyConnecting<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydHomologyConnecting<P, C, I>): string {
    return serializeCoreLfWorkspaceCanonicalJson(
        algebraPolynomialFreydHomologyConnectingData(value), 'polynomialFreydHomologyConnecting'
    );
}
