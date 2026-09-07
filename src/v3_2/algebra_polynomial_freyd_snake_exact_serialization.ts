/** Full native six-term result with checked references to its selected objects/maps. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraPolynomialFreydSnakeExactError, AlgebraPolynomialFreydSnakeExactSequence } from './algebra_polynomial_freyd_snake_exact';
import { serializeAlgebraPolynomialFreydSnakeConnecting } from './algebra_polynomial_freyd_snake_reference_operations';
import {
    serializeAlgebraPolynomialFreydKernel as kernel,
    serializeAlgebraPolynomialFreydCokernel as cokernel,
    serializeAlgebraPolynomialFreydKernelLift as kernelLift,
    serializeAlgebraPolynomialFreydCokernelColift as cokernelColift
} from './algebra_formal_freyd_preabelian';
import { serializeAlgebraPolynomialPresentationMorphism as morphism } from './algebra_polynomial_presentation_morphism_reference_operations';
import {
    serializeAlgebraPolynomialFreydChainPair as pair,
    serializeAlgebraPolynomialFreydExactnessAt as exactness
} from './algebra_polynomial_freyd_homology_reference_operations';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

export function serializeAlgebraPolynomialFreydSnakeExactSequence<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraPolynomialFreydSnakeExactSequence<P, C, I>): string {
    const expectedObjects = [value.alphaKernel.object, value.betaKernel.object, value.connecting.gammaKernel.object,
        value.connecting.alphaCokernel.object, value.betaCokernel.object, value.gammaCokernel.object];
    const expectedArrows = [value.kernelAlphaBeta.lift, value.kernelBetaGamma.lift, value.connecting.connecting,
        value.cokernelAlphaBeta.colift, value.cokernelBetaGamma.colift];
    if (value.objects.length !== 6 || value.arrows.length !== 5 || value.pairs.length !== 4 || value.exactness.length !== 4 ||
        value.objects.some((object, index) => object !== expectedObjects[index]) ||
        value.arrows.some((arrow, index) => arrow !== expectedArrows[index]) ||
        value.pairs.some((point, index) => point.dNext !== value.arrows[index] || point.d !== value.arrows[index + 1] ||
            value.exactness[index].homology.pair !== point)) {
        throw new AlgebraPolynomialFreydSnakeExactError('OWNER_MISMATCH', 'snakeExact.serialization',
            'Serialized object/map references must be the actual selected owners');
    }
    return serializeCoreLfWorkspaceCanonicalJson({
        kind: value.kind,
        ringIdentity: value.connecting.triple.delta.source.ambient.ring.identity.id,
        connecting: serializeAlgebraPolynomialFreydSnakeConnecting(value.connecting),
        alphaKernel: kernel(value.alphaKernel), betaKernel: kernel(value.betaKernel),
        betaCokernel: cokernel(value.betaCokernel), gammaCokernel: cokernel(value.gammaCokernel),
        kernelAlphaBeta: kernelLift(value.kernelAlphaBeta), kernelBetaGamma: kernelLift(value.kernelBetaGamma),
        cokernelAlphaBeta: cokernelColift(value.cokernelAlphaBeta), cokernelBetaGamma: cokernelColift(value.cokernelBetaGamma),
        objectOwners: ['alphaKernel', 'betaKernel', 'connecting.gammaKernel',
            'connecting.alphaCokernel', 'betaCokernel', 'gammaCokernel'],
        arrows: value.arrows.map(morphism),
        pairs: value.pairs.map(pair), exactness: value.exactness.map(exactness),
        isExact: value.isExact, assumesEndpointZeros: value.assumesEndpointZeros,
        assumesSplitEpimorphisms: value.assumesSplitEpimorphisms
    }, 'polynomialFreydSnakeExactSequence');
}
