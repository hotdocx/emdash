/** Automatic matrix prerequisites and explicit realization of native whole H. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydActualHomologyRealization } from './algebra_formal_freyd_actual_homology';
import { AlgebraFormalFreydNativeRealizationInput, createAlgebraFormalFreydNativeRealizationSession } from './algebra_formal_freyd_native_realization_session';

/**
 * Matrix equations are computed/reused; agreement of the supplied whole model
 * with the selected CAS presentation is explicitly trusted presentation semantics.
 * No caller naturality square, old model or formal selected-provider proof is used.
 */
export async function trustAlgebraFormalFreydNativeHomologyPoint<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydNativeRealizationInput & {
        readonly observationId: string;
        readonly actual: AlgebraFormalFreydActualHomologyRealization<P, C, I>;
    }
) {
    const session = createAlgebraFormalFreydNativeRealizationSession<P, C, I>(input, input.actual.reifier.formalRing);
    const { observation, observationInput } = await session.point(input.observationId, input.actual);
    const proof = await session.ensure(input.observationId + '/interpretation', observation.realization.claimType,
        'trusted-presentation-semantics', () => observation);
    return Object.freeze({ source: session.source, observation, proof, observationInput, counts: session.counts });
}
