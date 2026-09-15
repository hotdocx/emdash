/** One complete native H-arrow realization, including its original endpoints. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydNativeRealizationInput, createAlgebraFormalFreydNativeRealizationSession } from './algebra_formal_freyd_native_realization_session';
import { AlgebraFormalFreydModelMapPreparation, assertAlgebraFormalFreydModelMapPreparationCurrent,
    algebraFormalFreydModelMapSquareBundle } from './algebra_formal_freyd_model_map_preparation';
import { algebraFormalFreydNativeModelMapObservationBundle } from './algebra_formal_freyd_model_map_observation';
import { defineAlgebraFormalFreydActualHomologyRealization } from './algebra_formal_freyd_actual_homology';
import { createAlgebraPolynomialFreydKernelChoiceProviders } from './algebra_polynomial_selected_weak_pullback_provider';
import { prepareAlgebraFormalFreydKernelChoiceProviders } from './algebra_formal_freyd_kernel_choice_providers';

/**
 * Wrap the already selected source/target H data, compute/reuse only raw matrix
 * facts, and adopt one complete-arrow interpretation. No separate endpoint
 * interpretation claims or formal selected-provider proofs are prerequisites.
 */
export async function trustAlgebraFormalFreydNativeHomologyMap<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydNativeRealizationInput & {
        readonly observationId: string;
        readonly prepared: AlgebraFormalFreydModelMapPreparation<P, C, I>;
    }
) {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.observationId)) throw new Error('A stable native map observation ID is required');
    assertAlgebraFormalFreydModelMapPreparationCurrent(input.prepared);
    const prepared = input.prepared, reifier = prepared.reifier;
    const session = createAlgebraFormalFreydNativeRealizationSession<P, C, I>(input, reifier.formalRing);
    const actual = (which: 'source' | 'target') => {
        const selected = prepared.selected.chainMap[which];
        // The wrapper retains the original weak kernels; it runs no universal algorithm.
        const providers = prepareAlgebraFormalFreydKernelChoiceProviders({ reifier,
            selected: createAlgebraPolynomialFreydKernelChoiceProviders({ id: 'native-map/' + input.observationId + '/' + which,
                ring: selected.pair.d.source.ambient.ring, kernel: selected.cycles }) });
        return defineAlgebraFormalFreydActualHomologyRealization({ reifier, selected, providers });
    };
    const source = await session.point(input.observationId + '/source', actual('source'));
    const target = await session.point(input.observationId + '/target', actual('target'));
    const components = await (async () => {
        const first = await session.morphism(input.observationId + '/component-0', prepared.maps[4]);
        const second = await session.morphism(input.observationId + '/component-1', prepared.maps[5]);
        const third = await session.morphism(input.observationId + '/component-2', prepared.maps[6]);
        return [first, second, third] as const;
    })();
    // These are equations of the CAS input chain map; H action is already native.
    const upper = algebraFormalFreydModelMapSquareBundle(prepared, 'upper');
    const lower = algebraFormalFreydModelMapSquareBundle(prepared, 'lower');
    const upperLaw = await session.ensure(input.observationId + '/upper', upper.realization.claimType, 'computed-equation', () => upper);
    const lowerLaw = await session.ensure(input.observationId + '/lower', lower.realization.claimType, 'computed-equation', () => lower);
    const resultLaw = await session.morphism(input.observationId + '/result', prepared.result);
    const observationInput = { observationId: input.observationId, prepared, source: source.observation,
        target: target.observation, environment: session.source.environment, componentLaws: components, upperLaw, lowerLaw, resultLaw };
    const observation = algebraFormalFreydNativeModelMapObservationBundle(observationInput);
    const proof = await session.ensure(input.observationId + '/interpretation', observation.realization.claimType,
        'trusted-presentation-semantics', () => observation);
    assertAlgebraFormalFreydModelMapPreparationCurrent(prepared);
    return Object.freeze({ source: session.source, observation, proof, observationInput, counts: session.counts });
}
