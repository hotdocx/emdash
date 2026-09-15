/** Realize all five native snake arrows through one supplied model and original CAS result. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydNativeRealizationInput, createAlgebraFormalFreydNativeRealizationSession } from './algebra_formal_freyd_native_realization_session';
import { AlgebraFormalFreydNativeSnakePreparation, assertAlgebraFormalFreydNativeSnakePreparationCurrent,
    algebraFormalFreydNativeSnakeZeroBundle } from './algebra_formal_freyd_native_snake_preparation';
import { algebraFormalFreydNativeSnakeObservationBundle, assertAlgebraFormalFreydNativeSnakeContext } from './algebra_formal_freyd_native_snake_observation';
import { FREYD_NATIVE_SNAKE_MAP_ROLES, FreydNativeSnakeMapRole } from './algebra_formal_freyd_native_snake_signatures';
import { algebraFormalFreydNativeModelNormalityType } from './algebra_formal_freyd_native_model_signatures';
import { createCoreProofChecker } from './proof_checker';
import { KernelExpression } from './kernel';

export async function trustAlgebraFormalFreydNativeSnake<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydNativeRealizationInput & {
        readonly observationId: string;
        readonly prepared: AlgebraFormalFreydNativeSnakePreparation<P, C, I>;
        readonly normality: KernelExpression;
    }
) {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.observationId)) throw new Error('A stable native snake observation ID is required');
    const prepared = input.prepared;
    assertAlgebraFormalFreydNativeSnakePreparationCurrent(prepared);
    const session = createAlgebraFormalFreydNativeRealizationSession<P, C, I>(input, prepared.reifier.formalRing);
    assertAlgebraFormalFreydNativeSnakeContext(session.source.environment, prepared.reifier.formalRing, input.formalModel);
    const checker = createCoreProofChecker(session.source.environment);
    checker.check(checker.rootContext, input.normality, algebraFormalFreydNativeModelNormalityType(prepared.reifier.formalRing, input.formalModel));
    const laws: KernelExpression[] = [];
    for (const [i, map] of prepared.maps.entries()) laws.push(await session.morphism(input.observationId + '/input-' + i, map));
    const zeroBundle = algebraFormalFreydNativeSnakeZeroBundle(prepared);
    const zeroLaw = await session.ensure(input.observationId + '/triple-zero', zeroBundle.realization.claimType,
        'computed-equation', () => zeroBundle);
    const observations: Array<Readonly<{
        role: FreydNativeSnakeMapRole;
        observation: ReturnType<typeof algebraFormalFreydNativeSnakeObservationBundle<P, C, I>>;
        observationInput: Parameters<typeof algebraFormalFreydNativeSnakeObservationBundle<P, C, I>>[0];
        proof: KernelExpression;
    }>> = [];
    for (const [i, role] of FREYD_NATIVE_SNAKE_MAP_ROLES.entries()) {
        const resultLaw = await session.morphism(input.observationId + '/result-' + role, prepared.outputs[i]);
        const observationInput = Object.freeze({ modelId: input.modelId, observationId: input.observationId + '/' + role, role,
            formalModel: input.formalModel, normality: input.normality, prepared,
            environment: session.source.environment, inputLaws: laws, zeroLaw, resultLaw });
        const observation = algebraFormalFreydNativeSnakeObservationBundle(observationInput);
        const proof = await session.ensure(input.observationId + '/interpretation-' + role, observation.realization.claimType,
            'trusted-presentation-semantics', () => observation);
        observations.push(Object.freeze({ role, observation, observationInput, proof }));
    }
    assertAlgebraFormalFreydNativeSnakePreparationCurrent(prepared);
    return Object.freeze({ prepared, observations: Object.freeze(observations), inputLaws: Object.freeze(laws), zeroLaw,
        source: session.source, counts: Object.freeze({ ...session.counts, snakeReplays: 0 as const }),
        provesDisplayedCasExactness: false as const });
}
