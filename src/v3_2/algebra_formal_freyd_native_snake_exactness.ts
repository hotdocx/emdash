/** Derive the four native exactness witnesses at the original realized snake input. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { trustAlgebraFormalFreydNativeSnake } from './algebra_formal_freyd_native_snake_workflow';
import { validateAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { assertAlgebraFormalFreydNativeSnakeContext, ALGEBRA_FORMAL_FREYD_NATIVE_SNAKE_OBSERVATION_PROFILE } from './algebra_formal_freyd_native_snake_observation';
import { createFormalFreydNativeSnakeExactnessProofEnvironment, algebraFormalFreydNativeSnakeExactnessExpressions,
    FORMAL_FREYD_NATIVE_SNAKE_EXACTNESS_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_snake_exactness_signatures';
import { createCoreProofChecker } from './proof_checker';
import { kernelExpressionEquals } from './kernel';

/** This operation adds no assumption, trust decision or CAS computation. */
export function constructAlgebraFormalFreydNativeSnakeExactness<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    snake: Awaited<ReturnType<typeof trustAlgebraFormalFreydNativeSnake<P, C, I>>>
) {
    if (snake.observations.length !== 5 || snake.observations[2].role !== 'connecting') throw new Error('Retain the complete native snake realization');
    const connecting = snake.observations[2], realization = connecting.observation.realization;
    for (const item of snake.observations) {
        if (item.observation.profile.revision !== ALGEBRA_FORMAL_FREYD_NATIVE_SNAKE_OBSERVATION_PROFILE.revision ||
            item.observation.realization.prepared !== snake.prepared ||
            !kernelExpressionEquals(item.observation.realization.formalModel, realization.formalModel) ||
            !kernelExpressionEquals(item.observationInput.normality, connecting.observationInput.normality) ||
            !kernelExpressionEquals(item.observationInput.zeroLaw, snake.zeroLaw) ||
            item.observationInput.inputLaws !== snake.inputLaws) throw new Error('Exactness requires one original model and snake input');
        item.observation.adapter.normalizeRealization(item.observation.realization, 'nativeSnakeExactness.selection');
    }
    const source = validateAlgebraFormalAssumptionSource(snake.source), R = snake.prepared.reifier.formalRing;
    assertAlgebraFormalFreydNativeSnakeContext(source.environment, R, realization.formalModel);
    const expected = createFormalFreydNativeSnakeExactnessProofEnvironment([]);
    for (const name of Object.keys(FORMAL_FREYD_NATIVE_SNAKE_EXACTNESS_SIGNATURE_BINDINGS)) {
        const actual = source.environment.lookup(name), declaration = expected.lookup(name);
        if (!actual || actual.body !== undefined || !kernelExpressionEquals(actual.type, declaration!.type)) throw new Error('Missing or changed native snake exactness signature ' + name);
    }
    const [A, B, X, D] = realization.terms.presentations, [a, b, c] = realization.terms.morphisms;
    const evidence = algebraFormalFreydNativeSnakeExactnessExpressions({ R, M: realization.formalModel,
        N: connecting.observationInput.normality, A, B, X, D, a, b, c, z: realization.terms.zero });
    const checker = createCoreProofChecker(source.environment);
    for (const item of evidence) {
        checker.check(checker.rootContext, item.term, item.type);
        checker.check(checker.rootContext, item.data, item.dataType);
        checker.check(checker.rootContext, item.evidence, item.evidenceType);
    }
    return Object.freeze({ source, prepared: snake.prepared, evidence,
        assumptionsAdded: 0 as const, trustDecisions: 0 as const,
        wholeCategoricalEvidence: true as const, provesDisplayedCasExactness: false as const });
}
