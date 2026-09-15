/** Construct native categorical exactness from the already derived theorems. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { trustAlgebraFormalFreydNativeConnecting } from './algebra_formal_freyd_native_connecting_workflow';
import { ALGEBRA_FORMAL_FREYD_NATIVE_CONNECTING_OBSERVATION_PROFILE, assertAlgebraFormalFreydNativeConnectingContext } from './algebra_formal_freyd_model_connecting_observation';
import { validateAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { algebraFormalFreydNativeExactnessExpressions, createFormalFreydNativeExactnessProofEnvironment,
    FORMAL_FREYD_NATIVE_EXACTNESS_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_exactness_signatures';
import { kernelExpressionEquals } from './kernel';
import { createCoreProofChecker } from './proof_checker';

/** No CAS execution, trust decision or output-exactness assumption is introduced. */
export function constructAlgebraFormalFreydNativeExactness<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    connecting: Awaited<ReturnType<typeof trustAlgebraFormalFreydNativeConnecting<P, C, I>>>
) {
    const observation = connecting.observation;
    if (observation.profile.revision !== ALGEBRA_FORMAL_FREYD_NATIVE_CONNECTING_OBSERVATION_PROFILE.revision) {
        throw new Error('Use the direct native connecting observation for categorical exactness');
    }
    if (connecting.prepared !== observation.realization.prepared) {
        throw new Error('Native exactness must retain the original window preparation');
    }
    observation.adapter.normalizeRealization(observation.realization, 'nativeExactness.window');
    const source = validateAlgebraFormalAssumptionSource(connecting.source), values = observation.realization.values;
    assertAlgebraFormalFreydNativeConnectingContext(source.environment, values.R, values.M);
    const expected = createFormalFreydNativeExactnessProofEnvironment([]);
    for (const name of Object.keys(FORMAL_FREYD_NATIVE_EXACTNESS_SIGNATURE_BINDINGS)) {
        const declaration = source.environment.lookup(name);
        if (!declaration || declaration.body !== undefined || !kernelExpressionEquals(declaration.type, expected.lookup(name)!.type)) {
            throw new Error('Missing or changed native exactness theorem signature ' + name);
        }
    }
    const evidence = algebraFormalFreydNativeExactnessExpressions(values);
    const checker = createCoreProofChecker(source.environment);
    for (const item of evidence) checker.check(checker.rootContext, item.term, item.type);
    return Object.freeze({ source, prepared: connecting.prepared, evidence,
        assumptionsAdded: 0 as const, trustDecisions: 0 as const,
        wholeCategoricalEvidence: true as const, provesDisplayedCasExactness: false as const });
}
