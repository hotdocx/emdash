/** Direct native whole-δ realization with explicit native row contracts. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydModelConnectingPreparation, assertAlgebraFormalFreydModelConnectingPreparationCurrent,
    algebraFormalFreydConnectingSquareBundle } from './algebra_formal_freyd_model_connecting_preparation';
import { AlgebraFormalFreydConnectingRowLaws, algebraFormalFreydNativeShortExactObservationBundle,
    algebraFormalFreydNativeConnectingObservationBundle, assertAlgebraFormalFreydNativeConnectingContext }
    from './algebra_formal_freyd_model_connecting_observation';
import { AlgebraFormalFreydNativeRealizationInput, createAlgebraFormalFreydNativeRealizationSession } from './algebra_formal_freyd_native_realization_session';
import { algebraFormalFreydNativeModelNormalityType } from './algebra_formal_freyd_native_model_signatures';
import { defineAlgebraFormalFreydActualHomologyRealization } from './algebra_formal_freyd_actual_homology';
import { createAlgebraPolynomialFreydKernelChoiceProviders } from './algebra_polynomial_selected_weak_pullback_provider';
import { prepareAlgebraFormalFreydKernelChoiceProviders } from './algebra_formal_freyd_kernel_choice_providers';
import { createCoreProofChecker } from './proof_checker';
import { KernelExpression } from './kernel';

/** Matrix equations and model/row interpretation have distinct classifications. */
export async function trustAlgebraFormalFreydNativeConnecting<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydNativeRealizationInput & {
        readonly observationId: string;
        readonly prepared: AlgebraFormalFreydModelConnectingPreparation<P, C, I>;
        readonly normality: KernelExpression;
    }
) {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.observationId)) throw new Error('A stable native connecting observation ID is required');
    const prepared = input.prepared, reifier = prepared.reifier;
    assertAlgebraFormalFreydModelConnectingPreparationCurrent(prepared);
    const session = createAlgebraFormalFreydNativeRealizationSession<P, C, I>(input, reifier.formalRing);
    assertAlgebraFormalFreydNativeConnectingContext(session.source.environment, reifier.formalRing, input.formalModel);
    const checker = createCoreProofChecker(session.source.environment);
    checker.check(checker.rootContext, input.normality, algebraFormalFreydNativeModelNormalityType(reifier.formalRing, input.formalModel));
    const actual = (which: 'source' | 'target') => {
        const selected = prepared.selected[which];
        const providers = prepareAlgebraFormalFreydKernelChoiceProviders({ reifier,
            selected: createAlgebraPolynomialFreydKernelChoiceProviders({ id: 'native-connecting/' + input.observationId + '/' + which,
                ring: selected.pair.d.source.ambient.ring, kernel: selected.cycles }) });
        return defineAlgebraFormalFreydActualHomologyRealization({ reifier, selected, providers });
    };
    const sourcePoint = (await session.point(input.observationId + '/source', actual('source'))).observation;
    const targetPoint = (await session.point(input.observationId + '/target', actual('target'))).observation;
    const rows: AlgebraFormalFreydConnectingRowLaws[] = [];
    for (const [i, row] of prepared.rowPairs.entries()) {
        const above = await session.morphism(input.observationId + '/row-' + i + '/above', row.above);
        const below = await session.morphism(input.observationId + '/row-' + i + '/below', row.below);
        const zero = await session.chain(input.observationId + '/row-' + i + '/zero', row);
        const observation = algebraFormalFreydNativeShortExactObservationBundle({ prepared, index: i as 0 | 1 | 2 | 3,
            modelId: sourcePoint.realization.modelId, observationId: input.observationId + '/row-' + i,
            formalModel: sourcePoint.realization.formalModel, environment: session.source.environment,
            laws: { above, below, chain: zero } });
        const exact = await session.ensure(input.observationId + '/row-' + i + '/model-short-exact', observation.realization.claimType,
            'trusted-presentation-semantics', () => observation);
        rows.push(Object.freeze({ above, below, chain: zero, exact }));
    }
    const vertical = {
        am: await session.morphism(input.observationId + '/vertical/am', prepared.rowMaps[0].maps[4]),
        bm: await session.morphism(input.observationId + '/vertical/bm', prepared.rowMaps[0].maps[5]),
        b0: await session.morphism(input.observationId + '/vertical/b0', prepared.rowMaps[1].maps[5]),
        b1: await session.morphism(input.observationId + '/vertical/b1', prepared.rowMaps[2].maps[5]),
        d1: await session.morphism(input.observationId + '/vertical/d1', prepared.rowMaps[2].maps[6])
    };
    const squares = [];
    for (const i of [0, 1, 2] as const) {
        const upper = algebraFormalFreydConnectingSquareBundle(prepared, i, 'upper');
        const lower = algebraFormalFreydConnectingSquareBundle(prepared, i, 'lower');
        squares.push(Object.freeze({
            upper: await session.ensure(input.observationId + '/map-' + i + '/upper', upper.realization.claimType, 'computed-equation', () => upper),
            lower: await session.ensure(input.observationId + '/map-' + i + '/lower', lower.realization.claimType, 'computed-equation', () => lower)
        }));
    }
    const upperZero = await session.chain(input.observationId + '/middle/upper', prepared.upper);
    const lowerZero = await session.chain(input.observationId + '/middle/lower', prepared.lower);
    const resultLaw = await session.morphism(input.observationId + '/result', prepared.result);
    const observationInput = { observationId: input.observationId,
        source: sourcePoint, target: targetPoint, prepared, environment: session.source.environment,
        normality: input.normality, rows, vertical, squares, upperZero, lowerZero, resultLaw };
    const observation = algebraFormalFreydNativeConnectingObservationBundle(observationInput);
    const proof = await session.ensure(input.observationId + '/connecting-interpretation', observation.realization.claimType,
        'trusted-presentation-semantics', () => observation);
    assertAlgebraFormalFreydModelConnectingPreparationCurrent(prepared);
    return Object.freeze({ prepared, observation, observationInput, proof, source: session.source, rows: Object.freeze(rows),
        counts: Object.freeze({ ...session.counts, connectingReplays: 0 as const }) });
}
