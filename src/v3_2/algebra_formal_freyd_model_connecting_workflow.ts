/** Append explicit row/model interpretations for one retained connecting arrow. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydModelConnectingPreparation, assertAlgebraFormalFreydModelConnectingPreparationCurrent,
    algebraFormalFreydConnectingSquareBundle } from './algebra_formal_freyd_model_connecting_preparation';
import { algebraFormalFreydModelConnectingObservationBundle, algebraFormalFreydModelShortExactObservationBundle,
    AlgebraFormalFreydConnectingRowLaws, assertAlgebraFormalFreydModelConnectingContext } from './algebra_formal_freyd_model_connecting_observation';
import { algebraFormalFreydModelHomologyObservationBundle } from './algebra_formal_freyd_model_observation';
import { AlgebraFormalPresentationMorphismRealization } from './algebra_formal_presentation_morphism';
import { algebraFormalPresentationMorphismDelegationBundle } from './algebra_formal_presentation_morphism_delegation';
import { algebraFormalFreydChainPairDelegationBundle, AlgebraFormalFreydChainPairRealization } from './algebra_formal_freyd_chain_pair';
import { createAlgebraPolynomialFreydHomologyEngine } from './algebra_polynomial_freyd_homology_category';
import { createAlgebraTypeScriptReferenceEngine } from './algebra_reference_engine';
import { AlgebraFormalAssumptionSource, appendAlgebraFormalAssumption, validateAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { AlgebraFormalWorkflowInput, runAlgebraFormalWorkflow, trustAlgebraFormalWorkflow } from './algebra_formal_workflow';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { createCoreProofChecker } from './proof_checker';
import { algebraFormalFreydModelNormalityType } from './algebra_formal_freyd_model_connecting_signatures';
import { serializeCoreExpression } from './core_serialization';
import { CoreProofArtifactFingerprint } from './proof_document';
import { coreProofPlanHole } from './proof_plan';

type Point<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof algebraFormalFreydModelHomologyObservationBundle<P, C, I>>;

export async function trustAlgebraFormalFreydModelConnecting<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly artifactId: string; readonly prepared: AlgebraFormalFreydModelConnectingPreparation<P, C, I>;
    readonly modelSource: Point<P, C, I>; readonly modelTarget: Point<P, C, I>;
    readonly normality: KernelExpression; readonly source: AlgebraFormalAssumptionSource;
    readonly fingerprint: (goalId: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (goalId: string) => string;
}) {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.artifactId)) throw new Error('A stable connecting artifact ID is required');
    const prepared = input.prepared;
    assertAlgebraFormalFreydModelConnectingPreparationCurrent(prepared);
    let source = validateAlgebraFormalAssumptionSource(input.source);
    const known = new Map(source.entries.map(entry => [serializeCoreExpression(entry.declaration.type), entry.reference]));
    for (const point of [input.modelSource, input.modelTarget]) {
        if (!known.has(serializeCoreExpression(point.realization.claimType))) {
            throw new Error('Connecting needs the already adopted model H points');
        }
    }
    if (input.modelSource.realization.actual.selected !== prepared.selected.source ||
        input.modelTarget.realization.actual.selected !== prepared.selected.target) throw new Error('Connecting H selections differ');
    input.modelSource.adapter.normalizeRealization(input.modelSource.realization, 'connectingWorkflow.source');
    input.modelTarget.adapter.normalizeRealization(input.modelTarget.realization, 'connectingWorkflow.target');
    if (input.modelSource.realization.modelId !== input.modelTarget.realization.modelId ||
        !kernelExpressionEquals(input.modelSource.realization.formalModel, input.modelTarget.realization.formalModel)) {
        throw new Error('Connecting requires the same supplied model');
    }
    const checker = createCoreProofChecker(source.environment);
    assertAlgebraFormalFreydModelConnectingContext(source.environment, prepared.reifier.formalRing,
        input.modelSource.realization.formalModel);
    checker.check(checker.rootContext, input.normality,
        algebraFormalFreydModelNormalityType(prepared.reifier.formalRing, input.modelSource.realization.formalModel));
    const before = source.entries.length;
    let reused = 0;
    const ensure = async <R, A, B>(key: string, claimType: KernelExpression,
        classification: 'computed-equation' | 'trusted-presentation-semantics',
        make: () => Pick<AlgebraFormalWorkflowInput<R, A, B>, 'adapter' | 'realization' | 'engine'>
    ) => {
        const claim = serializeCoreExpression(claimType), old = known.get(claim);
        if (old) { reused++; return old; }
        const goalId = (input.artifactId + '/' + key).replace(/[^A-Za-z0-9_]/gu, '_');
        const p = provenance('derived', 'retained connecting claim ' + key);
        const run = await runAlgebraFormalWorkflow({ ...make(), goalId, document: {
            moduleId: source.moduleId, declarationId: goalId, environment: source.environment, type: claimType,
            plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target: claimType } }),
            provenance: p, fingerprint: input.fingerprint(goalId)
        } });
        const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: goalId,
            decision: { kind: 'trust-exact-algebra-computation', evidence: input.decisionEvidence(goalId) } });
        source = appendAlgebraFormalAssumption({ source, adoption, classification });
        const proof = source.entries.at(-1)!.reference;
        known.set(claim, proof);
        return proof;
    };
    const morphism = (key: string, value: AlgebraFormalPresentationMorphismRealization<P, C, I>) =>
        ensure(key, value.claimType, 'computed-equation', () => {
            const bundle = algebraFormalPresentationMorphismDelegationBundle({ reifier: prepared.reifier, selected: value.selected });
            return { ...bundle, engine: createAlgebraTypeScriptReferenceEngine({ id: input.artifactId + '/' + key,
                revision: 'v1', implementations: bundle.operations.implementations }) };
        });
    const chain = (key: string, value: AlgebraFormalFreydChainPairRealization<P, C, I>) =>
        ensure(key, value.claimType, 'computed-equation', () => {
            const bundle = algebraFormalFreydChainPairDelegationBundle({ reifier: prepared.reifier, selected: value.selected });
            return { ...bundle, engine: createAlgebraPolynomialFreydHomologyEngine(bundle.model) };
        });
    const rows: AlgebraFormalFreydConnectingRowLaws[] = [];
    for (const [i, row] of prepared.rowPairs.entries()) {
        const above = await morphism('row-' + i + '/above', row.above);
        const below = await morphism('row-' + i + '/below', row.below);
        const zero = await chain('row-' + i + '/zero', row);
        const observation = algebraFormalFreydModelShortExactObservationBundle({ prepared, index: i as 0 | 1 | 2 | 3,
            modelId: input.modelSource.realization.modelId, observationId: input.artifactId + '/row-' + i,
            formalModel: input.modelSource.realization.formalModel, environment: source.environment,
            laws: { above, below, chain: zero } });
        const exact = await ensure('row-' + i + '/model-short-exact', observation.realization.claimType,
            'trusted-presentation-semantics', () => observation);
        rows.push(Object.freeze({ above, below, chain: zero, exact }));
    }
    const vertical = {
        am: await morphism('vertical/am', prepared.rowMaps[0].maps[4]),
        bm: await morphism('vertical/bm', prepared.rowMaps[0].maps[5]),
        b0: await morphism('vertical/b0', prepared.rowMaps[1].maps[5]),
        b1: await morphism('vertical/b1', prepared.rowMaps[2].maps[5]),
        d1: await morphism('vertical/d1', prepared.rowMaps[2].maps[6])
    };
    const squares = [];
    for (const i of [0, 1, 2] as const) {
        const upper = algebraFormalFreydConnectingSquareBundle(prepared, i, 'upper');
        const lower = algebraFormalFreydConnectingSquareBundle(prepared, i, 'lower');
        squares.push(Object.freeze({
            upper: await ensure('map-' + i + '/upper', upper.realization.claimType, 'computed-equation', () => upper),
            lower: await ensure('map-' + i + '/lower', lower.realization.claimType, 'computed-equation', () => lower)
        }));
    }
    const upperZero = await chain('middle/upper', prepared.upper);
    const lowerZero = await chain('middle/lower', prepared.lower);
    const resultLaw = await morphism('result', prepared.result);
    const observation = algebraFormalFreydModelConnectingObservationBundle({ observationId: input.artifactId,
        source: input.modelSource, target: input.modelTarget, prepared, environment: source.environment,
        normality: input.normality, rows, vertical, squares, upperZero, lowerZero, resultLaw });
    const proof = await ensure('connecting-interpretation', observation.realization.claimType,
        'trusted-presentation-semantics', () => observation);
    assertAlgebraFormalFreydModelConnectingPreparationCurrent(prepared);
    return Object.freeze({ prepared, observation, proof, source, rows: Object.freeze(rows),
        counts: Object.freeze({ newAssumptions: source.entries.length - before, reusedClaims: reused,
            homologyReplays: 0 as const, universalReselections: 0 as const, connectingReplays: 0 as const }) });
}
