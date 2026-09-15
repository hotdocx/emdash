/** Shared native-model matrix preparation and explicit claim adoption. */
import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydActualHomologyRealization, defineAlgebraFormalFreydActualHomologyRealization } from './algebra_formal_freyd_actual_homology';
import { algebraFormalFreydNativeModelHomologyObservationBundle } from './algebra_formal_freyd_model_observation';
import { algebraFormalFreydChainPairDelegationBundle } from './algebra_formal_freyd_chain_pair';
import { algebraFormalPresentationMorphismDelegationBundle } from './algebra_formal_presentation_morphism_delegation';
import { createAlgebraTypeScriptReferenceEngine } from './algebra_reference_engine';
import { createAlgebraPolynomialFreydHomologyEngine } from './algebra_polynomial_freyd_homology_category';
import { AlgebraFormalAssumptionSource, appendAlgebraFormalAssumption, validateAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { AlgebraFormalWorkflowInput, runAlgebraFormalWorkflow, trustAlgebraFormalWorkflow } from './algebra_formal_workflow';
import { algebraFormalFreydNativeModelType, FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_model_signatures';
import { createFormalFreydNativeModelObservationProofEnvironment, FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS } from './algebra_formal_freyd_native_model_observation_signatures';
import { CoreProofArtifactFingerprint } from './proof_document';
import { coreProofPlanHole } from './proof_plan';
import { createCoreProofChecker } from './proof_checker';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { serializeCoreExpression } from './core_serialization';

import { AlgebraFormalPresentationMorphismRealization } from './algebra_formal_presentation_morphism';

export interface AlgebraFormalFreydNativeRealizationInput {
    readonly artifactId: string;
    readonly modelId: string;
    readonly formalModel: KernelExpression;
    readonly source: AlgebraFormalAssumptionSource;
    readonly fingerprint: (id: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (id: string) => string;
}

/** Local to one immutable-source workflow; callers never supply H naturality. */
export function createAlgebraFormalFreydNativeRealizationSession<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    input: AlgebraFormalFreydNativeRealizationInput, formalRing: KernelExpression
) {
    for (const id of [input.artifactId, input.modelId]) {
        if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(id)) throw new Error('A stable native homology interpretation ID is required');
    }
    let source = validateAlgebraFormalAssumptionSource(input.source);
    const expected = createFormalFreydNativeModelObservationProofEnvironment([]);
    for (const name of Object.keys({ ...FORMAL_FREYD_NATIVE_MODEL_SIGNATURE_BINDINGS, ...FORMAL_FREYD_NATIVE_MODEL_OBSERVATION_SIGNATURE_BINDINGS })) {
        const declaration = source.environment.lookup(name);
        if (!declaration || declaration.body !== undefined || !kernelExpressionEquals(declaration.type, expected.lookup(name)!.type)) {
            throw new Error('Missing or changed native model signature ' + name);
        }
    }
    const model = input.formalModel;
    if (model.tag !== 'reference' || model.namespace !== 'free' || source.environment.lookup(model.name)?.body !== undefined) {
        throw new Error('Supply a named native model input, not a reinterpretation of a defined model');
    }
    const checker = createCoreProofChecker(source.environment);
    checker.check(checker.rootContext, model, algebraFormalFreydNativeModelType(formalRing));
    const before = source.entries.length;
    const known = new Map(source.entries.map(e => [serializeCoreExpression(e.declaration.type), e.reference]));
    let reused = 0, computedEquations = 0, interpretationClaims = 0;
    const ensure = async <R, A, B>(key: string, type: KernelExpression,
        classification: 'computed-equation' | 'trusted-presentation-semantics',
        make: () => Pick<AlgebraFormalWorkflowInput<R, A, B>, 'adapter' | 'realization' | 'engine'>) => {
        const encoded = serializeCoreExpression(type), previous = known.get(encoded);
        if (previous) { reused++; return previous; }
        const goalId = (input.artifactId + '/' + key).replace(/[^A-Za-z0-9_]/gu, '_');
        const p = provenance('derived', 'native homology realization ' + goalId);
        const run = await runAlgebraFormalWorkflow({ ...make(), goalId, document: {
            moduleId: source.moduleId, declarationId: goalId, environment: source.environment, type,
            plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target: type } }),
            provenance: p, fingerprint: input.fingerprint(goalId)
        } });
        const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: goalId,
            decision: { kind: 'trust-exact-algebra-computation', evidence: input.decisionEvidence(goalId) } });
        source = appendAlgebraFormalAssumption({ source, adoption, classification });
        const proof = source.entries.at(-1)!.reference;
        known.set(encoded, proof);
        if (classification === 'computed-equation') computedEquations++; else interpretationClaims++;
        return proof;
    };
    const morphism = (key: string, value: AlgebraFormalPresentationMorphismRealization<P, C, I>) =>
        ensure(key, value.claimType, 'computed-equation', () => {
            const operation = algebraFormalPresentationMorphismDelegationBundle({ reifier: value.reifier, selected: value.selected });
            return { ...operation, engine: createAlgebraTypeScriptReferenceEngine({ id: input.artifactId + '/' + key,
                revision: 'v1', implementations: operation.operations.implementations }) };
        });
    const point = async (observationId: string, value: AlgebraFormalFreydActualHomologyRealization<P, C, I>) => {
        if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(observationId)) throw new Error('A stable native H observation ID is required');
        const actual = defineAlgebraFormalFreydActualHomologyRealization(value);
        if (actual.formalData !== value.formalData) throw new Error('Stale native homology realization');
        const checker = createCoreProofChecker(source.environment);
        checker.check(checker.rootContext, model, algebraFormalFreydNativeModelType(actual.reifier.formalRing));
        const aboveLaw = await morphism(observationId + '/above', actual.chain.above);
        const belowLaw = await morphism(observationId + '/below', actual.chain.below);
        const chainLaw = await ensure(observationId + '/chain', actual.chain.claimType, 'computed-equation', () => {
            const operation = algebraFormalFreydChainPairDelegationBundle({ reifier: actual.reifier, selected: actual.selected.pair });
            return { ...operation, engine: createAlgebraPolynomialFreydHomologyEngine(operation.model) };
        });
        const observationInput = { modelId: input.modelId, observationId, formalModel: model,
            environment: source.environment, actual, aboveLaw, belowLaw, chainLaw };
        const observation = algebraFormalFreydNativeModelHomologyObservationBundle(observationInput);
        return Object.freeze({ observation, observationInput });
    };
    return Object.freeze({ ensure, morphism, point,
        get source() { return source; },
        get counts() { return Object.freeze({ reused, computedEquations, interpretationClaims,
            newAssumptions: source.entries.length - before, homologyReplays: 0 as const, universalReselections: 0 as const }); }
    });
}
