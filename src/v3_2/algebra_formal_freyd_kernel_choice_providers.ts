/** Bind actual selected factor algorithms as explicit trusted provider semantics. */

import { AlgebraElement, AlgebraParent, sameAlgebraParent } from './algebra_parent';
import { algebraAlgorithmIdentity, defineAlgebraOperation, defineAlgebraRuntimeSchema } from './algebra_engine';
import { createAlgebraTypeScriptReferenceEngine, defineAlgebraReferenceImplementation } from './algebra_reference_engine';
import { AffineFormalPolynomialReifier } from './algebra_formal_reifier';
import { algebraFormalMatrixTerm } from './algebra_formal_finite_module';
import { defineAlgebraFormalPresentationMorphismRealization } from './algebra_formal_presentation_morphism';
import { delegateAlgebraFormalPresentationMorphismEquations } from './algebra_formal_presentation_morphism_batch';
import { algebraFormalFreydMorphismTerm } from './algebra_formal_freyd_chain_pair';
import {
    AlgebraFormalAssumptionSource, appendAlgebraFormalAssumption, validateAlgebraFormalAssumptionSource
} from './algebra_formal_assumption_source';
import { AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter } from './algebra_formal_delegation';
import { runAlgebraFormalWorkflow, trustAlgebraFormalWorkflow } from './algebra_formal_workflow';
import {
    AlgebraPolynomialFreydKernelChoiceProviders, AlgebraPolynomialSelectedWeakPullbackProvider,
    assertAlgebraPolynomialSelectedWeakPullbackProviderCurrent
} from './algebra_polynomial_selected_weak_pullback_provider';
import {
    FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS,
    createFormalFreydKernelChoiceProviderProofEnvironment
} from './algebra_formal_freyd_kernel_choice_provider_signatures';
import { FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, formalFreydSpineLanguage } from './algebra_formal_freyd_spine_signatures';
import { CoreLfScopedBuilder } from './lf_builder';
import { CoreProofArtifactFingerprint } from './proof_document';
import { coreProofPlanHole } from './proof_plan';
import { createCoreProofChecker } from './proof_checker';
import { KernelExpression, kernelExpressionEquals, kernelUniverse, provenance } from './kernel';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

export const ALGEBRA_FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-kernel-choice-providers-v1' as const,
    compatibilityClassification: 'computed-equation' as const,
    providerClassification: 'trusted-presentation-semantics' as const,
    universalLawAuthority: 'explicit-trust-in-the-bound-native-factor-algorithm' as const,
    interpretation: 'represented-native-ring-only' as const,
    finiteSamplesEstablishUniversality: false as const,
    reselectsWeakKernels: false as const,
    claimsFormalExactness: false as const,
    suppliesGlobalWeakKernels: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

type Provider<P extends AlgebraParent, C extends AlgebraElement<P>, I> = AlgebraPolynomialSelectedWeakPullbackProvider<P, C, I>;

const prepareProvider = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    reifier: AffineFormalPolynomialReifier<P, C, I>, provider: Provider<P, C, I>
) => {
    assertAlgebraPolynomialSelectedWeakPullbackProviderCurrent(provider);
    if (!sameAlgebraParent(reifier.algebra.quotient.polynomialRing, provider.ring)) {
        throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'selectedProvider.ring', 'Reifier and native provider have different rings');
    }
    if (reifier.algebra.quotient.basis.basis.length !== 0) {
        throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'selectedProvider.quotient',
            'A native polynomial provider requires the zero quotient ideal; its universal law cannot be specialized to a nonzero quotient');
    }
    const choice = provider.selected;
    const b = new CoreLfScopedBuilder(provenance('derived', 'selected weak-pullback provider matrices'));
    const L = formalFreydSpineLanguage(b);
    const ranks = [choice.left.source.rank, choice.left.target.rank, choice.right.source.rank, choice.object.rank] as const;
    const [x, y, z, k] = ranks.map(L.nat);
    const matrices = [choice.left, choice.right, choice.projectionLeft, choice.projectionRight].map(map =>
        algebraFormalMatrixTerm(reifier, map.columns, map.target.rank));
    const [a, c, p, q] = matrices.map(value => b.embed(value));
    const R = b.embed(reifier.formalRing);
    const compatibilityType = b.lower(L.equality(L.matrix(R, y, k), L.comp(R, y, x, k, a, p), L.comp(R, y, z, k, c, q)));
    const argumentsBeforeLaw = Object.freeze([reifier.formalRing, ...ranks.map(n => b.lower(L.nat(n))), ...matrices]);
    const data = serializeCoreLfWorkspaceCanonicalJson({
        provider: { id: provider.id, algorithmRevision: provider.algorithmRevision, selectionData: provider.selectionData },
        interpretation: ALGEBRA_FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_PROFILE.interpretation,
        arguments: argumentsBeforeLaw.map(value => serializeCoreExpression(value)), compatibility: serializeCoreExpression(compatibilityType)
    }, 'formalSelectedWeakPullbackProvider');
    return Object.freeze({ reifier, provider, ranks: Object.freeze(ranks), matrices: Object.freeze(matrices),
        argumentsBeforeLaw, compatibilityType, formalData: data });
};

type PreparedProvider<P extends AlgebraParent, C extends AlgebraElement<P>, I> = ReturnType<typeof prepareProvider<P, C, I>>;

const providerTerms = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    prepared: PreparedProvider<P, C, I>, compatibility: KernelExpression, evidence?: KernelExpression
) => {
    const b = new CoreLfScopedBuilder(provenance('derived', 'selected weak-pullback provider binding'));
    const L = formalFreydSpineLanguage(b);
    const args = [...prepared.argumentsBeforeLaw, compatibility].map(value => b.embed(value));
    const type = b.lower(L.tau(L.call('bridge_CommRingFiniteFreeWeakPullbackMatrixProvider', args)));
    return { type, ...(evidence === undefined ? {} : {
        whole: b.lower(L.call('bridge_comm_ring_finite_free_weak_pullback_from_matrix_provider', [...args, b.embed(evidence)])),
        factor: b.lower(L.call('bridge_comm_ring_finite_free_weak_pullback_matrix_provider_factor', [...args, b.embed(evidence)])),
        law: b.lower(L.call('bridge_comm_ring_finite_free_weak_pullback_matrix_provider_law', [...args, b.embed(evidence)]))
    }) };
};

/** A provider-binding operation returns the same executable handle, without reselection. */
const providerDelegation = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    prepared: PreparedProvider<P, C, I>, kind: 'compatibility' | 'provider', compatibility?: KernelExpression
) => {
    const current = () => {
        const rebuilt = prepareProvider(prepared.reifier, prepared.provider);
        if (rebuilt.formalData !== prepared.formalData) throw new AlgebraFormalDelegationError(
            'INVALID_REALIZATION', 'selectedProvider.current', 'Selected provider matrices or formal bindings have drifted');
    };
    current();
    const claimType = kind === 'compatibility' ? prepared.compatibilityType : providerTerms(prepared, compatibility!).type;
    const id = 'proof-cas.selected-weak-pullback/' + prepared.provider.id + '/' + kind;
    const schema = defineAlgebraRuntimeSchema<Provider<P, C, I>>({ id: id + '/handle', revision: 'v1', normalize(value) {
        if (value !== prepared.provider) throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'selectedProvider.handle', 'Foreign selected provider handle');
        current();
        return prepared.provider;
    } });
    const operation = defineAlgebraOperation({ id, revision: prepared.provider.algorithmRevision, input: schema, output: schema });
    const implementation = defineAlgebraReferenceImplementation({ operation,
        algorithm: algebraAlgorithmIdentity(id + '/bind-native-factor', prepared.provider.algorithmRevision),
        execute(value) { current(); return value; } });
    const engine = createAlgebraTypeScriptReferenceEngine({ id: id + '/engine', revision: 'v1', implementations: [implementation] });
    const realization = Object.freeze({ prepared, kind, claimType, compatibility });
    const serialize = () => serializeCoreLfWorkspaceCanonicalJson({
        formalData: prepared.formalData, kind, claim: serializeCoreExpression(claimType),
        compatibility: compatibility === undefined ? null : serializeCoreExpression(compatibility)
    }, 'selectedProviderBinding');
    const adapter = defineAlgebraFormalComputationAdapter({ id, revision: 'v1', operation,
        normalizeRealization(value: unknown) {
            if (value !== realization) throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'selectedProvider.realization', 'Foreign provider realization');
            current();
            return realization;
        },
        serializeRealization: serialize,
        acquire(goal) {
            if (!kernelExpressionEquals(goal.target, claimType)) throw new AlgebraFormalDelegationError(
                'CLAIM_TARGET_MISMATCH', 'selectedProvider.goal', 'Goal differs from the selected provider claim');
            current();
            return prepared.provider;
        },
        serializeInput: () => prepared.formalData,
        serializeOutput: value => { assertAlgebraPolynomialSelectedWeakPullbackProviderCurrent(value); return prepareProvider(prepared.reifier, value).formalData; },
        interpret: ({ goal, computed }) => {
            current();
            return computed.value === prepared.provider
                ? { kind: 'claim' as const, claimType: goal.target, summary: kind === 'compatibility'
                    ? 'selected projection matrices satisfy their checked compatibility equation'
                    : 'explicitly trust the retained native factor algorithm and its all-test semantics over the represented ring' }
                : { kind: 'observation' as const, summary: 'the selected provider handle changed' };
        }
    });
    return { realization, adapter, engine, claimType };
};

const preparations = new WeakMap<object, () => void>();

/** Prepare all coefficients before the caller fixes its proof environment. */
export function prepareAlgebraFormalFreydKernelChoiceProviders<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydKernelChoiceProviders<P, C, I>;
}) {
    input.selected.assertCurrent();
    const first = prepareProvider(input.reifier, input.selected.first);
    const second = prepareProvider(input.reifier, input.selected.second);
    const morphism = defineAlgebraFormalPresentationMorphismRealization({ reifier: input.reifier, selected: input.selected.kernel.morphism });
    const prepared = Object.freeze({ profileRevision: ALGEBRA_FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_PROFILE.revision,
        reifier: input.reifier, selected: input.selected, morphism, first, second });
    const current = () => {
        input.selected.assertCurrent();
        const firstCurrent = prepareProvider(input.reifier, input.selected.first);
        const secondCurrent = prepareProvider(input.reifier, input.selected.second);
        const map = defineAlgebraFormalPresentationMorphismRealization({ reifier: input.reifier, selected: input.selected.kernel.morphism });
        if (!kernelExpressionEquals(map.claimType, morphism.claimType) ||
            map.selectedOutputData !== morphism.selectedOutputData ||
            firstCurrent.formalData !== first.formalData || secondCurrent.formalData !== second.formalData) {
            throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'selectedChoices.prepared', 'Selected kernel provider preparation has drifted');
        }
    };
    preparations.set(prepared, current);
    return prepared;
}

export type AlgebraFormalFreydKernelChoiceProvidersPreparation<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof prepareAlgebraFormalFreydKernelChoiceProviders<P, C, I>>;

/** Universal provider assumptions are separately classified from compatibility equations. */
export async function trustAlgebraFormalFreydKernelChoiceProviders<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly artifactId: string;
    readonly prepared: AlgebraFormalFreydKernelChoiceProvidersPreparation<P, C, I>;
    readonly source: AlgebraFormalAssumptionSource;
    readonly fingerprint: (goalId: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (goalId: string) => string;
}) {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.artifactId)) throw new Error('A stable selected-provider artifact ID is required');
    const current = preparations.get(input.prepared);
    if (!current) throw new AlgebraFormalDelegationError('INVALID_REALIZATION', 'selectedChoices.prepared', 'Use the issued whole selected-provider preparation');
    current();
    const prepared = input.prepared;
    let source = validateAlgebraFormalAssumptionSource(input.source);
    const expected = createFormalFreydKernelChoiceProviderProofEnvironment([]);
    for (const name of Object.keys({ ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS })) {
        const actual = source.environment.lookup(name);
        if (!actual || !kernelExpressionEquals(actual.type, expected.lookup(name)!.type)) throw new Error('Missing or changed selected-provider signature ' + name);
    }
    const p = provenance('derived', 'actual selected kernel choices');
    const checker = createCoreProofChecker(source.environment);
    for (const claim of [prepared.morphism.claimType, prepared.first.compatibilityType, prepared.second.compatibilityType]) {
        checker.check(checker.rootContext, claim, kernelUniverse(p));
    }
    let morphismIndex = source.entries.findIndex(entry => kernelExpressionEquals(entry.declaration.type, prepared.morphism.claimType));
    if (morphismIndex < 0) {
        morphismIndex = source.entries.length;
        source = (await delegateAlgebraFormalPresentationMorphismEquations({ artifactId: input.artifactId + '-morphism',
            reifier: prepared.reifier, morphisms: [prepared.selected.kernel.morphism], agreements: [], chainSquares: [],
            source, fingerprint: input.fingerprint, decisionEvidence: input.decisionEvidence })).source;
    }
    const morphismLaw = source.entries[morphismIndex].reference;
    const stem = input.artifactId.replace(/[^A-Za-z0-9_]/gu, '_');
    const bindings: { readonly compatibility: KernelExpression; readonly provider: KernelExpression;
        readonly compatibilityIndex: number; readonly providerIndex: number }[] = [];
    for (const [index, selected] of [prepared.first, prepared.second].entries()) {
        current();
        let compatibility: KernelExpression | undefined;
        let compatibilityIndex = -1;
        for (const kind of ['compatibility', 'provider'] as const) {
            const delegation = providerDelegation(selected, kind, compatibility);
            const goalId = input.artifactId + '-' + index + '-' + kind;
            const run = await runAlgebraFormalWorkflow({ document: { moduleId: source.moduleId, declarationId: goalId,
                environment: source.environment, type: delegation.claimType, plan: coreProofPlanHole(goalId,
                    { provenance: p, expectation: { contextDepth: 0, target: delegation.claimType } }), provenance: p,
                fingerprint: input.fingerprint(goalId) }, goalId, ...delegation });
            current();
            const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: stem + '_' + index + '_' + kind,
                decision: { kind: 'trust-exact-algebra-computation', evidence: input.decisionEvidence(goalId) } });
            const sourceIndex = source.entries.length;
            source = appendAlgebraFormalAssumption({ source, adoption, classification: kind === 'compatibility'
                ? 'computed-equation' : 'trusted-presentation-semantics' });
            if (kind === 'compatibility') { compatibility = source.entries[sourceIndex].reference; compatibilityIndex = sourceIndex; }
            else bindings.push(Object.freeze({ compatibility: compatibility!, provider: source.entries[sourceIndex].reference,
                compatibilityIndex, providerIndex: sourceIndex }));
        }
    }
    current();
    const b = new CoreLfScopedBuilder(p);
    const L = formalFreydSpineLanguage(b);
    const map = prepared.selected.kernel.morphism;
    const ranks = [map.source.ambient.rank, map.source.relations.generators.length, map.target.ambient.rank, map.target.relations.generators.length];
    const R = b.embed(prepared.reifier.formalRing);
    const mapArgs = [R, ...ranks.map(L.nat), ...[prepared.morphism.formalSourceRelations, prepared.morphism.formalTargetRelations,
        prepared.morphism.formalMap, prepared.morphism.formalRelationWitness, morphismLaw].map(value => b.embed(value))];
    const stageArgs = [prepared.first, prepared.second].flatMap((stage, index) => [L.nat(stage.ranks[3]),
        ...[stage.matrices[2], stage.matrices[3], bindings[index].compatibility, bindings[index].provider].map(value => b.embed(value))]);
    const term = b.lower(L.call('bridge_comm_ring_freyd_kernel_choices_from_matrix_providers', [...mapArgs, ...stageArgs]));
    const morphism = algebraFormalFreydMorphismTerm(prepared.morphism, morphismLaw);
    const type = b.lower(L.tau(L.call('bridge_CommRingFreydKernelChoices', [R,
        L.presentation(R, L.nat(ranks[0]), L.nat(ranks[1]), b.embed(prepared.morphism.formalSourceRelations)),
        L.presentation(R, L.nat(ranks[2]), L.nat(ranks[3]), b.embed(prepared.morphism.formalTargetRelations)), b.embed(morphism)], 3)));
    const finalChecker = createCoreProofChecker(source.environment);
    finalChecker.check(finalChecker.rootContext, term, type);
    return Object.freeze({ profileRevision: prepared.profileRevision, source, native: prepared.selected.kernel,
        prepared, term, type, morphism, morphismLaw, bindings: Object.freeze(bindings),
        first: Object.freeze(providerTerms(prepared.first, bindings[0].compatibility, bindings[0].provider)),
        second: Object.freeze(providerTerms(prepared.second, bindings[1].compatibility, bindings[1].provider)) });
}
