/** Formal selected homology and exactness at every actual long-exact interior. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydLongExactAdoption, AlgebraFormalFreydLongExactDelegationBundle, ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE } from './algebra_formal_freyd_long_exact';
import { AlgebraPolynomialFreydLongExactSnakeReferences } from './algebra_polynomial_freyd_long_exact_reference_operations';
import { createAlgebraPolynomialFreydKernelChoiceProviders } from './algebra_polynomial_selected_weak_pullback_provider';
import { prepareAlgebraFormalFreydKernelChoiceProviders, trustAlgebraFormalFreydKernelChoiceProviders } from './algebra_formal_freyd_kernel_choice_providers';
import { algebraFormalFreydActualHomologyReconstructionBundle, algebraFormalFreydActualHomologyTerm, defineAlgebraFormalFreydActualHomologyRealization } from './algebra_formal_freyd_actual_homology';
import { prepareAlgebraFormalFreydLongExactEpimorphisms, trustAlgebraFormalFreydLongExactEpimorphisms } from './algebra_formal_freyd_long_exact_epimorphisms';
import { trustAlgebraFormalFreydLongExactSpine } from './algebra_formal_freyd_long_exact_spine';
import { algebraFormalFreydLongExactEquations, serializeAlgebraFormalFreydLongExactEquations } from './algebra_formal_freyd_long_exact_equations';
import { assertAlgebraFormalComputationResultCurrent } from './algebra_formal_adoption';
import { validateAlgebraFormalAssumptionSource, appendAlgebraFormalAssumption } from './algebra_formal_assumption_source';
import { AlgebraFormalDelegationError } from './algebra_formal_delegation';
import { runAlgebraFormalWorkflow, trustAlgebraFormalWorkflow } from './algebra_formal_workflow';
import { FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS } from './algebra_formal_freyd_spine_signatures';
import { FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS } from './algebra_formal_freyd_epimorphism_signatures';
import { FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS } from './algebra_formal_freyd_kernel_choice_provider_signatures';
import { createFormalFreydActualHomologyProofEnvironment, FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS } from './algebra_formal_freyd_actual_homology_signatures';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';
import { CoreProofArtifactFingerprint } from './proof_document';
import { coreProofPlanHole } from './proof_plan';
import { createCoreProofChecker } from './proof_checker';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

export const ALGEBRA_FORMAL_FREYD_LONG_EXACT_HOMOLOGY_PROFILE = Object.freeze({
    revision: 'emdash-formal-long-exact-actual-interior-homology-v1' as const,
    input: 'one-retained-whole-replay-and-adoption' as const,
    exactness: 'constructed-at-every-actual-interior-boundary' as const,
    universalAuthority: 'explicit-selected-native-provider-semantics' as const,
    replaysWholeHomology: false as const,
    suppliesGlobalWeakKernels: false as const,
    claimsGenericLongExactTheorem: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

const prepareEntries = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    bundle: AlgebraFormalFreydLongExactDelegationBundle<P, C, I>, value: AlgebraPolynomialFreydLongExactSnakeReferences<P, C, I>
) => Object.freeze(value.result.interior.map((point, index) => {
    if (point.term.position !== index + 1 || point.term !== value.result.terms[index + 1] ||
        point.pair.dNext !== value.result.arrows[index] || point.pair.d !== value.result.arrows[index + 1] ||
        point.exactness.homology.pair !== point.pair || !point.exactness.exact ||
        point.exactness.epimorphism?.morphism !== point.exactness.homology.boundaryMorphism) {
        throw new Error('Formal interior exactness must use the actual displayed pair, homology and boundary');
    }
    const label = 'long-exact/interior-homology/' + point.term.position;
    const providers = prepareAlgebraFormalFreydKernelChoiceProviders({ reifier: bundle.reifier,
        selected: createAlgebraPolynomialFreydKernelChoiceProviders({ id: label, ring: value.result.sequence.ring,
            kernel: point.exactness.homology.cycles }) });
    const reconstruction = algebraFormalFreydActualHomologyReconstructionBundle({ reifier: bundle.reifier,
        selected: point.exactness.homology, providers });
    return Object.freeze({ label, position: point.term.position, degree: point.term.degree, role: point.term.role,
        point, providers, reconstruction });
}));

const entriesData = (entries: readonly { readonly label: string; readonly position: number; readonly degree: number;
    readonly role: string; readonly reconstruction: { readonly realization: { readonly formalData: string } } }[]) =>
    serializeCoreLfWorkspaceCanonicalJson(entries.map(entry => ({ label: entry.label, position: entry.position,
        degree: entry.degree, role: entry.role, formalData: entry.reconstruction.realization.formalData })), 'formalLongExactActualHomologies');

const preparations = new WeakMap<object, () => void>();

/** Fix all matrix/coefficient bindings before constructing the proof environment. */
export function prepareAlgebraFormalFreydLongExactHomology<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    bundle: AlgebraFormalFreydLongExactDelegationBundle<P, C, I>
) {
    const entries = prepareEntries(bundle, bundle.selected);
    const epicities = prepareAlgebraFormalFreydLongExactEpimorphisms(bundle);
    const snapshot = entriesData(entries);
    const prepared = Object.freeze({ profileRevision: ALGEBRA_FORMAL_FREYD_LONG_EXACT_HOMOLOGY_PROFILE.revision,
        bundle, upstreamEquationsData: bundle.equationsData, entries, entriesData: snapshot, epicities });
    preparations.set(prepared, () => {
        if (prepared.upstreamEquationsData !== bundle.equationsData || entriesData(entries) !== snapshot) {
            throw new AlgebraFormalDelegationError('STALE_RESULT', 'actualHomologies.prepared', 'The prepared whole or labelled inventory changed');
        }
        entries.forEach(entry => {
            const current = defineAlgebraFormalFreydActualHomologyRealization(entry.reconstruction.realization);
            if (current.formalData !== entry.reconstruction.realization.formalData) throw new AlgebraFormalDelegationError(
                'STALE_RESULT', 'actualHomologies.prepared', 'A retained homology or selected provider changed');
        });
    });
    return prepared;
}

export type AlgebraFormalFreydLongExactHomologyPreparation<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof prepareAlgebraFormalFreydLongExactHomology<P, C, I>>;

/** Extend one source with actual interior homologies and their already witnessed exactness. */
export async function trustAlgebraFormalFreydLongExactHomology<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly artifactId: string;
    readonly prepared: AlgebraFormalFreydLongExactHomologyPreparation<P, C, I>;
    readonly adopted: AlgebraFormalFreydLongExactAdoption<P, C, I>;
    readonly fingerprint: (goalId: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (goalId: string) => string;
}) {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.artifactId)) throw new Error('A stable actual-homology artifact ID is required');
    const current = preparations.get(input.prepared);
    if (!current) throw new Error('Use the issued whole actual-homology preparation');
    current();
    if (input.adopted.profileRevision !== ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE.revision) throw new Error('Foreign whole-adoption profile');
    const bundle = input.prepared.bundle;
    const upstream = input.adopted.adoption.result;
    if (upstream.request.adapter !== bundle.adapter) throw new AlgebraFormalDelegationError(
        'STALE_RESULT', 'actualHomologies.upstream', 'Adoption belongs to another whole replay');
    assertAlgebraFormalComputationResultCurrent(upstream, upstream.request);
    let source = validateAlgebraFormalAssumptionSource(input.adopted.source);
    if (!source.entries.some(entry => entry.adoption === input.adopted.adoption)) throw new Error('Source is missing the original whole adoption');
    const expected = createFormalFreydActualHomologyProofEnvironment([]);
    for (const name of Object.keys({ ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS,
        ...FORMAL_FREYD_KERNEL_CHOICE_PROVIDER_SIGNATURE_BINDINGS, ...FORMAL_FREYD_ACTUAL_HOMOLOGY_SIGNATURE_BINDINGS })) {
        const declaration = source.environment.lookup(name);
        if (!declaration || declaration.body !== undefined || declaration.transparency !== 'opaque' ||
            !kernelExpressionEquals(declaration.type, expected.lookup(name)!.type)) throw new Error('Missing or changed actual-homology signature ' + name);
    }
    const equations = algebraFormalFreydLongExactEquations({ reifier: bundle.reifier, selected: upstream.computed.value });
    if (serializeAlgebraFormalFreydLongExactEquations(equations) !== input.prepared.upstreamEquationsData ||
        serializeAlgebraFormalFreydLongExactEquations(input.adopted.equations) !== input.prepared.upstreamEquationsData) {
        throw new AlgebraFormalDelegationError('STALE_RESULT', 'actualHomologies.equations', 'The actual replay differs from its adopted inventory');
    }
    const entries = prepareEntries(bundle, upstream.computed.value);
    if (entriesData(entries) !== input.prepared.entriesData) throw new AlgebraFormalDelegationError(
        'STALE_RESULT', 'actualHomologies.entries', 'Actual replay homologies differ from their prepared choices');
    const before = source.entries.length;
    const spine = await trustAlgebraFormalFreydLongExactSpine({ artifactId: input.artifactId + '-spine', bundle,
        adopted: input.adopted, fingerprint: input.fingerprint, decisionEvidence: input.decisionEvidence });
    const epicities = await trustAlgebraFormalFreydLongExactEpimorphisms({ artifactId: input.artifactId + '-epicities',
        prepared: input.prepared.epicities, adopted: Object.freeze({ ...input.adopted, source: spine.source }),
        fingerprint: input.fingerprint, decisionEvidence: input.decisionEvidence });
    source = epicities.source;
    const results: { readonly label: string; readonly position: number; readonly degree: number; readonly role: 'A' | 'B' | 'C';
        readonly point: (typeof entries)[number]['point'];
        readonly providers: Awaited<ReturnType<typeof trustAlgebraFormalFreydKernelChoiceProviders<P, C, I>>>;
        readonly constructed: ReturnType<typeof algebraFormalFreydActualHomologyTerm<P, C, I>>;
        readonly reconstruction: KernelExpression }[] = [];
    const mapLaw = (index: number, type: KernelExpression) => {
        const label = 'long-exact/map/' + index;
        const binding = input.adopted.bindings.find(entry => entry.labels.includes(label));
        if (!binding || !source.entries[binding.sourceIndex]) throw new Error('Missing displayed-map law ' + label);
        const reference = source.entries[binding.sourceIndex].reference;
        const checker = createCoreProofChecker(source.environment);
        checker.check(checker.rootContext, reference, type);
        return reference;
    };
    for (let index = 0; index < entries.length; index++) {
        const entry = entries[index];
        const providers = await trustAlgebraFormalFreydKernelChoiceProviders({ artifactId: input.artifactId + '-providers-' + entry.position,
            prepared: entry.providers, source, fingerprint: input.fingerprint, decisionEvidence: input.decisionEvidence });
        source = providers.source;
        const realization = entry.reconstruction.realization;
        let reconstruction = source.entries.find(value => kernelExpressionEquals(value.declaration.type, realization.claimType))?.reference;
        if (!reconstruction) {
            const goalId = input.artifactId + '-reconstruction-' + entry.position;
            const p = provenance('derived', 'actual interior reconstruction ' + entry.position);
            const run = await runAlgebraFormalWorkflow({ ...entry.reconstruction, goalId, document: {
                moduleId: source.moduleId, declarationId: goalId, environment: source.environment, type: realization.claimType,
                plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target: realization.claimType } }),
                provenance: p, fingerprint: input.fingerprint(goalId)
            } });
            const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: goalId.replace(/[^A-Za-z0-9_]/gu, '_'),
                decision: { kind: 'trust-exact-algebra-computation', evidence: input.decisionEvidence(goalId) } });
            source = appendAlgebraFormalAssumption({ source, adoption, classification: 'computed-equation' });
            reconstruction = source.entries[source.entries.length - 1].reference;
        }
        const epic = epicities.witnesses[index];
        if (epic.point !== entry.point || epic.homology !== entry.point.exactness.homology || epic.position !== entry.position) {
            throw new Error('The boundary epicity belongs to another interior homology');
        }
        const constructed = algebraFormalFreydActualHomologyTerm(realization, { providers,
            aboveLaw: mapLaw(index, realization.chain.above.claimType), belowLaw: mapLaw(index + 1, realization.chain.below.claimType),
            chain: spine.pairTerms[index], boundaryLaw: epic.morphismBinding.reference, reconstructionLaw: reconstruction,
            epic: epic.constructed.term });
        if (!kernelExpressionEquals(constructed.above, spine.arrows[index]) || !kernelExpressionEquals(constructed.below, spine.arrows[index + 1]) ||
            !kernelExpressionEquals(constructed.boundary, epic.constructed.morphism)) throw new Error('Actual homology construction changed a retained raw arrow');
        const checker = createCoreProofChecker(source.environment);
        checker.check(checker.rootContext, constructed.term, constructed.type);
        checker.check(checker.rootContext, constructed.exactness, constructed.exactnessType);
        results.push(Object.freeze({ label: entry.label, position: entry.position, degree: entry.degree, role: entry.role,
            point: entry.point, providers, constructed, reconstruction }));
    }
    current();
    assertAlgebraFormalComputationResultCurrent(upstream, upstream.request);
    return Object.freeze({ profileRevision: ALGEBRA_FORMAL_FREYD_LONG_EXACT_HOMOLOGY_PROFILE.revision,
        source, native: upstream.computed.value.result, upstreamAdoption: input.adopted, spine, epicities,
        interiors: Object.freeze(results), counts: Object.freeze({ positions: results.length,
            newAssumptions: source.entries.length - before, wholeHomologyReplays: 0 as const, weakKernelReselections: 0 as const }) });
}
