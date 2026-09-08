/** Formal epicity of every retained interior boundary after one whole replay. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydLongExactAdoption, AlgebraFormalFreydLongExactDelegationBundle, ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE } from './algebra_formal_freyd_long_exact';
import { algebraFormalFreydLongExactEquations, serializeAlgebraFormalFreydLongExactEquations } from './algebra_formal_freyd_long_exact_equations';
import { algebraFormalFreydEpimorphismBlockDelegationBundle, algebraFormalFreydEpimorphismTerm } from './algebra_formal_freyd_epimorphism';
import { FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS, createFormalFreydEpimorphismProofEnvironment } from './algebra_formal_freyd_epimorphism_signatures';
import { FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS } from './algebra_formal_freyd_spine_signatures';
import { AlgebraPolynomialFreydLongExactSnakeReferences } from './algebra_polynomial_freyd_long_exact_reference_operations';
import { AlgebraPolynomialPresentationMorphism } from './algebra_polynomial_presentation_morphism';
import { createAlgebraPolynomialFreydAbelianEngine } from './algebra_polynomial_freyd_abelian_category';
import { assertAlgebraFormalComputationResultCurrent } from './algebra_formal_adoption';
import { AlgebraFormalDelegationError } from './algebra_formal_delegation';
import { appendAlgebraFormalAssumption, validateAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { delegateAlgebraFormalPresentationMorphismEquations } from './algebra_formal_presentation_morphism_batch';
import { runAlgebraFormalWorkflow, trustAlgebraFormalWorkflow } from './algebra_formal_workflow';
import { CoreProofArtifactFingerprint } from './proof_document';
import { coreProofPlanHole } from './proof_plan';
import { createCoreProofChecker } from './proof_checker';
import { KernelExpression, kernelExpressionEquals, kernelUniverse, provenance } from './kernel';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';

export const ALGEBRA_FORMAL_FREYD_LONG_EXACT_EPIMORPHISMS_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-long-exact-boundary-epimorphisms-v1' as const,
    upstream: 'one-whole-replay-and-explicit-equation-adoption' as const,
    extraReplay: 'missing-boundary-relation-equations-and-epimorphism-blocks' as const,
    replaysHomologyPerWitness: false as const,
    claimsFormalChainExactness: false as const,
    suppliesWeakKernelCapability: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

const prepareEntries = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    bundle: AlgebraFormalFreydLongExactDelegationBundle<P, C, I>, selected: AlgebraPolynomialFreydLongExactSnakeReferences<P, C, I>
) => Object.freeze(selected.result.interior.map(point => {
    const homology = point.exactness.homology;
    const epimorphism = point.exactness.epimorphism;
    if (!point.exactness.exact || !epimorphism || homology.pair !== point.pair ||
        epimorphism.morphism !== homology.boundaryMorphism || homology.boundaryMorphism.target !== homology.cycleObject ||
        point.pair.dNext !== selected.result.arrows[point.term.position - 1] || point.pair.d !== selected.result.arrows[point.term.position]) {
        throw new Error('Each boundary epimorphism must retain its actual interior homology and displayed pair');
    }
    const label = 'long-exact/boundary-epic/' + point.term.position;
    return Object.freeze({ label, position: point.term.position, degree: point.term.degree, role: point.term.role,
        point, homology, boundary: homology.boundaryMorphism, epimorphism,
        block: algebraFormalFreydEpimorphismBlockDelegationBundle({ reifier: bundle.reifier, selected: epimorphism }) });
}));

const entriesData = (entries: readonly { readonly label: string; readonly position: number; readonly degree: number; readonly role: string;
    readonly block: { readonly realization: { readonly formalData: string } } }[]) => serializeCoreLfWorkspaceCanonicalJson(
    entries.map(entry => ({ label: entry.label, position: entry.position, degree: entry.degree, role: entry.role,
        formalData: entry.block.realization.formalData })), 'formalFreydLongExactBoundaryEpimorphisms');

/** Reify every boundary and both blocks before fixing the coefficient environment. */
export function prepareAlgebraFormalFreydLongExactEpimorphisms<P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    bundle: AlgebraFormalFreydLongExactDelegationBundle<P, C, I>
) {
    const entries = prepareEntries(bundle, bundle.selected);
    return Object.freeze({ profileRevision: ALGEBRA_FORMAL_FREYD_LONG_EXACT_EPIMORPHISMS_PROFILE.revision,
        upstreamBundle: bundle, upstreamEquationsData: bundle.equationsData, entries, entriesData: entriesData(entries) });
}

export type AlgebraFormalFreydLongExactEpimorphismsPreparation<P extends AlgebraParent, C extends AlgebraElement<P>, I> =
    ReturnType<typeof prepareAlgebraFormalFreydLongExactEpimorphisms<P, C, I>>;

/** Explicit adoption extends the original source; the whole homology is never rerun here. */
export async function trustAlgebraFormalFreydLongExactEpimorphisms<P extends AlgebraParent, C extends AlgebraElement<P>, I>(input: {
    readonly artifactId: string;
    readonly prepared: AlgebraFormalFreydLongExactEpimorphismsPreparation<P, C, I>;
    readonly adopted: AlgebraFormalFreydLongExactAdoption<P, C, I>;
    readonly fingerprint: (goalId: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (goalId: string) => string;
}) {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.artifactId)) throw new Error('A stable boundary-epimorphism artifact ID is required');
    if (input.prepared.profileRevision !== ALGEBRA_FORMAL_FREYD_LONG_EXACT_EPIMORPHISMS_PROFILE.revision ||
        input.adopted.profileRevision !== ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE.revision) {
        throw new Error('Foreign boundary-epimorphism or upstream adoption profile');
    }
    const bundle = input.prepared.upstreamBundle;
    const upstream = input.adopted.adoption.result;
    if (upstream.request.adapter !== bundle.adapter) throw new AlgebraFormalDelegationError(
        'STALE_RESULT', 'longExactEpimorphisms.upstream', 'The adopted whole result belongs to another prepared bundle');
    let source = validateAlgebraFormalAssumptionSource(input.adopted.source);
    if (!source.entries.some(entry => entry.adoption === input.adopted.adoption)) {
        throw new Error('The source must retain the original whole-replay adoption');
    }
    const expectedEnvironment = createFormalFreydEpimorphismProofEnvironment([]);
    for (const name of Object.keys({ ...FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS, ...FORMAL_FREYD_EPIMORPHISM_SIGNATURE_BINDINGS })) {
        const actual = source.environment.lookup(name);
        if (!actual || !kernelExpressionEquals(actual.type, expectedEnvironment.lookup(name)!.type)) {
            throw new Error('Prepare the source with createFormalFreydEpimorphismProofEnvironment; missing or changed ' + name);
        }
    }
    assertAlgebraFormalComputationResultCurrent(upstream, upstream.request);
    const equations = algebraFormalFreydLongExactEquations({ reifier: bundle.reifier, selected: upstream.computed.value });
    if (serializeAlgebraFormalFreydLongExactEquations(equations) !== bundle.equationsData ||
        input.prepared.upstreamEquationsData !== bundle.equationsData ||
        serializeAlgebraFormalFreydLongExactEquations(input.adopted.equations) !== bundle.equationsData) {
        throw new AlgebraFormalDelegationError('STALE_RESULT', 'longExactEpimorphisms.equations', 'The whole replay or adopted inventory has drifted');
    }
    // Fresh bundles use the actual replay objects, not mutable prepared aliases.
    const entries = prepareEntries(bundle, upstream.computed.value);
    if (entriesData(entries) !== input.prepared.entriesData || entriesData(input.prepared.entries) !== input.prepared.entriesData) {
        throw new AlgebraFormalDelegationError('STALE_RESULT', 'longExactEpimorphisms.boundaries', 'Prepared boundary labels, objects, or blocks have drifted');
    }
    const p = provenance('derived', 'formal whole long-exact boundary epimorphisms');
    const checker = createCoreProofChecker(source.environment);
    entries.forEach(entry => {
        checker.check(checker.rootContext, entry.block.realization.claimType, kernelUniverse(p));
        checker.check(checker.rootContext, entry.block.realization.morphism.claimType, kernelUniverse(p));
    });
    const missing: AlgebraPolynomialPresentationMorphism<P, C, I>[] = [];
    const pending = new Map<string, number>();
    const mapPositions = entries.map(entry => {
        const target = entry.block.realization.morphism.claimType;
        const existing = source.entries.findIndex(value => kernelExpressionEquals(value.declaration.type, target));
        if (existing >= 0) return { sourceIndex: existing };
        const key = serializeCoreExpression(target);
        let index = pending.get(key);
        if (index === undefined) {
            index = missing.length;
            pending.set(key, index);
            missing.push(entry.boundary);
        }
        return { missingIndex: index };
    });
    const beforeBoundaryLaws = source.entries.length;
    if (missing.length > 0) {
        source = (await delegateAlgebraFormalPresentationMorphismEquations({
            artifactId: input.artifactId + '-boundary-laws', reifier: bundle.reifier, morphisms: missing,
            agreements: [], chainSquares: [], source, fingerprint: input.fingerprint, decisionEvidence: input.decisionEvidence
        })).source;
    }
    const stem = input.artifactId.replace(/[^A-Za-z0-9_]/gu, '_');
    const witnesses: { readonly label: string; readonly position: number; readonly degree: number; readonly role: 'A' | 'B' | 'C';
        readonly point: (typeof entries)[number]['point']; readonly homology: (typeof entries)[number]['homology'];
        readonly boundary: (typeof entries)[number]['boundary']; readonly epimorphism: (typeof entries)[number]['epimorphism'];
        readonly constructed: ReturnType<typeof algebraFormalFreydEpimorphismTerm<P, C, I>>;
        readonly morphismBinding: { readonly label: string; readonly sourceIndex: number; readonly reference: KernelExpression; readonly reused: boolean };
        readonly blockBinding: { readonly label: string; readonly sourceIndex: number; readonly reference: KernelExpression } }[] = [];
    for (let index = 0; index < entries.length; index++) {
        const entry = entries[index];
        const location = mapPositions[index];
        const mapSourceIndex = location.sourceIndex ?? beforeBoundaryLaws + location.missingIndex!;
        const mapReference = source.entries[mapSourceIndex].reference;
        const target = entry.block.realization.claimType;
        const goalId = input.artifactId + '-block-' + entry.position;
        const run = await runAlgebraFormalWorkflow({ document: { moduleId: source.moduleId, declarationId: goalId,
            environment: source.environment, type: target, plan: coreProofPlanHole(goalId,
                { provenance: p, expectation: { contextDepth: 0, target } }), provenance: p, fingerprint: input.fingerprint(goalId) },
            goalId, adapter: entry.block.adapter, realization: entry.block.realization,
            engine: createAlgebraPolynomialFreydAbelianEngine(entry.block.model) });
        const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: stem + '_block_' + entry.position,
            decision: { kind: 'trust-exact-algebra-computation', evidence: input.decisionEvidence(entry.label + '/block') } });
        const blockSourceIndex = source.entries.length;
        source = appendAlgebraFormalAssumption({ source, adoption, classification: 'computed-equation' });
        const blockReference = source.entries[blockSourceIndex].reference;
        const constructed = algebraFormalFreydEpimorphismTerm(entry.block.realization, mapReference, blockReference);
        const finalChecker = createCoreProofChecker(source.environment);
        finalChecker.check(finalChecker.rootContext, constructed.term, constructed.type);
        witnesses.push(Object.freeze({ label: entry.label, position: entry.position, degree: entry.degree, role: entry.role,
            point: entry.point, homology: entry.homology, boundary: entry.boundary, epimorphism: entry.epimorphism, constructed,
            morphismBinding: Object.freeze({ label: entry.label + '/relation', sourceIndex: mapSourceIndex, reference: mapReference,
                reused: location.sourceIndex !== undefined }),
            blockBinding: Object.freeze({ label: entry.label + '/block', sourceIndex: blockSourceIndex, reference: blockReference }) }));
    }
    return Object.freeze({ profileRevision: ALGEBRA_FORMAL_FREYD_LONG_EXACT_EPIMORPHISMS_PROFILE.revision,
        source, native: upstream.computed.value.result, upstreamAdoption: input.adopted, witnesses: Object.freeze(witnesses),
        counts: Object.freeze({ boundaries: entries.length, reusedBoundaryLaws: mapPositions.filter(value => value.sourceIndex !== undefined).length,
            newBoundaryLaws: missing.length, newBlockLaws: entries.length, wholeHomologyReplays: 0 as const }) });
}
