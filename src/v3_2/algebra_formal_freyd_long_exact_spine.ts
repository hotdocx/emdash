/** Downstream construction of the actual formal spine from a whole replay/adoption. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AlgebraFormalFreydLongExactAdoption, AlgebraFormalFreydLongExactDelegationBundle } from './algebra_formal_freyd_long_exact';
import { algebraFormalFreydLongExactEquations, serializeAlgebraFormalFreydLongExactEquations } from './algebra_formal_freyd_long_exact_equations';
import { algebraFormalFreydChainPairDelegationBundle, algebraFormalFreydChainPairTerm, algebraFormalFreydMorphismTerm } from './algebra_formal_freyd_chain_pair';
import { algebraFormalFreydBoundedSpineTerm } from './algebra_formal_freyd_bounded_spine';
import { FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS } from './algebra_formal_freyd_spine_signatures';
import { assertAlgebraFormalComputationResultCurrent } from './algebra_formal_adoption';
import { AlgebraFormalDelegationError } from './algebra_formal_delegation';
import { appendAlgebraFormalAssumption, validateAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { createAlgebraPolynomialFreydHomologyEngine } from './algebra_polynomial_freyd_homology_category';
import { runAlgebraFormalWorkflow, trustAlgebraFormalWorkflow } from './algebra_formal_workflow';
import { CoreProofArtifactFingerprint } from './proof_document';
import { coreProofPlanHole } from './proof_plan';
import { createCoreProofChecker } from './proof_checker';
import { KernelExpression, kernelExpressionEquals, provenance } from './kernel';

export const ALGEBRA_FORMAL_FREYD_LONG_EXACT_SPINE_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-long-exact-spine-v1' as const,
    upstream: 'one-whole-replay-and-explicit-equation-adoption' as const,
    extraReplay: 'semantic-raw-chain-pairs-only' as const,
    claimsFormalExactness: false as const,
    suppliesWeakKernelCapability: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

/** Explicit trust action for the extra semantic-composition equations only. */
export async function trustAlgebraFormalFreydLongExactSpine<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(input: {
    readonly artifactId: string;
    readonly bundle: AlgebraFormalFreydLongExactDelegationBundle<P, C, I>;
    readonly adopted: AlgebraFormalFreydLongExactAdoption<P, C, I>;
    readonly fingerprint: (goalId: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (goalId: string) => string;
}) {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.artifactId)) throw new Error('A stable formal-spine artifact ID is required');
    const upstream = input.adopted.adoption.result;
    assertAlgebraFormalComputationResultCurrent(upstream, upstream.request);
    if (upstream.request.adapter !== input.bundle.adapter) throw new AlgebraFormalDelegationError(
        'STALE_RESULT', 'freydSpine.upstream', 'The adopted result belongs to another prepared whole bundle');
    let source = validateAlgebraFormalAssumptionSource(input.adopted.source);
    for (const name of Object.keys(FORMAL_FREYD_SPINE_SIGNATURE_BINDINGS)) if (!source.environment.lookup(name)) {
        throw new Error('Prepare the source with createFormalFreydSpineProofEnvironment; missing ' + name);
    }
    const equations = algebraFormalFreydLongExactEquations({ reifier: input.bundle.reifier, selected: upstream.computed.value });
    if (serializeAlgebraFormalFreydLongExactEquations(equations) !== input.bundle.equationsData) {
        throw new AlgebraFormalDelegationError('STALE_RESULT', 'freydSpine.equations', 'The actual replay no longer matches preparation');
    }
    const whole = upstream.computed.value.result;
    const checker = createCoreProofChecker(source.environment);
    const mapLaws = whole.arrows.map((_, index) => {
        const label = 'long-exact/map/' + index;
        const equation = equations.entries.find(entry => entry.id === label);
        const binding = input.adopted.bindings.find(entry => entry.labels.includes(label));
        if (!equation || equation.kind !== 'morphism' || !binding) throw new Error('Missing adopted morphism equation ' + label);
        const entry = source.entries[binding.sourceIndex];
        if (!entry) throw new Error('Missing source entry for ' + label);
        checker.check(checker.rootContext, entry.reference, equation.realization.claimType);
        return Object.freeze({ realization: equation.realization, proof: entry.reference });
    });
    const arrows = mapLaws.map(value => algebraFormalFreydMorphismTerm(value.realization, value.proof));
    const pairTerms: KernelExpression[] = [];
    const presentations: KernelExpression[] = [];
    const semanticBindings: { readonly position: number; readonly sourceIndex: number; readonly reference: KernelExpression }[] = [];
    const stem = input.artifactId.replace(/[^A-Za-z0-9_]/gu, '_');
    for (let index = 0; index < whole.interior.length; index++) {
        const selected = whole.interior[index].pair;
        const bundle = algebraFormalFreydChainPairDelegationBundle({ reifier: input.bundle.reifier, selected });
        const target = bundle.realization.claimType;
        const goalId = input.artifactId + '-semantic-zero-' + index;
        const p = provenance('derived', 'long-exact formal spine at position ' + index);
        const run = await runAlgebraFormalWorkflow({
            document: { moduleId: source.moduleId, declarationId: goalId, environment: source.environment,
                type: target, plan: coreProofPlanHole(goalId, { provenance: p, expectation: { contextDepth: 0, target } }),
                provenance: p, fingerprint: input.fingerprint(goalId) },
            goalId, adapter: bundle.adapter, realization: bundle.realization,
            engine: createAlgebraPolynomialFreydHomologyEngine(bundle.model)
        });
        const adoption = trustAlgebraFormalWorkflow({ run, assumptionName: stem + '_semantic_zero_' + index,
            decision: { kind: 'trust-exact-algebra-computation', evidence: input.decisionEvidence(goalId) } });
        const sourceIndex = source.entries.length;
        source = appendAlgebraFormalAssumption({ source, adoption, classification: 'computed-equation' });
        const reference = source.entries[sourceIndex].reference;
        semanticBindings.push(Object.freeze({ position: index, sourceIndex, reference }));
        const pair = algebraFormalFreydChainPairTerm(bundle.realization, mapLaws[index].proof, mapLaws[index + 1].proof, reference);
        if (!kernelExpressionEquals(pair.above, arrows[index]) || !kernelExpressionEquals(pair.below, arrows[index + 1])) {
            throw new AlgebraFormalDelegationError('CLAIM_TARGET_MISMATCH', 'freydSpine.pair', 'The constructed pair changed its displayed arrows');
        }
        if (index === 0) presentations.push(...bundle.realization.presentations);
        else {
            if (!kernelExpressionEquals(presentations[index], bundle.realization.presentations[0]) ||
                !kernelExpressionEquals(presentations[index + 1], bundle.realization.presentations[1])) {
                throw new Error('Formal consecutive pairs have different selected presentation endpoints');
            }
            presentations.push(bundle.realization.presentations[2]);
        }
        pairTerms.push(pair.term);
    }
    const spine = algebraFormalFreydBoundedSpineTerm({ formalRing: input.bundle.reifier.formalRing,
        presentations, arrows, laws: pairTerms });
    const finalChecker = createCoreProofChecker(source.environment);
    finalChecker.check(finalChecker.rootContext, spine.term, spine.type);
    return Object.freeze({ profileRevision: ALGEBRA_FORMAL_FREYD_LONG_EXACT_SPINE_PROFILE.revision,
        source, native: whole, spine, arrows: Object.freeze(arrows), presentations: Object.freeze(presentations),
        pairTerms: Object.freeze(pairTerms), semanticBindings: Object.freeze(semanticBindings) });
}
