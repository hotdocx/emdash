/** One whole categorical replay followed by explicit selected-equation adoption. */

import { AlgebraElement, AlgebraParent } from './algebra_parent';
import { AffineFormalPolynomialReifier } from './algebra_formal_reifier';
import {
    AlgebraFormalDelegationError, defineAlgebraFormalComputationAdapter
} from './algebra_formal_delegation';
import { assertAlgebraFormalComputationResultCurrent } from './algebra_formal_adoption';
import {
    AlgebraFormalWorkflowRun, createAlgebraFormalWorkflowReceipt, trustAlgebraFormalWorkflow
} from './algebra_formal_workflow';
import {
    AlgebraFormalAssumptionSource, appendAlgebraFormalAssumption, serializeAlgebraFormalAssumptionSource
} from './algebra_formal_assumption_source';
import { delegateAlgebraFormalPresentationMorphismEquations } from './algebra_formal_presentation_morphism_batch';
import {
    AlgebraPolynomialPresentationMorphism, AlgebraPolynomialPresentationMorphismAgreement
} from './algebra_polynomial_presentation_morphism';
import {
    AlgebraFormalFreydLongExactEquations, algebraFormalFreydLongExactEquations,
    serializeAlgebraFormalFreydLongExactEquations
} from './algebra_formal_freyd_long_exact_equations';
import {
    AlgebraPolynomialFreydBoundedShortExactInput, AlgebraPolynomialFreydLongExactSnakeReferences,
    serializeAlgebraPolynomialFreydLongExactSnakeReferences
} from './algebra_polynomial_freyd_long_exact_reference_operations';
import {
    algebraPolynomialFreydLongExactCategoryModel, compileAlgebraPolynomialFreydLongExactProgram,
    createAlgebraPolynomialFreydLongExactEngine
} from './algebra_polynomial_freyd_long_exact_category';
import { createCategoricalProgramBuilder } from './algebra_categorical_program';
import { executeAlgebraComputationGraph } from './algebra_graph';
import { algebraAlgorithmIdentity, defineAlgebraOperation } from './algebra_engine';
import { createAlgebraTypeScriptReferenceEngine, defineAlgebraReferenceImplementation } from './algebra_reference_engine';
import {
    serializeAlgebraPolynomialFreydBoundedComplex, serializeAlgebraPolynomialFreydBoundedChainMap
} from './algebra_polynomial_freyd_bounded_short_exact_serialization';
import { KernelExpression, kernelExpressionEquals } from './kernel';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import { CoreProofArtifactFingerprint } from './proof_document';
import { encodeAlgebraFormalFreydLongExactData } from './algebra_formal_freyd_long_exact_encoding';

export const ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE = Object.freeze({
    revision: 'emdash-formal-freyd-long-exact-v1' as const,
    replay: 'one-whole-categorical-graph' as const,
    encoding: 'lossless-selected-data-table-v1' as const,
    adoption: 'explicit-unique-computed-equations' as const,
    genericReusePolicyChanged: false as const,
    claimsGenericFormalExactness: false as const,
    claimsQuotientPathDecoding: false as const,
    addsCoreOwner: false as const,
    performsIo: false as const
});

export interface AlgebraFormalFreydLongExactRealization<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> {
    readonly profileRevision: typeof ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE.revision;
    readonly equations: AlgebraFormalFreydLongExactEquations<P, C, I>;
    readonly anchorId: string;
    readonly claimType: KernelExpression;
}

const serializeInput = <P extends AlgebraParent, C extends AlgebraElement<P>, I>(
    value: AlgebraPolynomialFreydBoundedShortExactInput<P, C, I>
) => serializeCoreLfWorkspaceCanonicalJson({
    subcomplex: serializeAlgebraPolynomialFreydBoundedComplex(value.subcomplex),
    middleComplex: serializeAlgebraPolynomialFreydBoundedComplex(value.middleComplex),
    quotientComplex: serializeAlgebraPolynomialFreydBoundedComplex(value.quotientComplex),
    inclusion: serializeAlgebraPolynomialFreydBoundedChainMap(value.inclusion),
    projection: serializeAlgebraPolynomialFreydBoundedChainMap(value.projection)
}, 'formalFreydLongExactInput');

/** Prepare all claim types before constructing the caller's coefficient environment. */
export function algebraFormalFreydLongExactDelegationBundle<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(input: {
    readonly reifier: AffineFormalPolynomialReifier<P, C, I>;
    readonly selected: AlgebraPolynomialFreydLongExactSnakeReferences<P, C, I>;
    readonly anchorId?: string;
}) {
    const equations = algebraFormalFreydLongExactEquations(input);
    const equationsData = serializeAlgebraFormalFreydLongExactEquations(equations);
    const anchorId = input.anchorId ?? 'connecting/' + Math.min(1, input.selected.result.topDegree) + '/reconstruction';
    const anchor = equations.entries.find(entry => entry.id === anchorId);
    if (!anchor) throw new Error('Unknown long-exact equation anchor: ' + anchorId);
    const realization: AlgebraFormalFreydLongExactRealization<P, C, I> = Object.freeze({
        profileRevision: ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE.revision,
        equations, anchorId, claimType: anchor.realization.claimType
    });
    const sequence = input.selected.result.sequence;
    const operationInput = Object.freeze({
        subcomplex: sequence.subcomplex, middleComplex: sequence.middleComplex,
        quotientComplex: sequence.quotientComplex, inclusion: sequence.inclusion, projection: sequence.projection
    });
    const model = algebraPolynomialFreydLongExactCategoryModel(sequence.ring);
    const builder = createCategoricalProgramBuilder('proof-cas.freyd-long-exact-replay', 'v1');
    const initial = builder.input('sequence-input', model.operations.boundedShortExact.input);
    const checkedSequence = builder.operation('sequence', model.operations.boundedShortExact, initial);
    const whole = builder.operation('long-exact', model.operations.boundedLongExact, checkedSequence);
    const references = builder.operation('snake-references', model.operations.snakeReferences, whole);
    const compilation = compileAlgebraPolynomialFreydLongExactProgram(model, builder.build([{ id: 'references', value: references }]));
    const graphEngine = createAlgebraPolynomialFreydLongExactEngine(model);
    const operation = defineAlgebraOperation({
        id: 'algebra.proof-cas.freyd-long-exact-replay/' + sequence.ring.identity.id,
        revision: ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE.revision,
        input: model.native.boundedShortExact.input,
        output: model.native.snakeReferences.output
    });
    const implementation = defineAlgebraReferenceImplementation({
        operation,
        algorithm: algebraAlgorithmIdentity('algebra.typescript-reference/' + operation.identity.id, 'v1'),
        async execute(value, context) {
            const execution = await executeAlgebraComputationGraph({
                graph: compilation.graph, engine: graphEngine,
                inputs: [{ id: 'sequence-input', value }], context
            });
            return operation.output.normalize(execution.outputs[0].value, 'longExactReplay.output');
        }
    });
    const engine = createAlgebraTypeScriptReferenceEngine({
        id: 'algebra.typescript-reference.proof-cas-long-exact/' + sequence.ring.identity.id,
        revision: 'v1', implementations: [implementation]
    });
    const adapter = defineAlgebraFormalComputationAdapter<
        AlgebraFormalFreydLongExactRealization<P, C, I>,
        AlgebraPolynomialFreydBoundedShortExactInput<P, C, I>,
        AlgebraPolynomialFreydLongExactSnakeReferences<P, C, I>
    >({
        id: 'proof-cas.freyd-long-exact/' + sequence.ring.identity.id,
        revision: ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE.revision, operation,
        normalizeRealization(value, path) {
            const candidate = value as AlgebraFormalFreydLongExactRealization<P, C, I>;
            if (!candidate || candidate.profileRevision !== realization.profileRevision || candidate.anchorId !== anchorId ||
                !kernelExpressionEquals(candidate.claimType, realization.claimType) ||
                serializeAlgebraFormalFreydLongExactEquations(candidate.equations) !== equationsData) {
                throw new AlgebraFormalDelegationError('INVALID_REALIZATION', path, 'Selected long-exact equation inventory has drifted');
            }
            return candidate;
        },
        serializeRealization: value => serializeCoreLfWorkspaceCanonicalJson({
            profileRevision: value.profileRevision,
            equations: serializeAlgebraFormalFreydLongExactEquations(value.equations),
            anchorId: value.anchorId, claim: serializeCoreExpression(value.claimType)
        }, 'formalFreydLongExactRealization'),
        acquire(goal, value) {
            if (!kernelExpressionEquals(goal.target, value.claimType)) {
                throw new AlgebraFormalDelegationError('CLAIM_TARGET_MISMATCH', 'longExact.goal', 'Goal differs from the selected equation anchor');
            }
            return operationInput;
        },
        serializeInput,
        serializeOutput: value => encodeAlgebraFormalFreydLongExactData(serializeAlgebraPolynomialFreydLongExactSnakeReferences(value)),
        interpret: ({ goal, computed }) => encodeAlgebraFormalFreydLongExactData(
            serializeAlgebraPolynomialFreydLongExactSnakeReferences(computed.value)) === equations.selectedOutputData
            ? { kind: 'claim', claimType: goal.target, summary: 'whole bounded homology replay matches the selected indexed equations' }
            : { kind: 'observation', summary: 'computed bounded homology differs from the selected whole result' }
    });
    return Object.freeze({
        reifier: input.reifier, selected: input.selected, equations, equationsData,
        realization, adapter, engine, operation, compilation, model
    });
}

export type AlgebraFormalFreydLongExactDelegationBundle<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = ReturnType<typeof algebraFormalFreydLongExactDelegationBundle<P, C, I>>;

/** Explicitly trust the whole replay and the inexpensive unique equation batches. */
export async function trustAlgebraFormalFreydLongExact<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(input: {
    readonly artifactId: string;
    readonly bundle: AlgebraFormalFreydLongExactDelegationBundle<P, C, I>;
    readonly run: AlgebraFormalWorkflowRun<AlgebraFormalFreydLongExactRealization<P, C, I>,
        AlgebraPolynomialFreydBoundedShortExactInput<P, C, I>, AlgebraPolynomialFreydLongExactSnakeReferences<P, C, I>>;
    readonly source: AlgebraFormalAssumptionSource;
    readonly fingerprint: (goalId: string) => CoreProofArtifactFingerprint;
    readonly decisionEvidence: (goalId: string) => string;
}) {
    if (!/^[A-Za-z][A-Za-z0-9._/-]*$/u.test(input.artifactId)) throw new Error('A stable artifact ID is required');
    assertAlgebraFormalComputationResultCurrent(input.run.result, input.run.request);
    if (input.run.request.adapter !== input.bundle.adapter) {
        throw new AlgebraFormalDelegationError('STALE_RESULT', 'longExact.adoption', 'The run belongs to another prepared bundle');
    }
    // Rebuild the inventory from the actual replay, not caller-supplied
    // mutable selections, before creating any assumptions.
    const equations = algebraFormalFreydLongExactEquations({
        reifier: input.bundle.reifier, selected: input.run.result.computed.value
    });
    if (serializeAlgebraFormalFreydLongExactEquations(equations) !== input.bundle.equationsData) {
        throw new AlgebraFormalDelegationError('STALE_RESULT', 'longExact.equations', 'Replayed equations differ from the prepared inventory');
    }
    const stem = input.artifactId.replace(/[^A-Za-z0-9_]/gu, '_');
    const adoption = trustAlgebraFormalWorkflow({
        run: input.run, assumptionName: stem + '_whole_replay',
        decision: { kind: 'trust-exact-algebra-computation', evidence: input.decisionEvidence(input.bundle.realization.anchorId) }
    });
    const start = input.source.entries.length;
    const source = appendAlgebraFormalAssumption({ source: input.source, adoption, classification: 'computed-equation' });
    const anchorIndex = equations.claims.findIndex(claim => claim.labels.includes(input.bundle.realization.anchorId));
    if (anchorIndex < 0) throw new Error('Prepared anchor is absent from the replayed claims');
    const morphisms: AlgebraPolynomialPresentationMorphism<P, C, I>[] = [];
    const agreements: AlgebraPolynomialPresentationMorphismAgreement<P, C, I>[] = [];
    const positions = new Map<number, { kind: 'morphism' | 'agreement'; index: number }>();
    equations.claims.forEach((claim, index) => {
        if (index === anchorIndex) return;
        if (claim.representative.kind === 'morphism') {
            positions.set(index, { kind: 'morphism', index: morphisms.length });
            morphisms.push(claim.representative.realization.selected);
        } else {
            positions.set(index, { kind: 'agreement', index: agreements.length });
            agreements.push(claim.representative.realization.selected);
        }
    });
    const batch = await delegateAlgebraFormalPresentationMorphismEquations({
        artifactId: input.artifactId, reifier: input.bundle.reifier,
        morphisms, agreements, chainSquares: [], source,
        fingerprint: input.fingerprint, decisionEvidence: input.decisionEvidence
    });
    const bindings = Object.freeze(equations.claims.map((claim, index) => {
        const position = positions.get(index);
        const sourceIndex = index === anchorIndex ? start : start + 1 +
            (position!.kind === 'morphism' ? position!.index : morphisms.length + position!.index);
        const entry = batch.source.entries[sourceIndex];
        if (!kernelExpressionEquals(entry.declaration.type, claim.representative.realization.claimType)) {
            throw new AlgebraFormalDelegationError('CLAIM_TARGET_MISMATCH', 'longExact.bindings', 'Adopted claim does not match its labelled equations');
        }
        return Object.freeze({ labels: claim.labels, sourceIndex, assumptionName: entry.declaration.name, reference: entry.reference });
    }));
    return Object.freeze({
        profileRevision: ALGEBRA_FORMAL_FREYD_LONG_EXACT_PROFILE.revision,
        source: batch.source, equations, bindings, adoption, batch,
        wholeReplayReceipt: createAlgebraFormalWorkflowReceipt(input.run)
    });
}

export type AlgebraFormalFreydLongExactAdoption<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
> = Awaited<ReturnType<typeof trustAlgebraFormalFreydLongExact<P, C, I>>>;

export function serializeAlgebraFormalFreydLongExactAdoption<
    P extends AlgebraParent, C extends AlgebraElement<P>, I
>(value: AlgebraFormalFreydLongExactAdoption<P, C, I>): string {
    return encodeAlgebraFormalFreydLongExactData(serializeCoreLfWorkspaceCanonicalJson({
        profileRevision: value.profileRevision,
        source: serializeAlgebraFormalAssumptionSource(value.source),
        equations: serializeAlgebraFormalFreydLongExactEquations(value.equations),
        wholeReplayReceipt: value.wholeReplayReceipt,
        bindings: value.bindings.map(binding => ({
            labels: binding.labels, sourceIndex: binding.sourceIndex,
            assumptionName: binding.assumptionName, reference: serializeCoreExpression(binding.reference)
        }))
    }, 'formalFreydLongExactAdoption'));
}
