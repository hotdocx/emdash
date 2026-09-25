/** One shared polynomial source for computation, a derived view and an open goal. */

import { RATIONAL_DOMAIN } from './algebra_exact';
import {
    algebraGroebnerBasis, algebraIdealMembership, algebraPolynomialIdeal
} from './algebra_ideal';
import {
    AlgebraIdealWitnessInput, AlgebraRationalPolynomial, AlgebraRationalPolynomialIdeal,
    algebraIdealWitnessSource, checkAlgebraIdealWitness, normalizeAlgebraIdealWitnessInput
} from './algebra_ideal_witness';
import { computeSingularIdealWitness } from './algebra_ideal_singular';
import { AlgebraOracleTransport } from './algebra_oracle';
import {
    algebraPolynomialMultiply, algebraPolynomialOne, algebraPolynomialPower,
    algebraPolynomialRing, algebraPolynomialSchema, algebraPolynomialSubtract,
    algebraPolynomialVariable, serializeAlgebraPolynomial
} from './algebra_polynomial';
import { sampleAlgebraPolynomialCurves, AlgebraCurveViewport } from './algebra_polynomial_plot';
import { algebraPolynomialQuotientRing } from './algebra_quotient';
import { algebraPresentedAlgebra } from './algebra_presented_algebra';
import { defineAffineFormalPolynomialReifier } from './algebra_formal_reifier';
import {
    algebraFormalIdealEqualityDelegationBundle, defineAlgebraFormalIdealEqualityRealization
} from './algebra_formal_ideal_delegation';
import {
    affineFormalCommRingType, affineFormalRingElementType, affineFormalRingEqualityType
} from './algebra_formal_conformance';
import { createAffineFormalZariskiProofEnvironment } from './algebra_formal_zariski_signatures';
import { createAlgebraTypeScriptReferenceEngine } from './algebra_reference_engine';
import {
    createAlgebraFormalComputationRequest, defineAlgebraFormalComputationGoal
} from './algebra_formal_delegation';
import { executeAlgebraFormalComputationRequest } from './algebra_formal_delegation_execution';
import { checkAlgebraFormalComputationData } from './algebra_formal_adoption';
import {
    CoreProofArtifactFingerprint, serializeCoreProofDocumentProfile
} from './proof_document';
import { coreProofPlanHole } from './proof_plan';
import { KernelExpression, kernelCall, kernelFree, provenance } from './kernel';
import { serializeCoreExpression } from './core_serialization';

export interface AlgebraPolynomialWorkspace {
    readonly ideal: AlgebraRationalPolynomialIdeal;
    readonly left: AlgebraRationalPolynomial;
    readonly right: AlgebraRationalPolynomial;
}

export function algebraPolynomialWorkspaceInput(workspace: AlgebraPolynomialWorkspace): AlgebraIdealWitnessInput {
    const schema = algebraPolynomialSchema(workspace.ideal.ring);
    return normalizeAlgebraIdealWitnessInput({
        ideal: workspace.ideal,
        polynomial: algebraPolynomialSubtract(
            schema.normalize(workspace.left, 'workspace.left'),
            schema.normalize(workspace.right, 'workspace.right')
        )
    });
}

export function algebraPolynomialWorkspaceSource(workspace: AlgebraPolynomialWorkspace): string {
    return JSON.stringify({
        revision: 'emdash-polynomial-workspace-v1',
        input: algebraIdealWitnessSource(algebraPolynomialWorkspaceInput(workspace)),
        left: serializeAlgebraPolynomial(workspace.left),
        right: serializeAlgebraPolynomial(workspace.right)
    });
}

/** The only place where the example's formulas are constructed. */
export function createAlgebraPolynomialWorkbenchExample(): AlgebraPolynomialWorkspace {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0), y = algebraPolynomialVariable(ring, 1);
    const one = algebraPolynomialOne(ring);
    return Object.freeze({
        ideal: algebraPolynomialIdeal(ring, [
            algebraPolynomialSubtract(y, algebraPolynomialPower(x, 2n)),
            algebraPolynomialSubtract(algebraPolynomialMultiply(x, y), one)
        ]),
        left: algebraPolynomialPower(x, 3n), right: one
    });
}

export async function computeAlgebraPolynomialWorkbench(
    workspace: AlgebraPolynomialWorkspace,
    transport: AlgebraOracleTransport,
    viewport?: AlgebraCurveViewport
) {
    const input = algebraPolynomialWorkspaceInput(workspace);
    const source = algebraPolynomialWorkspaceSource(workspace);
    const native = algebraIdealMembership(input.polynomial, algebraGroebnerBasis(input.ideal));
    const nativeWitness = native.member ? checkAlgebraIdealWitness(input, {
        source: algebraIdealWitnessSource(input), coefficients: native.coefficients
    }) : undefined;
    const external = await computeSingularIdealWitness(input, transport);
    if (algebraPolynomialWorkspaceSource(workspace) !== source) {
        throw new Error('Workspace changed while the computation was running');
    }
    return Object.freeze({
        source, input, native, nativeWitness, external,
        agrees: native.member === (external.kind === 'witness'),
        view: sampleAlgebraPolynomialCurves(input, viewport)
    });
}

export function assertAlgebraPolynomialWorkbenchCurrent(
    workspace: AlgebraPolynomialWorkspace,
    result: Awaited<ReturnType<typeof computeAlgebraPolynomialWorkbench>>
): void {
    const input = algebraPolynomialWorkspaceInput(workspace);
    if (result.source !== algebraPolynomialWorkspaceSource(workspace) ||
        result.external.source !== algebraIdealWitnessSource(input) ||
        result.view.source !== algebraIdealWitnessSource(input)) {
        throw new Error('Stale polynomial workbench result; recompute from the changed source');
    }
    if (result.nativeWitness) checkAlgebraIdealWitness(input, result.nativeWitness);
    if (result.external.kind === 'witness') checkAlgebraIdealWitness(input, result.external.witness);
}

/** Hashing stays in an outer adapter, as required by the proof-document owner. */
export type AlgebraWorkbenchFingerprint = (
    sourceText: string, profileText: string
) => CoreProofArtifactFingerprint;

/** Reify source polynomials without running either ideal-membership algorithm. */
export function createAlgebraPolynomialWorkbenchReifier(workspace: AlgebraPolynomialWorkspace) {
    const input = algebraPolynomialWorkspaceInput(workspace);
    const because = provenance('derived', 'shared polynomial workbench goal');
    const formalRing = kernelFree('workbench_R', because);
    const formalVariables = input.ideal.ring.variables.map((_, index) =>
        kernelFree(`workbench_variable_${index}`, because));
    const ringCall = (name: string, ...values: KernelExpression[]) => kernelCall(
        kernelFree(name, because), [formalRing, ...values].map(value =>
            ({ plicity: 'explicit' as const, value })), because);
    const zero = () => ringCall('bridge_comm_ring_zero');
    const one = () => ringCall('bridge_comm_ring_one');
    const natural = (value: bigint): KernelExpression => {
        if (value === 0n) return zero();
        if (value === 1n) return one();
        const half = natural(value / 2n);
        const double = ringCall('bridge_comm_ring_add', half, half);
        return value % 2n === 0n ? double : ringCall('bridge_comm_ring_add', double, one());
    };
    const reifier = defineAffineFormalPolynomialReifier({
        algebra: algebraPresentedAlgebra(algebraPolynomialQuotientRing(
            algebraPolynomialIdeal(input.ideal.ring, []))),
        formalRing, generatorTerms: formalVariables, status: 'explicit-data',
        coefficientReifier: coefficient => {
            const absolute = coefficient.numerator < 0n ? -coefficient.numerator : coefficient.numerator;
            if (coefficient.denominator !== 1n || absolute > 4096n) {
                throw new Error('This formal goal requires integer coefficients of magnitude at most 4096; a rational-field interpretation is not supplied');
            }
            const term = natural(absolute);
            return coefficient.numerator < 0n ? ringCall('bridge_comm_ring_neg', term) : term;
        }
    });
    return Object.freeze({
        input, reifier, formalRing, formalVariables: Object.freeze(formalVariables), zero
    });
}

export async function prepareAlgebraPolynomialWorkbenchGoal(
    workspace: AlgebraPolynomialWorkspace,
    fingerprint: AlgebraWorkbenchFingerprint
) {
    const { input, reifier, formalRing, formalVariables, zero } =
        createAlgebraPolynomialWorkbenchReifier(workspace);
    const source = algebraPolynomialWorkspaceSource(workspace);
    const because = provenance('derived', 'shared polynomial workbench goal');
    const realization = defineAlgebraFormalIdealEqualityRealization({
        basis: algebraGroebnerBasis(input.ideal), left: workspace.left,
        right: workspace.right, reifier
    });
    // These are the stated premises of the goal, never consequences of the CAS.
    const hypotheses = realization.formalIdealGenerators.map((generator, index) => ({
        name: `workbench_hypothesis_${index}`,
        type: affineFormalRingEqualityType(formalRing, generator, zero())
    }));
    const environment = createAffineFormalZariskiProofEnvironment([
        { name: formalRing.name, type: affineFormalCommRingType() },
        ...formalVariables.map(term => ({
            name: term.name, type: affineFormalRingElementType(formalRing)
        })), ...hypotheses
    ]);
    const profileText = JSON.stringify({
        proofDocument: serializeCoreProofDocumentProfile(),
        signatures: environment.declarations.map(declaration => ({
            name: declaration.name, type: serializeCoreExpression(declaration.type)
        })),
        target: serializeCoreExpression(realization.claimType)
    });
    const goalId = 'polynomial-ideal-consequence';
    const document = Object.freeze({
        moduleId: 'algebra.workbench', declarationId: 'polynomial_consequence',
        type: realization.claimType, environment,
        plan: coreProofPlanHole(goalId, { provenance: because, expectation: {
            contextDepth: 0, target: realization.claimType
        } }),
        provenance: because, fingerprint: fingerprint(source, profileText)
    });
    const goal = defineAlgebraFormalComputationGoal({ document, goalId });
    const bundle = algebraFormalIdealEqualityDelegationBundle(input.ideal.ring);
    const request = createAlgebraFormalComputationRequest({
        adapter: bundle.adapter, goal, realization,
        engine: createAlgebraTypeScriptReferenceEngine({
            id: 'algebra.workbench.native', revision: 'v1',
            implementations: bundle.operations.implementations
        })
    });
    const delegated = await executeAlgebraFormalComputationRequest(request);
    checkAlgebraFormalComputationData(delegated);
    return Object.freeze({
        source, goal, document, hypotheses: Object.freeze(hypotheses), delegated,
        status: 'open' as const,
        reason: 'The existing ideal adapter reifies a claim and coefficient data but has no proof-plan reconstruction. Its opaque ring signature mirrors do not include ring-law proof constructors. No computation assumption has been adopted.'
    });
}
