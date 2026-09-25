/** Actual external coefficients become module data, a whole complex and an internal action. */

import { computeSingularIdealWitness } from './algebra_ideal_singular';
import { algebraIdealWitnessSource, checkAlgebraIdealWitness } from './algebra_ideal_witness';
import {
    AlgebraPolynomialWorkspace, AlgebraWorkbenchFingerprint,
    algebraPolynomialWorkspaceSource, algebraPolynomialWorkspaceInput,
    createAlgebraPolynomialWorkbenchReifier
} from './algebra_polynomial_workbench';
import {
    algebraPolynomialNegate, algebraPolynomialOne, serializeAlgebraPolynomial
} from './algebra_polynomial';
import {
    algebraPolynomialFreeModule, algebraPolynomialModuleVector
} from './algebra_polynomial_module';
import { algebraPolynomialModuleMap } from './algebra_polynomial_presentation';
import { algebraPolynomialBoundedFreeComplex } from './algebra_polynomial_bounded_complex';
import { defineAlgebraFormalBoundedComplexRealization } from './algebra_formal_bounded_complex';
import { createFormalPresentationMorphismProofEnvironment } from './algebra_formal_presentation_morphism_signatures';
import { affineFormalCommRingType, affineFormalRingElementType } from './algebra_formal_conformance';
import { createCoreProofChecker } from './proof_checker';
import { serializeCoreExpression } from './core_serialization';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import { serializeCoreProofDocumentProfile } from './proof_document';
import { binderMode, kernelFree, provenance } from './kernel';
import {
    FORMAL_BOUNDED_COMPLEX_ASSEMBLY_PROFILE, assembleFormalTwoStepComplex,
    extendFormalBoundedComplexAssemblySignatures, formalComplexCall,
    formalComplexMatrixType, formalComplexNat, formalComplexVectorType,
    formalTwoStepUpperDifferential
} from './algebra_formal_bounded_complex_assembly';
import { AlgebraFormalTrustedAdoptionDecision } from './algebra_formal_adoption';
import { createAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { delegateAlgebraFormalBoundedComplexLaws } from './algebra_formal_bounded_complex_delegation';

export const ALGEBRA_EXTERNAL_MODULE_REUSE_PROFILE = Object.freeze({
    revision: 'emdash-external-module-reuse-v1',
    externalData: 'original-generator-coefficients',
    construction: 'two-step-finite-free-complex',
    interpretation: 'bounded-integer-polynomials-in-a-supplied-commutative-ring',
    automaticCertification: false,
    performsIo: false,
    substitutesNativeMembershipOutput: false
} as const);

export type AlgebraExternalIdealResult = Awaited<ReturnType<typeof computeSingularIdealWitness>>;

/** Both source and chosen result matter: two valid witnesses may give different columns. */
export function algebraExternalModuleSource(
    workspace: AlgebraPolynomialWorkspace, external: AlgebraExternalIdealResult
): string {
    const input = algebraPolynomialWorkspaceInput(workspace);
    if (external.kind !== 'witness') throw new Error('Internal reuse requires a positive external witness');
    if (external.source !== algebraIdealWitnessSource(input)) throw new Error('Stale external source');
    const checked = checkAlgebraIdealWitness(input, external.witness);
    return serializeCoreLfWorkspaceCanonicalJson({
        profile: ALGEBRA_EXTERNAL_MODULE_REUSE_PROFILE,
        workspace: algebraPolynomialWorkspaceSource(workspace),
        external: {
            version: external.version, backend: external.backend, request: external.request,
            source: external.source, coefficients: checked.coefficients.map(serializeAlgebraPolynomial)
        }
    }, 'externalModuleReuse.source');
}

/** No native ideal-membership solver is called here. */
export function prepareAlgebraExternalModuleData(
    workspace: AlgebraPolynomialWorkspace, external: AlgebraExternalIdealResult
) {
    const sourceData = algebraExternalModuleSource(workspace, external);
    if (external.kind !== 'witness') throw new Error('Positive external witness required');
    const { input, reifier, formalRing, formalVariables } = createAlgebraPolynomialWorkbenchReifier(workspace);
    const coefficients = checkAlgebraIdealWitness(input, external.witness).coefficients;
    const ring = input.ideal.ring;
    const line = algebraPolynomialFreeModule(ring, 1);
    const middle = algebraPolynomialFreeModule(ring, input.ideal.generators.length + 1);
    const lower = algebraPolynomialModuleMap(middle, line,
        [...input.ideal.generators, input.polynomial].map(polynomial =>
            algebraPolynomialModuleVector(line, [polynomial])));
    const column = algebraPolynomialModuleVector(middle,
        [...coefficients, algebraPolynomialNegate(algebraPolynomialOne(ring))]);
    const upper = algebraPolynomialModuleMap(line, middle, [column]);
    const complex = algebraPolynomialBoundedFreeComplex({
        terms: [line, middle, line], differentials: [lower, upper]
    });
    if (!complex.isComplex) throw new Error('External relation does not define a complex');
    const realization = defineAlgebraFormalBoundedComplexRealization({ reifier, selected: complex });
    const environment = createFormalPresentationMorphismProofEnvironment([
        { name: formalRing.name, type: affineFormalCommRingType() },
        ...formalVariables.map(term => ({ name: term.name, type: affineFormalRingElementType(formalRing) }))
    ]);
    const one = formalComplexNat(1), width = formalComplexNat(middle.rank);
    const lowerType = formalComplexMatrixType(formalRing, one, width);
    const upperType = formalComplexMatrixType(formalRing, width, one);
    const checker = createCoreProofChecker(environment);
    checker.validateEnvironment();
    checker.check(checker.rootContext, realization.formalDifferentials[0], lowerType);
    checker.check(checker.rootContext, realization.formalDifferentials[1], upperType);
    const composite = formalComplexCall('bridge_comm_ring_matrix_comp',
        [formalRing, one, width, one, ...realization.formalDifferentials]);
    const compositeType = formalComplexMatrixType(formalRing, one, one);
    checker.check(checker.rootContext, composite, compositeType);
    return Object.freeze({
        sourceData, external, input, reifier, formalRing, formalVariables,
        coefficients, column, lower, upper, complex, realization, environment,
        lowerType, upperType, composite, compositeType
    });
}

/** Build a whole internal complex using an explicitly adopted computed equation. */
export async function adoptAlgebraExternalModuleComplex(input: {
    readonly workspace: AlgebraPolynomialWorkspace;
    readonly external: AlgebraExternalIdealResult;
    readonly decision: AlgebraFormalTrustedAdoptionDecision;
    readonly fingerprint: AlgebraWorkbenchFingerprint;
}) {
    if (input.decision?.kind !== 'trust-exact-algebra-computation' ||
        typeof input.decision.evidence !== 'string' || !input.decision.evidence.trim()) {
        throw new Error('Internal complex assembly requires an explicit adoption decision');
    }
    const data = prepareAlgebraExternalModuleData(input.workspace, input.external);
    const base = extendFormalBoundedComplexAssemblySignatures(data.environment);
    const profileData = serializeCoreLfWorkspaceCanonicalJson({
        proofDocument: serializeCoreProofDocumentProfile(),
        assembly: FORMAL_BOUNDED_COMPLEX_ASSEMBLY_PROFILE,
        declarations: base.declarations.map(d => ({ name: d.name, type: serializeCoreExpression(d.type) }))
    }, 'externalModuleReuse.profile');
    const source = createAlgebraFormalAssumptionSource({
        moduleId: 'algebra.external.module', sourceId: 'generated/external-module-assumptions.ts',
        baseEnvironment: base
    });
    // This verifies composites of the retained external data; it never resolves membership again.
    const adopted = await delegateAlgebraFormalBoundedComplexLaws({
        artifactId: 'algebra.external.module', reifier: data.reifier,
        complex: data.complex, chainMaps: [], source,
        fingerprint: goalId => input.fingerprint(serializeCoreLfWorkspaceCanonicalJson({
            source: data.sourceData, decision: input.decision, goalId
        }, 'externalModuleReuse.goal'), profileData),
        decisionEvidence: () => input.decision.evidence
    });
    if (algebraExternalModuleSource(input.workspace, input.external) !== data.sourceData) {
        throw new Error('External source/result changed during adoption');
    }
    const assembled = assembleFormalTwoStepComplex({
        formalRing: data.formalRing, ranks: [1, data.column.parent.rank, 1],
        lower: data.realization.formalDifferentials[0],
        upper: data.realization.formalDifferentials[1], law: adopted.complex.lawTerms[0]
    });
    const p = provenance('derived', 'internal reuse of actual external module data');
    let environment = adopted.source.environment.extend({
        name: 'external_reuse_complex', type: assembled.type, body: assembled.term,
        transparency: 'transparent', mode: binderMode('explicit', 'functorial'), provenance: p
    });
    const complexReference = kernelFree('external_reuse_complex', p);
    const projected = formalTwoStepUpperDifferential(data.formalRing, complexReference);
    const argumentType = formalComplexVectorType(data.formalRing, projected.columns);
    environment = environment.extend({
        name: 'external_reuse_argument', type: argumentType,
        mode: binderMode('explicit', 'functorial'), provenance: p
    });
    const argument = kernelFree('external_reuse_argument', p);
    const image = formalComplexCall('bridge_comm_ring_matrix_apply',
        [data.formalRing, projected.rows, projected.columns, projected.term, argument]);
    const imageType = formalComplexVectorType(data.formalRing, projected.rows);
    environment = environment.extend({
        name: 'external_reuse_image', type: imageType, body: image,
        transparency: 'transparent', mode: binderMode('explicit', 'functorial'), provenance: p
    });
    const checker = createCoreProofChecker(environment);
    checker.validateEnvironment();
    checker.check(checker.rootContext, complexReference, assembled.type);
    checker.check(checker.rootContext, projected.term, projected.type);
    checker.check(checker.rootContext, image, imageType);
    return Object.freeze({
        sourceData: data.sourceData, profileData, data, adopted,
        assembled, complexReference, projected, argument, argumentType,
        image, imageType, environment,
        status: 'typed-internal-reuse-with-explicit-computed-equation' as const
    });
}

/** Source/result freshness only; serialized Core artifacts still require fresh checking. */
export function assertAlgebraExternalModuleReuseCurrent(
    workspace: AlgebraPolynomialWorkspace, external: AlgebraExternalIdealResult,
    result: Awaited<ReturnType<typeof adoptAlgebraExternalModuleComplex>>
): void {
    if (result.sourceData !== algebraExternalModuleSource(workspace, external)) {
        throw new Error('Stale internal reuse: source or external coefficient choice changed');
    }
}
