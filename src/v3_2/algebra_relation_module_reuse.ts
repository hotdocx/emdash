/** Reuse an already checked relation through existing native and internal module owners. */
import {
    type AlgebraIdealWitness, type AlgebraIdealWitnessInput,
    checkAlgebraIdealWitness, normalizeAlgebraIdealWitnessInput
} from './algebra_ideal_witness';
import {
    type AlgebraPolynomialWorkspace, type AlgebraWorkbenchFingerprint,
    createAlgebraPolynomialWorkbenchReifier
} from './algebra_polynomial_workbench';
import { algebraPolynomialNegate, algebraPolynomialOne } from './algebra_polynomial';
import { algebraPolynomialFreeModule, algebraPolynomialModuleVector } from './algebra_polynomial_module';
import { algebraPolynomialModuleMap, algebraPolynomialModuleMapApply } from './algebra_polynomial_presentation';
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
import { type AlgebraFormalTrustedAdoptionDecision } from './algebra_formal_adoption';
import { createAlgebraFormalAssumptionSource } from './algebra_formal_assumption_source';
import { delegateAlgebraFormalBoundedComplexLaws } from './algebra_formal_bounded_complex_delegation';

/** This finite check does not run a membership solver or replace the retained coefficients. */
export function createAlgebraRelationComplex(input: AlgebraIdealWitnessInput, witness: AlgebraIdealWitness) {
    const normalized = normalizeAlgebraIdealWitnessInput(input);
    const coefficients = checkAlgebraIdealWitness(normalized, witness).coefficients;
    const ring = normalized.ideal.ring;
    const line = algebraPolynomialFreeModule(ring, 1);
    const middle = algebraPolynomialFreeModule(ring, normalized.ideal.generators.length + 1);
    const lower = algebraPolynomialModuleMap(middle, line,
        [...normalized.ideal.generators, normalized.polynomial].map(polynomial =>
            algebraPolynomialModuleVector(line, [polynomial])));
    const column = algebraPolynomialModuleVector(middle,
        [...coefficients, algebraPolynomialNegate(algebraPolynomialOne(ring))]);
    const upper = algebraPolynomialModuleMap(line, middle, [column]);
    const complex = algebraPolynomialBoundedFreeComplex({
        terms: [line, middle, line], differentials: [lower, upper]
    });
    if (!complex.isComplex) throw new Error('Retained relation does not define a complex');
    const unitImage = algebraPolynomialModuleMapApply(upper,
        algebraPolynomialModuleVector(line, [algebraPolynomialOne(ring)]));
    return Object.freeze({ input: normalized, coefficients, line, middle, column, lower, upper, complex, unitImage });
}

export function prepareAlgebraRelationModuleData(
    workspace: AlgebraPolynomialWorkspace, witness: AlgebraIdealWitness, sourceData: string
) {
    const { input, reifier, formalRing, formalVariables } = createAlgebraPolynomialWorkbenchReifier(workspace);
    const native = createAlgebraRelationComplex(input, witness);
    const realization = defineAlgebraFormalBoundedComplexRealization({ reifier, selected: native.complex });
    const environment = createFormalPresentationMorphismProofEnvironment([
        { name: formalRing.name, type: affineFormalCommRingType() },
        ...formalVariables.map(term => ({ name: term.name, type: affineFormalRingElementType(formalRing) }))
    ]);
    const one = formalComplexNat(1), width = formalComplexNat(native.middle.rank);
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
        ...native, sourceData, reifier, formalRing, formalVariables,
        realization, environment, lowerType, upperType, composite, compositeType
    });
}

export function assertAlgebraRelationAdoptionDecision(decision: AlgebraFormalTrustedAdoptionDecision): void {
    if (decision?.kind !== 'trust-exact-algebra-computation' ||
        typeof decision.evidence !== 'string' || !decision.evidence.trim()) {
        throw new Error('Internal complex assembly requires an explicit adoption decision');
    }
}

export interface AlgebraRelationInternalNames {
    readonly moduleId: string;
    readonly sourceId: string;
    readonly prefix: string;
    readonly provenance: string;
}

/** Existing constructors and one explicitly supplied computed law, then an actual internal action. */
export async function adoptAlgebraRelationModuleComplex<T extends ReturnType<typeof prepareAlgebraRelationModuleData>>(input: {
    readonly data: T;
    readonly decision: AlgebraFormalTrustedAdoptionDecision;
    readonly fingerprint: AlgebraWorkbenchFingerprint;
    readonly names: AlgebraRelationInternalNames;
    readonly assertCurrent: () => void;
}) {
    assertAlgebraRelationAdoptionDecision(input.decision);
    const { data, names } = input;
    const base = extendFormalBoundedComplexAssemblySignatures(data.environment);
    const profileData = serializeCoreLfWorkspaceCanonicalJson({
        proofDocument: serializeCoreProofDocumentProfile(),
        assembly: FORMAL_BOUNDED_COMPLEX_ASSEMBLY_PROFILE,
        declarations: base.declarations.map(d => ({ name: d.name, type: serializeCoreExpression(d.type) }))
    }, 'relationModuleReuse.profile');
    const source = createAlgebraFormalAssumptionSource({
        moduleId: names.moduleId, sourceId: names.sourceId, baseEnvironment: base
    });
    const adopted = await delegateAlgebraFormalBoundedComplexLaws({
        artifactId: names.moduleId, reifier: data.reifier,
        complex: data.complex, chainMaps: [], source,
        fingerprint: goalId => input.fingerprint(serializeCoreLfWorkspaceCanonicalJson({
            source: data.sourceData, decision: input.decision, goalId
        }, 'relationModuleReuse.goal'), profileData),
        decisionEvidence: () => input.decision.evidence
    });
    input.assertCurrent();
    const assembled = assembleFormalTwoStepComplex({
        formalRing: data.formalRing, ranks: [1, data.column.parent.rank, 1],
        lower: data.realization.formalDifferentials[0],
        upper: data.realization.formalDifferentials[1], law: adopted.complex.lawTerms[0]
    });
    const p = provenance('derived', names.provenance);
    let environment = adopted.source.environment.extend({
        name: `${names.prefix}_complex`, type: assembled.type, body: assembled.term,
        transparency: 'transparent', mode: binderMode('explicit', 'functorial'), provenance: p
    });
    const complexReference = kernelFree(`${names.prefix}_complex`, p);
    const projected = formalTwoStepUpperDifferential(data.formalRing, complexReference);
    const argumentType = formalComplexVectorType(data.formalRing, projected.columns);
    environment = environment.extend({
        name: `${names.prefix}_argument`, type: argumentType,
        mode: binderMode('explicit', 'functorial'), provenance: p
    });
    const argument = kernelFree(`${names.prefix}_argument`, p);
    const image = formalComplexCall('bridge_comm_ring_matrix_apply',
        [data.formalRing, projected.rows, projected.columns, projected.term, argument]);
    const imageType = formalComplexVectorType(data.formalRing, projected.rows);
    environment = environment.extend({
        name: `${names.prefix}_image`, type: imageType, body: image,
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
