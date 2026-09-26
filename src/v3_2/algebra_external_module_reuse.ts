/** Actual external coefficients become module data, a whole complex and an internal action. */

import { computeSingularIdealWitness } from './algebra_ideal_singular';
import { algebraIdealWitnessSource, checkAlgebraIdealWitness } from './algebra_ideal_witness';
import {
    AlgebraPolynomialWorkspace, AlgebraWorkbenchFingerprint,
    algebraPolynomialWorkspaceSource, algebraPolynomialWorkspaceInput
} from './algebra_polynomial_workbench';
import { serializeAlgebraPolynomial } from './algebra_polynomial';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import { AlgebraFormalTrustedAdoptionDecision } from './algebra_formal_adoption';
import {
    adoptAlgebraRelationModuleComplex, assertAlgebraRelationAdoptionDecision,
    prepareAlgebraRelationModuleData
} from './algebra_relation_module_reuse';

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
    return Object.freeze({
        ...prepareAlgebraRelationModuleData(workspace, external.witness, sourceData), external
    });
}

/** Build a whole internal complex using an explicitly adopted computed equation. */
export async function adoptAlgebraExternalModuleComplex(input: {
    readonly workspace: AlgebraPolynomialWorkspace;
    readonly external: AlgebraExternalIdealResult;
    readonly decision: AlgebraFormalTrustedAdoptionDecision;
    readonly fingerprint: AlgebraWorkbenchFingerprint;
}) {
    assertAlgebraRelationAdoptionDecision(input.decision);
    const data = prepareAlgebraExternalModuleData(input.workspace, input.external);
    return adoptAlgebraRelationModuleComplex({
        data, decision: input.decision, fingerprint: input.fingerprint,
        names: {
            moduleId: 'algebra.external.module', sourceId: 'generated/external-module-assumptions.ts',
            prefix: 'external_reuse', provenance: 'internal reuse of actual external module data'
        },
        assertCurrent: () => {
            if (algebraExternalModuleSource(input.workspace, input.external) !== data.sourceData) {
                throw new Error('External source/result changed during adoption');
            }
        }
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
