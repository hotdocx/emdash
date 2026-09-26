/** Workspace consumer of the existing retained-relation and internal-complex owners. */
import {
    AlgebraGoalError, ALGEBRA_GOAL_SOURCE_PROFILE, algebraGoalInput,
    algebraGoalPolynomialTerms, checkAlgebraGoalRelation
} from './algebra_goal_source';
import { algebraGoalSha256, withAlgebraGoalConstruction } from './algebra_goal_workspace';
import {
    adoptAlgebraRelationModuleComplex, createAlgebraRelationComplex,
    prepareAlgebraRelationModuleData
} from './algebra_relation_module_reuse';
import { algebraPolynomialText, algebraPolynomialZero, serializeAlgebraPolynomial } from './algebra_polynomial';
import { serializeCoreExpression } from './core_serialization';
import { createCoreProofArtifactFingerprint } from './proof_document';
import { serializeCoreLfWorkspaceCanonicalJson } from './lf_workspace';
import { FORMAL_BOUNDED_COMPLEX_ASSEMBLY_PROFILE } from './algebra_formal_bounded_complex_assembly';

export async function constructAlgebraGoalWorkspace(root: string, options: {
    readonly mode?: unknown; readonly adoptionReason?: unknown;
}) {
    const mode = options.mode ?? 'native';
    if (mode !== 'native' && mode !== 'internal') throw new AlgebraGoalError('INVALID_MODE', 'Choose native or internal construction');
    if (mode === 'internal' && (typeof options.adoptionReason !== 'string' ||
        !options.adoptionReason.trim() || options.adoptionReason.length > 2048)) {
        throw new AlgebraGoalError('ADOPTION_REQUIRED', 'Internal construction requires an explicit reason for adopting its computed equation');
    }
    if (mode === 'native' && options.adoptionReason !== undefined) {
        throw new AlgebraGoalError('INVALID_MODE', 'An adoption reason is only used in internal mode');
    }
    return withAlgebraGoalConstruction(root, async current => {
        const input = algebraGoalInput(current.source);
        const relation = checkAlgebraGoalRelation(current.source, current.computation);
        const native = createAlgebraRelationComplex(input, relation);
        const ranks = native.complex.terms.map(term => term.module.rank);
        const summary = {
            mode, construction: 'two-step-finite-free-complex', ranks,
            nativeUpperColumn: native.column.components.map(algebraPolynomialText),
            nativeImageOfOne: native.unitImage.components.map(algebraPolynomialText),
            compositeIsZero: native.complex.isComplex,
            relationOrigin: 'retained-native-result-checked-by-exact-arithmetic',
            algorithmRecorded: ALGEBRA_GOAL_SOURCE_PROFILE.engine
        };
        const nativeArtifact = {
            kind: native.complex.kind, ranks, ring: current.source.ring,
            differentials: [native.lower, native.upper].map(map => ({
                sourceRank: map.source.rank, targetRank: map.target.rank,
                columns: map.columns.map(column => column.components.map(algebraGoalPolynomialTerms))
            })),
            imageOfOne: native.unitImage.components.map(algebraGoalPolynomialTerms),
            mathematicalSource: relation.source
        };
        if (mode === 'native') {
            const result = { ...summary, resultStatus: 'native-complex-and-module-action', adoptedEquationCount: 0 };
            return { artifact: { ...result, native: nativeArtifact }, summary: result };
        }

        const workspace = { ideal: input.ideal, left: input.polynomial, right: algebraPolynomialZero(input.ideal.ring) };
        const sourceData = serializeCoreLfWorkspaceCanonicalJson({
            revision: 'emdash-goal-internal-relation-v1',
            sourceRevision: current.sourceRevision, computationRevision: current.computationRevision,
            origin: { kind: 'retained-native-computation', engine: ALGEBRA_GOAL_SOURCE_PROFILE.engine },
            mathematicalSource: relation.source, coefficients: relation.coefficients.map(serializeAlgebraPolynomial)
        }, 'goalConstruction.source');
        const data = prepareAlgebraRelationModuleData(workspace, relation, sourceData);
        const decision = { kind: 'trust-exact-algebra-computation' as const, evidence: options.adoptionReason as string };
        const fingerprintMaterials: { source: string; profile: string; sourceSha256: string; profileSha256: string }[] = [];
        const internal = await adoptAlgebraRelationModuleComplex({
            data, decision,
            names: {
                moduleId: 'algebra.goal.module', sourceId: 'generated/goal-module-assumptions.ts',
                prefix: 'goal_reuse', provenance: 'internal reuse of retained native relation data'
            },
            assertCurrent: () => { checkAlgebraGoalRelation(current.source, current.computation); },
            fingerprint: (source, profile) => {
                const material = { source, profile, sourceSha256: algebraGoalSha256(source), profileSha256: algebraGoalSha256(profile) };
                fingerprintMaterials.push(material);
                return createCoreProofArtifactFingerprint({
                    source: { id: `emdash-goal-computed-law-${fingerprintMaterials.length}`, sha256: material.sourceSha256 },
                    profileSha256: material.profileSha256
                });
            }
        });
        const assumptions = internal.adopted.source.entries.map(entry => ({
            name: entry.declaration.name, type: serializeCoreExpression(entry.declaration.type),
            classification: entry.classification, hasProofBody: entry.declaration.body !== undefined,
            authority: entry.adoptionArtifact.authority, artifact: entry.adoptionArtifact
        }));
        const definitions = ['goal_reuse_complex', 'goal_reuse_image'].map(name => {
            const declaration = internal.environment.lookup(name)!;
            return { name, type: serializeCoreExpression(declaration.type),
                body: serializeCoreExpression(declaration.body!), transparency: declaration.transparency };
        });
        const result = { ...summary, resultStatus: internal.status,
            adoptedEquationCount: assumptions.length, adoptionReason: decision.evidence,
            internalComplex: 'goal_reuse_complex', internalAction: 'goal_reuse_image',
            internalArgument: 'a supplied formal vector of rank one',
            internalActionMeaning: 'd2(a) for a supplied formal argument a; nativeImageOfOne reports native d2(1), not the action on arbitrary a',
            qualification: 'Core checks construction and action types; complex projection reduction is not newly qualified in the standalone TypeScript runtime' };
        return {
            summary: result,
            artifact: {
                ...result, native: nativeArtifact, sourceData,
                internal: {
                    profile: FORMAL_BOUNDED_COMPLEX_ASSEMBLY_PROFILE, profileData: internal.profileData,
                    assumptions, decision, definitions, fingerprintMaterials,
                    complexReference: serializeCoreExpression(internal.complexReference),
                    upperDifferential: serializeCoreExpression(internal.projected.term),
                    argument: serializeCoreExpression(internal.argument), argumentType: serializeCoreExpression(internal.argumentType),
                    image: serializeCoreExpression(internal.image), imageType: serializeCoreExpression(internal.imageType)
                }
            }
        };
    });
}
