/** Focused ALC-COVER/CECH uniform whole-cover delegation tests. */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    ALGEBRA_FORMAL_CECH_DELEGATION_PROFILE,
    RATIONAL_DOMAIN,
    affineFormalCommRingHomType,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraAffineCover,
    algebraAffineScheme,
    algebraFormalZariskiDelegationBundle,
    algebraFormalCechFaceDelegationBundle,
    algebraLocalizationReferenceOperations,
    algebraPolynomialIdeal,
    algebraPolynomialOne,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable,
    algebraPresentedAlgebra,
    algebraQuotientElement,
    algebraQuotientText,
    appendAlgebraFormalAssumption,
    checkLambdapiProbe,
    coreProofPlanHole,
    createAffineFormalLocalizationProofEnvironment,
    createAlgebraComputationGraphBuilder,
    createAlgebraFormalAssumptionSource,
    createAlgebraTypeScriptReferenceEngine,
    createCoreProofArtifactFingerprint,
    computeAlgebraOperation,
    defineAffineFormalCoverRealization,
    defineAffineFormalLocalizationRealization,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalZariskiDelegationRealization,
    delegateAffineFormalCechCover,
    executeAlgebraComputationGraph,
    kernelFree,
    provenance,
    runAlgebraFormalWorkflow,
    serializeAffineFormalConformanceProbe,
    trustAlgebraFormalWorkflow
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);
const hex = (value: string): string => Array.from(new TextEncoder().encode(value))
    .map(byte => byte.toString(16).padStart(2, '0')).join('');

const buildCase = async (arity: 2 | 3) => {
    const id = arity === 2 ? 'delegated_binary' : 'delegated_ternary';
    const variables = arity === 2 ? ['x'] : ['x', 'y'];
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, variables, 'lex');
    const vars = variables.map((_, index) => algebraPolynomialVariable(ring, index));
    const one = algebraPolynomialOne(ring);
    const polynomials = arity === 2
        ? [vars[0], algebraPolynomialSubtract(one, vars[0])]
        : [
            vars[0],
            vars[1],
            algebraPolynomialSubtract(
                algebraPolynomialSubtract(one, vars[0]),
                vars[1]
            )
        ];
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []));
    const algebra = algebraPresentedAlgebra(quotient);
    const cover = algebraAffineCover(
        algebraAffineScheme(algebra),
        polynomials.map(value => algebraQuotientElement(quotient, value)),
        arity - 1
    );
    const formalSource = kernelFree(`${id}_R`, because('formal source'));
    const sourceGenerators = variables.map((_, index) =>
        kernelFree(`${id}_source_generator_${index}`, because('source generator'))
    );
    const sourceCoefficients = new Map<string, ReturnType<typeof kernelFree>>();
    const sourceReifier = defineAffineFormalPolynomialReifier({
        algebra,
        formalRing: formalSource,
        generatorTerms: sourceGenerators,
        coefficientReifier: coefficient => {
            const text = RATIONAL_DOMAIN.text(coefficient);
            let term = sourceCoefficients.get(text);
            if (term === undefined) {
                term = kernelFree(`${id}_source_coefficient_${hex(text)}`,
                    because(`source coefficient ${text}`));
                sourceCoefficients.set(text, term);
            }
            return term;
        },
        status: 'trusted-computation'
    });
    const trustedCover = defineAffineFormalCoverRealization({
        cover,
        algebra: sourceReifier.realization,
        status: 'trusted-computation'
    });
    const zariski = defineAlgebraFormalZariskiDelegationRealization({
        ideal: cover.unimodular.ideal,
        reifier: sourceReifier,
        candidateCoefficients: cover.unimodular.coefficients,
        formalCover: trustedCover
    });
    const targetData = cover.simplices.map((simplex, simplexIndex) => {
        const localization = simplex.chart.chart.localization;
        const formalRing = kernelFree(`${id}_L_${simplexIndex}`, because('target'));
        const generators = localization.extendedRing.variables.map((_, index) =>
            kernelFree(`${id}_L_${simplexIndex}_generator_${index}`,
                because('target generator'))
        );
        const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
        const reifier = defineAffineFormalPolynomialReifier({
            algebra: localization.algebra,
            formalRing,
            generatorTerms: generators,
            coefficientReifier: coefficient => {
                const text = RATIONAL_DOMAIN.text(coefficient);
                let term = coefficients.get(text);
                if (term === undefined) {
                    term = kernelFree(
                        `${id}_L_${simplexIndex}_coefficient_${hex(text)}`,
                        because(`target coefficient ${text}`)
                    );
                    coefficients.set(text, term);
                }
                return term;
            },
            status: 'trusted-computation'
        });
        const formalMap = kernelFree(`${id}_map_${simplexIndex}`, because('map'));
        const trusted = defineAffineFormalLocalizationRealization({
            localization,
            source: sourceReifier.realization,
            target: reifier.realization,
            formalMap,
            status: 'trusted-computation'
        });
        return { formalRing, generators, coefficients, reifier, formalMap, trusted };
    });
    const sourceElement = affineFormalRingElementType(formalSource);
    const inputs = [
        { name: formalSource.name, type: affineFormalCommRingType() },
        ...sourceGenerators.map(term => ({ name: term.name, type: sourceElement })),
        ...[...sourceCoefficients.values()].map(term => ({
            name: term.name, type: sourceElement
        })),
        ...targetData.flatMap(data => {
            const elementType = affineFormalRingElementType(data.formalRing);
            return [
                { name: data.formalRing.name, type: affineFormalCommRingType() },
                ...data.generators.map(term => ({ name: term.name, type: elementType })),
                ...[...data.coefficients.values()].map(term => ({
                    name: term.name, type: elementType
                })),
                {
                    name: data.formalMap.name,
                    type: affineFormalCommRingHomType(formalSource, data.formalRing)
                }
            ];
        })
    ];
    const environment = createAffineFormalLocalizationProofEnvironment(inputs);
    let source = createAlgebraFormalAssumptionSource({
        moduleId: `${id}.assumptions`,
        sourceId: `generated/${id}-assumptions.ts`,
        baseEnvironment: environment
    });
    const zBundle = algebraFormalZariskiDelegationBundle(ring);
    const zEngine = createAlgebraTypeScriptReferenceEngine({
        id: `${id}.zariski-reference`, revision: 'v1',
        implementations: zBundle.operations.implementations
    });
    const goalId = `${id}-cover-law`;
    const document = Object.freeze({
        moduleId: `${id}.cover`, declarationId: goalId,
        environment: source.environment, type: zariski.claimType,
        plan: coreProofPlanHole(goalId, {
            provenance: because('cover hole'),
            expectation: { contextDepth: 0, target: zariski.claimType }
        }),
        provenance: because('cover root'),
        fingerprint: createCoreProofArtifactFingerprint({
            source: { id: `tests/${goalId}.ts`, sha256: `sha256:${'4'.repeat(64)}` },
            profileSha256: `sha256:${'5'.repeat(64)}`
        })
    });
    const zRun = await runAlgebraFormalWorkflow({
        document, goalId, adapter: zBundle.adapter,
        realization: zariski, engine: zEngine
    });
    const zAdoption = trustAlgebraFormalWorkflow({
        run: zRun, assumptionName: `${id}_cover_law`,
        decision: {
            kind: 'trust-exact-algebra-computation',
            evidence: 'adopt exact cover computation'
        }
    });
    source = appendAlgebraFormalAssumption({
        source, adoption: zAdoption, classification: 'computed-equation'
    });
    const formalCover = defineAffineFormalCoverRealization({
        cover, algebra: sourceReifier.realization, status: 'explicit-data',
        lawTerm: source.entries[0].reference
    });
    const localizationOps = algebraLocalizationReferenceOperations(algebra);
    const localizationEngine = createAlgebraTypeScriptReferenceEngine({
        id: `${id}.localization-reference`, revision: 'v1',
        implementations: localizationOps.implementations
    });
    const result = await delegateAffineFormalCechCover({
        artifactId: id,
        cover: formalCover,
        trustedLocalizations: targetData.map(data => data.trusted),
        source,
        localizationEngine,
        fingerprint: goal => createCoreProofArtifactFingerprint({
            source: { id: `tests/${goal}.ts`, sha256: `sha256:${'6'.repeat(64)}` },
            profileSha256: `sha256:${'7'.repeat(64)}`
        }),
        decisionEvidence: goal => `explicit adoption for ${goal}`
    });
    return { id, cover, result, inputs };
};

describe('ALC-COVER/CECH uniform whole-cover delegation', () => {
    it('builds the binary cover without manual localization or face evidence',
        async () => {
            const { result } = await buildCase(2);
            assert.equal(result.simplices.length, 3);
            assert.equal(result.faceRealizations.length, 2);
            assert.equal(result.overlap.faces.length, 2);
            assert.equal(result.artifact.outputs.length, 17);
            assert.equal(result.source.entries.length, 9);
            assert.equal(result.faceUnits.flat().length, 2);
        });

    it('builds the ternary two-skeleton through the same architecture',
        async () => {
            const { result } = await buildCase(3);
            assert.equal(result.simplices.length, 7);
            assert.equal(result.faceRealizations.length, 9);
            assert.equal(result.overlap.faces.length, 9);
            assert.equal(result.artifact.outputs.length, 47);
            assert.equal(result.source.entries.length, 24);
            assert.equal(result.faceUnits.flat().length, 9);
            assert.equal(
                result.source.entries.filter(entry =>
                    entry.classification === 'trusted-presentation-semantics'
                ).length,
                7
            );
        });

    it('records that every face unit is formally derived', () => {
        assert.equal(ALGEBRA_FORMAL_CECH_DELEGATION_PROFILE.handwrittenFaceEvidence,
            false);
        assert.equal(ALGEBRA_FORMAL_CECH_DELEGATION_PROFILE.faceUnitSource,
            'formal-transport-and-left-factor');
    });

    it('agrees with graph execution for a retained face decomposition',
        async () => {
            const value = await buildCase(2);
            const realization = value.result.faceRealizations[0];
            const bundle = algebraFormalCechFaceDelegationBundle(
                realization.input.domainProduct
            );
            const engine = createAlgebraTypeScriptReferenceEngine({
                id: 'delegated.face-graph-reference',
                revision: 'v1',
                implementations: bundle.operations.implementations
            });
            const direct = await computeAlgebraOperation({
                engine,
                operation: bundle.operations.operation,
                input: realization.input
            });
            const builder = createAlgebraComputationGraphBuilder(
                'delegated.face-graph',
                'v1'
            );
            const input = builder.input('face', bundle.operations.inputSchema);
            const output = builder.operation(
                'equation',
                bundle.operations.operation,
                input
            );
            const graph = builder.build([{ id: 'result', value: output }]);
            const executed = await executeAlgebraComputationGraph({
                graph,
                engine,
                inputs: [{ id: 'face', value: realization.input }]
            });
            const graphValue = executed.outputs[0].value as typeof direct.value;
            assert.equal(direct.value.holds, true);
            assert.equal(graphValue.holds, true);
            assert.equal(
                algebraQuotientText(direct.value.product),
                algebraQuotientText(graphValue.product)
            );
        }
    );

    it(
        'passes bounded Lambdapi checking for binary and ternary artifacts',
        { skip: process.env.EMDASH_RUN_AFFINE_CECH_DELEGATION !== '1' },
        async () => {
            for (const arity of [2, 3] as const) {
                const value = await buildCase(arity);
                const allDeclarations = [
                    ...value.inputs,
                    ...value.result.source.entries.map(entry => ({
                        name: entry.declaration.name,
                        type: entry.declaration.type,
                        label: entry.classification
                    }))
                ];
                const required = new Set(value.result.artifact.inputReferences);
                const declarations = allDeclarations.filter(declaration =>
                    required.has(declaration.name)
                );
                const serialized = serializeAffineFormalConformanceProbe({
                    artifact: value.result.artifact,
                    declarations,
                    sourceId: `tests/${value.id}.surface.ts`
                });
                const checked = checkLambdapiProbe(serialized, {
                    packageRoot: resolve(__dirname, '..', 'emdash2'),
                    timeoutMs: 60_000
                });
                assert.equal(checked.timedOut, false, checked.diagnostics);
                assert.equal(checked.accepted, true, checked.diagnostics);
            }
        }
    );
});
