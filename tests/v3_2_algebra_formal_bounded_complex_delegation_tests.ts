/** Focused ordered adoption and negative observations for bounded complexes. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    affineFormalCommRingType,
    affineFormalRingElementType,
    algebraFormalBoundedChainMapSquareBundle,
    algebraFormalBoundedComplexConditionBundle,
    algebraPolynomialBoundedChainMap,
    algebraPolynomialBoundedFreeComplex,
    algebraPolynomialFreeModule,
    algebraPolynomialIdeal,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialOne,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPolynomialZero,
    algebraPresentedAlgebra,
    coreProofPlanHole,
    createAlgebraFormalAssumptionSource,
    createAlgebraTypeScriptReferenceEngine,
    createCoreProofArtifactFingerprint,
    createFormalPresentationMorphismProofEnvironment,
    defineAffineFormalPolynomialReifier,
    delegateAlgebraFormalBoundedComplexLaws,
    kernelFree,
    provenance,
    runAlgebraFormalWorkflow,
    serializeAlgebraFormalBoundedComplexBatchResult
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

describe('FBC proof–CAS recursive law delegation', () => {
    it('adopts recursive laws and retains invalid composites/squares', async () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const zero = algebraPolynomialZero(ring);
        const one = algebraPolynomialOne(ring);
        const module = algebraPolynomialFreeModule(ring, 1);
        const map = (value: typeof x) => algebraPolynomialModuleMap(
            module,
            module,
            [algebraPolynomialModuleVector(module, [value])]
        );
        const complex = algebraPolynomialBoundedFreeComplex({
            terms: [module, module, module],
            differentials: [map(x), map(zero)]
        });
        const invalidComplex = algebraPolynomialBoundedFreeComplex({
            terms: [module, module, module],
            differentials: [map(x), map(one)]
        });
        const chainMap = algebraPolynomialBoundedChainMap({
            source: complex,
            target: complex,
            components: [map(y), map(y), map(y)]
        });
        const invalidMap = algebraPolynomialBoundedChainMap({
            source: complex,
            target: complex,
            components: [map(one), map(y), map(y)]
        });
        const algebra = algebraPresentedAlgebra(
            algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []))
        );
        const formalRing = kernelFree('formal_delegate_complex_R', because('ring'));
        const formalX = kernelFree('formal_delegate_complex_x', because('x'));
        const formalY = kernelFree('formal_delegate_complex_y', because('y'));
        const coefficients = new Map<string, ReturnType<typeof kernelFree>>();
        const reifier = defineAffineFormalPolynomialReifier({
            algebra,
            formalRing,
            generatorTerms: [formalX, formalY],
            coefficientReifier: coefficient => {
                const text = RATIONAL_DOMAIN.text(coefficient);
                let term = coefficients.get(text);
                if (term === undefined) {
                    term = kernelFree(
                        `formal_delegate_complex_coefficient_${text.replace('-', 'neg')}`,
                        because('coefficient')
                    );
                    coefficients.set(text, term);
                }
                return term;
            },
            status: 'trusted-computation'
        });
        const invalidComplexBundle = algebraFormalBoundedComplexConditionBundle({
            reifier,
            selected: invalidComplex,
            conditionIndex: 0
        });
        const invalidMapBundle = algebraFormalBoundedChainMapSquareBundle({
            reifier,
            selected: invalidMap,
            squareIndex: 0
        });
        const elementType = affineFormalRingElementType(formalRing);
        const environment = createFormalPresentationMorphismProofEnvironment([
            { name: formalRing.name, type: affineFormalCommRingType() },
            { name: formalX.name, type: elementType },
            { name: formalY.name, type: elementType },
            ...[...coefficients.values()].map(term => ({
                name: term.name,
                type: elementType
            }))
        ]);
        const source = createAlgebraFormalAssumptionSource({
            moduleId: 'proof.cas.bounded-complex.assumptions',
            sourceId: 'generated/bounded-complex-assumptions.ts',
            baseEnvironment: environment
        });
        const fingerprint = (goalId: string) =>
            createCoreProofArtifactFingerprint({
                source: {
                    id: `tests/${goalId}.ts`,
                    sha256: `sha256:${'a'.repeat(64)}`
                },
                profileSha256: `sha256:${'b'.repeat(64)}`
            });
        const result = await delegateAlgebraFormalBoundedComplexLaws({
            artifactId: 'bounded-complex',
            reifier,
            complex,
            chainMaps: [chainMap],
            source,
            fingerprint,
            decisionEvidence: goalId => `adopt exact recursive law ${goalId}`
        });
        assert.deepEqual(
            result.source.entries.map(entry => entry.declaration.name),
            [
                'bounded_complex_complex_0',
                'bounded_complex_map_0_0',
                'bounded_complex_map_0_1'
            ]
        );
        assert.equal(result.complex.lawTerms.length, 1);
        assert.equal(result.chainMaps[0].lawTerms.length, 2);
        const serialized = serializeAlgebraFormalBoundedComplexBatchResult(result);
        assert.equal(
            serialized,
            serializeAlgebraFormalBoundedComplexBatchResult(result)
        );

        const document = (
            goalId: string,
            type: typeof invalidComplexBundle.realization.conditions[0]['claimType']
        ) => Object.freeze({
            moduleId: 'proof.cas.bounded-complex.negative',
            declarationId: goalId,
            environment,
            type,
            plan: coreProofPlanHole(goalId, {
                provenance: because(`${goalId} hole`),
                expectation: { contextDepth: 0, target: type }
            }),
            provenance: because(`${goalId} root`),
            fingerprint: fingerprint(goalId)
        });
        const complexEngine = createAlgebraTypeScriptReferenceEngine({
            id: 'bounded-complex-negative-reference',
            revision: 'v1',
            implementations: invalidComplexBundle.operations.implementations
        });
        const complexGoal = 'bounded-complex-negative';
        const complexRun = await runAlgebraFormalWorkflow({
            document: document(
                complexGoal,
                invalidComplexBundle.realization.conditions[0].claimType
            ),
            goalId: complexGoal,
            adapter: invalidComplexBundle.adapter,
            realization: invalidComplexBundle.realization,
            engine: complexEngine
        });
        const mapGoal = 'bounded-chain-map-negative';
        const mapRun = await runAlgebraFormalWorkflow({
            document: document(
                mapGoal,
                invalidMapBundle.realization.squares[0].claimType
            ),
            goalId: mapGoal,
            adapter: invalidMapBundle.adapter,
            realization: invalidMapBundle.realization,
            engine: complexEngine
        });
        assert.equal(complexRun.result.interpretation.kind, 'observation');
        assert.equal(mapRun.result.interpretation.kind, 'observation');
        assert.equal(invalidComplex.conditions[0].zero, false);
        assert.equal(invalidMap.squares[0].commutes, false);
    });
});
