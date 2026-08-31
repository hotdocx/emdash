/** Focused PAM-CONFORMANCE-10A end-to-end affine module artifacts. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement
} from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra } from '../src/v3_2/algebra_presented_algebra';
import { algebraAffineScheme } from '../src/v3_2/algebra_affine_scheme';
import { algebraAffineCover } from '../src/v3_2/algebra_cech';
import {
    algebraPresentedAlgebraFreeModule,
    algebraPresentedAlgebraModule,
    algebraPresentedAlgebraModuleVector
} from '../src/v3_2/algebra_presented_module';
import { algebraAffineQuasiCoherentPresentation } from
    '../src/v3_2/algebra_quasicoherent';
import { serializeAlgebraAffineQuasiCoherentCechDiagram } from
    '../src/v3_2/algebra_quasicoherent_cech';
import {
    ALGEBRA_PRESENTED_MODULE_ARTIFACT_PROFILE,
    AlgebraPresentedModuleArtifactError,
    algebraPresentedModuleDescentArtifact,
    serializeAlgebraPresentedModuleDescentArtifact
} from '../src/v3_2/algebra_presented_module_artifact';
import { algebraPresentedModuleReferenceOperations } from
    '../src/v3_2/algebra_presented_module_reference_operations';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import { createAlgebraTypeScriptReferenceEngine } from
    '../src/v3_2/algebra_reference_engine';

const fixture = (arity: 2 | 3) => {
    const variables = arity === 2 ? ['x'] : ['x', 'y'];
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, variables, 'lex');
    const generators = variables.map((_, index) =>
        algebraPolynomialVariable(ring, index)
    );
    const quotient = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, [])
    );
    const algebra = algebraPresentedAlgebra(quotient);
    const scheme = algebraAffineScheme(algebra);
    const free = algebraPresentedAlgebraFreeModule(algebra, 1);
    const module = algebraPresentedAlgebraModule(
        free,
        generators.map(generator => algebraPresentedAlgebraModuleVector(free, [
            algebraQuotientElement(quotient, generator)
        ]))
    );
    const presentation = algebraAffineQuasiCoherentPresentation(scheme, module);
    const coverPolynomials = arity === 2
        ? [
            generators[0],
            algebraPolynomialSubtract(algebraPolynomialOne(ring), generators[0])
        ]
        : [
            generators[0],
            generators[1],
            algebraPolynomialSubtract(
                algebraPolynomialSubtract(
                    algebraPolynomialOne(ring),
                    generators[0]
                ),
                generators[1]
            )
        ];
    const cover = algebraAffineCover(
        scheme,
        coverPolynomials.map(polynomial =>
            algebraQuotientElement(quotient, polynomial)
        ),
        arity - 1
    );
    const id = arity === 2 ? 'a1_module_cover' : 'a2_module_cover';
    return {
        ring,
        generators,
        quotient,
        algebra,
        scheme,
        free,
        module,
        presentation,
        cover,
        artifact: algebraPresentedModuleDescentArtifact(id, presentation, cover)
    };
};

describe('v3.2 end-to-end presented-module affine descent', () => {
    it('retains the binary A/(x) support artifact', () => {
        const value = fixture(2);
        assert.deepEqual(value.artifact.summary, {
            simplexCount: 3,
            faceCount: 2,
            comparisonCount: 0,
            zeroSimplexCount: 2,
            degreeCounts: [
                { degree: 0, simplices: 2, incomingFaces: 2 },
                { degree: 1, simplices: 1, incomingFaces: 0 }
            ]
        });
        assert.deepEqual(
            value.artifact.diagram.faces.map(face => face.face.sign),
            [1, -1]
        );
    });

    it('retains the ternary A/(x,y) two-skeleton artifact', () => {
        const value = fixture(3);
        assert.deepEqual(value.artifact.summary, {
            simplexCount: 7,
            faceCount: 9,
            comparisonCount: 3,
            zeroSimplexCount: 6,
            degreeCounts: [
                { degree: 0, simplices: 3, incomingFaces: 6 },
                { degree: 1, simplices: 3, incomingFaces: 3 },
                { degree: 2, simplices: 1, incomingFaces: 0 }
            ]
        });
        assert.equal(value.artifact.diagram.comparisons.every(value =>
            value.holds
        ), true);
    });

    it('serializes both artifacts deterministically without a proof claim', () => {
        [fixture(2).artifact, fixture(3).artifact].forEach(artifact => {
            const first = serializeAlgebraPresentedModuleDescentArtifact(artifact);
            const second = serializeAlgebraPresentedModuleDescentArtifact(artifact);
            assert.equal(first, second);
            assert.equal((JSON.parse(first) as { id: string }).id, artifact.id);
        });
        assert.equal(ALGEBRA_PRESENTED_MODULE_ARTIFACT_PROFILE.proofClaim, false);
    });

    it('agrees with native graph execution for both concrete covers', async () => {
        for (const value of [fixture(2), fixture(3)]) {
            const operations = algebraPresentedModuleReferenceOperations<
                typeof RATIONAL_DOMAIN.parent,
                typeof RATIONAL_DOMAIN.zero,
                string | bigint
            >();
            const builder = createAlgebraComputationGraphBuilder(
                `fixture.${value.artifact.id}.graph`,
                'v1'
            );
            const input = builder.input('input', operations.cechInputSchema);
            const output = builder.operation('cech', operations.cech, input);
            const execution = await executeAlgebraComputationGraph({
                graph: builder.build([{ id: 'result', value: output }]),
                engine: createAlgebraTypeScriptReferenceEngine({
                    implementations: operations.implementations
                }),
                inputs: [{
                    id: 'input',
                    value: {
                        presentation: value.presentation,
                        cover: value.cover
                    }
                }]
            });
            assert.equal(
                serializeAlgebraAffineQuasiCoherentCechDiagram(
                    execution.outputs[0].value as never
                ),
                serializeAlgebraAffineQuasiCoherentCechDiagram(
                    value.artifact.diagram
                )
            );
        }
    });

    it('rejects a nonportable artifact identity', () => {
        const value = fixture(2);
        assert.throws(
            () => algebraPresentedModuleDescentArtifact(
                'not valid',
                value.presentation,
                value.cover
            ),
            (error: unknown) => {
                assert.ok(error instanceof AlgebraPresentedModuleArtifactError);
                assert.equal(error.code, 'INVALID_ARTIFACT_ID');
                return true;
            }
        );
    });
});
