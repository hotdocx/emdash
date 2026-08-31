/** Focused QCC-CONFORMANCE-6A end-to-end cochain artifacts. */

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
    algebraPresentedAlgebraModuleBasisVector,
    algebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleElementZero,
    algebraPresentedAlgebraModuleVector
} from '../src/v3_2/algebra_presented_module';
import { algebraAffineQuasiCoherentPresentation } from
    '../src/v3_2/algebra_quasicoherent';
import { algebraAffineQuasiCoherentCechDiagram } from
    '../src/v3_2/algebra_quasicoherent_cech';
import {
    algebraAffineQuasiCoherentCochain,
    algebraAffineQuasiCoherentCochainDegree,
    algebraAffineQuasiCoherentCochainFromGlobalElement
} from '../src/v3_2/algebra_quasicoherent_cochain';
import { serializeAlgebraAffineQuasiCoherentDifferential } from
    '../src/v3_2/algebra_quasicoherent_differential';
import { serializeAlgebraAffineQuasiCoherentDifferentialSquare } from
    '../src/v3_2/algebra_quasicoherent_differential_square';
import {
    algebraQuasiCoherentCochainReferenceOperations,
    createAlgebraQuasiCoherentCochainEngine
} from '../src/v3_2/algebra_quasicoherent_cochain_reference_operations';
import {
    ALGEBRA_QUASICOHERENT_COCHAIN_ARTIFACT_PROFILE,
    AlgebraQuasiCoherentCochainArtifactError,
    algebraAffineQuasiCoherentCochainArtifact,
    serializeAlgebraAffineQuasiCoherentCochainArtifact
} from '../src/v3_2/algebra_quasicoherent_cochain_artifact';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';

const fixture = (arity: 2 | 3, supportRelation = false) => {
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
        supportRelation ? generators.map(generator =>
            algebraPresentedAlgebraModuleVector(free, [
                algebraQuotientElement(quotient, generator)
            ])
        ) : []
    );
    const globalBasis = algebraPresentedAlgebraModuleElement(
        module,
        algebraPresentedAlgebraModuleBasisVector(free, 0)
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
    const diagram = algebraAffineQuasiCoherentCechDiagram(presentation, cover);
    const degree = algebraAffineQuasiCoherentCochainDegree(diagram, 0);
    const global = algebraAffineQuasiCoherentCochainFromGlobalElement(
        degree,
        globalBasis
    );
    return {
        ring,
        generators,
        quotient,
        algebra,
        scheme,
        free,
        module,
        globalBasis,
        presentation,
        cover,
        diagram,
        degree,
        global
    };
};

describe('v3.2 end-to-end quasi-coherent Cech cochain artifacts', () => {
    it('retains binary diagonal and asymmetric differential outcomes', () => {
        const value = fixture(2);
        const diagonal = algebraAffineQuasiCoherentCochainArtifact(
            'a1_free_diagonal',
            value.global
        );
        const asymmetricInput = algebraAffineQuasiCoherentCochain(
            value.degree,
            [
                algebraPresentedAlgebraModuleElementZero(
                    value.degree.data.simplices[0].value.module
                ),
                value.global.components[1]
            ]
        );
        const asymmetric = algebraAffineQuasiCoherentCochainArtifact(
            'a1_free_asymmetric',
            asymmetricInput
        );
        assert.equal(diagonal.summary.differentialIsZero, true);
        assert.equal(asymmetric.summary.differentialIsZero, false);
        assert.equal(diagonal.summary.contributionCount, 2);
        assert.equal(diagonal.summary.squareAvailable, false);
        assert.equal(asymmetric.summary.zeroSimplexModuleCount, 0);
    });

    it('retains the A/(x) support cochain without changing orientation', () => {
        const value = fixture(2, true);
        const artifact = algebraAffineQuasiCoherentCochainArtifact(
            'a1_support_global',
            value.global
        );
        assert.equal(artifact.summary.zeroSimplexModuleCount, 2);
        assert.equal(artifact.summary.differentialIsZero, true);
        assert.deepEqual(
            artifact.differential.targets[0].contributions.map(value =>
                value.sign
            ),
            [1, -1]
        );
    });

    it('retains a nontrivial ternary differential with a zero square', () => {
        const value = fixture(3);
        const input = algebraAffineQuasiCoherentCochain(value.degree, [
            value.global.components[0],
            algebraPresentedAlgebraModuleElementZero(
                value.degree.data.simplices[1].value.module
            ),
            value.global.components[2]
        ]);
        const artifact = algebraAffineQuasiCoherentCochainArtifact(
            'a2_free_square',
            input
        );
        assert.equal(artifact.summary.sourceComponentCount, 3);
        assert.equal(artifact.summary.targetComponentCount, 3);
        assert.equal(artifact.summary.contributionCount, 6);
        assert.equal(artifact.summary.differentialIsZero, false);
        assert.equal(artifact.summary.squareAvailable, true);
        assert.equal(artifact.summary.cancellationCount, 3);
        assert.equal(artifact.summary.squareHolds, true);
        assert.equal(artifact.square?.holds, true);
    });

    it('serializes all three artifact profiles deterministically', () => {
        const binary = fixture(2);
        const support = fixture(2, true);
        const ternary = fixture(3);
        const artifacts = [
            algebraAffineQuasiCoherentCochainArtifact(
                'binary',
                binary.global
            ),
            algebraAffineQuasiCoherentCochainArtifact(
                'support',
                support.global
            ),
            algebraAffineQuasiCoherentCochainArtifact(
                'ternary',
                ternary.global
            )
        ];
        artifacts.forEach(artifact => assert.equal(
            serializeAlgebraAffineQuasiCoherentCochainArtifact(artifact),
            serializeAlgebraAffineQuasiCoherentCochainArtifact(artifact)
        ));
        assert.equal(ALGEBRA_QUASICOHERENT_COCHAIN_ARTIFACT_PROFILE.proofClaim,
            false);
    });

    it('agrees with native graph execution for binary d and ternary d-squared',
        async () => {
            const binary = fixture(2);
            const binaryOperations = algebraQuasiCoherentCochainReferenceOperations(
                binary.degree
            );
            const binaryBuilder = createAlgebraComputationGraphBuilder(
                'fixture.cochain.binary',
                'v1'
            );
            const binaryInput = binaryBuilder.input(
                'input',
                binaryOperations.inputSchema
            );
            const binaryOutput = binaryBuilder.operation(
                'd',
                binaryOperations.differential,
                binaryInput
            );
            const binaryExecution = await executeAlgebraComputationGraph({
                graph: binaryBuilder.build([{ id: 'result', value: binaryOutput }]),
                engine: createAlgebraQuasiCoherentCochainEngine(binaryOperations),
                inputs: [{ id: 'input', value: binary.global }]
            });
            const binaryArtifact = algebraAffineQuasiCoherentCochainArtifact(
                'binary_graph',
                binary.global
            );
            assert.equal(
                serializeAlgebraAffineQuasiCoherentDifferential(
                    binaryExecution.outputs[0].value as never
                ),
                serializeAlgebraAffineQuasiCoherentDifferential(
                    binaryArtifact.differential
                )
            );

            const ternary = fixture(3);
            const ternaryOperations = algebraQuasiCoherentCochainReferenceOperations(
                ternary.degree
            );
            assert.ok(ternaryOperations.square);
            const ternaryBuilder = createAlgebraComputationGraphBuilder(
                'fixture.cochain.ternary',
                'v1'
            );
            const ternaryInput = ternaryBuilder.input(
                'input',
                ternaryOperations.inputSchema
            );
            const ternaryOutput = ternaryBuilder.operation(
                'square',
                ternaryOperations.square,
                ternaryInput
            );
            const ternaryExecution = await executeAlgebraComputationGraph({
                graph: ternaryBuilder.build([{ id: 'result', value: ternaryOutput }]),
                engine: createAlgebraQuasiCoherentCochainEngine(ternaryOperations),
                inputs: [{ id: 'input', value: ternary.global }]
            });
            const ternaryArtifact = algebraAffineQuasiCoherentCochainArtifact(
                'ternary_graph',
                ternary.global
            );
            assert.equal(
                serializeAlgebraAffineQuasiCoherentDifferentialSquare(
                    ternaryExecution.outputs[0].value as never
                ),
                serializeAlgebraAffineQuasiCoherentDifferentialSquare(
                    ternaryArtifact.square!
                )
            );
        });

    it('rejects a nonportable artifact identity', () => {
        const value = fixture(2);
        assert.throws(
            () => algebraAffineQuasiCoherentCochainArtifact(
                'not valid',
                value.global
            ),
            (error: unknown) => {
                assert.ok(error instanceof AlgebraQuasiCoherentCochainArtifactError);
                assert.equal(error.code, 'INVALID_ARTIFACT_ID');
                return true;
            }
        );
    });
});
