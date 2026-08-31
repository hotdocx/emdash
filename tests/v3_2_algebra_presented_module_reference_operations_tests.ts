/** Focused PAM-GRAPH-8A1 native module/affine graph-operation tests. */

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
import {
    algebraPresentedAlgebra,
    algebraPresentedAlgebraMapIdentity
} from '../src/v3_2/algebra_presented_algebra';
import { algebraAffineScheme } from '../src/v3_2/algebra_affine_scheme';
import { algebraAffineCover } from '../src/v3_2/algebra_cech';
import {
    algebraPresentedAlgebraFreeModule,
    algebraPresentedAlgebraModule,
    algebraPresentedAlgebraModuleBasisVector,
    algebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleVector
} from '../src/v3_2/algebra_presented_module';
import { algebraPresentedAlgebraModuleSemilinearMapIdentity } from
    '../src/v3_2/algebra_presented_module_map';
import { algebraAffineQuasiCoherentPresentation } from
    '../src/v3_2/algebra_quasicoherent';
import {
    ALGEBRA_PRESENTED_MODULE_REFERENCE_PROFILE,
    algebraPresentedModuleReferenceOperations
} from '../src/v3_2/algebra_presented_module_reference_operations';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import { createAlgebraTypeScriptReferenceEngine } from
    '../src/v3_2/algebra_reference_engine';

const fixture = (arity: 1 | 2 = 1) => {
    const variables = arity === 1 ? ['x'] : ['x', 'y'];
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
    const basis = algebraPresentedAlgebraModuleElement(
        module,
        algebraPresentedAlgebraModuleBasisVector(free, 0)
    );
    const presentation = algebraAffineQuasiCoherentPresentation(scheme, module);
    return {
        ring,
        generators,
        quotient,
        algebra,
        scheme,
        free,
        module,
        basis,
        presentation
    };
};

describe('v3.2 native presented-module affine graph operations', () => {
    it('executes map application and identity base change as graph nodes',
        async () => {
            const value = fixture();
            const operations = algebraPresentedModuleReferenceOperations<
                typeof RATIONAL_DOMAIN.parent,
                typeof RATIONAL_DOMAIN.zero,
                string | bigint
            >();
            const engine = createAlgebraTypeScriptReferenceEngine({
                implementations: operations.implementations
            });
            const mapBuilder = createAlgebraComputationGraphBuilder(
                'fixture.presented-module.map',
                'v1'
            );
            const mapInput = mapBuilder.input(
                'input',
                operations.mapApplyInputSchema
            );
            const mapOutput = mapBuilder.operation(
                'apply',
                operations.mapApply,
                mapInput
            );
            const mapExecution = await executeAlgebraComputationGraph({
                graph: mapBuilder.build([{ id: 'result', value: mapOutput }]),
                engine,
                inputs: [{
                    id: 'input',
                    value: {
                        map: algebraPresentedAlgebraModuleSemilinearMapIdentity(
                            value.module
                        ),
                        element: value.basis
                    }
                }]
            });
            assert.equal(
                (mapExecution.outputs[0].value as { parent: { identity: unknown } })
                    .parent.identity,
                value.module.identity
            );

            const changeBuilder = createAlgebraComputationGraphBuilder(
                'fixture.presented-module.base-change',
                'v1'
            );
            const changeInput = changeBuilder.input(
                'input',
                operations.baseChangeInputSchema
            );
            const changeOutput = changeBuilder.operation(
                'baseChange',
                operations.baseChange,
                changeInput
            );
            const changeExecution = await executeAlgebraComputationGraph({
                graph: changeBuilder.build([{ id: 'result', value: changeOutput }]),
                engine,
                inputs: [{
                    id: 'input',
                    value: {
                        scalarMap: algebraPresentedAlgebraMapIdentity(value.algebra),
                        module: value.module
                    }
                }]
            });
            assert.deepEqual(
                (changeExecution.outputs[0].value as {
                    target: { identity: unknown };
                }).target.identity,
                value.module.identity
            );
        });

    it('executes the A/(x) localization support computation in a graph',
        async () => {
            const value = fixture();
            const operations = algebraPresentedModuleReferenceOperations<
                typeof RATIONAL_DOMAIN.parent,
                typeof RATIONAL_DOMAIN.zero,
                string | bigint
            >();
            const builder = createAlgebraComputationGraphBuilder(
                'fixture.presented-module.localization',
                'v1'
            );
            const input = builder.input('input', operations.localizationInputSchema);
            const output = builder.operation(
                'localize',
                operations.localization,
                input
            );
            const execution = await executeAlgebraComputationGraph({
                graph: builder.build([{ id: 'result', value: output }]),
                engine: createAlgebraTypeScriptReferenceEngine({
                    implementations: operations.implementations
                }),
                inputs: [{
                    id: 'input',
                    value: {
                        module: value.module,
                        element: algebraQuotientElement(
                            value.quotient,
                            value.generators[0]
                        )
                    }
                }]
            });
            assert.equal(
                (execution.outputs[0].value as { isZero: boolean }).isZero,
                true
            );
        });

    it('executes the ternary quasi-coherent Cech two-skeleton in a graph',
        async () => {
            const value = fixture(2);
            const [x, y] = value.generators;
            const cover = algebraAffineCover(value.scheme, [
                algebraQuotientElement(value.quotient, x),
                algebraQuotientElement(value.quotient, y),
                algebraQuotientElement(
                    value.quotient,
                    algebraPolynomialSubtract(
                        algebraPolynomialSubtract(
                            algebraPolynomialOne(value.ring),
                            x
                        ),
                        y
                    )
                )
            ], 2);
            const operations = algebraPresentedModuleReferenceOperations<
                typeof RATIONAL_DOMAIN.parent,
                typeof RATIONAL_DOMAIN.zero,
                string | bigint
            >();
            const builder = createAlgebraComputationGraphBuilder(
                'fixture.presented-module.cech',
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
                    value: { presentation: value.presentation, cover }
                }]
            });
            const diagram = execution.outputs[0].value as {
                simplices: readonly unknown[];
                faces: readonly unknown[];
                comparisons: readonly unknown[];
            };
            assert.equal(diagram.simplices.length, 7);
            assert.equal(diagram.faces.length, 9);
            assert.equal(diagram.comparisons.length, 3);
            assert.equal(
                ALGEBRA_PRESENTED_MODULE_REFERENCE_PROFILE.wholeResults,
                true
            );
        });

    it('rejects malformed native operation inputs through their schemas', () => {
        const operations = algebraPresentedModuleReferenceOperations();
        assert.throws(
            () => operations.localizationInputSchema.normalize(null, 'input'),
            /does not satisfy schema/u
        );
        assert.throws(
            () => operations.cechInputSchema.normalize([], 'input'),
            /does not satisfy schema/u
        );
    });
});
