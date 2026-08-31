/** Category/compiler compatibility for one formal presentation morphism. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    algebraPolynomialIdeal,
    algebraPolynomialQuotientRing,
    algebraPolynomialRing,
    algebraPolynomialVariable,
    algebraPresentedAlgebra,
    algebraPresentedAlgebraFreeModule,
    algebraPresentedAlgebraModule,
    algebraPresentedAlgebraModuleBasisVector,
    algebraPresentedAlgebraModuleElement,
    algebraPresentedAlgebraModuleElementEquals,
    algebraPresentedAlgebraModuleLinearMap,
    algebraPresentedAlgebraModuleSemilinearMapApply,
    algebraPresentedAlgebraModuleSemilinearMapCompose,
    algebraPresentedAlgebraModuleVector,
    algebraPresentedModuleCategoricalModel,
    algebraQuotientElement,
    compileAlgebraPresentedModuleProgram,
    createAlgebraPresentedModuleEngine,
    createCategoricalProgramBuilder,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalPresentationMorphismCategoryCompatibility,
    executeAlgebraComputationGraph,
    kernelFree,
    provenance,
    serializeCoreExpression
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

describe('FPMAP categorical and formal representation agreement', () => {
    it('shares one map across composition, graph lowering, and formal W',
        async () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
            const y = algebraPolynomialVariable(ring, 1);
            const quotient = algebraPolynomialQuotientRing(
                algebraPolynomialIdeal(ring, [])
            );
            const algebra = algebraPresentedAlgebra(quotient);
            const free = algebraPresentedAlgebraFreeModule(algebra, 1);
            const module = algebraPresentedAlgebraModule(free, [
                algebraPresentedAlgebraModuleVector(free, [
                    algebraQuotientElement(quotient, x)
                ])
            ]);
            const yElement = algebraPresentedAlgebraModuleElement(
                module,
                algebraPresentedAlgebraModuleVector(free, [
                    algebraQuotientElement(quotient, y)
                ])
            );
            const multiplyY = algebraPresentedAlgebraModuleLinearMap(
                module,
                module,
                [yElement]
            );
            const composite = algebraPresentedAlgebraModuleSemilinearMapCompose(
                multiplyY,
                multiplyY
            );
            const formalRing = kernelFree('formal_category_map_R', because('ring'));
            const reifier = defineAffineFormalPolynomialReifier({
                algebra,
                formalRing,
                generatorTerms: [
                    kernelFree('formal_category_map_x', because('x')),
                    kernelFree('formal_category_map_y', because('y'))
                ],
                coefficientReifier: coefficient => kernelFree(
                    `formal_category_map_coefficient_` +
                        RATIONAL_DOMAIN.text(coefficient),
                    because('coefficient')
                ),
                status: 'trusted-computation'
            });
            const compatibility =
                defineAlgebraFormalPresentationMorphismCategoryCompatibility({
                    reifier,
                    map: composite
                });
            assert.equal(compatibility.computation.preservesRelations, true);
            assert.match(
                serializeCoreExpression(compatibility.formal.claimType),
                /bridge_comm_ring_matrix_comp/u
            );

            const model = algebraPresentedModuleCategoricalModel<
                typeof RATIONAL_DOMAIN.parent,
                typeof RATIONAL_DOMAIN.zero,
                string | bigint
            >();
            const basis = algebraPresentedAlgebraModuleElement(
                module,
                algebraPresentedAlgebraModuleBasisVector(free, 0)
            );
            const inputValue = Object.freeze({ map: composite, element: basis });
            const builder = createCategoricalProgramBuilder(
                'formal.presentation-morphism.map-action',
                'v1'
            );
            const programInput = builder.input(
                'input',
                model.native.mapApplyInputSchema
            );
            const output = builder.operation(
                'apply',
                model.operations.mapApply,
                programInput
            );
            const compilation = compileAlgebraPresentedModuleProgram(
                model,
                builder.build([{ id: 'result', value: output }])
            );
            const execution = await executeAlgebraComputationGraph({
                graph: compilation.graph,
                engine: createAlgebraPresentedModuleEngine(model),
                inputs: [{ id: 'input', value: inputValue }]
            });
            const direct = algebraPresentedAlgebraModuleSemilinearMapApply(
                composite,
                basis
            );
            assert.equal(
                algebraPresentedAlgebraModuleElementEquals(
                    execution.outputs[0].value as typeof direct,
                    direct
                ),
                true
            );
            assert.equal(
                compilation.nodes[0].selectedMethodId,
                'algebra.presented-module.map-apply.primitive'
            );
            assert.equal(compilation.reinterpretationRules.length, 1);
        }
    );
});
