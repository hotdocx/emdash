/** Focused formal-presentation compatibility with categorical lowering. */

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
    algebraPresentedAlgebraModuleSemilinearMapApply,
    algebraPresentedAlgebraModuleSemilinearMapIdentity,
    algebraPresentedAlgebraModuleVector,
    algebraPresentedModuleCategoricalModel,
    compileAlgebraPresentedModuleProgram,
    createAlgebraPresentedModuleEngine,
    createCategoricalProgramBuilder,
    defineAffineFormalPolynomialReifier,
    defineAlgebraFormalPresentedModuleCompatibility,
    executeAlgebraComputationGraph,
    kernelFree,
    provenance,
    algebraQuotientElement,
    serializeCoreExpression
} from '../src/v3_2';

const because = (detail: string) => provenance('surface', detail);

describe('FPM-CATEGORY formal presentation compatibility', () => {
    it('lowers a categorical map action over the same relation columns',
        async () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
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
            const formalRing = kernelFree('formal_category_R', because('ring'));
            const reifier = defineAffineFormalPolynomialReifier({
                algebra,
                formalRing,
                generatorTerms: [
                    kernelFree('formal_category_x', because('generator'))
                ],
                coefficientReifier: coefficient => kernelFree(
                    `formal_category_coefficient_${RATIONAL_DOMAIN.text(coefficient)}`,
                    because('coefficient')
                ),
                status: 'trusted-computation'
            });
            const compatibility =
                defineAlgebraFormalPresentedModuleCompatibility({
                    reifier,
                    module
                });
            assert.equal(compatibility.relationRows, 1);
            assert.equal(compatibility.relationColumns, 1);
            assert.equal(compatibility.modeledModule, module);
            assert.equal(compatibility.restoredModule, module);
            assert.match(
                serializeCoreExpression(compatibility.formalRelationMatrix),
                /formal_category_x/u
            );

            const model = algebraPresentedModuleCategoricalModel<
                typeof RATIONAL_DOMAIN.parent,
                typeof RATIONAL_DOMAIN.zero,
                string | bigint
            >();
            const map = algebraPresentedAlgebraModuleSemilinearMapIdentity(module);
            const element = algebraPresentedAlgebraModuleElement(
                module,
                algebraPresentedAlgebraModuleBasisVector(free, 0)
            );
            const inputValue = Object.freeze({ map, element });
            const builder = createCategoricalProgramBuilder(
                'formal.presented-module.map-action',
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
                map,
                element
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
