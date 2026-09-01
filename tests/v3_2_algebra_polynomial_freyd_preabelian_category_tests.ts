/** Focused pre-Abelian polynomial Freyd category, doctrine, compiler, and graph tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    executeCategoryOperation
} from '../src/v3_2/algebra_category';
import {
    createCategoricalProgramBuilder
} from '../src/v3_2/algebra_categorical_program';
import {
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import { INTEGER_DOMAIN, RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraPolynomialRing,
    algebraPolynomialSubtract,
    algebraPolynomialVariable,
    algebraPolynomialZero
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialFreeModule,
    algebraPolynomialModuleVector,
    algebraPolynomialSubmodule
} from '../src/v3_2/algebra_polynomial_module';
import {
    algebraPresentedPolynomialModule,
    algebraPolynomialModuleMap
} from '../src/v3_2/algebra_polynomial_presentation';
import {
    algebraPolynomialPresentationMorphism
} from '../src/v3_2/algebra_polynomial_presentation_morphism';
import {
    algebraPolynomialPresentationMorphismZero
} from '../src/v3_2/algebra_polynomial_freyd_category';
import {
    algebraPolynomialFreydPreAbelianCategoryModel,
    compileAlgebraPolynomialFreydPreAbelianProgram,
    createAlgebraPolynomialFreydPreAbelianEngine
} from '../src/v3_2/algebra_polynomial_freyd_preabelian_category';

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const zero = algebraPolynomialZero(ring);
    const sourceAmbient = algebraPolynomialFreeModule(ring, 2);
    const targetAmbient = algebraPolynomialFreeModule(ring, 1);
    const source = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(sourceAmbient, [])
    );
    const target = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(targetAmbient, [])
    );
    const morphism = algebraPolynomialPresentationMorphism({
        source,
        target,
        map: algebraPolynomialModuleMap(sourceAmbient, targetAmbient, [
            algebraPolynomialModuleVector(targetAmbient, [x]),
            algebraPolynomialModuleVector(targetAmbient, [y])
        ])
    });
    const testAmbient = algebraPolynomialFreeModule(ring, 1);
    const testSource = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(testAmbient, [])
    );
    const test = algebraPolynomialPresentationMorphism({
        source: testSource,
        target: source,
        map: algebraPolynomialModuleMap(testAmbient, sourceAmbient, [
            algebraPolynomialModuleVector(sourceAmbient, [
                algebraPolynomialSubtract(zero, y),
                x
            ])
        ])
    });
    return { ring, source, target, morphism, test };
};

describe('v3.2 polynomial Freyd pre-Abelian category', () => {
    it('qualifies only with the complete kernel/cokernel role families', () => {
        const { ring } = fixture();
        const model = algebraPolynomialFreydPreAbelianCategoryModel(ring);
        assert.equal(model.qualification.status, 'qualified');
        assert.equal(model.tower.outputDoctrineId, 'preabelian-category');
        assert.deepEqual(model.qualification.missingRoles, []);
        assert.deepEqual(model.qualification.requiredRoles, [
            'add-morphisms',
            'biproduct',
            'cokernel',
            'cokernel-colift',
            'cokernel-object',
            'cokernel-projection',
            'kernel',
            'kernel-embedding',
            'kernel-lift',
            'kernel-object',
            'negate-morphism',
            'zero-morphism',
            'zero-object'
        ]);
        assert.equal(model.tower.constructors.at(-1)?.introducedRoles.length, 8);
        assert.equal(model.base.doctrineQualification.status, 'qualified');
    });

    it('executes whole constructions and every derived usability role', async () => {
        const { ring, morphism, test } = fixture();
        const model = algebraPolynomialFreydPreAbelianCategoryModel(ring);
        const kernel = (await executeCategoryOperation(
            model.category,
            model.operations.kernel,
            morphism
        )).value;
        const kernelObject = await executeCategoryOperation(
            model.category,
            model.operations.kernelObject,
            morphism
        );
        const kernelEmbedding = await executeCategoryOperation(
            model.category,
            model.operations.kernelEmbedding,
            morphism
        );
        const kernelLift = await executeCategoryOperation(
            model.category,
            model.operations.kernelLift,
            { morphism, test }
        );
        assert.equal(model.category.equalObjects(
            kernelObject.value,
            kernel.object
        ), true);
        assert.equal(model.category.equalMorphisms(
            kernelEmbedding.value,
            kernel.embedding
        ), true);
        assert.equal(kernelLift.value.reconstructs, true);
        assert.equal(
            kernelObject.plan.prerequisites[0].operation.id,
            model.operations.kernel.id
        );

        const cokernel = (await executeCategoryOperation(
            model.category,
            model.operations.cokernel,
            morphism
        )).value;
        const cokernelObject = await executeCategoryOperation(
            model.category,
            model.operations.cokernelObject,
            morphism
        );
        const cokernelProjection = await executeCategoryOperation(
            model.category,
            model.operations.cokernelProjection,
            morphism
        );
        const cokernelColift = await executeCategoryOperation(
            model.category,
            model.operations.cokernelColift,
            { morphism, test: cokernel.projection }
        );
        assert.equal(model.category.equalObjects(
            cokernelObject.value,
            cokernel.object
        ), true);
        assert.equal(model.category.equalMorphisms(
            cokernelProjection.value,
            cokernel.projection
        ), true);
        assert.equal(cokernelColift.value.reconstructs, true);
        assert.equal(
            cokernelProjection.plan.prerequisites[0].operation.id,
            model.operations.cokernel.id
        );
    });

    it('compiles and executes whole kernel/cokernel graphs', async () => {
        const { ring, morphism } = fixture();
        const model = algebraPolynomialFreydPreAbelianCategoryModel(ring);
        const builder = createCategoricalProgramBuilder(
            'polynomial-freyd-preabelian.whole',
            'v1'
        );
        const input = builder.input('morphism', model.operations.kernel.input);
        const kernel = builder.operation('kernel', model.operations.kernel, input);
        const cokernel = builder.operation(
            'cokernel',
            model.operations.cokernel,
            input
        );
        const compilation = compileAlgebraPolynomialFreydPreAbelianProgram(
            model,
            builder.build([
                { id: 'kernel', value: kernel },
                { id: 'cokernel', value: cokernel }
            ])
        );
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph,
            engine: createAlgebraPolynomialFreydPreAbelianEngine(model),
            inputs: [{ id: 'morphism', value: morphism }]
        });
        assert.equal(
            (execution.outputs[0].value as { annihilates: boolean }).annihilates,
            true
        );
        assert.equal(
            (execution.outputs[1].value as { annihilates: boolean }).annihilates,
            true
        );
        assert.deepEqual(compilation.nodes.map(node => node.selectedMethodId), [
            'algebra.polynomial-freyd-preabelian.kernel.primitive',
            'algebra.polynomial-freyd-preabelian.cokernel.primitive'
        ]);
    });

    it('compiles and executes kernel lifts and cokernel colifts', async () => {
        const { ring, morphism, test } = fixture();
        const model = algebraPolynomialFreydPreAbelianCategoryModel(ring);
        const directCokernel = (await executeCategoryOperation(
            model.category,
            model.operations.cokernel,
            morphism
        )).value;
        const builder = createCategoricalProgramBuilder(
            'polynomial-freyd-preabelian.factors',
            'v1'
        );
        const kernelInput = builder.input(
            'kernel-input',
            model.operations.kernelLift.input
        );
        const cokernelInput = builder.input(
            'cokernel-input',
            model.operations.cokernelColift.input
        );
        const kernelLift = builder.operation(
            'kernel-lift',
            model.operations.kernelLift,
            kernelInput
        );
        const cokernelColift = builder.operation(
            'cokernel-colift',
            model.operations.cokernelColift,
            cokernelInput
        );
        const compilation = compileAlgebraPolynomialFreydPreAbelianProgram(
            model,
            builder.build([
                { id: 'kernel-lift', value: kernelLift },
                { id: 'cokernel-colift', value: cokernelColift }
            ])
        );
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph,
            engine: createAlgebraPolynomialFreydPreAbelianEngine(model),
            inputs: [
                { id: 'kernel-input', value: { morphism, test } },
                {
                    id: 'cokernel-input',
                    value: { morphism, test: directCokernel.projection }
                }
            ]
        });
        assert.equal(
            (execution.outputs[0].value as { reconstructs: boolean }).reconstructs,
            true
        );
        assert.equal(
            (execution.outputs[1].value as { reconstructs: boolean }).reconstructs,
            true
        );
    });

    it('retains inherited additive operations and rejects non-field providers', async () => {
        const { ring, source, target } = fixture();
        const model = algebraPolynomialFreydPreAbelianCategoryModel(ring);
        const zero = (await executeCategoryOperation(
            model.category,
            model.base.operations.zeroMorphism,
            { source, target }
        )).value;
        assert.equal(
            model.category.equalMorphisms(
                zero,
                algebraPolynomialPresentationMorphismZero(source, target)
            ),
            true
        );
        const integerRing = algebraPolynomialRing(INTEGER_DOMAIN, ['x'], 'lex');
        assert.throws(() =>
            algebraPolynomialFreydPreAbelianCategoryModel(integerRing)
        );
    });
});
