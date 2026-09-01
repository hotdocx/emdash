/** Focused finite-free weak-kernel category, doctrine, and graph tests. */

import './v3_2_algebra_polynomial_weak_kernel_singular_tests';

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
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import {
    algebraPolynomialAdd,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialFreeModule,
    algebraPolynomialModuleVector
} from '../src/v3_2/algebra_polynomial_module';
import {
    algebraPolynomialModuleMap,
    algebraPolynomialModuleMapAdd,
    algebraPolynomialModuleMapCompose,
    algebraPolynomialModuleMapIdentity,
    algebraPolynomialModuleMapNegate,
    algebraPolynomialModuleMapZero
} from '../src/v3_2/algebra_polynomial_presentation';
import {
    algebraPolynomialModuleMapEquals
} from '../src/v3_2/algebra_polynomial_presentation_morphism';
import {
    algebraPolynomialModuleMapWeakKernel
} from '../src/v3_2/algebra_polynomial_weak_kernel';
import {
    ALGEBRA_POLYNOMIAL_WEAK_KERNEL_ZERO_INPUT,
    algebraPolynomialWeakKernelCategoryModel,
    compileAlgebraPolynomialWeakKernelProgram,
    createAlgebraPolynomialWeakKernelEngine
} from '../src/v3_2/algebra_polynomial_weak_kernel_category';

describe('v3.2 polynomial finite-free weak-kernel category', () => {
    it('qualifies the additive computational-weak-kernel doctrine', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const model = algebraPolynomialWeakKernelCategoryModel(ring);
        assert.equal(model.qualification.status, 'qualified');
        assert.equal(
            model.tower.outputDoctrineId,
            'additive-category-with-computational-weak-kernels'
        );
        assert.deepEqual(model.qualification.missingRoles, []);
        assert.deepEqual(model.qualification.requiredRoles, [
            'add-morphisms',
            'biproduct',
            'negate-morphism',
            'weak-kernel',
            'weak-kernel-lift',
            'weak-kernel-morphism',
            'weak-kernel-object',
            'zero-morphism',
            'zero-object'
        ]);
        assert.equal(
            model.category.operations.methods.some(method =>
                method.operation.id === model.operations.weakKernel.id
            ),
            true
        );
    });

    it('computes the additive finite-free category operations', async () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const model = algebraPolynomialWeakKernelCategoryModel(ring);
        const left = algebraPolynomialFreeModule(ring, 1);
        const right = algebraPolynomialFreeModule(ring, 2);
        const zeroObject = await executeCategoryOperation(
            model.category,
            model.operations.zeroObject,
            ALGEBRA_POLYNOMIAL_WEAK_KERNEL_ZERO_INPUT
        );
        assert.equal(zeroObject.value.rank, 0);
        const biproduct = (await executeCategoryOperation(
            model.category,
            model.operations.biproduct,
            { left, right }
        )).value;
        assert.equal(biproduct.object.rank, 3);
        assert.equal(model.category.equalMorphisms(
            model.category.compose(
                biproduct.projectionLeft,
                biproduct.injectionLeft
            ),
            model.category.identityMorphism(left)
        ), true);
        assert.equal(model.category.equalMorphisms(
            model.category.compose(
                biproduct.projectionRight,
                biproduct.injectionLeft
            ),
            algebraPolynomialModuleMapZero(left, right)
        ), true);
        const diagonal = algebraPolynomialModuleMapAdd(
            model.category.compose(
                biproduct.injectionLeft,
                biproduct.projectionLeft
            ),
            model.category.compose(
                biproduct.injectionRight,
                biproduct.projectionRight
            )
        );
        assert.equal(model.category.equalMorphisms(
            diagonal,
            model.category.identityMorphism(biproduct.object)
        ), true);
        const identityLeft = algebraPolynomialModuleMapIdentity(left);
        const zeroLeft = (await executeCategoryOperation(
            model.category,
            model.operations.zeroMorphism,
            { source: left, target: left }
        )).value;
        const sum = (await executeCategoryOperation(
            model.category,
            model.operations.addMorphisms,
            { left: identityLeft, right: zeroLeft }
        )).value;
        assert.equal(algebraPolynomialModuleMapEquals(sum, identityLeft), true);
        const negative = (await executeCategoryOperation(
            model.category,
            model.operations.negateMorphism,
            identityLeft
        )).value;
        assert.equal(algebraPolynomialModuleMapEquals(
            algebraPolynomialModuleMapAdd(identityLeft, negative),
            zeroLeft
        ), true);
    });

    it('derives object and morphism observations and computes lifts', async () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const source = algebraPolynomialFreeModule(ring, 3);
        const target = algebraPolynomialFreeModule(ring, 1);
        const map = algebraPolynomialModuleMap(source, target, [
            algebraPolynomialModuleVector(target, [x]),
            algebraPolynomialModuleVector(target, [y]),
            algebraPolynomialModuleVector(target, [algebraPolynomialAdd(x, y)])
        ]);
        const model = algebraPolynomialWeakKernelCategoryModel(ring);
        const whole = (await executeCategoryOperation(
            model.category,
            model.operations.weakKernel,
            map
        )).value;
        const objectResult = await executeCategoryOperation(
            model.category,
            model.operations.weakKernelObject,
            map
        );
        const morphismResult = await executeCategoryOperation(
            model.category,
            model.operations.weakKernelMorphism,
            map
        );
        assert.equal(objectResult.value.identity.id, whole.object.identity.id);
        assert.equal(
            objectResult.plan.prerequisites[0].operation.id,
            model.operations.weakKernel.id
        );
        assert.equal(algebraPolynomialModuleMapEquals(
            morphismResult.value,
            whole.morphism
        ), true);
        const test = whole.morphism;
        const liftResult = await executeCategoryOperation(
            model.category,
            model.operations.weakKernelLift,
            { map, test }
        );
        assert.equal(liftResult.value.reconstructs, true);
        assert.equal(algebraPolynomialModuleMapEquals(
            algebraPolynomialModuleMapCompose(
                whole.morphism,
                liftResult.value.lift
            ),
            test
        ), true);
    });

    it('compiles and executes whole weak kernels and selected lifts', async () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const source = algebraPolynomialFreeModule(ring, 2);
        const target = algebraPolynomialFreeModule(ring, 1);
        const map = algebraPolynomialModuleMap(source, target, [
            algebraPolynomialModuleVector(target, [x]),
            algebraPolynomialModuleVector(target, [x])
        ]);
        const model = algebraPolynomialWeakKernelCategoryModel(ring);
        const builder = createCategoricalProgramBuilder(
            'polynomial-finite-free.weak-kernel-program',
            'v1'
        );
        const mapInput = builder.input('map', model.operations.weakKernel.input);
        const result = builder.operation(
            'weak-kernel',
            model.operations.weakKernel,
            mapInput
        );
        const compilation = compileAlgebraPolynomialWeakKernelProgram(
            model,
            builder.build([{ id: 'result', value: result }])
        );
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph,
            engine: createAlgebraPolynomialWeakKernelEngine(model),
            inputs: [{ id: 'map', value: map }]
        });
        const weakKernel = execution.outputs[0].value as {
            readonly object: { readonly rank: number };
        };
        assert.equal(weakKernel.object.rank, 1);
        assert.equal(
            compilation.nodes[0].selectedMethodId,
            'algebra.polynomial-finite-free.weak-kernel.primitive'
        );

        const directWeakKernel = algebraPolynomialModuleMapWeakKernel(map);
        const liftBuilder = createCategoricalProgramBuilder(
            'polynomial-finite-free.weak-kernel-lift-program',
            'v1'
        );
        const liftInput = liftBuilder.input(
            'lift-input',
            model.operations.weakKernelLift.input
        );
        const liftOutput = liftBuilder.operation(
            'weak-kernel-lift',
            model.operations.weakKernelLift,
            liftInput
        );
        const liftCompilation = compileAlgebraPolynomialWeakKernelProgram(
            model,
            liftBuilder.build([{ id: 'result', value: liftOutput }])
        );
        const liftExecution = await executeAlgebraComputationGraph({
            graph: liftCompilation.graph,
            engine: createAlgebraPolynomialWeakKernelEngine(model),
            inputs: [{
                id: 'lift-input',
                value: { map, test: directWeakKernel.morphism }
            }]
        });
        assert.equal(
            (liftExecution.outputs[0].value as { reconstructs: boolean })
                .reconstructs,
            true
        );
    });

    it('preserves direct-sum identity and composition', async () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const model = algebraPolynomialWeakKernelCategoryModel(ring);
        const left = algebraPolynomialFreeModule(ring, 1);
        const right = algebraPolynomialFreeModule(ring, 2);
        const leftIdentity = algebraPolynomialModuleMapIdentity(left);
        const rightIdentity = algebraPolynomialModuleMapIdentity(right);
        const sumIdentity = (await executeCategoryOperation(
            model.category,
            model.operations.directSumMorphism,
            { left: leftIdentity, right: rightIdentity }
        )).value;
        const biproduct = (await executeCategoryOperation(
            model.category,
            model.operations.biproduct,
            { left, right }
        )).value;
        assert.equal(algebraPolynomialModuleMapEquals(
            sumIdentity,
            model.category.identityMorphism(biproduct.object)
        ), true);
        const negative = algebraPolynomialModuleMapNegate(leftIdentity);
        const mixed = (await executeCategoryOperation(
            model.category,
            model.operations.directSumMorphism,
            { left: negative, right: rightIdentity }
        )).value;
        assert.equal(algebraPolynomialModuleMapEquals(
            model.category.compose(mixed, sumIdentity),
            mixed
        ), true);
    });
});
