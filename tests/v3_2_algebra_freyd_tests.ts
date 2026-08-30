/** Focused CAS-FREYD-6B compilation and reinterpretation tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    AlgebraRational,
    AlgebraRationalField,
    AlgebraRationalInput,
    RATIONAL_DOMAIN
} from '../src/v3_2/algebra_exact';
import {
    algebraMatrix,
    algebraMatrixEquals,
    algebraMatrixSpace,
    algebraZeroMatrix
} from '../src/v3_2/algebra_matrix';
import {
    AlgebraModuleCokernel,
    AlgebraModuleKernel,
    algebraFreeModule,
    algebraModuleCokernel,
    algebraModuleKernel,
    algebraModuleMorphism
} from '../src/v3_2/algebra_module';
import {
    AlgebraCategoricalProgramError,
    compileCategoricalProgram,
    createCategoricalProgramBuilder
} from '../src/v3_2/algebra_categorical_program';
import {
    ALGEBRA_FREYD_PROFILE,
    AlgebraFieldModuleFreydModel,
    algebraFieldModuleFreydModel,
    compileAlgebraFieldModuleFreydProgram,
    createAlgebraFieldModuleFreydEngine
} from '../src/v3_2/algebra_freyd';
import {
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';

type RationalFreydModel = AlgebraFieldModuleFreydModel<
    AlgebraRationalField,
    AlgebraRational,
    AlgebraRationalInput
>;
type RationalModuleKernel = AlgebraModuleKernel<
    AlgebraRationalField,
    AlgebraRational,
    AlgebraRationalInput
>;
type RationalModuleCokernel = AlgebraModuleCokernel<
    AlgebraRationalField,
    AlgebraRational,
    AlgebraRationalInput
>;

const freydError = (code: AlgebraCategoricalProgramError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraCategoricalProgramError);
        assert.equal(error.code, code);
        return true;
    };

const fixtureMorphism = () => {
    const source = algebraFreeModule(RATIONAL_DOMAIN, 3);
    const target = algebraFreeModule(RATIONAL_DOMAIN, 2);
    return algebraModuleMorphism(
        source,
        target,
        algebraMatrix(
            algebraMatrixSpace(RATIONAL_DOMAIN, 2, 3),
            [['1', '0', '0'], ['0', '0', '0']]
        ),
        algebraZeroMatrix(algebraMatrixSpace(RATIONAL_DOMAIN, 0, 0))
    );
};

const assertKernelEqual = (
    actual: RationalModuleKernel,
    expected: RationalModuleKernel,
    model: RationalFreydModel
) => {
    assert.ok(model.runtime.category.equalObjects(actual.object, expected.object));
    assert.ok(model.runtime.category.equalMorphisms(
        actual.inclusion,
        expected.inclusion
    ));
    assert.ok(algebraMatrixEquals(actual.inducedMatrix, expected.inducedMatrix));
    assert.equal(
        actual.sourceRealization.dimension,
        expected.sourceRealization.dimension
    );
    assert.ok(algebraMatrixEquals(
        actual.sourceRealization.projection,
        expected.sourceRealization.projection
    ));
    assert.ok(algebraMatrixEquals(
        actual.sourceRealization.section,
        expected.sourceRealization.section
    ));
    assert.equal(
        actual.targetRealization.dimension,
        expected.targetRealization.dimension
    );
    assert.ok(algebraMatrixEquals(
        actual.targetRealization.projection,
        expected.targetRealization.projection
    ));
    assert.ok(algebraMatrixEquals(
        actual.targetRealization.section,
        expected.targetRealization.section
    ));
};

const assertCokernelEqual = (
    actual: RationalModuleCokernel,
    expected: RationalModuleCokernel,
    model: RationalFreydModel
) => {
    assert.ok(model.runtime.category.equalObjects(actual.object, expected.object));
    assert.ok(model.runtime.category.equalMorphisms(
        actual.projection,
        expected.projection
    ));
};

describe('v3.2 Freyd/additive-closure field-module lowering', () => {
    it('packages the constructor tower as a direct presentation reinterpretation', () => {
        const model = algebraFieldModuleFreydModel(RATIONAL_DOMAIN);
        const module = algebraFreeModule(RATIONAL_DOMAIN, 3);
        assert.equal(model.profileRevision, ALGEBRA_FREYD_PROFILE.revision);
        assert.equal(model.tower.outputDoctrineId, 'additive-category');
        assert.deepEqual(model.tower.introducedRoles, [
            'biproduct',
            'cokernel',
            'zero-object'
        ]);
        assert.deepEqual(model.tower.loweringRules.map(rule => rule.id), [
            'additive-closure.matrix-lowering',
            'freyd.presentation-lowering'
        ]);
        assert.equal(
            model.reinterpretation.fromModel(
                model.reinterpretation.toModel(module)
            ),
            module
        );
        assert.equal(
            model.reinterpretation.loweringRules[0].kind,
            'reinterpretation'
        );
        assert.equal(model.lowerings.length, 2);
        assert.equal(
            model.operations.kernel.input.identity.id,
            model.runtime.operations.kernel.input.identity.id
        );
        assert.equal(
            model.operations.cokernel.output.identity.id,
            model.runtime.operations.cokernel.output.identity.id
        );
        assert.equal(ALGEBRA_FREYD_PROFILE.runtimeBoxing, false);
        assert.ok(Object.isFrozen(model));
    });

    it('compiles whole kernels and cokernels to direct module computations', async () => {
        const model = algebraFieldModuleFreydModel(RATIONAL_DOMAIN);
        const morphism = fixtureMorphism();
        const builder = createCategoricalProgramBuilder(
            'fixture.freyd.whole-constructions',
            'v1'
        );
        const input = builder.input(
            'morphism',
            model.runtime.category.morphismSchema
        );
        const kernel = builder.operation(
            'kernel',
            model.runtime.operations.kernel,
            input
        );
        const cokernel = builder.operation(
            'cokernel',
            model.runtime.operations.cokernel,
            input
        );
        const program = builder.build([
            { id: 'kernel-result', value: kernel },
            { id: 'cokernel-result', value: cokernel }
        ]);
        const compilation = compileAlgebraFieldModuleFreydProgram(
            model,
            program
        );
        assert.deepEqual(compilation.nodes.map(node => ({
            method: node.selectedMethodId,
            kind: node.selectedMethodKind,
            operation: node.algebraOperationId
        })), [
            {
                method: 'algebra.module.kernel.primitive',
                kind: 'primitive',
                operation: model.operations.kernel.identity.id
            },
            {
                method: 'algebra.module.cokernel.primitive',
                kind: 'primitive',
                operation: model.operations.cokernel.identity.id
            }
        ]);
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph,
            engine: createAlgebraFieldModuleFreydEngine(model),
            inputs: [{ id: 'morphism', value: morphism }]
        });
        const byId = new Map(execution.outputs.map(output => [
            output.id,
            output.value
        ]));
        assertKernelEqual(
            byId.get('kernel-result') as RationalModuleKernel,
            algebraModuleKernel(morphism),
            model
        );
        assertCokernelEqual(
            byId.get('cokernel-result') as RationalModuleCokernel,
            algebraModuleCokernel(morphism),
            model
        );
        assert.deepEqual(compilation.towerRules.map(rule => rule.id), [
            'additive-closure.matrix-lowering',
            'freyd.presentation-lowering'
        ]);
        assert.deepEqual(
            compilation.reinterpretationRules.map(rule => rule.id),
            [`freyd.direct-presentation/${RATIONAL_DOMAIN.parent.identity.id}`]
        );
        assert.deepEqual(compilation.loweringRules.map(rule => rule.kind), [
            'operation-lowering',
            'operation-lowering',
            'reinterpretation'
        ]);
    });

    it('requires an explicit lowering for every selected whole operation', () => {
        const model = algebraFieldModuleFreydModel(RATIONAL_DOMAIN);
        const builder = createCategoricalProgramBuilder(
            'fixture.freyd.missing-lowering',
            'v1'
        );
        const input = builder.input(
            'morphism',
            model.runtime.category.morphismSchema
        );
        const cokernel = builder.operation(
            'cokernel',
            model.runtime.operations.cokernel,
            input
        );
        const program = builder.build([{ id: 'result', value: cokernel }]);
        assert.throws(
            () => compileCategoricalProgram({
                program,
                category: model.runtime.category as never,
                tower: model.tower,
                lowerings: [model.lowerings[0]]
            }),
            freydError('MISSING_LOWERING')
        );
        assert.throws(
            () => compileCategoricalProgram({
                program,
                category: model.runtime.category as never,
                tower: model.tower,
                lowerings: model.lowerings,
                reinterpretations: [
                    model.reinterpretation,
                    model.reinterpretation
                ]
            }),
            freydError('DUPLICATE_COMPILER_RULE')
        );
        assert.throws(
            () => compileCategoricalProgram({
                program,
                category: model.runtime.category as never,
                tower: model.tower,
                lowerings: model.lowerings,
                reinterpretations: [{
                    ...model.reinterpretation,
                    publicCategoryId: 'fixture.foreign-category'
                }]
            }),
            freydError('FOREIGN_REINTERPRETATION')
        );
    });
});
