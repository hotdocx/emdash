/** Focused CAS-CONSTRUCTIBLE-8A3 tower/category/compiler tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraConstructibleEquivalence,
    algebraConstructibleFull,
    algebraConstructibleSet,
    algebraLocallyClosedPiece
} from '../src/v3_2/algebra_constructible';
import {
    AlgebraConstructibleCategoryError,
    algebraConstructibleInclusion,
    algebraConstructibleModel,
    compileAlgebraConstructibleProgram,
    createAlgebraConstructibleEngine
} from '../src/v3_2/algebra_constructible_category';
import {
    ALGEBRA_CONSTRUCTIBLE_TOWER_PROFILE
} from '../src/v3_2/algebra_constructible_tower';
import {
    createCategoricalProgramBuilder
} from '../src/v3_2/algebra_categorical_program';
import { executeCategoryOperation } from '../src/v3_2/algebra_category';
import { executeAlgebraComputationGraph } from '../src/v3_2/algebra_graph';
import {
    algebraPolynomialOne,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';

const categoryError = (code: AlgebraConstructibleCategoryError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraConstructibleCategoryError);
        assert.equal(error.code, code);
        return true;
    };

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const one = algebraPolynomialOne(ring);
    const closedX = algebraConstructibleSet(ring, [
        algebraLocallyClosedPiece(algebraPolynomialIdeal(ring, [x]), one)
    ]);
    const openX = algebraConstructibleSet(ring, [
        algebraLocallyClosedPiece(algebraPolynomialIdeal(ring, []), x)
    ]);
    const full = algebraConstructibleFull(ring);
    return { ring, x, closedX, openX, full };
};

describe('v3.2 constructible tower and computable category', () => {
    it('retains every constructor and the direct reinterpretation', () => {
        const { ring, full } = fixture();
        const model = algebraConstructibleModel(ring);
        assert.deepEqual(model.towerModel.tower.constructors.map(value => value.id), [
            'category-constructor.additive-closure',
            'category-constructor.slice-over-tensor-unit',
            'category-constructor.poset-reflection',
            'category-constructor.stable-poset',
            'category-constructor.opposite/category',
            'category-constructor.differences',
            'category-constructor.finite-unions'
        ]);
        assert.deepEqual(model.towerModel.tower.loweringRules.map(value => value.id), [
            'additive-closure.matrix-lowering',
            'constructible.slice-to-ideal',
            'constructible.poset-to-radical-comparison',
            'constructible.stable-to-saturation',
            'opposite.category.dual-lowering',
            'constructible.difference-to-locally-closed',
            'constructible.union-to-piece-list'
        ]);
        assert.equal(
            model.towerModel.reinterpretation.fromModel(
                model.towerModel.reinterpretation.toModel(full)
            ),
            full
        );
        assert.equal(ALGEBRA_CONSTRUCTIBLE_TOWER_PROFILE.runtimeBoxing, false);
    });

    it('computes the inclusion-poset category and whole Boolean methods', async () => {
        const { ring, closedX, openX, full } = fixture();
        const model = algebraConstructibleModel(ring);
        const inclusion = algebraConstructibleInclusion(closedX, full);
        assert.equal(inclusion.difference.empty, true);
        assert.throws(
            () => algebraConstructibleInclusion(full, closedX),
            categoryError('NOT_INCLUDED')
        );
        const difference = await executeCategoryOperation(
            model.runtime.category as never,
            model.runtime.operations.difference,
            { left: full, right: closedX }
        );
        assert.equal(difference.plan.method.id,
            'algebra.constructible.difference.primitive');
        assert.equal(
            algebraConstructibleEquivalence(difference.value, openX).equivalent,
            true
        );
    });

    it('compiles and executes a direct constructible difference program', async () => {
        const { ring, closedX, openX, full } = fixture();
        const model = algebraConstructibleModel(ring);
        const builder = createCategoricalProgramBuilder(
            'fixture.constructible.difference',
            'v1'
        );
        const input = builder.input('pair', model.runtime.binarySchema);
        const result = builder.operation(
            'difference',
            model.runtime.operations.difference,
            input
        );
        const compilation = compileAlgebraConstructibleProgram(
            model,
            builder.build([{ id: 'result', value: result }])
        );
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph,
            engine: createAlgebraConstructibleEngine(model),
            inputs: [{ id: 'pair', value: { left: full, right: closedX } }]
        });
        assert.equal(
            algebraConstructibleEquivalence(
                execution.outputs[0].value as typeof openX,
                openX
            ).equivalent,
            true
        );
        assert.equal(compilation.nodes[0].selectedMethodKind, 'primitive');
        assert.equal(compilation.towerRules.length, 7);
        assert.equal(compilation.reinterpretationRules.length, 1);
        assert.equal(compilation.loweringRules.length, 8);
    });
});
