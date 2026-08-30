/** Focused AFFINE-GRAPH-5A affine tower/compiler tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import { algebraPolynomialQuotientRing, algebraQuotientElement } from '../src/v3_2/algebra_quotient';
import { algebraPresentedAlgebra, algebraPresentedAlgebraMap } from '../src/v3_2/algebra_presented_algebra';
import { algebraAffineMorphism, algebraAffineScheme } from '../src/v3_2/algebra_affine_scheme';
import {
    ALGEBRA_AFFINE_TOWER_PROFILE,
    algebraAffineCategoricalModel,
    compileAlgebraAffineProgram,
    createAlgebraAffineEngine
} from '../src/v3_2/algebra_affine_tower';
import { createCategoricalProgramBuilder } from '../src/v3_2/algebra_categorical_program';
import { executeCategoryOperation } from '../src/v3_2/algebra_category';
import { executeAlgebraComputationGraph } from '../src/v3_2/algebra_graph';

const free = (variable: string) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [variable], 'lex');
    const generator = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, []));
    const algebra = algebraPresentedAlgebra(quotient);
    return { ring, generator, quotient, algebra, scheme: algebraAffineScheme(algebra) };
};

const cusp = () => {
    const base = free('t');
    const left = free('x');
    const right = free('y');
    const leftMap = algebraPresentedAlgebraMap(base.algebra, left.algebra, [
        algebraQuotientElement(left.quotient, algebraPolynomialPower(left.generator, 2n))
    ]);
    const rightMap = algebraPresentedAlgebraMap(base.algebra, right.algebra, [
        algebraQuotientElement(right.quotient, algebraPolynomialPower(right.generator, 3n))
    ]);
    return {
        left: algebraAffineMorphism(left.scheme, base.scheme, leftMap),
        right: algebraAffineMorphism(right.scheme, base.scheme, rightMap)
    };
};

describe('v3.2 affine constructor tower and staged compiler', () => {
    it('retains the affine constructor path and direct reinterpretation', () => {
        const model = algebraAffineCategoricalModel<
            typeof RATIONAL_DOMAIN.parent,
            typeof RATIONAL_DOMAIN.zero,
            string | bigint
        >();
        assert.deepEqual(model.towerModel.tower.constructors.map(value => value.id), [
            'category-constructor.presented-algebras',
            'category-constructor.opposite/category',
            'category-constructor.affine-spec',
            'category-constructor.principal-opens',
            'category-constructor.finite-affine-covers',
            'category-constructor.affine-cech-nerve'
        ]);
        assert.equal(model.towerModel.tower.loweringRules.length, 6);
        assert.equal(ALGEBRA_AFFINE_TOWER_PROFILE.runtimeBoxing, false);
    });

    it('executes the primitive affine fiber-product category method', async () => {
        const model = algebraAffineCategoricalModel<
            typeof RATIONAL_DOMAIN.parent,
            typeof RATIONAL_DOMAIN.zero,
            string | bigint
        >();
        const input = cusp();
        const result = await executeCategoryOperation(
            model.category as never,
            model.operations.fiberProduct,
            input
        );
        assert.equal(result.value.compatible, true);
        assert.equal(result.plan.method.id, 'algebra.affine.fiber-product.primitive');
    });

    it('compiles and executes a retained affine fiber-product program', async () => {
        const model = algebraAffineCategoricalModel<
            typeof RATIONAL_DOMAIN.parent,
            typeof RATIONAL_DOMAIN.zero,
            string | bigint
        >();
        const builder = createCategoricalProgramBuilder(
            'fixture.affine.staged-fiber-product',
            'v1'
        );
        const input = builder.input('input', model.native.fiberInputSchema);
        const output = builder.operation(
            'fiber-product',
            model.operations.fiberProduct,
            input
        );
        const compilation = compileAlgebraAffineProgram(
            model,
            builder.build([{ id: 'result', value: output }])
        );
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph,
            engine: createAlgebraAffineEngine(model),
            inputs: [{ id: 'input', value: cusp() }]
        });
        assert.equal(
            (execution.outputs[0].value as { compatible: boolean }).compatible,
            true
        );
        assert.equal(compilation.nodes[0].selectedMethodKind, 'primitive');
        assert.equal(compilation.towerRules.length, 6);
        assert.equal(compilation.reinterpretationRules.length, 1);
        assert.equal(compilation.loweringRules.length, 7);
    });
});
