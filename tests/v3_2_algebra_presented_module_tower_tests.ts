/** Focused PAM-GRAPH-8A2 semilinear category/tower/compiler tests. */

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
    algebraPresentedAlgebraMap
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
import {
    algebraPresentedAlgebraModuleSemilinearMap,
    algebraPresentedAlgebraModuleSemilinearMapEquals
} from '../src/v3_2/algebra_presented_module_map';
import { algebraAffineQuasiCoherentPresentation } from
    '../src/v3_2/algebra_quasicoherent';
import { executeCategoryOperation } from '../src/v3_2/algebra_category';
import { createCategoricalProgramBuilder } from
    '../src/v3_2/algebra_categorical_program';
import { executeAlgebraComputationGraph } from '../src/v3_2/algebra_graph';
import {
    ALGEBRA_PRESENTED_MODULE_TOWER_PROFILE,
    algebraPresentedModuleCategoricalModel,
    algebraPresentedModuleTowerModel,
    compileAlgebraPresentedModuleProgram,
    createAlgebraPresentedModuleEngine
} from '../src/v3_2/algebra_presented_module_tower';

const fixture = (variable: string) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [variable], 'lex');
    const generator = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(
        algebraPolynomialIdeal(ring, [])
    );
    const algebra = algebraPresentedAlgebra(quotient);
    const scheme = algebraAffineScheme(algebra);
    const free = algebraPresentedAlgebraFreeModule(algebra, 1);
    const module = algebraPresentedAlgebraModule(free, [
        algebraPresentedAlgebraModuleVector(free, [
            algebraQuotientElement(quotient, generator)
        ])
    ]);
    const basis = algebraPresentedAlgebraModuleElement(
        module,
        algebraPresentedAlgebraModuleBasisVector(free, 0)
    );
    return { ring, generator, quotient, algebra, scheme, free, module, basis };
};

const scalarMap = (
    source: ReturnType<typeof fixture>,
    target: ReturnType<typeof fixture>
) => algebraPresentedAlgebraMap(source.algebra, target.algebra, [
    algebraQuotientElement(target.quotient, target.generator)
]);

describe('v3.2 presented-module total category and categorical compilation', () => {
    it('forms a strict total category of modules and semilinear maps', () => {
        const a = fixture('x');
        const b = fixture('y');
        const c = fixture('z');
        const model = algebraPresentedModuleCategoricalModel<
            typeof RATIONAL_DOMAIN.parent,
            typeof RATIONAL_DOMAIN.zero,
            string | bigint
        >();
        const ab = algebraPresentedAlgebraModuleSemilinearMap(
            a.module,
            b.module,
            scalarMap(a, b),
            [b.basis]
        );
        const bc = algebraPresentedAlgebraModuleSemilinearMap(
            b.module,
            c.module,
            scalarMap(b, c),
            [c.basis]
        );
        const composite = model.category.compose(bc, ab);
        assert.equal(model.category.source(composite), a.module);
        assert.equal(model.category.target(composite), c.module);
        assert.equal(model.category.equalMorphisms(
            model.category.compose(
                composite,
                model.category.identityMorphism(a.module)
            ),
            composite
        ), true);
        assert.equal(
            ALGEBRA_PRESENTED_MODULE_TOWER_PROFILE.additiveAcrossVaryingRings,
            false
        );
    });

    it('executes whole localization and Cech category methods', async () => {
        const value = fixture('x');
        const model = algebraPresentedModuleCategoricalModel<
            typeof RATIONAL_DOMAIN.parent,
            typeof RATIONAL_DOMAIN.zero,
            string | bigint
        >();
        const localization = await executeCategoryOperation(
            model.category as never,
            model.operations.localization,
            {
                module: value.module,
                element: algebraQuotientElement(value.quotient, value.generator)
            }
        );
        assert.equal(localization.plan.method.id,
            'algebra.presented-module.localization.primitive');
        assert.equal(localization.value.isZero, true);

        const cover = algebraAffineCover(value.scheme, [
            algebraQuotientElement(value.quotient, value.generator),
            algebraQuotientElement(
                value.quotient,
                algebraPolynomialSubtract(
                    algebraPolynomialOne(value.ring),
                    value.generator
                )
            )
        ], 1);
        const cech = await executeCategoryOperation(
            model.category as never,
            model.operations.cech,
            {
                presentation: algebraAffineQuasiCoherentPresentation(
                    value.scheme,
                    value.module
                ),
                cover
            }
        );
        assert.equal(cech.value.simplices.length, 3);
        assert.equal(cech.value.faces.length, 2);
    });

    it('retains four constructor rules and one direct reinterpretation', () => {
        const value = fixture('x');
        const tower = algebraPresentedModuleTowerModel<
            typeof RATIONAL_DOMAIN.parent,
            typeof RATIONAL_DOMAIN.zero,
            string | bigint
        >();
        assert.equal(tower.tower.outputDoctrineId, 'category');
        assert.equal(tower.tower.constructors.length, 4);
        assert.equal(tower.tower.loweringRules.length, 4);
        assert.equal(tower.reinterpretation.toModel(value.module), value.module);
        assert.equal(tower.reinterpretation.fromModel(value.module), value.module);
        assert.equal(tower.reinterpretation.loweringRules.length, 1);
    });

    it('compiles and executes a schema-preserving localization program',
        async () => {
            const value = fixture('x');
            const model = algebraPresentedModuleCategoricalModel<
                typeof RATIONAL_DOMAIN.parent,
                typeof RATIONAL_DOMAIN.zero,
                string | bigint
            >();
            const builder = createCategoricalProgramBuilder(
                'fixture.presented-module.localization-program',
                'v1'
            );
            const input = builder.input(
                'input',
                model.native.localizationInputSchema
            );
            const localized = builder.operation(
                'localize',
                model.operations.localization,
                input
            );
            const program = builder.build([{ id: 'result', value: localized }]);
            const compilation = compileAlgebraPresentedModuleProgram(
                model,
                program
            );
            assert.equal(compilation.nodes[0].selectedMethodId,
                'algebra.presented-module.localization.primitive');
            assert.equal(compilation.towerRules.length, 4);
            assert.equal(compilation.reinterpretationRules.length, 1);
            const execution = await executeAlgebraComputationGraph({
                graph: compilation.graph,
                engine: createAlgebraPresentedModuleEngine(model),
                inputs: [{
                    id: 'input',
                    value: {
                        module: value.module,
                        element: algebraQuotientElement(
                            value.quotient,
                            value.generator
                        )
                    }
                }]
            });
            assert.equal(
                (execution.outputs[0].value as { isZero: boolean }).isZero,
                true
            );
        });

    it('uses canonical generator-image equality in the total category', () => {
        const a = fixture('x');
        const b = fixture('y');
        const map = algebraPresentedAlgebraModuleSemilinearMap(
            a.module,
            b.module,
            scalarMap(a, b),
            [b.basis]
        );
        const model = algebraPresentedModuleCategoricalModel();
        assert.equal(model.category.equalMorphisms(map, map), true);
        assert.equal(
            algebraPresentedAlgebraModuleSemilinearMapEquals(map, map),
            true
        );
    });
});
