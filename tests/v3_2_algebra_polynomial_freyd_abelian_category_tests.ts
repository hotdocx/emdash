/** Focused polynomial Freyd Abelian doctrine, methods, compiler, and graph. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    INTEGER_DOMAIN,
    RATIONAL_DOMAIN,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydAbelianCategoryModel,
    algebraPolynomialFreydCokernel,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialMultiply,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPresentedPolynomialModule,
    compileAlgebraPolynomialFreydAbelianProgram,
    createAlgebraPolynomialFreydAbelianEngine,
    createCategoricalProgramBuilder,
    executeAlgebraComputationGraph,
    executeCategoryOperation
} from '../src/v3_2';

const fixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
    const x = algebraPolynomialVariable(ring, 0);
    const y = algebraPolynomialVariable(ring, 1);
    const free = algebraPolynomialFreeModule(ring, 1);
    const presentation = algebraPresentedPolynomialModule(
        algebraPolynomialSubmodule(free, [])
    );
    const map = (value: typeof x) => algebraPolynomialModuleMap(
        free,
        free,
        [algebraPolynomialModuleVector(free, [value])]
    );
    const morphism = algebraPolynomialPresentationMorphism({
        source: presentation,
        target: presentation,
        map: map(x)
    });
    const monoTest = algebraPolynomialPresentationMorphism({
        source: presentation,
        target: presentation,
        map: map(algebraPolynomialMultiply(x, y))
    });
    const quotient = algebraPolynomialFreydCokernel(morphism);
    return { ring, morphism, monoTest, quotient };
};

describe('v3.2 polynomial Freyd Abelian category', () => {
    it('qualifies only after all normality and image roles are plannable', () => {
        const value = fixture();
        const model = algebraPolynomialFreydAbelianCategoryModel(value.ring);
        assert.equal(model.qualification.status, 'qualified');
        assert.equal(model.tower.outputDoctrineId, 'abelian-category');
        assert.deepEqual(model.qualification.missingRoles, []);
        assert.equal(model.tower.constructors.at(-1)?.introducedRoles.length, 14);
        [
            'monomorphism-witness',
            'epimorphism-witness',
            'lift-along-monomorphism',
            'colift-along-epimorphism',
            'image',
            'coimage',
            'coimage-image-comparison',
            'coimage-image-isomorphism'
        ].forEach(role => assert.ok(
            model.qualification.requiredRoles.includes(role),
            role
        ));
        assert.equal(model.base.qualification.status, 'qualified');
    });

    it('executes normality and every image/coimage observation', async () => {
        const value = fixture();
        const model = algebraPolynomialFreydAbelianCategoryModel(value.ring);
        const mono = await executeCategoryOperation(
            model.category,
            model.operations.monomorphismWitness,
            value.morphism
        );
        const lift = await executeCategoryOperation(
            model.category,
            model.operations.liftAlongMonomorphism,
            { morphism: value.morphism, test: value.monoTest }
        );
        const epi = await executeCategoryOperation(
            model.category,
            model.operations.epimorphismWitness,
            value.quotient.projection
        );
        const colift = await executeCategoryOperation(
            model.category,
            model.operations.coliftAlongEpimorphism,
            {
                morphism: value.quotient.projection,
                test: value.quotient.projection
            }
        );
        assert.equal(mono.value.monic, true);
        assert.equal(lift.value.reconstructs, true);
        assert.equal(epi.value.epic, true);
        assert.equal(colift.value.reconstructs, true);

        const iso = (await executeCategoryOperation(
            model.category,
            model.operations.coimageImageIsomorphism,
            value.morphism
        )).value;
        const observations = await Promise.all([
            executeCategoryOperation(model.category, model.operations.image,
                value.morphism),
            executeCategoryOperation(model.category, model.operations.imageObject,
                value.morphism),
            executeCategoryOperation(model.category, model.operations.imageEmbedding,
                value.morphism),
            executeCategoryOperation(model.category,
                model.operations.coastrictionToImage, value.morphism),
            executeCategoryOperation(model.category, model.operations.coimage,
                value.morphism),
            executeCategoryOperation(model.category, model.operations.coimageObject,
                value.morphism),
            executeCategoryOperation(model.category,
                model.operations.coimageProjection, value.morphism),
            executeCategoryOperation(model.category,
                model.operations.astrictionFromCoimage, value.morphism),
            executeCategoryOperation(model.category,
                model.operations.coimageImageComparison, value.morphism)
        ]);
        assert.equal(iso.isomorphism, true);
        assert.equal(observations[0].value.kind, 'algebra-polynomial-freyd-kernel');
        assert.equal(model.category.equalObjects(
            observations[1].value as typeof iso.comparison.image.object,
            iso.comparison.image.object
        ), true);
        assert.equal(model.category.equalMorphisms(
            observations[8].value as typeof iso.comparison.comparison,
            iso.comparison.comparison
        ), true);
        assert.equal(
            lift.plan.prerequisites[0].operation.id,
            model.operations.monomorphismWitness.id
        );
    });

    it('compiles and executes normality plus whole isomorphism graphs', async () => {
        const value = fixture();
        const model = algebraPolynomialFreydAbelianCategoryModel(value.ring);
        const builder = createCategoricalProgramBuilder(
            'polynomial-freyd-abelian.operations',
            'v1'
        );
        const morphism = builder.input(
            'morphism',
            model.operations.coimageImageIsomorphism.input
        );
        const liftInput = builder.input(
            'lift-input',
            model.operations.liftAlongMonomorphism.input
        );
        const iso = builder.operation(
            'iso',
            model.operations.coimageImageIsomorphism,
            morphism
        );
        const lift = builder.operation(
            'lift',
            model.operations.liftAlongMonomorphism,
            liftInput
        );
        const compilation = compileAlgebraPolynomialFreydAbelianProgram(
            model,
            builder.build([
                { id: 'iso', value: iso },
                { id: 'lift', value: lift }
            ])
        );
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph,
            engine: createAlgebraPolynomialFreydAbelianEngine(model),
            inputs: [
                { id: 'morphism', value: value.morphism },
                {
                    id: 'lift-input',
                    value: { morphism: value.morphism, test: value.monoTest }
                }
            ]
        });
        assert.equal(
            (execution.outputs[0].value as { isomorphism: boolean }).isomorphism,
            true
        );
        assert.equal(
            (execution.outputs[1].value as { reconstructs: boolean }).reconstructs,
            true
        );
        assert.equal(compilation.nodes.length, 2);
    });

    it('inherits pre-Abelian methods and rejects non-field coefficients', () => {
        const value = fixture();
        const model = algebraPolynomialFreydAbelianCategoryModel(value.ring);
        assert.ok(model.category.operations.methods.some(method =>
            method.operation.id === model.base.operations.kernel.id
        ));
        const integerRing = algebraPolynomialRing(INTEGER_DOMAIN, ['x'], 'lex');
        assert.throws(
            () => algebraPolynomialFreydAbelianCategoryModel(integerRing),
            /requires field coefficients/u
        );
    });
});
