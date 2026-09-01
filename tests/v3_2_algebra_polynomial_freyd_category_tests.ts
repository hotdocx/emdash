/** Focused direct Freyd category and representable-element tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    ALGEBRA_POLYNOMIAL_FREYD_ZERO_OBJECT_INPUT,
    RATIONAL_DOMAIN,
    algebraPolynomialFreydBiproduct,
    algebraPolynomialFreydCategoryModel,
    algebraPolynomialFreydDirectSumPresentation,
    algebraPolynomialFreydElement,
    algebraPolynomialFreydElementAgreement,
    algebraPolynomialFreydZeroPresentation,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleVector,
    algebraPolynomialOne,
    algebraPolynomialPresentationMorphismAdd,
    algebraPolynomialPresentationMorphismCongruence,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialPresentationMorphismNegate,
    algebraPolynomialPresentationMorphismDirectSum,
    algebraPolynomialPresentationMorphismZero,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialVariable,
    algebraPolynomialWeakKernelCapability,
    algebraPolynomialZero,
    algebraPresentedPolynomialModule,
    compileAlgebraPolynomialFreydProgram,
    createAlgebraPolynomialFreydEngine,
    createCategoricalProgramBuilder,
    executeAlgebraComputationGraph,
    executeCategoryOperation,
    serializeAlgebraPolynomialPresentationMorphism
} from '../src/v3_2';

describe('FRP direct polynomial Freyd category', () => {
    it('uses target-relation congruence and representable elements', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x', 'y'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const y = algebraPolynomialVariable(ring, 1);
        const one = algebraPolynomialOne(ring);
        const zero = algebraPolynomialZero(ring);
        const ambient = algebraPolynomialFreeModule(ring, 1);
        const presentation = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [
                algebraPolynomialModuleVector(ambient, [x])
            ])
        );
        const model = algebraPolynomialFreydCategoryModel(ring);
        const identity = algebraPolynomialPresentationMorphismIdentity(presentation);
        assert.equal(model.category.equalMorphisms(
            model.category.compose(identity, identity),
            identity
        ), true);

        const xElement = algebraPolynomialFreydElement(
            presentation,
            algebraPolynomialModuleVector(ambient, [x])
        );
        const zeroElement = algebraPolynomialFreydElement(
            presentation,
            algebraPolynomialModuleVector(ambient, [zero])
        );
        const yElement = algebraPolynomialFreydElement(
            presentation,
            algebraPolynomialModuleVector(ambient, [y])
        );
        const xAgreement = algebraPolynomialFreydElementAgreement(
            xElement,
            zeroElement
        );
        const yAgreement = algebraPolynomialFreydElementAgreement(
            yElement,
            zeroElement
        );
        assert.equal(xAgreement.agrees, true);
        assert.equal(yAgreement.agrees, false);
        assert.equal(algebraPolynomialPresentationMorphismCongruence(
            xElement.morphism,
            zeroElement.morphism
        ).agrees, true);
        assert.equal(model.category.equalMorphisms(
            xElement.morphism,
            zeroElement.morphism
        ), true);
        assert.equal(model.category.equalMorphisms(
            yElement.morphism,
            zeroElement.morphism
        ), false);
        assert.equal(
            algebraPolynomialFreydElement(
                presentation,
                algebraPolynomialModuleVector(ambient, [one])
            ).morphism.preservesRelations,
            true
        );
    });

    it('exposes the qualified provider without claiming Abelian structure', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const capability = algebraPolynomialWeakKernelCapability(ring);
        assert.equal(capability.basis, 'groebner-syzygy');
        assert.equal(capability.qualification, 'qualified');
        assert.equal(capability.provider.qualification.status, 'qualified');
        assert.equal(
            capability.provider.tower.outputDoctrineId,
            'additive-category-with-computational-weak-kernels'
        );
        assert.equal(capability.claimsAbelianStructure, false);
    });

    it('computes additive Hom operations and bilinearity on representatives', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const ambient = algebraPolynomialFreeModule(ring, 1);
        const presentation = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [
                algebraPolynomialModuleVector(ambient, [x])
            ])
        );
        const model = algebraPolynomialFreydCategoryModel(ring);
        const identity = algebraPolynomialPresentationMorphismIdentity(presentation);
        const zero = algebraPolynomialPresentationMorphismZero(
            presentation,
            presentation
        );
        const negative = algebraPolynomialPresentationMorphismNegate(identity);
        const sumWithZero = algebraPolynomialPresentationMorphismAdd(
            identity,
            zero
        );
        const cancellation = algebraPolynomialPresentationMorphismAdd(
            identity,
            negative
        );
        assert.equal(model.category.equalMorphisms(sumWithZero, identity), true);
        assert.equal(model.category.equalMorphisms(cancellation, zero), true);

        const rightDistributed = algebraPolynomialPresentationMorphismAdd(
            model.category.compose(identity, identity),
            model.category.compose(identity, zero)
        );
        assert.equal(model.category.equalMorphisms(
            model.category.compose(identity, sumWithZero),
            rightDistributed
        ), true);

        const leftDistributed = algebraPolynomialPresentationMorphismAdd(
            model.category.compose(identity, identity),
            model.category.compose(zero, identity)
        );
        assert.equal(model.category.equalMorphisms(
            model.category.compose(sumWithZero, identity),
            leftDistributed
        ), true);
        assert.equal(
            model.additiveHomOperations.formalLawBoundary,
            'arbitrary-quotient-points'
        );
        assert.equal(
            model.additiveHomOperations.formalStructure,
            'additive-category'
        );
        assert.equal(
            model.additiveHomOperations.zero(presentation, presentation)
                .preservesRelations,
            true
        );
    });

    it('qualifies and computes the selected additive operations', async () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const x = algebraPolynomialVariable(ring, 0);
        const leftAmbient = algebraPolynomialFreeModule(ring, 1);
        const rightAmbient = algebraPolynomialFreeModule(ring, 2);
        const left = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(leftAmbient, [
                algebraPolynomialModuleVector(leftAmbient, [x])
            ])
        );
        const right = algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(rightAmbient, [])
        );
        const model = algebraPolynomialFreydCategoryModel(ring);

        assert.equal(model.doctrineQualification.status, 'qualified');
        assert.deepEqual(model.doctrineQualification.missingRoles, []);
        assert.deepEqual(model.doctrineQualification.availableRoles, [
            'add-morphisms',
            'biproduct',
            'negate-morphism',
            'zero-morphism',
            'zero-object'
        ]);
        assert.equal(model.tower.outputDoctrineId, 'additive-category');

        const directSum = algebraPolynomialFreydDirectSumPresentation(
            left,
            right
        );
        assert.equal(directSum.ambient.rank, 3);
        assert.equal(directSum.relations.generators.length, 1);

        const zero = algebraPolynomialFreydZeroPresentation(ring);
        assert.equal(zero.ambient.rank, 0);
        assert.equal(zero.relations.generators.length, 0);
        assert.equal(model.category.equalMorphisms(
            model.category.identityMorphism(zero),
            algebraPolynomialPresentationMorphismZero(zero, zero)
        ), true);

        const biproduct = algebraPolynomialFreydBiproduct(left, right);
        assert.equal(biproduct.object.ambient.rank, 3);
        assert.equal(biproduct.injectionLeft.preservesRelations, true);
        assert.equal(biproduct.injectionRight.preservesRelations, true);
        assert.equal(biproduct.projectionLeft.preservesRelations, true);
        assert.equal(biproduct.projectionRight.preservesRelations, true);
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
            algebraPolynomialPresentationMorphismZero(left, right)
        ), true);
        assert.equal(model.category.equalMorphisms(
            model.category.compose(
                biproduct.projectionRight,
                biproduct.injectionRight
            ),
            model.category.identityMorphism(right)
        ), true);
        assert.equal(model.category.equalMorphisms(
            model.category.compose(
                biproduct.projectionLeft,
                biproduct.injectionRight
            ),
            algebraPolynomialPresentationMorphismZero(right, left)
        ), true);
        const diagonal = algebraPolynomialPresentationMorphismAdd(
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

        const directSumIdentity = algebraPolynomialPresentationMorphismDirectSum(
            model.category.identityMorphism(left),
            model.category.identityMorphism(right)
        );
        assert.equal(model.category.equalMorphisms(
            directSumIdentity,
            model.category.identityMorphism(biproduct.object)
        ), true);
        const zeroEndomorphism = algebraPolynomialPresentationMorphismZero(
            left,
            left
        );
        const mixedDirectSum = algebraPolynomialPresentationMorphismDirectSum(
            zeroEndomorphism,
            model.category.identityMorphism(right)
        );
        assert.equal(model.category.equalMorphisms(
            algebraPolynomialPresentationMorphismDirectSum(
                model.category.compose(zeroEndomorphism, zeroEndomorphism),
                model.category.compose(
                    model.category.identityMorphism(right),
                    model.category.identityMorphism(right)
                )
            ),
            model.category.compose(mixedDirectSum, mixedDirectSum)
        ), true);

        const zeroResult = await executeCategoryOperation(
            model.category,
            model.operations.zeroObject,
            ALGEBRA_POLYNOMIAL_FREYD_ZERO_OBJECT_INPUT
        );
        assert.equal(zeroResult.plan.method.id,
            'algebra.polynomial-freyd.zero-object.primitive');
        assert.equal(zeroResult.value.ambient.rank, 0);
        const identityLeft = model.category.identityMorphism(left);
        const zeroLeft = (await executeCategoryOperation(
            model.category,
            model.operations.zeroMorphism,
            { source: left, target: left }
        )).value;
        const sumLeft = (await executeCategoryOperation(
            model.category,
            model.operations.addMorphisms,
            { left: identityLeft, right: zeroLeft }
        )).value;
        assert.equal(model.category.equalMorphisms(sumLeft, identityLeft), true);
        const negativeLeft = (await executeCategoryOperation(
            model.category,
            model.operations.negateMorphism,
            identityLeft
        )).value;
        assert.equal(model.category.equalMorphisms(
            algebraPolynomialPresentationMorphismAdd(
                identityLeft,
                negativeLeft
            ),
            zeroLeft
        ), true);
        const biproductResult = await executeCategoryOperation(
            model.category,
            model.operations.biproduct,
            { left, right }
        );
        assert.equal(biproductResult.value.object.ambient.rank, 3);
        const directSumResult = await executeCategoryOperation(
            model.category,
            model.operations.directSumMorphism,
            {
                left: identityLeft,
                right: model.category.identityMorphism(right)
            }
        );
        assert.equal(model.category.equalMorphisms(
            directSumResult.value,
            model.category.identityMorphism(biproduct.object)
        ), true);

        const builder = createCategoricalProgramBuilder(
            'polynomial-freyd.biproduct-program',
            'v1'
        );
        const pairInput = builder.input(
            'pair',
            model.operations.biproduct.input
        );
        const biproductOutput = builder.operation(
            'biproduct',
            model.operations.biproduct,
            pairInput
        );
        const compilation = compileAlgebraPolynomialFreydProgram(
            model,
            builder.build([{ id: 'result', value: biproductOutput }])
        );
        const execution = await executeAlgebraComputationGraph({
            graph: compilation.graph,
            engine: createAlgebraPolynomialFreydEngine(model),
            inputs: [{ id: 'pair', value: { left, right } }]
        });
        assert.equal(
            compilation.nodes[0].selectedMethodId,
            'algebra.polynomial-freyd.biproduct.primitive'
        );
        assert.equal(
            (execution.outputs[0].value as typeof biproduct).object.ambient.rank,
            3
        );
    });

    it('lowers raw morphism construction through the categorical compiler',
        async () => {
            const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
            const x = algebraPolynomialVariable(ring, 0);
            const ambient = algebraPolynomialFreeModule(ring, 1);
            const presentation = algebraPresentedPolynomialModule(
                algebraPolynomialSubmodule(ambient, [
                    algebraPolynomialModuleVector(ambient, [x])
                ])
            );
            const model = algebraPolynomialFreydCategoryModel(ring);
            const map = algebraPolynomialPresentationMorphismIdentity(presentation);
            const inputValue = {
                source: presentation,
                target: presentation,
                map: map.map
            };
            const builder = createCategoricalProgramBuilder(
                'polynomial-freyd.morphism-program',
                'v1'
            );
            const input = builder.input('input', model.native.morphismInputSchema);
            const output = builder.operation(
                'morphism',
                model.morphismOperation,
                input
            );
            const compilation = compileAlgebraPolynomialFreydProgram(
                model,
                builder.build([{ id: 'result', value: output }])
            );
            const execution = await executeAlgebraComputationGraph({
                graph: compilation.graph,
                engine: createAlgebraPolynomialFreydEngine(model),
                inputs: [{ id: 'input', value: inputValue }]
            });
            assert.equal(
                serializeAlgebraPolynomialPresentationMorphism(
                    execution.outputs[0].value as typeof map
                ),
                serializeAlgebraPolynomialPresentationMorphism(map)
            );
            assert.equal(
                compilation.nodes[0].selectedMethodId,
                'algebra.polynomial-freyd.morphism.primitive'
            );
            assert.equal(compilation.reinterpretationRules.length, 1);
        }
    );
});
