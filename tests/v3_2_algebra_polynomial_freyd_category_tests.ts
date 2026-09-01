/** Focused direct Freyd category and representable-element tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    RATIONAL_DOMAIN,
    algebraPolynomialFreydCategoryModel,
    algebraPolynomialFreydElement,
    algebraPolynomialFreydElementAgreement,
    algebraPolynomialFreeModule,
    algebraPolynomialModuleVector,
    algebraPolynomialOne,
    algebraPolynomialPresentationMorphismAdd,
    algebraPolynomialPresentationMorphismCongruence,
    algebraPolynomialPresentationMorphismIdentity,
    algebraPolynomialPresentationMorphismNegate,
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

    it('records weak-kernel evidence without claiming Abelian structure', () => {
        const ring = algebraPolynomialRing(RATIONAL_DOMAIN, ['x'], 'lex');
        const capability = algebraPolynomialWeakKernelCapability(ring);
        assert.equal(capability.basis, 'groebner-syzygy');
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
            'generating-raw-classes'
        );
        assert.equal(
            model.additiveHomOperations.zero(presentation, presentation)
                .preservesRelations,
            true
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
