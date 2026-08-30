/** Focused AFFINE-MAPS-1B relation-checked algebra-map tests. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import { RATIONAL_DOMAIN } from '../src/v3_2/algebra_exact';
import { algebraPolynomialIdeal } from '../src/v3_2/algebra_ideal';
import {
    algebraPolynomialAdd,
    algebraPolynomialOne,
    algebraPolynomialPower,
    algebraPolynomialRing,
    algebraPolynomialVariable
} from '../src/v3_2/algebra_polynomial';
import {
    algebraPolynomialQuotientRing,
    algebraQuotientElement,
    algebraQuotientEquals,
    algebraQuotientText
} from '../src/v3_2/algebra_quotient';
import {
    ALGEBRA_PRESENTED_ALGEBRA_PROFILE,
    AlgebraPresentedAlgebraError,
    algebraPresentedAlgebra,
    algebraPresentedAlgebraMap,
    algebraPresentedAlgebraMapApply,
    algebraPresentedAlgebraMapCompose,
    algebraPresentedAlgebraMapEquals,
    algebraPresentedAlgebraMapIdentity,
    algebraPresentedAlgebraMapSchema
} from '../src/v3_2/algebra_presented_algebra';
import { algebraPresentedMapReferenceOperations } from '../src/v3_2/algebra_presented_algebra_reference_operations';
import {
    createAlgebraComputationGraphBuilder,
    executeAlgebraComputationGraph
} from '../src/v3_2/algebra_graph';
import { createAlgebraTypeScriptReferenceEngine } from '../src/v3_2/algebra_reference_engine';

const mapError = (code: AlgebraPresentedAlgebraError['code']) =>
    (error: unknown) => {
        assert.ok(error instanceof AlgebraPresentedAlgebraError);
        assert.equal(error.code, code);
        return true;
    };

const algebra = (variable: string) => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [variable], 'lex');
    const generator = algebraPolynomialVariable(ring, 0);
    const quotient = algebraPolynomialQuotientRing(algebraPolynomialIdeal(ring, [
        algebraPolynomialPower(generator, 2n)
    ]));
    return {
        ring,
        generator,
        quotient,
        algebra: algebraPresentedAlgebra(quotient)
    };
};

describe('v3.2 finitely presented algebras and maps', () => {
    it('constructs a map exactly when source relations vanish', () => {
        const source = algebra('x');
        const target = algebra('y');
        const map = algebraPresentedAlgebraMap(
            source.algebra,
            target.algebra,
            [algebraQuotientElement(target.quotient, target.generator)]
        );
        assert.equal(map.generatorImages.length, 1);
        assert.equal(map.relationImages.length, 1);
        assert.equal(algebraQuotientText(map.relationImages[0].image), '[0]');
        assert.equal(ALGEBRA_PRESENTED_ALGEBRA_PROFILE.mapValidation,
            'source-relations-evaluate-to-canonical-zero');
        assert.ok(Object.isFrozen(map));
        assert.ok(Object.isFrozen(map.relationImages));
    });

    it('rejects a generator image that violates a source relation', () => {
        const source = algebra('x');
        const target = algebra('y');
        assert.throws(
            () => algebraPresentedAlgebraMap(
                source.algebra,
                target.algebra,
                [algebraQuotientElement(
                    target.quotient,
                    algebraPolynomialOne(target.ring)
                )]
            ),
            mapError('SOURCE_RELATION_FAILED')
        );
        assert.throws(
            () => algebraPresentedAlgebraMap(source.algebra, target.algebra, []),
            mapError('INVALID_GENERATOR_IMAGES')
        );
    });

    it('applies maps to canonical quotient elements', () => {
        const source = algebra('x');
        const target = algebra('y');
        const map = algebraPresentedAlgebraMap(
            source.algebra,
            target.algebra,
            [algebraQuotientElement(target.quotient, target.generator)]
        );
        const value = algebraQuotientElement(
            source.quotient,
            algebraPolynomialAdd(
                source.generator,
                algebraPolynomialOne(source.ring)
            )
        );
        assert.equal(algebraQuotientText(algebraPresentedAlgebraMapApply(map, value)),
            '[1*y + 1]');
    });

    it('computes identity and composition from generator images', () => {
        const first = algebra('x');
        const second = algebra('y');
        const third = algebra('z');
        const xy = algebraPresentedAlgebraMap(
            first.algebra,
            second.algebra,
            [algebraQuotientElement(second.quotient, second.generator)]
        );
        const yz = algebraPresentedAlgebraMap(
            second.algebra,
            third.algebra,
            [algebraQuotientElement(third.quotient, third.generator)]
        );
        const xz = algebraPresentedAlgebraMapCompose(yz, xy);
        assert.ok(algebraQuotientEquals(
            xz.generatorImages[0],
            algebraQuotientElement(third.quotient, third.generator)
        ));
        const identity = algebraPresentedAlgebraMapIdentity(first.algebra);
        assert.ok(algebraPresentedAlgebraMapEquals(
            algebraPresentedAlgebraMapCompose(xy, identity),
            xy
        ));
    });

    it('uses canonical generator images for map equality', () => {
        const source = algebra('x');
        const target = algebra('y');
        const first = algebraPresentedAlgebraMap(
            source.algebra,
            target.algebra,
            [algebraQuotientElement(target.quotient, target.generator)]
        );
        const second = algebraPresentedAlgebraMap(
            source.algebra,
            target.algebra,
            [algebraQuotientElement(
                target.quotient,
                algebraPolynomialAdd(
                    target.generator,
                    algebraPolynomialPower(target.generator, 2n)
                )
            )]
        );
        assert.equal(algebraPresentedAlgebraMapEquals(first, second), true);
        assert.equal(
            algebraPresentedAlgebraMapSchema(
                source.algebra,
                target.algebra
            ).normalize(second, 'map').kind,
            'algebra-presented-algebra-map'
        );
    });

    it('rejects foreign source elements and noncomposable maps', () => {
        const first = algebra('x');
        const second = algebra('y');
        const third = algebra('z');
        const xy = algebraPresentedAlgebraMap(
            first.algebra,
            second.algebra,
            [algebraQuotientElement(second.quotient, second.generator)]
        );
        assert.throws(
            () => algebraPresentedAlgebraMapApply(
                xy,
                algebraQuotientElement(third.quotient, third.generator) as never
            ),
            mapError('FOREIGN_SOURCE_ALGEBRA')
        );
        const zx = algebraPresentedAlgebraMap(
            third.algebra,
            first.algebra,
            [algebraQuotientElement(first.quotient, first.generator)]
        );
        assert.throws(
            () => algebraPresentedAlgebraMapCompose(zx, xy),
            mapError('NON_COMPOSABLE_ALGEBRA_MAPS')
        );
    });

    it('applies a validated algebra map in a retained graph', async () => {
        const source = algebra('x');
        const target = algebra('y');
        const map = algebraPresentedAlgebraMap(
            source.algebra,
            target.algebra,
            [algebraQuotientElement(target.quotient, target.generator)]
        );
        const operations = algebraPresentedMapReferenceOperations(map);
        const builder = createAlgebraComputationGraphBuilder(
            'fixture.presented-map.apply',
            'v1'
        );
        const input = builder.input('element', operations.apply.input);
        const output = builder.operation('image', operations.apply, input);
        const execution = await executeAlgebraComputationGraph({
            graph: builder.build([{ id: 'result', value: output }]),
            engine: createAlgebraTypeScriptReferenceEngine({
                implementations: operations.implementations
            }),
            inputs: [{
                id: 'element',
                value: algebraQuotientElement(
                    source.quotient,
                    algebraPolynomialAdd(
                        source.generator,
                        algebraPolynomialOne(source.ring)
                    )
                )
            }]
        });
        assert.equal(
            algebraQuotientText(
                execution.outputs[0].value as ReturnType<typeof algebraQuotientElement>
            ),
            '[1*y + 1]'
        );
    });
});
