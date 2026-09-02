/** Constant-field and CAP differential for the polynomial Freyd snake map. */

import assert from 'node:assert/strict';
import { describe, it } from 'node:test';
import {
    ALGEBRA_MODULE_CAP_SNAKE_REFERENCE_PROFILE,
    RATIONAL_DOMAIN,
    algebraFreeModule,
    algebraMatrix,
    algebraMatrixMultiply,
    algebraMatrixSpace,
    algebraModuleCapSnakeConnecting,
    algebraModuleRealization,
    algebraModuleMorphism,
    algebraPolynomialConstant,
    algebraPolynomialFreeModule,
    algebraPolynomialFreydSnakeConnecting,
    algebraPolynomialFreydSnakeTriple,
    algebraPolynomialModuleMap,
    algebraPolynomialModuleVector,
    algebraPolynomialPresentationMorphism,
    algebraPolynomialRing,
    algebraPolynomialSubmodule,
    algebraPolynomialText,
    algebraPresentedPolynomialModule,
    algebraPresentedModule,
    algebraZeroMatrix
} from '../src/v3_2';

const CAP_SOURCE = Object.freeze({
    repository: 'homalg-project/CAP_project',
    commit: 'd21dc5f5f420829f53cf3e00eef7d971cfa6ea8b',
    path: 'Manual/GAP_tex/vecspaces_example/SnakeLemmaImplementation.tex'
});

const EXPECTED_RAW_CONNECTING = Object.freeze([
    Object.freeze(['0', '0']),
    Object.freeze(['0', '-1'])
]);

const EXPECTED_INDUCED_CONNECTING = Object.freeze([
    Object.freeze(['-1'])
]);

const fieldFixture = () => {
    const module = (dimension: number) =>
        algebraFreeModule(RATIONAL_DOMAIN, dimension);
    const zeroWitness = () => algebraZeroMatrix(algebraMatrixSpace(
        RATIONAL_DOMAIN,
        0,
        0
    ));
    const morphism = (
        sourceDimension: number,
        targetDimension: number,
        entries: readonly (readonly string[])[]
    ) => algebraModuleMorphism(
        module(sourceDimension),
        module(targetDimension),
        algebraMatrix(
            algebraMatrixSpace(
                RATIONAL_DOMAIN,
                targetDimension,
                sourceDimension
            ),
            entries
        ),
        zeroWitness()
    );
    return {
        delta: morphism(2, 2, [['1', '0'], ['0', '0']]),
        beta: morphism(2, 3, [['2', '3'], ['4', '5'], ['0', '0']]),
        lambda: morphism(3, 1, [['0', '0', '1']])
    };
};

const polynomialFixture = () => {
    const ring = algebraPolynomialRing(RATIONAL_DOMAIN, [], 'lex');
    const module = (rank: number) => algebraPolynomialFreeModule(ring, rank);
    const presentation = (rank: number) => {
        const ambient = module(rank);
        return algebraPresentedPolynomialModule(
            algebraPolynomialSubmodule(ambient, [])
        );
    };
    const A = presentation(2);
    const B = presentation(2);
    const X = presentation(3);
    const D = presentation(1);
    const scalar = (value: string) => algebraPolynomialConstant(ring, value);
    const morphism = (
        source: typeof A,
        target: typeof A,
        columns: readonly (readonly string[])[]
    ) => algebraPolynomialPresentationMorphism({
        source,
        target,
        map: algebraPolynomialModuleMap(
            source.ambient,
            target.ambient,
            columns.map(column => algebraPolynomialModuleVector(
                target.ambient,
                column.map(scalar)
            ))
        )
    });
    return {
        delta: morphism(A, B, [['1', '0'], ['0', '0']]),
        beta: morphism(B, X, [['2', '4', '0'], ['3', '5', '0']]),
        lambda: morphism(X, D, [['0'], ['0'], ['1']])
    };
};

const fieldMatrixFromColumns = (
    rows: number,
    columns: readonly (readonly string[])[]
) => algebraMatrix(
    algebraMatrixSpace(RATIONAL_DOMAIN, rows, columns.length),
    Array.from({ length: rows }, (_, row) =>
        columns.map(column => column[row]))
);

describe('v3.2 polynomial Freyd snake differential', () => {
    it('agrees with an independent split-field CAP construction', () => {
        const field = fieldFixture();
        const fieldResult = algebraModuleCapSnakeConnecting(
            field.delta,
            field.beta,
            field.lambda
        );
        const polynomial = polynomialFixture();
        const polynomialResult = algebraPolynomialFreydSnakeConnecting(
            algebraPolynomialFreydSnakeTriple(
                polynomial.delta,
                polynomial.beta,
                polynomial.lambda
            )
        );
        const fieldEntries = fieldResult.connecting.entries.map(row =>
            row.map(RATIONAL_DOMAIN.text)
        );
        const polynomialRawEntries = polynomialResult.connecting.map.columns
            .map(column => column.components.map(algebraPolynomialText));
        const source = algebraPresentedModule(
            RATIONAL_DOMAIN,
            polynomialResult.connecting.source.ambient.rank,
            fieldMatrixFromColumns(
                polynomialResult.connecting.source.ambient.rank,
                polynomialResult.connecting.source.relations.generators.map(
                    relation => relation.components.map(algebraPolynomialText)
                )
            )
        );
        const target = algebraPresentedModule(
            RATIONAL_DOMAIN,
            polynomialResult.connecting.target.ambient.rank,
            fieldMatrixFromColumns(
                polynomialResult.connecting.target.ambient.rank,
                polynomialResult.connecting.target.relations.generators.map(
                    relation => relation.components.map(algebraPolynomialText)
                )
            )
        );
        const polynomialRawMatrix = fieldMatrixFromColumns(
            polynomialResult.connecting.target.ambient.rank,
            polynomialResult.connecting.map.columns.map(column =>
                column.components.map(algebraPolynomialText)
            )
        );
        const polynomialInduced = algebraMatrixMultiply(
            algebraMatrixMultiply(
                algebraModuleRealization(target).projection,
                polynomialRawMatrix
            ),
            algebraModuleRealization(source).section
        );
        const polynomialInducedEntries = polynomialInduced.entries.map(row =>
            row.map(RATIONAL_DOMAIN.text)
        );
        assert.deepEqual(polynomialRawEntries, EXPECTED_RAW_CONNECTING);
        assert.deepEqual(fieldEntries, EXPECTED_INDUCED_CONNECTING);
        assert.deepEqual(polynomialInducedEntries, EXPECTED_INDUCED_CONNECTING);
        assert.deepEqual(fieldEntries, polynomialInducedEntries);
        assert.equal(fieldResult.fiberCompatible, true);
        assert.equal(fieldResult.pushoutCompatible, true);
        assert.equal(fieldResult.uReconstructs, true);
        assert.equal(fieldResult.connectingReconstructs, true);
        assert.equal(fieldResult.nonAuthoritative, true);
        assert.equal(
            ALGEBRA_MODULE_CAP_SNAKE_REFERENCE_PROFILE.suitableForGeneralModules,
            false
        );
        assert.equal(CAP_SOURCE.commit.length, 40);
    });
});
