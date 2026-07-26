/**
 * Focused USABILITY-1D ergonomic categorical-program facade tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import * as browserApi from '../src/v3_2/browser';
import {
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    coreCategoricalDiagnosticFromError
} from '../src/v3_2';

const program = (
    sourceFile = 'tests/fixtures/categorical-program.ts'
) => new CoreCategoricalProgram({ sourceFile });

describe('TypeScript v3.2 USABILITY-1D categorical program', () => {
    it('freezes the exact deterministic identity fixture', () => {
        const emdash = program();
        const A = emdash.category('A', { line: 1 });
        let callbackCount = 0;
        const identity = emdash.lambda(
            'x',
            A,
            A,
            x => {
                callbackCount += 1;
                return x;
            },
            { source: { line: 2 } }
        );
        const result = emdash.compile(identity);

        assert.equal(callbackCount, 1);
        assert.equal(
            result.explicitCore,
            '(call ' +
            '(free "emdash.categorical.identity-functor") ' +
            '(implicit (free "A")))'
        );
        assert.equal(
            result.explicitInferredType,
            '(owner "decode" ' +
            '(explicit (owner "functor-classifier" ' +
            '(explicit (free "A")) (explicit (free "A")))))'
        );
        assert.deepEqual(
            result.structuralPrerequisites,
            ['identity-functor']
        );
        assert.equal(result.productionLambdapiDependency, false);
    });

    it('checks pointwise application through pairing and evaluation', () => {
        const emdash = program();
        const A = emdash.category('A', { line: 1 });
        const B = emdash.category('B', { line: 2 });
        const C = emdash.category('C', { line: 3 });
        const functorsBC = emdash.functorCategory(B, C, { line: 4 });
        const H = emdash.functor('H', A, functorsBC, { line: 5 });
        const K = emdash.functor('K', A, B, { line: 6 });
        const pointwise = emdash.lambda(
            'x',
            A,
            C,
            x => emdash.apply(
                emdash.apply(H, x, {
                    source: { line: 8, column: 5 }
                }),
                emdash.apply(K, x, {
                    source: { line: 8, column: 10 }
                }),
                { source: { line: 8, column: 1 } }
            ),
            { source: { line: 7 } }
        );
        const result = emdash.compile(pointwise);

        assert.equal(
            result.explicitCore.includes(
                '"emdash.categorical.product-pair"'
            ),
            true
        );
        assert.equal(
            result.explicitCore.includes(
                '"emdash.categorical.evaluation-functor"'
            ),
            true
        );
        assert.equal(
            result.explicitCore.includes('comp_cat_fapp0'),
            false
        );
        assert.deepEqual(
            result.structuralPrerequisites,
            [
                'identity-functor',
                'functor-composition',
                'product-category',
                'product-pair',
                'evaluation-functor'
            ]
        );
        assert.equal(
            result.explicitInferredType,
            result.explicitExpectedType
        );
    });

    it('is alpha- and provenance-invariant after immediate lowering', () => {
        const build = (
            file: string,
            line: number,
            hint: string
        ): string => {
            const emdash = program(file);
            const A = emdash.category('A', { line });
            const B = emdash.category('B', { line: line + 1 });
            const F = emdash.functor('F', A, B, {
                line: line + 2
            });
            return emdash.compile(emdash.lambda(
                hint,
                A,
                B,
                x => emdash.apply(F, x, {
                    source: { line: line + 4 }
                }),
                { source: { line: line + 3 } }
            )).explicitCore;
        };

        assert.equal(
            build('first.ts', 1, 'x'),
            build('second.ts', 80, 'renamed')
        );
    });

    it('exposes object, capped-arrow, and whole-Hom action uniformly', () => {
        const emdash = program();
        const A = emdash.category('A', { line: 1 });
        const B = emdash.category('B', { line: 2 });
        const x = emdash.object('x', A, { line: 3 });
        const y = emdash.object('y', A, { line: 4 });
        const f = emdash.hom('f', A, x, y, { line: 5 });
        const F = emdash.functor('F', A, B, { line: 6 });

        assert.equal(
            emdash.compile(emdash.apply(F, x, {
                source: { line: 7 }
            })).explicitCore.includes('"functor-object"'),
            true
        );
        assert.equal(
            emdash.compile(emdash.apply(F, f, {
                source: { line: 8 }
            })).explicitCore.includes('"functor-hom-capped"'),
            true
        );
        const boundary = emdash.homBoundary(
            A,
            x,
            y,
            { line: 9 }
        );
        assert.equal(
            emdash.compile(emdash.apply(F, boundary, {
                expectedShape: 'whole-hom-action',
                source: { line: 9 }
            })).explicitCore.includes('"functor-hom-full"'),
            true
        );
    });

    it('normalizes a classifier error with its exact source site', () => {
        const emdash = program('bad-program.ts');
        const A = emdash.category('A', { line: 1 });
        const B = emdash.category('B', { line: 2 });
        const C = emdash.category('C', { line: 3 });
        const F = emdash.functor('F', A, B, { line: 4 });
        const c = emdash.object('c', C, { line: 5 });

        let captured: unknown;
        try {
            emdash.apply(F, c, {
                source: {
                    line: 41,
                    column: 9,
                    detail: 'F applied to wrong-category c'
                }
            });
        } catch (error: unknown) {
            captured = error;
        }
        const normalized =
            coreCategoricalDiagnosticFromError(captured);
        assert.deepEqual(normalized, {
            phase: 'surface',
            code: 'CLASSIFIER_ARGUMENT_MISMATCH',
            message:
                'Argument is neither an object nor an arrow of the ' +
                'functor source category at bad-program.ts:41:9',
            detail: 'F applied to wrong-category c',
            span: {
                file: 'bad-program.ts',
                start: { line: 41, column: 9 },
                end: { line: 41, column: 10 }
            },
            location: 'bad-program.ts:41:9'
        });
    });

    it('rejects categories from another program with a stable diagnostic', () => {
        const first = program('first-program.ts');
        const second = program('second-program.ts');
        const foreign = first.category('A', { line: 1 });
        assert.throws(
            () => second.object('x', foreign, {
                line: 12,
                column: 4
            }),
            error => {
                const normalized =
                    coreCategoricalDiagnosticFromError(error);
                return (
                    error instanceof CoreCategoricalProgramError &&
                    normalized?.code === 'FOREIGN_CATEGORY' &&
                    normalized.location === 'second-program.ts:12:4'
                );
            }
        );
    });

    it('keeps the facade and serializer out of the frozen browser API', () => {
        assert.equal('CoreCategoricalProgram' in browserApi, false);
        assert.equal('serializeCoreExpression' in browserApi, false);
        assert.equal(
            'serializeCoreCategoricalExpression' in browserApi,
            false
        );
    });
});
