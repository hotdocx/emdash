/**
 * Focused D-DTTLF-USABILITY-033 recursive-mixed text-parity tests.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_TEXT_REVISION,
    CoreCategoricalCategory,
    CoreCategoricalProgram,
    CoreCategoricalTerm,
    CoreCategoricalTextBinding,
    CoreCategoricalTextError,
    elaborateCoreCategoricalText
} from '../src/v3_2';

const sourceFile =
    'tests/fixtures/categorical-text-recursive-mixed.emdash';

const routedCategory = (
    label: string
): CoreCategoricalCategory => Object.freeze({
    routeKind: 'category',
    label
}) as unknown as CoreCategoricalCategory;

const routedTerm = (
    label: string
): CoreCategoricalTerm => Object.freeze({
    routeKind: 'term',
    label
}) as unknown as CoreCategoricalTerm;

interface HomRouteCall {
    readonly category: CoreCategoricalCategory;
    readonly source: CoreCategoricalTerm;
    readonly target: CoreCategoricalTerm;
    readonly result: CoreCategoricalCategory;
}

const assertTextError = (
    action: () => unknown,
    code: CoreCategoricalTextError['code'],
    startColumn?: number
): void => {
    assert.throws(
        action,
        error => {
            assert.ok(error instanceof CoreCategoricalTextError);
            assert.equal(error.code, code);
            if (startColumn !== undefined) {
                assert.equal(error.span.start.line, 1);
                assert.equal(error.span.start.column, startColumn);
            }
            return true;
        }
    );
};

describe('D-033 recursive-mixed text parity', () => {
    it('routes recursive hom category spines through one typed method', () => {
        const C = routedCategory('C');
        const x = routedTerm('x');
        const y = routedTerm('y');
        const f = routedTerm('f');
        const g = routedTerm('g');
        const calls: HomRouteCall[] = [];
        const routingProgram = {
            inspect: (value: CoreCategoricalTerm): unknown => value,
            serializeCategory: (): string => 'routed-category',
            homCategory: (
                category: CoreCategoricalCategory,
                source: CoreCategoricalTerm,
                target: CoreCategoricalTerm
            ): CoreCategoricalCategory => {
                const result = routedCategory(`hom-${calls.length}`);
                calls.push(Object.freeze({
                    category,
                    source,
                    target,
                    result
                }));
                return result;
            }
        } as unknown as CoreCategoricalProgram;
        const environment: readonly CoreCategoricalTextBinding[] =
            Object.freeze([
                { name: 'C', kind: 'category', value: C },
                { name: 'x', kind: 'term', value: x },
                { name: 'y', kind: 'term', value: y },
                { name: 'f', kind: 'term', value: f },
                { name: 'g', kind: 'term', value: g }
            ]);

        const result = elaborateCoreCategoricalText(
            routingProgram,
            {
                source: 'hom (hom C x y) f g',
                sourceFile,
                environment,
                expected: { kind: 'category' }
            }
        );

        assert.equal(calls.length, 2);
        assert.deepEqual(
            calls[0],
            {
                category: C,
                source: x,
                target: y,
                result: calls[0].result
            }
        );
        assert.equal(calls[1].category, calls[0].result);
        assert.equal(calls[1].source, f);
        assert.equal(calls[1].target, g);
        assert.equal(result, calls[1].result);
    });

    it('agrees with direct construction for ordinary Hom', () => {
        const program = new CoreCategoricalProgram({ sourceFile });
        const A = program.category('text_recursive_A');
        const x = program.object('text_recursive_x', A);
        const y = program.object('text_recursive_y', A);
        const parsed = elaborateCoreCategoricalText(program, {
            source: 'hom A x y',
            sourceFile,
            environment: Object.freeze([
                { name: 'A', kind: 'category', value: A },
                { name: 'x', kind: 'term', value: x },
                { name: 'y', kind: 'term', value: y }
            ]),
            expected: { kind: 'category' }
        });
        const direct = program.homCategory(A, x, y);

        assert.equal(
            program.compareCategories(parsed, direct).status,
            'equal'
        );
    });

    it('recurses for two named Hom levels over the canonical mixed fibre',
        () => {
            const program = new CoreCategoricalProgram({
                sourceFile,
                profile: 'fibred-displayed-mixed-nest-1'
            });
            const K = program.category('text_recursive_mixed_K');
            const Z = program.category('text_recursive_mixed_Z');
            const E = program.displayedFamily(
                'text_recursive_mixed_E',
                Z
            );
            const D = program.displayedFamily(
                'text_recursive_mixed_D',
                Z
            );
            const classifier = program.constantDisplayedFamily(
                K,
                program.displayedFunctorCategory(E, D)
            );
            const FFbar = program.section(
                'text_recursive_mixed_FFbar',
                program.oppositeDisplayedFamily(classifier)
            );
            const GGbar = program.section(
                'text_recursive_mixed_GGbar',
                classifier
            );
            const nested = program.mixedDisplayedHomFamily(
                classifier,
                FFbar,
                GGbar
            );
            const k = program.object('text_recursive_mixed_k', K);
            const root = program.fibre(nested, k);
            const theta = program.object(
                'text_recursive_mixed_theta',
                root
            );
            const eta = program.object(
                'text_recursive_mixed_eta',
                root
            );
            const first = program.homCategory(root, theta, eta);
            const alpha = program.hom(
                'text_recursive_mixed_alpha',
                root,
                theta,
                eta
            );
            const beta = program.hom(
                'text_recursive_mixed_beta',
                root,
                theta,
                eta
            );
            const direct = program.homCategory(first, alpha, beta);
            const environment: readonly CoreCategoricalTextBinding[] =
                Object.freeze([
                    {
                        name: 'Nested',
                        kind: 'displayed-family',
                        value: nested
                    },
                    { name: 'k', kind: 'term', value: k },
                    { name: 'theta', kind: 'term', value: theta },
                    { name: 'eta', kind: 'term', value: eta },
                    { name: 'alpha', kind: 'term', value: alpha },
                    { name: 'beta', kind: 'term', value: beta }
                ]);

            const parsed = elaborateCoreCategoricalText(program, {
                source:
                    'hom (hom (fibre Nested k) theta eta) alpha beta',
                sourceFile,
                environment,
                expected: { kind: 'category' }
            });

            assert.equal(
                program.compareCategories(parsed, direct).status,
                'equal'
            );
        }
    );

    it('fails closed on arity, kinds, endpoints, and foreign values', () => {
        const program = new CoreCategoricalProgram({ sourceFile });
        const A = program.category('text_recursive_negative_A');
        const B = program.category('text_recursive_negative_B');
        const x = program.object('text_recursive_negative_x', A);
        const y = program.object('text_recursive_negative_y', A);
        const b = program.object('text_recursive_negative_b', B);
        const foreignProgram = new CoreCategoricalProgram({
            sourceFile: 'tests/fixtures/categorical-text-foreign.emdash'
        });
        const foreignA = foreignProgram.category(
            'text_recursive_negative_foreign_A'
        );
        const foreign = foreignProgram.object(
            'text_recursive_negative_foreign',
            foreignA
        );
        const environment: readonly CoreCategoricalTextBinding[] =
            Object.freeze([
                { name: 'A', kind: 'category', value: A },
                { name: 'B', kind: 'category', value: B },
                { name: 'x', kind: 'term', value: x },
                { name: 'y', kind: 'term', value: y },
                { name: 'b', kind: 'term', value: b },
                { name: 'foreign', kind: 'term', value: foreign }
            ]);
        const parse = (source: string): CoreCategoricalCategory =>
            elaborateCoreCategoricalText(program, {
                source,
                sourceFile,
                environment,
                expected: { kind: 'category' }
            });

        assertTextError(
            () => parse('hom A x'),
            'EXPECTED_CATEGORY',
            1
        );
        assertTextError(
            () => parse('hom x x y'),
            'EXPECTED_CATEGORY',
            5
        );
        assertTextError(
            () => parse('hom A A y'),
            'EXPECTED_TERM',
            7
        );
        assertTextError(
            () => parse('hom A x b'),
            'CATEGORICAL_REJECTION',
            1
        );
        assertTextError(
            () => parse('hom A x foreign'),
            'CATEGORICAL_REJECTION',
            9
        );
    });

    it('publishes the reviewed recursive-mixed adapter revision', () => {
        assert.equal(
            CORE_CATEGORICAL_TEXT_REVISION,
            'CONTEXTUAL-ND-TELESCOPE-TEXT-PARITY-1AN-CATEGORICAL-TEXT-1'
        );
    });
});
