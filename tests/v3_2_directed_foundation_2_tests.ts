/**
 * Executable boundary for the approved DIRECTED-FOUNDATION-2 runtime.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_DIRECTED_FOUNDATION_2_REVIEW,
    CoreDirectedFoundation2RuntimeProgram,
    CoreLfDeclarationEnvironment,
    KernelExpression,
    coreLfDefinitionalCompare,
    kernelApplication,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from '../src/v3_2';

const because = (detail: string) =>
    provenance('derived', `DIRECTED-FOUNDATION-2 test ${detail}`);

const owner = (
    name: Parameters<typeof kernelApplication>[0],
    arguments_: readonly KernelExpression[] = []
): KernelExpression => kernelApplication(
    name,
    arguments_.map(value => ({ value })),
    because(`owner ${name}`)
);

const A = kernelFree('foundation2_A', because('A'));
const B = kernelFree('foundation2_B', because('B'));
const categoryOfCategories = owner('category-of-categories');

const rawCatHom = (
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => owner('hom-classifier', [
    categoryOfCategories,
    source,
    target
]);

const decodedCatHom = (
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => owner('decode', [rawCatHom(source, target)]);

const decodedFunctor = (
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => owner('decode', [
    owner('functor-classifier', [source, target])
]);

describe('TypeScript v3.2 reviewed DIRECTED foundation 2 runtime', () => {
    it('compiles exactly the one approved rule', () => {
        const runtime =
            CoreDirectedFoundation2RuntimeProgram.create();
        assert.equal(
            runtime.revision,
            'DIRECTED-FOUNDATION-2-REVIEWED'
        );
        assert.deepEqual(
            runtime.ruleIds,
            ['directed.category-hom.decode']
        );
        assert.deepEqual(
            runtime.ruleIds,
            CORE_DIRECTED_FOUNDATION_2_REVIEW.authorization
                .runtimeRuleIds
        );
        assert.equal(Object.isFrozen(runtime), true);
        assert.equal(Object.isFrozen(runtime.rules), true);
        assert.equal(Object.isFrozen(runtime.ruleIds), true);
    });

    it('rewrites only decoded Cat hom to the decoded functor classifier', () => {
        const runtime =
            CoreDirectedFoundation2RuntimeProgram.create();
        const result = runtime.rewriteHead(decodedCatHom(A, B));
        assert.equal(result.status, 'rewritten');
        if (result.status !== 'rewritten') return;
        assert.equal(result.ruleId, 'directed.category-hom.decode');
        assert.equal(result.ruleIndex, 0);
        assert.deepEqual(result.match.bindings, [A, B]);
        assert.equal(
            kernelExpressionEquals(
                result.after,
                decodedFunctor(A, B)
            ),
            true
        );
    });

    it('is opt-in and preserves endpoint orientation', () => {
        const environment = CoreLfDeclarationEnvironment.empty();
        const runtime =
            CoreDirectedFoundation2RuntimeProgram.create();
        const left = decodedCatHom(A, B);
        const right = decodedFunctor(A, B);

        assert.equal(
            coreLfDefinitionalCompare(
                environment,
                left,
                right,
                4
            ).status,
            'not-equal'
        );
        const reviewed = coreLfDefinitionalCompare(
            environment,
            left,
            right,
            4,
            undefined,
            runtime
        );
        assert.equal(reviewed.status, 'equal');
        assert.equal(reviewed.steps, 1);
        assert.equal(
            coreLfDefinitionalCompare(
                environment,
                left,
                decodedFunctor(B, A),
                4,
                undefined,
                runtime
            ).status,
            'not-equal'
        );
    });

    it('leaves raw classifiers, category heads, and non-Cat homs irreducible', () => {
        const runtime =
            CoreDirectedFoundation2RuntimeProgram.create();
        const stable = [
            rawCatHom(A, B),
            owner('hom-category', [
                categoryOfCategories,
                A,
                B
            ]),
            owner('decode', [
                owner('hom-classifier', [
                    owner('opposite-category', [
                        categoryOfCategories
                    ]),
                    A,
                    B
                ])
            ]),
            owner('decode', [
                owner('hom-classifier', [
                    A,
                    A,
                    B
                ])
            ])
        ];

        for (const expression of stable) {
            assert.equal(
                runtime.rewriteHead(expression).status,
                'irreducible'
            );
        }
    });
});
