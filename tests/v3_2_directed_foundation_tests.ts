/**
 * Executable boundary for the approved DIRECTED-FOUNDATION-1 runtime.
 */

import assert from 'node:assert/strict';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_DIRECTED_1A_PRIMITIVE_NAMES,
    CORE_DIRECTED_FOUNDATION_REVIEW,
    CoreDirectedFoundationRuntimeProgram,
    CoreLfDeclarationEnvironment,
    KernelExpression,
    binderMode,
    coreLfDefinitionalCompare,
    kernelApplication,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    provenance
} from '../src/v3_2';

const because = (detail: string) =>
    provenance('derived', `DIRECTED-FOUNDATION-1 test ${detail}`);

const owner = (
    name: Parameters<typeof kernelApplication>[0],
    arguments_: readonly KernelExpression[] = []
): KernelExpression => kernelApplication(
    name,
    arguments_.map(value => ({ value })),
    because(`owner ${name}`)
);

const decodeObject = (
    category: KernelExpression
): KernelExpression => owner('decode', [
    owner('object-classifier', [category])
]);

const K = kernelFree('foundation_K', because('K'));
const E = kernelFree('foundation_E', because('E'));
const D = kernelFree('foundation_D', because('D'));
const categoryOfCategories = owner('category-of-categories');

const displayedCategory = owner(
    'displayed-category-category',
    [K]
);

const displayedFunctorCategory = kernelCall(
    kernelFree(
        CORE_DIRECTED_1A_PRIMITIVE_NAMES[
            'displayed-functor-category'
        ],
        because('displayed functor category')
    ),
    [
        { plicity: 'implicit', value: K },
        { plicity: 'explicit', value: E },
        { plicity: 'explicit', value: D }
    ],
    because('displayed functor category call')
);

describe('TypeScript v3.2 reviewed DIRECTED foundation runtime', () => {
    it('compiles exactly the three approved rules in review order', () => {
        const runtime = CoreDirectedFoundationRuntimeProgram.create();
        assert.equal(
            runtime.revision,
            'DIRECTED-FOUNDATION-1-REVIEWED'
        );
        assert.deepEqual(runtime.ruleIds, [
            'directed.category-object.decode',
            'directed.displayed-family.decode',
            'directed.displayed-functor.decode'
        ]);
        assert.deepEqual(
            runtime.ruleIds,
            CORE_DIRECTED_FOUNDATION_REVIEW.authorization
                .runtimeRuleIds
        );
        assert.equal(Object.isFrozen(runtime), true);
        assert.equal(Object.isFrozen(runtime.rules), true);
        assert.equal(Object.isFrozen(runtime.ruleIds), true);
    });

    it('executes all three object-level facade reductions exactly', () => {
        const runtime = CoreDirectedFoundationRuntimeProgram.create();
        const cases: readonly {
            readonly input: KernelExpression;
            readonly expected: KernelExpression;
            readonly ruleId: string;
            readonly ruleIndex: number;
            readonly bindingCount: number;
        }[] = [
            {
                input: decodeObject(categoryOfCategories),
                expected: owner('category-universe'),
                ruleId: 'directed.category-object.decode',
                ruleIndex: 0,
                bindingCount: 0
            },
            {
                input: decodeObject(displayedCategory),
                expected: owner('decode', [
                    owner('functor-classifier', [
                        K,
                        categoryOfCategories
                    ])
                ]),
                ruleId: 'directed.displayed-family.decode',
                ruleIndex: 1,
                bindingCount: 1
            },
            {
                input: decodeObject(displayedFunctorCategory),
                expected: owner('decode', [
                    owner('transfor-classifier', [
                        K,
                        categoryOfCategories,
                        E,
                        D
                    ])
                ]),
                ruleId: 'directed.displayed-functor.decode',
                ruleIndex: 2,
                bindingCount: 3
            }
        ];

        for (const expected of cases) {
            const result = runtime.rewriteHead(expected.input);
            assert.equal(result.status, 'rewritten');
            if (result.status !== 'rewritten') continue;
            assert.equal(result.ruleId, expected.ruleId);
            assert.equal(result.ruleIndex, expected.ruleIndex);
            assert.equal(
                result.match.bindings.length,
                expected.bindingCount
            );
            assert.equal(
                kernelExpressionEquals(
                    result.after,
                    expected.expected
                ),
                true
            );
        }
    });

    it('is opt-in to the directed catalog conversion path', () => {
        const environment = CoreLfDeclarationEnvironment.empty();
        const runtime = CoreDirectedFoundationRuntimeProgram.create();
        const left = decodeObject(displayedCategory);
        const right = owner('decode', [
            owner('functor-classifier', [
                K,
                categoryOfCategories
            ])
        ]);

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
        assert.deepEqual(
            reviewed.trace.map(entry =>
                entry.reduction.kind === 'runtime'
                    ? entry.reduction.ruleId
                    : entry.reduction.kind
            ),
            ['directed.displayed-family.decode']
        );
    });

    it('does not rewrite stable category heads or unapproved Cat hom decoding', () => {
        const runtime = CoreDirectedFoundationRuntimeProgram.create();
        const stableHeads = [
            categoryOfCategories,
            displayedCategory,
            displayedFunctorCategory,
            owner('object-classifier', [displayedCategory]),
            owner('decode', [
                owner('hom-classifier', [
                    categoryOfCategories,
                    K,
                    E
                ])
            ])
        ];

        for (const expression of stableHeads) {
            assert.equal(
                runtime.rewriteHead(expression).status,
                'irreducible'
            );
        }
    });

    it('rejects plicity and facade-shape near misses structurally', () => {
        const runtime = CoreDirectedFoundationRuntimeProgram.create();
        const wrongPlicity = kernelCall(
            kernelFree(
                CORE_DIRECTED_1A_PRIMITIVE_NAMES[
                    'displayed-functor-category'
                ],
                because('wrong-plicity facade')
            ),
            [
                { plicity: 'explicit', value: K },
                { plicity: 'explicit', value: E },
                { plicity: 'explicit', value: D }
            ],
            because('wrong-plicity facade call')
        );
        const ordinaryCategory = kernelCall(
            kernelFree(
                CORE_DIRECTED_1A_PRIMITIVE_NAMES[
                    'displayed-functor-category'
                ],
                because('wrong head')
            ),
            [{
                plicity: binderMode('implicit', 'functorial').plicity,
                value: K
            }],
            because('wrong facade arity')
        );

        assert.equal(
            runtime.rewriteHead(decodeObject(wrongPlicity)).status,
            'irreducible'
        );
        assert.equal(
            runtime.rewriteHead(decodeObject(ordinaryCategory)).status,
            'irreducible'
        );
    });
});
