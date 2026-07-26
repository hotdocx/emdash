/**
 * Focused USABILITY-1C ordinary categorical bracket-abstraction corpus.
 */

import assert from 'node:assert/strict';
import {
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    CoreCategoricalScopedBuilder,
    CoreType,
    ElaboratedSurfaceTerm,
    KernelExpression,
    binderMode,
    checkLambdapiProbe,
    compileCoreCategoricalStructuralTransfer,
    coreCategoricalStructuralCoreName,
    coreCategoricalStructuralSymbolCoreName,
    coreTypeToKernelType,
    kernelApplication,
    kernelCall,
    kernelFree,
    provenance,
    sourceSpan
} from '../src/v3_2';

const fixture = 'tests/fixtures/categorical-bracket.ts';
const span = sourceSpan(fixture, 1, 1);
const at = (detail: string) =>
    provenance('surface', detail, span);

const A = kernelFree('bracket_A', at('category A'));
const B = kernelFree('bracket_B', at('category B'));
const C = kernelFree('bracket_C', at('category C'));
const lambdapiRoot = resolve(__dirname, '..', 'emdash2');

const functorCategory = (
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => kernelCall(
    kernelFree(
        coreCategoricalStructuralSymbolCoreName(
            CORE_CATEGORICAL_STRUCTURAL_SYMBOLS.functorCategory
        ),
        at('Functor_cat')
    ),
    [
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ],
    at('functor category')
);

const elaborated = (
    name: string,
    type: CoreType
): ElaboratedSurfaceTerm => ({
    term: kernelFree(name, at(name)),
    type,
    sourceSpan: span,
    recovered: []
});

const referenceNames = (
    expression: KernelExpression
): readonly string[] => {
    const result: string[] = [];
    const visit = (current: KernelExpression): void => {
        switch (current.tag) {
            case 'reference':
                if (!result.includes(current.name)) {
                    result.push(current.name);
                }
                return;
            case 'universe':
            case 'bound':
                return;
            case 'meta':
                current.spine.forEach(visit);
                return;
            case 'application':
                current.arguments.forEach(argument =>
                    visit(argument.value)
                );
                return;
            case 'call':
                visit(current.callee);
                current.arguments.forEach(argument =>
                    visit(argument.value)
                );
                return;
            case 'pi':
            case 'lambda':
                visit(current.binder.type);
                visit(current.body);
                return;
            default: {
                const exhaustive: never = current;
                return exhaustive;
            }
        }
    };
    visit(expression);
    return result;
};

const categoryType = (
    nodeProvenance = at('category type')
): KernelExpression => kernelApplication(
    'category-universe',
    [],
    nodeProvenance
);

describe('TypeScript v3.2 USABILITY-1C categorical bracket lowering', () => {
    it('lowers ordinary composition without evaluation machinery', () => {
        const builder = new CoreCategoricalScopedBuilder();
        const F = builder.fromElaborated(elaborated('bracket_F', {
            tag: 'functor',
            sourceCategory: A,
            targetCategory: B
        }));
        const G = builder.fromElaborated(elaborated('bracket_G', {
            tag: 'functor',
            sourceCategory: B,
            targetCategory: C
        }));
        const composite = builder.categoricalLambda(
            'x',
            A,
            C,
            x => builder.apply(G, builder.apply(F, x))
        );
        const compiled = builder.compile(composite);
        const evidence = builder.inspect(composite).abstractions.at(-1);
        assert.equal(compiled.term.tag, 'call');
        assert.deepEqual(
            evidence?.structuralPrerequisites,
            ['identity-functor', 'functor-composition']
        );
        assert.equal(
            referenceNames(compiled.term).includes(
                coreCategoricalStructuralCoreName(
                    'functor-composition'
                )
            ),
            true
        );
        assert.equal(
            referenceNames(compiled.term).includes(
                coreCategoricalStructuralCoreName(
                    'evaluation-functor'
                )
            ),
            false
        );
    });

    it('makes duplicated input explicit through evaluation and diagonal', () => {
        const builder = new CoreCategoricalScopedBuilder();
        const H = builder.fromElaborated(elaborated('bracket_HAA', {
            tag: 'functor',
            sourceCategory: A,
            targetCategory: functorCategory(A, C)
        }));
        const diagonal = builder.categoricalLambda(
            'x',
            A,
            C,
            x => builder.apply(builder.apply(H, x), x)
        );
        const compiled = builder.compile(diagonal);
        const evidence = builder.inspect(diagonal).abstractions.at(-1);
        assert.deepEqual(
            evidence?.structuralPrerequisites,
            ['diagonal-functor-abstraction']
        );
        const names = referenceNames(compiled.term);
        assert.equal(
            names.includes(
                coreCategoricalStructuralCoreName(
                    'diagonal-functor-abstraction'
                )
            ),
            true
        );
    });

    it('lowers general application to evaluation after typed pairing', () => {
        const builder = new CoreCategoricalScopedBuilder();
        const H = builder.fromElaborated(elaborated('bracket_HAB', {
            tag: 'functor',
            sourceCategory: A,
            targetCategory: functorCategory(B, C)
        }));
        const K = builder.fromElaborated(elaborated('bracket_K', {
            tag: 'functor',
            sourceCategory: A,
            targetCategory: B
        }));
        const application = builder.categoricalLambda(
            'x',
            A,
            C,
            x => builder.apply(
                builder.apply(H, x),
                builder.apply(K, x)
            )
        );
        const compiled = builder.compile(application);
        const evidence = builder.inspect(application).abstractions.at(-1);
        assert.equal(
            evidence?.structuralPrerequisites.includes('product-pair'),
            true
        );
        assert.equal(
            evidence?.structuralPrerequisites.includes(
                'evaluation-functor'
            ),
            true
        );
        const names = referenceNames(compiled.term);
        assert.equal(
            names.includes(
                coreCategoricalStructuralCoreName('product-pair')
            ),
            true
        );
        assert.equal(
            names.includes(
                coreCategoricalStructuralCoreName('evaluation-functor')
            ),
            true
        );
    });

    it('recognizes exchanged nested eta through sym_func_func', () => {
        const builder = new CoreCategoricalScopedBuilder();
        const H = builder.fromElaborated(elaborated('bracket_HBA', {
            tag: 'functor',
            sourceCategory: B,
            targetCategory: functorCategory(A, C)
        }));
        const exchange = builder.categoricalLambda(
            'x',
            A,
            functorCategory(B, C),
            x => builder.categoricalLambda(
                'y',
                B,
                C,
                y => builder.apply(builder.apply(H, y), x)
            )
        );
        const compiled = builder.compile(exchange);
        const evidence = builder.inspect(exchange).abstractions.at(-1);
        assert.deepEqual(
            evidence?.structuralPrerequisites,
            ['exchange-functor-abstraction']
        );
        assert.equal(
            referenceNames(compiled.term).includes(
                coreCategoricalStructuralCoreName(
                    'exchange-functor-abstraction'
                )
            ),
            true
        );
    });

    it('lowers a general nested abstraction through product wiring and curry', () => {
        const builder = new CoreCategoricalScopedBuilder();
        const P = builder.fromElaborated(elaborated('bracket_P', {
            tag: 'functor',
            sourceCategory: A,
            targetCategory: C
        }));
        const nested = builder.categoricalLambda(
            'x',
            A,
            functorCategory(B, C),
            x => builder.categoricalLambda(
                'y',
                B,
                C,
                _y => builder.apply(P, x)
            )
        );
        const compiled = builder.compile(nested);
        const evidence = builder.inspect(nested).abstractions.at(-1);
        assert.equal(
            evidence?.structuralPrerequisites.includes(
                'product-left-projection'
            ),
            true
        );
        assert.equal(
            evidence?.structuralPrerequisites.includes('curry-package'),
            true
        );
        const names = referenceNames(compiled.term);
        assert.equal(
            names.includes(
                coreCategoricalStructuralCoreName(
                    'product-left-projection'
                )
            ),
            true
        );
        assert.equal(
            names.includes(
                coreCategoricalStructuralCoreName('curry-package')
            ),
            true
        );
    });

    it('checks the bracket corpus in the generic LF environment', () => {
        const compilation =
            compileCoreCategoricalStructuralTransfer();
        let environment = compilation.compiled.environment;
        const mode = binderMode('explicit', 'functorial');
        for (const category of ['bracket_A', 'bracket_B', 'bracket_C']) {
            environment = environment.extend({
                name: category,
                type: categoryType(),
                mode,
                provenance: at(category)
            });
        }
        const declarations = [
            {
                name: 'bracket_F',
                type: {
                    tag: 'functor',
                    sourceCategory: A,
                    targetCategory: B
                } as const
            },
            {
                name: 'bracket_G',
                type: {
                    tag: 'functor',
                    sourceCategory: B,
                    targetCategory: C
                } as const
            },
            {
                name: 'bracket_HAA',
                type: {
                    tag: 'functor',
                    sourceCategory: A,
                    targetCategory: functorCategory(A, C)
                } as const
            },
            {
                name: 'bracket_HBA',
                type: {
                    tag: 'functor',
                    sourceCategory: B,
                    targetCategory: functorCategory(A, C)
                } as const
            },
            {
                name: 'bracket_P',
                type: {
                    tag: 'functor',
                    sourceCategory: A,
                    targetCategory: C
                } as const
            },
            {
                name: 'bracket_HAB',
                type: {
                    tag: 'functor',
                    sourceCategory: A,
                    targetCategory: functorCategory(B, C)
                } as const
            },
            {
                name: 'bracket_K',
                type: {
                    tag: 'functor',
                    sourceCategory: A,
                    targetCategory: B
                } as const
            },
            {
                name: 'bracket_b',
                type: {
                    tag: 'object',
                    category: B
                } as const
            }
        ];
        for (const declaration of declarations) {
            environment = environment.extend({
                name: declaration.name,
                type: coreTypeToKernelType(
                    declaration.type,
                    span,
                    declaration.name
                ),
                mode,
                provenance: at(declaration.name)
            });
        }
        const checker = compilation.compiled.createChecker(environment);

        const builder = new CoreCategoricalScopedBuilder();
        const F = builder.fromElaborated(elaborated(
            'bracket_F',
            declarations[0].type
        ));
        const G = builder.fromElaborated(elaborated(
            'bracket_G',
            declarations[1].type
        ));
        const HAA = builder.fromElaborated(elaborated(
            'bracket_HAA',
            declarations[2].type
        ));
        const HBA = builder.fromElaborated(elaborated(
            'bracket_HBA',
            declarations[3].type
        ));
        const P = builder.fromElaborated(elaborated(
            'bracket_P',
            declarations[4].type
        ));
        const HAB = builder.fromElaborated(elaborated(
            'bracket_HAB',
            declarations[5].type
        ));
        const K = builder.fromElaborated(elaborated(
            'bracket_K',
            declarations[6].type
        ));
        const b = builder.fromElaborated(elaborated(
            'bracket_b',
            declarations[7].type
        ));
        const ordinaryResult = {
            tag: 'functor',
            sourceCategory: A,
            targetCategory: C
        } as const;
        const nestedResult = {
            tag: 'functor',
            sourceCategory: A,
            targetCategory: functorCategory(B, C)
        } as const;
        const identityResult = {
            tag: 'functor',
            sourceCategory: A,
            targetCategory: A
        } as const;
        const constantResult = {
            tag: 'functor',
            sourceCategory: A,
            targetCategory: B
        } as const;
        const expressions = [
            {
                detail: 'identity',
                result: identityResult,
                term: builder.categoricalLambda(
                    'identity_x',
                    A,
                    A,
                    x => x
                )
            },
            {
                detail: 'constant',
                result: constantResult,
                term: builder.categoricalLambda(
                    'constant_x',
                    A,
                    B,
                    _x => b
                )
            },
            {
                detail: 'composition',
                result: ordinaryResult,
                term: builder.categoricalLambda(
                    'composition_x',
                    A,
                    C,
                    x => builder.apply(G, builder.apply(F, x))
                )
            },
            {
                detail: 'diagonal',
                result: ordinaryResult,
                term: builder.categoricalLambda(
                    'diagonal_x',
                    A,
                    C,
                    x => builder.apply(builder.apply(HAA, x), x)
                )
            },
            {
                detail: 'exchange',
                result: nestedResult,
                term: builder.categoricalLambda(
                    'exchange_x',
                    A,
                    functorCategory(B, C),
                    x => builder.categoricalLambda(
                        'exchange_y',
                        B,
                        C,
                        y => builder.apply(
                            builder.apply(HBA, y),
                            x
                        )
                    )
                )
            },
            {
                detail: 'evaluation after pairing',
                result: ordinaryResult,
                term: builder.categoricalLambda(
                    'application_x',
                    A,
                    C,
                    x => builder.apply(
                        builder.apply(HAB, x),
                        builder.apply(K, x)
                    )
                )
            },
            {
                detail: 'nested curry',
                result: nestedResult,
                term: builder.categoricalLambda(
                    'nested_x',
                    A,
                    functorCategory(B, C),
                    x => builder.categoricalLambda(
                        'nested_y',
                        B,
                        C,
                        _y => builder.apply(P, x)
                    )
                )
            }
        ];
        for (const candidate of expressions) {
            const expression = builder.compile(candidate.term);
            checker.check(
                checker.rootContext,
                expression.term,
                coreTypeToKernelType(
                    candidate.result,
                    span,
                    `${candidate.detail} bracket result`
                )
            );
        }
    });

    it(
        'matches the active Lambdapi structural basis and rejects a bad codomain',
        {
            skip:
                process.env
                    .EMDASH_RUN_LAMBDAPI_CATEGORICAL_BRACKET_PROBES !==
                    '1'
        },
        () => {
            const header = [
                'require open emdash.emdash3_2;',
                'symbol bracket_A : Cat;',
                'symbol bracket_B : Cat;',
                'symbol bracket_C : Cat;',
                'symbol bracket_b : τ (Obj bracket_B);',
                'symbol bracket_F : τ (Functor bracket_A bracket_B);',
                'symbol bracket_G : τ (Functor bracket_B bracket_C);',
                'symbol bracket_HAA : τ (Functor bracket_A ' +
                    '(Functor_cat bracket_A bracket_C));',
                'symbol bracket_HAB : τ (Functor bracket_A ' +
                    '(Functor_cat bracket_B bracket_C));',
                'symbol bracket_K : τ (Functor bracket_A bracket_B);',
                'symbol bracket_HBA : τ (Functor bracket_B ' +
                    '(Functor_cat bracket_A bracket_C));',
                'symbol bracket_P : τ (Functor bracket_A bracket_C);'
            ];
            const positive = checkLambdapiProbe(
                {
                    source: [
                        ...header,
                        'symbol bracket_identity : τ ' +
                            '(Functor bracket_A bracket_A) ' +
                            '≔ @id_func bracket_A;',
                        'symbol bracket_constant : τ ' +
                            '(Functor bracket_A bracket_B) ' +
                            '≔ fapp0 (@Const_func_func bracket_A ' +
                            'bracket_B) bracket_b;',
                        'symbol bracket_composition : τ ' +
                            '(Functor bracket_A bracket_C) ' +
                            '≔ @comp_cat_fapp0 bracket_A bracket_B ' +
                            'bracket_C bracket_G bracket_F;',
                        'symbol bracket_diagonal : τ ' +
                            '(Functor bracket_A bracket_C) ' +
                            '≔ fapp0 (@diag_func_func bracket_A ' +
                            'bracket_C) bracket_HAA;',
                        'symbol bracket_exchange : τ ' +
                            '(Functor bracket_A ' +
                            '(Functor_cat bracket_B bracket_C)) ' +
                            '≔ fapp0 (@sym_func_func bracket_B ' +
                            'bracket_A bracket_C) bracket_HBA;',
                        'symbol bracket_left : τ (Functor ' +
                            '(Product_cat bracket_A bracket_B) ' +
                            'bracket_A) ≔ @Product_projL_func ' +
                            'bracket_A bracket_B;',
                        'symbol bracket_right : τ (Functor ' +
                            '(Product_cat bracket_A bracket_B) ' +
                            'bracket_B) ≔ @Product_projR_func ' +
                            'bracket_A bracket_B;',
                        'symbol bracket_map : τ (Functor ' +
                            '(Product_cat bracket_A bracket_B) ' +
                            '(Product_cat bracket_A bracket_B)) ' +
                            '≔ @Product_map_func bracket_A bracket_A ' +
                            'bracket_B bracket_B (@id_func bracket_A) ' +
                            '(@id_func bracket_B);',
                        'symbol bracket_evaluation : τ ' +
                            '(Functor bracket_A bracket_C) ' +
                            '≔ @comp_cat_fapp0 bracket_A ' +
                            '(Product_cat ' +
                            '(Functor_cat bracket_B bracket_C) ' +
                            'bracket_B) bracket_C ' +
                            '(@Eval_func bracket_B bracket_C) ' +
                            '(@Product_pair ' +
                            '(Functor_cat bracket_A ' +
                            '(Functor_cat bracket_B bracket_C)) ' +
                            '(Functor_cat bracket_A bracket_B) ' +
                            'bracket_HAB bracket_K);',
                        'symbol bracket_nested : τ (Functor bracket_A ' +
                            '(Functor_cat bracket_B bracket_C)) ' +
                            '≔ fapp0 (@curry_func_func bracket_A ' +
                            'bracket_B bracket_C) ' +
                            '(@comp_cat_fapp0 ' +
                            '(Product_cat bracket_A bracket_B) ' +
                            'bracket_A bracket_C bracket_P ' +
                            '(@Product_projL_func bracket_A bracket_B));',
                        'symbol bracket_uncurried : τ (Functor ' +
                            '(Product_cat bracket_A bracket_B) ' +
                            'bracket_C) ≔ fapp0 ' +
                            '(@uncurry_func_func bracket_A bracket_B ' +
                            'bracket_C) bracket_HAB;',
                        'assert ⊢ Functor_cat bracket_A ' +
                            '(Product_cat bracket_B bracket_C) ≡ ' +
                            'Product_cat ' +
                            '(Functor_cat bracket_A bracket_B) ' +
                            '(Functor_cat bracket_A bracket_C);'
                    ].join('\n'),
                    sourceMap: []
                },
                {
                    packageRoot: lambdapiRoot,
                    timeoutMs: 30_000
                }
            );
            assert.equal(
                positive.accepted,
                true,
                positive.diagnostics
            );
            assert.equal(positive.timedOut, false);

            const negative = checkLambdapiProbe(
                {
                    source: [
                        ...header,
                        'symbol bracket_wrong : τ ' +
                            '(Functor bracket_A bracket_B) ' +
                            '≔ @comp_cat_fapp0 bracket_A bracket_B ' +
                            'bracket_C bracket_G bracket_F;'
                    ].join('\n'),
                    sourceMap: []
                },
                {
                    packageRoot: lambdapiRoot,
                    timeoutMs: 30_000
                }
            );
            assert.equal(negative.accepted, false);
            assert.equal(negative.timedOut, false);
            assert.match(
                negative.diagnostics,
                /bracket_B ≡ bracket_C/u
            );
        }
    );
});
