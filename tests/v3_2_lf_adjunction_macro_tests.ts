import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CoreLfAdjunctionAvailableGlobalInput,
    CoreLfAdjunctionDeclarationCommand,
    CoreLfAdjunctionMacroError,
    CoreLfAdjunctionMacroScope,
    CoreLfAdjunctionOwnerBindingsInput,
    CoreLfAdjunctionTransposeOwnerBindingsInput,
    CoreLfQualifiedSymbol,
    CoreLfTransferExpression,
    checkLambdapiProbe,
    createCoreLfModuleSpec,
    emitCoreLfAdjunctionLambdapiFragment
} from '../src/v3_2';

const kernelModule = 'emdash.emdash3_2';
const consumerModule = 'review.adjunction_consumer';

const symbol = (
    name: string,
    moduleId = kernelModule
): CoreLfQualifiedSymbol => ({ moduleId, name });

const owners: CoreLfAdjunctionOwnerBindingsInput = {
    decode: symbol('τ'),
    category: symbol('Cat'),
    functor: symbol('Functor'),
    transformation: symbol('Transf'),
    identityFunctor: symbol('id_func'),
    composeFunctors: symbol('comp_cat_fapp0'),
    adjunction: symbol('Adjunction'),
    unitObservation: symbol('unit_adj_transf'),
    counitObservation: symbol('counit_adj_transf'),
    trivialConstraint: symbol('tt')
};

const transposeOwners: CoreLfAdjunctionTransposeOwnerBindingsInput = {
    profunctorCategory: symbol('Prof_cat'),
    profunctorMap: symbol('ProfMap'),
    homProfunctorAlong: symbol('Hom_prof_along'),
    defisoForward: symbol('defiso_to'),
    adjunctionHomComparison: symbol('Adjunction_hom_prof_comparison')
};

const global = (
    value: CoreLfQualifiedSymbol
): CoreLfTransferExpression => ({ tag: 'global', symbol: value });

const call = (
    head: CoreLfQualifiedSymbol,
    arguments_: readonly {
        readonly plicity: 'explicit' | 'implicit';
        readonly value: CoreLfTransferExpression;
    }[]
): CoreLfTransferExpression => ({
    tag: 'call',
    callee: global(head),
    arguments: arguments_
});

const explicit = (value: CoreLfTransferExpression) => ({
    plicity: 'explicit' as const,
    value
});

const implicit = (value: CoreLfTransferExpression) => ({
    plicity: 'implicit' as const,
    value
});

const decoded = (classifier: CoreLfTransferExpression) =>
    call(owners.decode, [explicit(classifier)]);

const functorType = (
    source: CoreLfQualifiedSymbol,
    target: CoreLfQualifiedSymbol
) => decoded(call(owners.functor, [
    explicit(global(source)),
    explicit(global(target))
]));

const identityFunctor = (category: CoreLfQualifiedSymbol) =>
    call(owners.identityFunctor, [implicit(global(category))]);

const composeFunctors = (
    source: CoreLfQualifiedSymbol,
    middle: CoreLfQualifiedSymbol,
    target: CoreLfQualifiedSymbol,
    outer: CoreLfQualifiedSymbol,
    inner: CoreLfQualifiedSymbol
) => call(owners.composeFunctors, [
    implicit(global(source)),
    implicit(global(middle)),
    implicit(global(target)),
    explicit(global(outer)),
    explicit(global(inner))
]);

const transformationType = (
    category: CoreLfQualifiedSymbol,
    sourceFunctor: CoreLfTransferExpression,
    targetFunctor: CoreLfTransferExpression
) => decoded(call(owners.transformation, [
    implicit(global(category)),
    implicit(global(category)),
    explicit(sourceFunctor),
    explicit(targetFunctor)
]));

const homProfunctorAlong = (
    leftBase: CoreLfQualifiedSymbol,
    rightBase: CoreLfQualifiedSymbol,
    ambient: CoreLfQualifiedSymbol,
    leftEndpoint: CoreLfTransferExpression,
    rightEndpoint: CoreLfTransferExpression
) => call(transposeOwners.homProfunctorAlong, [
    implicit(global(leftBase)),
    implicit(global(rightBase)),
    implicit(global(ambient)),
    explicit(leftEndpoint),
    explicit(rightEndpoint)
]);

const profunctorMapType = (
    leftBase: CoreLfQualifiedSymbol,
    rightBase: CoreLfQualifiedSymbol,
    source: CoreLfTransferExpression,
    target: CoreLfTransferExpression
) => decoded(call(transposeOwners.profunctorMap, [
    implicit(global(leftBase)),
    implicit(global(rightBase)),
    explicit(source),
    explicit(target)
]));

const R = symbol('ReviewR', consumerModule);
const L = symbol('ReviewL', consumerModule);
const F = symbol('ReviewF', consumerModule);
const G = symbol('ReviewG', consumerModule);
const eta = symbol('ReviewEta', consumerModule);
const epsilon = symbol('ReviewEpsilon', consumerModule);
const eta2 = symbol('ReviewEta2', consumerModule);
const epsilon2 = symbol('ReviewEpsilon2', consumerModule);
const unrelatedEta = symbol('ReviewUnrelatedEta', consumerModule);
const triEpsilon = symbol('ReviewTriEpsilon', consumerModule);
const transpose = symbol('ReviewTranspose', consumerModule);
const unrelatedTranspose = symbol(
    'ReviewUnrelatedTranspose',
    consumerModule
);

const availableFixture = (): CoreLfAdjunctionAvailableGlobalInput[] => {
    const ownerGlobals = Object.values(owners).map(owner => ({
        symbol: owner,
        type: { tag: 'type' as const },
        availability: 'dependency-module' as const
    }));
    return [
        ...ownerGlobals,
        {
            symbol: R,
            type: global(owners.category),
            availability: 'earlier-fragment' as const,
            order: 0
        },
        {
            symbol: L,
            type: global(owners.category),
            availability: 'earlier-fragment' as const,
            order: 1
        },
        {
            symbol: F,
            type: functorType(R, L),
            availability: 'earlier-fragment' as const,
            order: 2
        },
        {
            symbol: G,
            type: functorType(L, R),
            availability: 'earlier-fragment' as const,
            order: 3
        },
        {
            symbol: eta,
            type: transformationType(
                R,
                identityFunctor(R),
                composeFunctors(R, L, R, G, F)
            ),
            availability: 'earlier-fragment' as const,
            order: 4
        },
        {
            symbol: epsilon,
            type: transformationType(
                L,
                composeFunctors(L, R, L, F, G),
                identityFunctor(L)
            ),
            availability: 'earlier-fragment' as const,
            order: 5
        }
    ];
};

const forwardTransposeType = () => profunctorMapType(
    R,
    L,
    homProfunctorAlong(
        R,
        L,
        L,
        global(F),
        identityFunctor(L)
    ),
    homProfunctorAlong(
        R,
        L,
        R,
        identityFunctor(R),
        global(G)
    )
);

const transposeAvailableFixture = ():
CoreLfAdjunctionAvailableGlobalInput[] => [
    ...availableFixture(),
    ...Object.values(transposeOwners).map(owner => ({
        symbol: owner,
        type: { tag: 'type' as const },
        availability: 'dependency-module' as const
    })),
    {
        symbol: triEpsilon,
        type: transformationType(
            L,
            composeFunctors(L, R, L, F, G),
            identityFunctor(L)
        ),
        availability: 'earlier-fragment' as const,
        order: 6
    },
    {
        symbol: transpose,
        type: forwardTransposeType(),
        availability: 'earlier-fragment' as const,
        order: 7
    },
    {
        symbol: unrelatedTranspose,
        type: forwardTransposeType(),
        availability: 'earlier-fragment' as const,
        order: 8
    }
];

const transposeFixture = (
    available = transposeAvailableFixture()
) => {
    const scope = new CoreLfAdjunctionMacroScope(
        consumerModule,
        available,
        owners,
        transposeOwners
    );
    const expansion = scope.assumeAdjunctionFromCounitTranspose({
        order: 12,
        name: 'reviewTriAdj',
        sourceCategory: scope.resolve(R),
        targetCategory: scope.resolve(L),
        leftAdjoint: scope.resolve(F),
        rightAdjoint: scope.resolve(G),
        counit: scope.resolve(triEpsilon),
        transpose: scope.resolve(transpose),
        provenance: {
            authorityPath: 'tests/fixtures/adjunction_consumer.lp',
            sourceFragment:
                'assumeAdjunctionFromCounitTranspose reviewTriAdj',
            canonicalCommandOrdinal: 9
        }
    });
    return { scope, expansion, available };
};

const fixture = (
    available = availableFixture()
) => {
    const scope = new CoreLfAdjunctionMacroScope(
        consumerModule,
        available,
        owners
    );
    const command: CoreLfAdjunctionDeclarationCommand = {
        kind: 'adjunction-declaration',
        order: 10,
        name: 'reviewAdj',
        sourceCategory: scope.resolve(R),
        targetCategory: scope.resolve(L),
        leftAdjoint: scope.resolve(F),
        rightAdjoint: scope.resolve(G),
        unit: scope.resolve(eta),
        counit: scope.resolve(epsilon),
        provenance: {
            authorityPath: 'tests/fixtures/adjunction_consumer.lp',
            sourceFragment: 'assumeAdjunction reviewAdj',
            canonicalCommandOrdinal: 6
        }
    };
    return { scope, command, available };
};

const conformanceFixture = () => {
    const available = [
        ...availableFixture(),
        {
            symbol: eta2,
            type: transformationType(
                R,
                identityFunctor(R),
                composeFunctors(R, L, R, G, F)
            ),
            availability: 'earlier-fragment' as const,
            order: 6
        },
        {
            symbol: epsilon2,
            type: transformationType(
                L,
                composeFunctors(L, R, L, F, G),
                identityFunctor(L)
            ),
            availability: 'earlier-fragment' as const,
            order: 7
        },
        {
            symbol: unrelatedEta,
            type: transformationType(
                R,
                identityFunctor(R),
                composeFunctors(R, L, R, G, F)
            ),
            availability: 'earlier-fragment' as const,
            order: 8
        }
    ];
    const scope = new CoreLfAdjunctionMacroScope(
        consumerModule,
        available,
        owners
    );
    const provenance = {
        authorityPath: 'tests/fixtures/adjunction_consumer.lp',
        sourceFragment: 'generated adjunction conformance consumer',
        canonicalCommandOrdinal: 9
    };
    const shared = {
        sourceCategory: scope.resolve(R),
        targetCategory: scope.resolve(L),
        leftAdjoint: scope.resolve(F),
        rightAdjoint: scope.resolve(G),
        provenance
    };
    const first = scope.assumeAdjunction({
        ...shared,
        order: 10,
        name: 'reviewAdj',
        unit: scope.resolve(eta),
        counit: scope.resolve(epsilon)
    });
    const second = scope.assumeAdjunction({
        ...shared,
        order: first.nextOrder,
        name: 'reviewAdj2',
        unit: scope.resolve(eta2),
        counit: scope.resolve(epsilon2)
    });
    return { first, second };
};

const buildLambdapiConformanceSource = (): string => {
    const { first, second } = conformanceFixture();
    const rectangularFragment = [first, second].map(expansion =>
        emitCoreLfAdjunctionLambdapiFragment(expansion, {
            backendName: value => value.name
        })
    ).join('\n');
    const triangular = transposeFixture().expansion;
    const triangularFragment = emitCoreLfAdjunctionLambdapiFragment(
        triangular,
        { backendName: value => value.name }
    );
    const unitClassifier =
        '@Transf ReviewR ReviewR ' +
        '(@id_func ReviewR) ' +
        '(@comp_cat_fapp0 ReviewR ReviewL ReviewR ReviewG ReviewF)';
    const counitClassifier =
        '@Transf ReviewL ReviewL ' +
        '(@comp_cat_fapp0 ReviewL ReviewR ReviewL ReviewF ReviewG) ' +
        '(@id_func ReviewL)';
    const unit1 =
        '@unit_adj_transf ReviewR ReviewL ReviewF ReviewG reviewAdj';
    const counit1 =
        '@counit_adj_transf ReviewR ReviewL ReviewF ReviewG reviewAdj';
    const unit2 =
        '@unit_adj_transf ReviewR ReviewL ReviewF ReviewG reviewAdj2';
    const sourceHomProfunctor =
        '@Hom_prof_along ReviewR ReviewL ReviewL ' +
        'ReviewF (@id_func ReviewL)';
    const targetHomProfunctor =
        '@Hom_prof_along ReviewR ReviewL ReviewR ' +
        '(@id_func ReviewR) ReviewG';
    const transposeClassifier =
        `@ProfMap ReviewR ReviewL (${sourceHomProfunctor}) ` +
        `(${targetHomProfunctor})`;
    const canonicalComparison =
        '@Adjunction_hom_prof_comparison ReviewR ReviewL ' +
        'ReviewF ReviewG reviewTriAdj';
    const canonicalTranspose = `defiso_to (${canonicalComparison})`;
    const canonicalInverseTranspose =
        `defiso_from (${canonicalComparison})`;

    return [
        '/* Generated rectangular-adjunction macro conformance consumer. */',
        'require open emdash.emdash3_2;',
        '',
        'constant symbol ReviewR : Cat;',
        'constant symbol ReviewL : Cat;',
        'constant symbol ReviewF : τ (Functor ReviewR ReviewL);',
        'constant symbol ReviewG : τ (Functor ReviewL ReviewR);',
        `constant symbol ReviewEta : τ (${unitClassifier});`,
        `constant symbol ReviewEpsilon : τ (${counitClassifier});`,
        `constant symbol ReviewEta2 : τ (${unitClassifier});`,
        `constant symbol ReviewEpsilon2 : τ (${counitClassifier});`,
        `constant symbol ReviewUnrelatedEta : τ (${unitClassifier});`,
        `constant symbol ReviewTriEpsilon : τ (${counitClassifier});`,
        `constant symbol ReviewTranspose : τ (${transposeClassifier});`,
        'constant symbol ReviewUnrelatedTranspose :',
        `  τ (${transposeClassifier});`,
        '',
        rectangularFragment.trimEnd(),
        '',
        triangularFragment.trimEnd(),
        '',
        '// Both orientations use declaration-backed proof-time agreement.',
        'symbol review_unit_agreement_forward :',
        `  τ (@= (${unitClassifier}) (${unit1}) ReviewEta)`,
        `≔ @eq_refl (${unitClassifier}) (${unit1});`,
        '',
        'symbol review_unit_agreement_reverse :',
        `  τ (@= (${unitClassifier}) ReviewEta (${unit1}))`,
        `≔ @eq_refl (${unitClassifier}) ReviewEta;`,
        '',
        'symbol review_counit_agreement :',
        `  τ (@= (${counitClassifier}) (${counit1}) ReviewEpsilon)`,
        `≔ @eq_refl (${counitClassifier}) (${counit1});`,
        '',
        'symbol review_second_unit_agreement :',
        `  τ (@= (${unitClassifier}) (${unit2}) ReviewEta2)`,
        `≔ @eq_refl (${unitClassifier}) (${unit2});`,
        '',
        '// Agreements do not become runtime conversion.',
        `assertnot ⊢ ${unit1} ≡ ReviewEta;`,
        `assertnot ⊢ ${counit1} ≡ ReviewEpsilon;`,
        '',
        '// Proof-time agreement is instance-specific and name-specific.',
        `assertnot ⊢ @eq_refl (${unitClassifier}) (${unit1})`,
        `  : τ (@= (${unitClassifier}) (${unit1}) ReviewEta2);`,
        `assertnot ⊢ @eq_refl (${unitClassifier}) (${unit1})`,
        `  : τ (@= (${unitClassifier}) (${unit1}) ReviewUnrelatedEta);`,
        '',
        '// The full-functor presentation compares at the whole ProfMap.',
        'symbol review_transpose_agreement_forward :',
        `  τ (@= (${transposeClassifier}) (${canonicalTranspose})`,
        '    ReviewTranspose)',
        `≔ @eq_refl (${transposeClassifier}) (${canonicalTranspose});`,
        '',
        'symbol review_transpose_agreement_reverse :',
        `  τ (@= (${transposeClassifier}) ReviewTranspose`,
        `    (${canonicalTranspose}))`,
        `≔ @eq_refl (${transposeClassifier}) ReviewTranspose;`,
        '',
        '// Transpose agreement remains proof-time and instance-specific.',
        `assertnot ⊢ ${canonicalTranspose} ≡ ReviewTranspose;`,
        `assertnot ⊢ @eq_refl (${transposeClassifier})`,
        `  (${canonicalTranspose})`,
        `  : τ (@= (${transposeClassifier}) (${canonicalTranspose})`,
        '      ReviewUnrelatedTranspose);',
        '',
        '// The selected map remains the DefIso cancellation owner.',
        'assert ⊢',
        '  @comp_fapp0',
        '    (@Prof_cat ReviewR ReviewL)',
        `    (${sourceHomProfunctor})`,
        `    (${targetHomProfunctor})`,
        `    (${sourceHomProfunctor})`,
        `    (${canonicalInverseTranspose})`,
        `    (${canonicalTranspose})`,
        '  ≡ @id',
        '      (@Prof_cat ReviewR ReviewL)',
        `      (${sourceHomProfunctor});`,
        '',
        '// The provided name is not installed as a runtime cancellation alias.',
        'assertnot ⊢',
        '  @comp_fapp0',
        '    (@Prof_cat ReviewR ReviewL)',
        `    (${sourceHomProfunctor})`,
        `    (${targetHomProfunctor})`,
        `    (${sourceHomProfunctor})`,
        `    (${canonicalInverseTranspose})`,
        '    ReviewTranspose',
        '  ≡ @id',
        '      (@Prof_cat ReviewR ReviewL)',
        `      (${sourceHomProfunctor});`,
        '',
        'constant symbol ReviewX : τ (Obj ReviewR);',
        'constant symbol ReviewXp : τ (Obj ReviewR);',
        'constant symbol ReviewY : τ (Obj ReviewL);',
        'constant symbol ReviewGArrow :',
        '  τ (Hom ReviewR ReviewX ReviewXp);',
        'constant symbol ReviewFArrow :',
        '  τ (Hom ReviewL (@fapp0 ReviewR ReviewL ReviewF ReviewXp) ReviewY);',
        '',
        '// The canonical observations still select triangle computation.',
        'assert ⊢',
        '  comp_fapp0',
        '    (@tapp1_fapp0',
        '      ReviewL ReviewL',
        '      (@comp_cat_fapp0 ReviewL ReviewR ReviewL ReviewF ReviewG)',
        '      (@id_func ReviewL)',
        '      (@fapp0 ReviewR ReviewL ReviewF ReviewXp)',
        '      ReviewY',
        `      (${counit1})`,
        '      ReviewFArrow)',
        '    (@fapp1_fapp0',
        '      ReviewR ReviewL ReviewF',
        '      ReviewX',
        '      (@fapp0 ReviewL ReviewR ReviewG',
        '        (@fapp0 ReviewR ReviewL ReviewF ReviewXp))',
        '      (@tapp1_fapp0',
        '        ReviewR ReviewR',
        '        (@id_func ReviewR)',
        '        (@comp_cat_fapp0 ReviewR ReviewL ReviewR ReviewG ReviewF)',
        '        ReviewX ReviewXp',
        `        (${unit1})`,
        '        ReviewGArrow))',
        '  ≡ comp_fapp0',
        '      ReviewFArrow',
        '      (@fapp1_fapp0',
        '        ReviewR ReviewL ReviewF ReviewX ReviewXp ReviewGArrow);',
        '',
        '// Raw declared names intentionally do not select that runtime rule.',
        'assertnot ⊢',
        '  comp_fapp0',
        '    (@tapp1_fapp0',
        '      ReviewL ReviewL',
        '      (@comp_cat_fapp0 ReviewL ReviewR ReviewL ReviewF ReviewG)',
        '      (@id_func ReviewL)',
        '      (@fapp0 ReviewR ReviewL ReviewF ReviewXp)',
        '      ReviewY ReviewEpsilon ReviewFArrow)',
        '    (@fapp1_fapp0',
        '      ReviewR ReviewL ReviewF',
        '      ReviewX',
        '      (@fapp0 ReviewL ReviewR ReviewG',
        '        (@fapp0 ReviewR ReviewL ReviewF ReviewXp))',
        '      (@tapp1_fapp0',
        '        ReviewR ReviewR',
        '        (@id_func ReviewR)',
        '        (@comp_cat_fapp0 ReviewR ReviewL ReviewR ReviewG ReviewF)',
        '        ReviewX ReviewXp ReviewEta ReviewGArrow))',
        '  ≡ comp_fapp0',
        '      ReviewFArrow',
        '      (@fapp1_fapp0',
        '        ReviewR ReviewL ReviewF ReviewX ReviewXp ReviewGArrow);',
        ''
    ].join('\n');
};

const throwsCode = (
    action: () => unknown,
    code: CoreLfAdjunctionMacroError['code'],
    path: string
): void => {
    assert.throws(action, error => {
        assert.equal(error instanceof CoreLfAdjunctionMacroError, true);
        const macroError = error as CoreLfAdjunctionMacroError;
        assert.equal(macroError.code, code);
        assert.equal(macroError.path, path);
        return true;
    });
};

describe('v3.2 outer-LF adjunction declaration macro', () => {
    it('expands atomically to one witness and two ground proof rules', () => {
        const { scope, command, available } = fixture();
        const expansion = scope.assumeAdjunction(command);

        assert.deepEqual(expansion.sourceOrders, [10, 11, 12]);
        assert.equal(expansion.nextOrder, 13);
        assert.deepEqual(expansion.declaration.symbol, {
            moduleId: consumerModule,
            name: 'reviewAdj'
        });
        assert.deepEqual(expansion.declaration.modifiers, {
            visibility: 'public',
            rigidity: 'constant',
            sourceOpacity: 'opaque'
        });
        assert.equal(expansion.proofRules.length, 2);
        assert.deepEqual(
            expansion.proofRules.map(rule => ({
                order: rule.order,
                id: rule.id,
                variables: rule.variables.length,
                constraints: rule.generatedConstraints.length
            })),
            [
                {
                    order: 11,
                    id: 'adjunction.reviewAdj.unit-agreement',
                    variables: 0,
                    constraints: 1
                },
                {
                    order: 12,
                    id: 'adjunction.reviewAdj.counit-agreement',
                    variables: 0,
                    constraints: 1
                }
            ]
        );
        assert.deepEqual(expansion.handle.declaredUnit, eta);
        assert.deepEqual(expansion.handle.declaredCounit, epsilon);
        assert.equal(Object.isFrozen(expansion), true);
        assert.equal(Object.isFrozen(expansion.handle.unit), true);

        const externalSymbols = available.map(entry => ({
            symbol: entry.symbol,
            availability: entry.availability
        }));
        const module = createCoreLfModuleSpec({
            revision: 'adjunction-macro-fixture-1',
            moduleId: consumerModule,
            fragmentId: 'adjunction-macro',
            authorityPath: 'tests/fixtures/adjunction_consumer.lp',
            sourceSha256:
                'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
            dependencies: [kernelModule],
            externalSymbols,
            declarations: [expansion.declaration],
            inductives: [],
            runtimeRules: [],
            proofRules: [...expansion.proofRules]
        });
        assert.deepEqual(
            module.proofRules.map(rule => rule.order),
            [11, 12]
        );
    });

    it('is deterministic and emits the canonical Lambdapi fragment', () => {
        const leftFixture = fixture();
        const rightFixture = fixture();
        const left = leftFixture.scope.assumeAdjunction(
            leftFixture.command
        );
        const right = rightFixture.scope.assumeAdjunction(
            rightFixture.command
        );
        assert.deepEqual(left, right);

        const source = emitCoreLfAdjunctionLambdapiFragment(left, {
            backendName: value => value.name
        });
        assert.equal(source, [
            'constant symbol reviewAdj : '
                + 'τ (@Adjunction ReviewR ReviewL ReviewF ReviewG);',
            '',
            'unif_rule @unit_adj_transf ReviewR ReviewL ReviewF ReviewG '
                + 'reviewAdj ≡ ReviewEta ↪ [ tt ≡ tt ];',
            '',
            'unif_rule @counit_adj_transf ReviewR ReviewL ReviewF ReviewG '
                + 'reviewAdj ≡ ReviewEpsilon ↪ [ tt ≡ tt ];',
            ''
        ].join('\n'));
    });

    it('expands a coherent counit/transpose presentation without a new classifier', () => {
        const leftFixture = transposeFixture();
        const left = leftFixture.expansion;
        const right = transposeFixture().expansion;

        assert.deepEqual(left, right);
        assert.equal(
            left.kind,
            'expanded-adjunction-counit-transpose-declaration'
        );
        assert.deepEqual(left.sourceOrders, [12, 13, 14]);
        assert.deepEqual(
            left.proofRules.map(rule => ({
                id: rule.id,
                order: rule.order,
                owner: rule.sourceOwner.name
            })),
            [
                {
                    id: 'adjunction.reviewTriAdj.counit-agreement',
                    order: 13,
                    owner: 'counit_adj_transf'
                },
                {
                    id: 'adjunction.reviewTriAdj.transpose-agreement',
                    order: 14,
                    owner: 'defiso_to'
                }
            ]
        );
        assert.deepEqual(left.handle.declaredCounit, triEpsilon);
        assert.deepEqual(left.handle.declaredTranspose, transpose);
        const witness = global({
            moduleId: consumerModule,
            name: 'reviewTriAdj'
        });
        assert.deepEqual(
            left.handle.transpose,
            call(transposeOwners.defisoForward, [
                implicit(call(transposeOwners.profunctorCategory, [
                    explicit(global(R)),
                    explicit(global(L))
                ])),
                implicit(homProfunctorAlong(
                    R,
                    L,
                    L,
                    global(F),
                    identityFunctor(L)
                )),
                implicit(homProfunctorAlong(
                    R,
                    L,
                    R,
                    identityFunctor(R),
                    global(G)
                )),
                explicit(call(
                    transposeOwners.adjunctionHomComparison,
                    [
                        implicit(global(R)),
                        implicit(global(L)),
                        implicit(global(F)),
                        implicit(global(G)),
                        explicit(witness)
                    ]
                ))
            ])
        );

        const module = createCoreLfModuleSpec({
            revision: 'adjunction-counit-transpose-macro-fixture-1',
            moduleId: consumerModule,
            fragmentId: 'adjunction-counit-transpose-macro',
            authorityPath: 'tests/fixtures/adjunction_consumer.lp',
            sourceSha256:
                'sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb',
            dependencies: [kernelModule],
            externalSymbols: leftFixture.available.map(entry => ({
                symbol: entry.symbol,
                availability: entry.availability
            })),
            declarations: [left.declaration],
            inductives: [],
            runtimeRules: [],
            proofRules: [...left.proofRules]
        });
        assert.deepEqual(
            module.proofRules.map(rule => rule.order),
            [13, 14]
        );

        assert.equal(
            emitCoreLfAdjunctionLambdapiFragment(left, {
                backendName: value => value.name
            }),
            [
                'constant symbol reviewTriAdj : '
                    + 'τ (@Adjunction ReviewR ReviewL ReviewF ReviewG);',
                '',
                'unif_rule @counit_adj_transf ReviewR ReviewL ReviewF '
                    + 'ReviewG reviewTriAdj ≡ ReviewTriEpsilon '
                    + '↪ [ tt ≡ tt ];',
                '',
                'unif_rule defiso_to '
                    + '(@Adjunction_hom_prof_comparison ReviewR ReviewL '
                    + 'ReviewF ReviewG reviewTriAdj) '
                    + '≡ ReviewTranspose ↪ [ tt ≡ tt ];',
                ''
            ].join('\n')
        );
    });

    it('rejects malformed transpose data and absent optional owners', () => {
        const wrongType = transposeAvailableFixture().map(entry =>
            entry.symbol.moduleId === transpose.moduleId &&
            entry.symbol.name === transpose.name
                ? { ...entry, type: functorType(R, L) }
                : entry
        );
        throwsCode(
            () => transposeFixture(wrongType),
            'TYPE_MISMATCH',
            'command.transpose'
        );

        const available = transposeAvailableFixture();
        const scope = new CoreLfAdjunctionMacroScope(
            consumerModule,
            available,
            owners
        );
        throwsCode(
            () => scope.assumeAdjunctionFromCounitTranspose({
                order: 12,
                name: 'missingOwnersAdj',
                sourceCategory: scope.resolve(R),
                targetCategory: scope.resolve(L),
                leftAdjoint: scope.resolve(F),
                rightAdjoint: scope.resolve(G),
                counit: scope.resolve(triEpsilon),
                transpose: scope.resolve(transpose),
                provenance: {
                    authorityPath: 'tests/fixtures/missing_owners.lp',
                    sourceFragment: 'missing transpose owners'
                }
            }),
            'INVALID_OWNER_BINDINGS',
            'scope.transposeOwnerBindings'
        );
    });

    it('rejects a unit/counit swap at the exact input', () => {
        const { scope, command } = fixture();
        throwsCode(
            () => scope.expand({
                ...command,
                unit: command.counit,
                counit: command.unit
            }),
            'TYPE_MISMATCH',
            'command.unit'
        );
    });

    it('rejects reversed adjoint directions', () => {
        const { scope, command } = fixture();
        throwsCode(
            () => scope.expand({
                ...command,
                leftAdjoint: command.rightAdjoint
            }),
            'TYPE_MISMATCH',
            'command.leftAdjoint'
        );

        throwsCode(
            () => scope.expand({
                ...command,
                rightAdjoint: command.leftAdjoint
            }),
            'TYPE_MISMATCH',
            'command.rightAdjoint'
        );
    });

    it('rejects wrong transformation endpoints and non-transformations', () => {
        const wrongEndpointAvailable = availableFixture().map(entry =>
            entry.symbol.moduleId === eta.moduleId &&
            entry.symbol.name === eta.name
                ? {
                    ...entry,
                    type: transformationType(
                        R,
                        identityFunctor(R),
                        identityFunctor(R)
                    )
                }
                : entry
        );
        const wrongEndpoint = fixture(wrongEndpointAvailable);
        throwsCode(
            () => wrongEndpoint.scope.assumeAdjunction(
                wrongEndpoint.command
            ),
            'TYPE_MISMATCH',
            'command.unit'
        );

        const nonTransformationAvailable = availableFixture().map(entry =>
            entry.symbol.moduleId === epsilon.moduleId &&
            entry.symbol.name === epsilon.name
                ? { ...entry, type: functorType(R, L) }
                : entry
        );
        const nonTransformation = fixture(nonTransformationAvailable);
        throwsCode(
            () => nonTransformation.scope.assumeAdjunction(
                nonTransformation.command
            ),
            'TYPE_MISMATCH',
            'command.counit'
        );
    });

    it('accepts adjunction data imported from a dependency module', () => {
        const importedModule = 'review.imported_adjunction_data';
        const importedR = symbol('ImportedR', importedModule);
        const importedL = symbol('ImportedL', importedModule);
        const importedF = symbol('ImportedF', importedModule);
        const importedG = symbol('ImportedG', importedModule);
        const importedEta = symbol('ImportedEta', importedModule);
        const importedEpsilon = symbol('ImportedEpsilon', importedModule);
        const available = [
            ...availableFixture().filter(entry =>
                entry.symbol.moduleId === kernelModule
            ),
            {
                symbol: importedR,
                type: global(owners.category),
                availability: 'dependency-module' as const
            },
            {
                symbol: importedL,
                type: global(owners.category),
                availability: 'dependency-module' as const
            },
            {
                symbol: importedF,
                type: functorType(importedR, importedL),
                availability: 'dependency-module' as const
            },
            {
                symbol: importedG,
                type: functorType(importedL, importedR),
                availability: 'dependency-module' as const
            },
            {
                symbol: importedEta,
                type: transformationType(
                    importedR,
                    identityFunctor(importedR),
                    composeFunctors(
                        importedR,
                        importedL,
                        importedR,
                        importedG,
                        importedF
                    )
                ),
                availability: 'dependency-module' as const
            },
            {
                symbol: importedEpsilon,
                type: transformationType(
                    importedL,
                    composeFunctors(
                        importedL,
                        importedR,
                        importedL,
                        importedF,
                        importedG
                    ),
                    identityFunctor(importedL)
                ),
                availability: 'dependency-module' as const
            }
        ];
        const scope = new CoreLfAdjunctionMacroScope(
            consumerModule,
            available,
            owners
        );
        const expansion = scope.assumeAdjunction({
            order: 0,
            name: 'importedAdj',
            sourceCategory: scope.resolve(importedR),
            targetCategory: scope.resolve(importedL),
            leftAdjoint: scope.resolve(importedF),
            rightAdjoint: scope.resolve(importedG),
            unit: scope.resolve(importedEta),
            counit: scope.resolve(importedEpsilon),
            provenance: {
                authorityPath: 'tests/fixtures/imported_adjunction.lp',
                sourceFragment: 'assumeAdjunction importedAdj'
            }
        });

        assert.deepEqual(expansion.handle.declaredUnit, importedEta);
        assert.deepEqual(expansion.handle.declaredCounit, importedEpsilon);
        assert.equal(expansion.handle.witness.moduleId, consumerModule);
    });

    it('rejects foreign and forward resolved globals', () => {
        const first = fixture();
        const second = fixture();
        throwsCode(
            () => first.scope.expand({
                ...first.command,
                unit: second.command.unit
            }),
            'FOREIGN_GLOBAL',
            'command.unit'
        );

        const forwardAvailable = availableFixture().map(entry =>
            entry.symbol.moduleId === consumerModule &&
            entry.symbol.name === eta.name
                ? { ...entry, order: 10 }
                : entry
        );
        const forward = fixture(forwardAvailable);
        throwsCode(
            () => forward.scope.expand(forward.command),
            'FORWARD_GLOBAL',
            'command.unit'
        );
    });

    it('rejects duplicate witness names and unavailable owners', () => {
        const duplicateAvailable = [
            ...availableFixture(),
            {
                symbol: symbol('reviewAdj', consumerModule),
                type: { tag: 'type' as const },
                availability: 'earlier-fragment' as const,
                order: 6
            }
        ];
        const duplicate = fixture(duplicateAvailable);
        throwsCode(
            () => duplicate.scope.expand(duplicate.command),
            'DUPLICATE_SYMBOL',
            'command.name'
        );

        const missingOwner = availableFixture().filter(entry =>
            entry.symbol.name !== owners.unitObservation.name
        );
        throwsCode(
            () => new CoreLfAdjunctionMacroScope(
                consumerModule,
                missingOwner,
                owners
            ),
            'INVALID_OWNER_BINDINGS',
            'scope.ownerBindings.unitObservation'
        );
    });

    it('rejects malformed trusted-declaration provenance explicitly', () => {
        const { scope, command } = fixture();
        throwsCode(
            () => scope.assumeAdjunction({
                ...command,
                provenance: undefined as never
            }),
            'INVALID_COMMAND',
            'command.provenance'
        );
        throwsCode(
            () => scope.assumeAdjunction({
                ...command,
                provenance: {
                    ...command.provenance,
                    canonicalCommandOrdinal: -1
                }
            }),
            'INVALID_COMMAND',
            'command.provenance'
        );
    });

    it('rejects open and rule-bearing available types without mutating input', () => {
        const open = availableFixture();
        open[open.length - 1] = {
            ...open[open.length - 1],
            type: { tag: 'bound', index: 0 }
        };
        assert.equal(Object.isFrozen(open), false);
        throwsCode(
            () => new CoreLfAdjunctionMacroScope(
                consumerModule,
                open,
                owners
            ),
            'INVALID_SCOPE',
            `scope.availableGlobals[${open.length - 1}].type`
        );
        assert.equal(Object.isFrozen(open), false);

        const capture = availableFixture();
        capture[capture.length - 1] = {
            ...capture[capture.length - 1],
            type: { tag: 'capture', name: 'x' }
        };
        throwsCode(
            () => new CoreLfAdjunctionMacroScope(
                consumerModule,
                capture,
                owners
            ),
            'INVALID_SCOPE',
            `scope.availableGlobals[${capture.length - 1}].type`
        );
    });

    it(
        'has its generated agreement and non-collapse contract accepted by Lambdapi',
        {
            skip:
                process.env.EMDASH_RUN_LAMBDAPI_ADJUNCTION_PROBES !== '1'
        },
        () => {
            const source = buildLambdapiConformanceSource();
            const result = checkLambdapiProbe(
                { source, sourceMap: [] },
                {
                    packageRoot: resolve(__dirname, '../emdash2'),
                    timeoutMs: 55_000
                }
            );

            assert.equal(result.timedOut, false, result.diagnostics);
            assert.equal(
                result.accepted,
                true,
                `Generated adjunction consumer was rejected:\n` +
                `${result.diagnostics}\n${source}`
            );
        }
    );
});
