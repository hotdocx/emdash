/**
 * Focused USABILITY-2A0 facade evidence for dependent sections and displayed
 * functors at closed base indices.
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
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalProgramError,
    CoreCategoricalSurfaceError,
    checkLambdapiProbe,
    coreCategoricalDiagnosticFromError,
    selectCoreCategoricalApplication
} from '../src/v3_2';

const program = (
    sourceFile = 'tests/fixtures/categorical-dependent-program.ts'
) => new CoreCategoricalProgram({ sourceFile });

const lambdapiRoot = resolve(__dirname, '..', 'emdash2');

describe(
    'TypeScript v3.2 USABILITY-2A0 categorical dependent program',
    () => {
        it('checks a dependent section at a closed base object', () => {
            const emdash = program();
            const K = emdash.category('K', { line: 1 });
            const E = emdash.displayedFamily('E', K, { line: 2 });
            const x = emdash.object('x', K, { line: 3 });
            const s = emdash.section('s', E, { line: 4 });
            const result = emdash.compile(emdash.apply(s, x, {
                expectedShape: 'dependent-object',
                source: { line: 5 }
            }));

            assert.equal(
                result.explicitCore,
                '(call ' +
                '(free "emdash.categorical.' +
                'section-object-evaluation") ' +
                '(implicit (free "K")) ' +
                '(implicit (free "E")) ' +
                '(explicit (free "s")) ' +
                '(explicit (free "x")))'
            );
            assert.deepEqual(
                result.dependentPrerequisites,
                ['section-object-evaluation']
            );
            assert.deepEqual(result.structuralPrerequisites, []);
            assert.equal(
                result.explicitInferredType,
                result.explicitExpectedType
            );
            assert.equal(result.productionLambdapiDependency, false);
        });

        it('projects and applies a displayed functor in one fibre', () => {
            const emdash = program();
            const K = emdash.category('K', { line: 1 });
            const E = emdash.displayedFamily('E', K, { line: 2 });
            const D = emdash.displayedFamily('D', K, { line: 3 });
            const x = emdash.object('x', K, { line: 4 });
            const FF = emdash.displayedFunctor(
                'FF',
                E,
                D,
                { line: 5 }
            );
            const FFx = emdash.apply(FF, x, {
                expectedShape: 'fibre-functor',
                source: { line: 6 }
            });
            const u = emdash.object(
                'u',
                emdash.fibre(E, x, { line: 7 }),
                { line: 7 }
            );
            const result = emdash.compile(emdash.apply(FFx, u, {
                source: { line: 8 }
            }));

            assert.equal(
                result.explicitCore.includes(
                    '"emdash.categorical.displayed-functor-fibre"'
                ),
                true
            );
            assert.equal(
                result.explicitCore.includes('"functor-object"'),
                true
            );
            assert.deepEqual(
                result.dependentPrerequisites,
                ['displayed-functor-fibre']
            );
            assert.equal(
                result.explicitInferredType,
                result.explicitExpectedType
            );
        });

        it('selects heterogeneous transport over a closed base arrow', () => {
            const emdash = program();
            const K = emdash.category('K', { line: 1 });
            const E = emdash.displayedFamily('E', K, { line: 2 });
            const D = emdash.displayedFamily('D', K, { line: 3 });
            const x = emdash.object('x', K, { line: 4 });
            const y = emdash.object('y', K, { line: 5 });
            const p = emdash.hom('p', K, x, y, { line: 6 });
            const FF = emdash.displayedFunctor(
                'FF',
                E,
                D,
                { line: 7 }
            );
            const result = emdash.compile(emdash.apply(FF, p, {
                expectedShape: 'transport-functor',
                source: { line: 8 }
            }));

            assert.equal(
                result.explicitCore.includes(
                    '"emdash.categorical.' +
                    'displayed-functor-transport"'
                ),
                true
            );
            assert.deepEqual(
                result.dependentPrerequisites,
                ['displayed-functor-transport']
            );
            assert.equal(
                result.explicitInferredType,
                result.explicitExpectedType
            );
        });

        it('qualifies only the transferred USABILITY-1A rows', () => {
            const qualification = {
                transferredTargets: [
                    'displayed-functor-fibre',
                    'displayed-functor-transport'
                ] as const
            };
            const fibre = selectCoreCategoricalApplication({
                layer: 'categorical',
                subjectClassifier: 'displayed-functor',
                subjectForm: 'term',
                argumentDimension: 'object',
                expectedShape: 'fibre-functor',
                dependency: 'displayed'
            }, qualification);
            assert.equal(fibre.target, 'displayed-functor-fibre');

            assert.throws(
                () => selectCoreCategoricalApplication({
                    layer: 'categorical',
                    subjectClassifier: 'displayed-functor',
                    subjectForm: 'term',
                    argumentDimension: 'arrow',
                    expectedShape: 'whole-laxity-transfor',
                    dependency: 'displayed'
                }, {
                    transferredTargets: [
                        'displayed-functor-laxity'
                    ]
                }),
                error =>
                    error instanceof CoreCategoricalSurfaceError &&
                    error.code === 'UNAVAILABLE_DISPLAYED_ACTION'
            );
        });

        it('fails closed at the inactive whole-laxity boundary', () => {
            const emdash = program('inactive-laxity.ts');
            const K = emdash.category('K', { line: 1 });
            const E = emdash.displayedFamily('E', K, { line: 2 });
            const D = emdash.displayedFamily('D', K, { line: 3 });
            const x = emdash.object('x', K, { line: 4 });
            const y = emdash.object('y', K, { line: 5 });
            const p = emdash.hom('p', K, x, y, { line: 6 });
            const FF = emdash.displayedFunctor(
                'FF',
                E,
                D,
                { line: 7 }
            );

            let captured: unknown;
            try {
                emdash.apply(FF, p, {
                    expectedShape: 'whole-laxity-transfor',
                    source: {
                        line: 31,
                        column: 7,
                        detail: 'request inactive displayed laxity'
                    }
                });
            } catch (error: unknown) {
                captured = error;
            }
            const normalized =
                coreCategoricalDiagnosticFromError(captured);
            assert.equal(
                normalized?.code,
                'UNAVAILABLE_DISPLAYED_ACTION'
            );
            assert.equal(normalized?.location, 'inactive-laxity.ts:31:7');
            assert.match(
                normalized?.message ?? '',
                /functord_laxity_transf is deliberately inactive/u
            );
        });

        it('does not mistake closed projection for an indexed binder', () => {
            const emdash = program('indexed-slot.ts');
            const K = emdash.category('K', { line: 1 });
            const E = emdash.displayedFamily('E', K, { line: 2 });
            const D = emdash.displayedFamily('D', K, { line: 3 });
            const FF = emdash.displayedFunctor(
                'FF',
                E,
                D,
                { line: 4 }
            );

            assert.throws(
                () => emdash.lambda(
                    'k',
                    K,
                    K,
                    k => emdash.apply(FF, k, {
                        expectedShape: 'fibre-functor',
                        source: { line: 20 }
                    }),
                    { source: { line: 19 } }
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'UNAVAILABLE_DISPLAYED_ACTION' &&
                    /USABILITY-2A1/u.test(error.message)
            );
        });

        it('rejects mismatched and foreign displayed families', () => {
            const emdash = program('family-mismatch.ts');
            const other = program('foreign-family.ts');
            const K = emdash.category('K', { line: 1 });
            const L = emdash.category('L', { line: 2 });
            const E = emdash.displayedFamily('E', K, { line: 3 });
            const D = emdash.displayedFamily('D', L, { line: 4 });
            const l = emdash.object('l', L, { line: 5 });
            const foreignBase = other.category('K2', { line: 1 });
            const foreign = other.displayedFamily(
                'Foreign',
                foreignBase,
                { line: 2 }
            );

            assert.throws(
                () => emdash.displayedFunctor('badFF', E, D, {
                    line: 40,
                    column: 3
                }),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'DISPLAYED_BASE_MISMATCH'
            );
            assert.throws(
                () => emdash.section('badSection', foreign, {
                    line: 41,
                    column: 3
                }),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'FOREIGN_DISPLAYED_FAMILY'
            );
            assert.throws(
                () => emdash.fibre(E, l, {
                    line: 42,
                    column: 3
                }),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'EXPECTED_CATEGORY_OBJECT'
            );
        });

        it(
            'matches active section/fibre/transport signatures and rejects a wrong fibre',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_CATEGORICAL_DEPENDENT_PROBES !==
                        '1'
            },
            () => {
                const header = [
                    'require open emdash.emdash3_2;',
                    'symbol dep_K : Cat;',
                    'symbol dep_E : τ (Catd dep_K);',
                    'symbol dep_D : τ (Catd dep_K);',
                    'symbol dep_x : τ (Obj dep_K);',
                    'symbol dep_y : τ (Obj dep_K);',
                    'symbol dep_p : τ (Hom dep_K dep_x dep_y);',
                    'symbol dep_s : τ (Obj (Pi_cat dep_E));',
                    'symbol dep_FF : τ (Functord dep_E dep_D);'
                ];
                const positive = checkLambdapiProbe(
                    {
                        source: [
                            ...header,
                            'symbol dep_sx : τ (Obj ' +
                                '(Fibre_cat dep_E dep_x)) ' +
                                '≔ @piapp0 dep_K dep_E dep_s dep_x;',
                            'symbol dep_FFx : τ (Functor ' +
                                '(Fibre_cat dep_E dep_x) ' +
                                '(Fibre_cat dep_D dep_x)) ' +
                                '≔ @Fibre_func dep_K dep_E dep_D ' +
                                'dep_FF dep_x;',
                            'symbol dep_FFp : τ (Functor ' +
                                '(Fibre_cat dep_E dep_x) ' +
                                '(Fibre_cat dep_D dep_y)) ' +
                                '≔ @functord_transport_func dep_K ' +
                                'dep_E dep_D dep_FF dep_x dep_y dep_p;'
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
                            'symbol dep_wrong : τ (Functor ' +
                                '(Fibre_cat dep_E dep_x) ' +
                                '(Fibre_cat dep_D dep_x)) ' +
                                '≔ @functord_transport_func dep_K ' +
                                'dep_E dep_D dep_FF dep_x dep_y dep_p;'
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
                    /is not unifiable with/u
                );
            }
        );
    }
);
