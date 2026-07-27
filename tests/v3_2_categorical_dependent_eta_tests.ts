/**
 * Focused USABILITY-2A1 evidence for one honest natural/indexed section eta.
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
    CoreCategoricalTerm,
    checkLambdapiProbe,
    coreCategoricalDiagnosticFromError,
    selectCoreCategoricalAbstraction
} from '../src/v3_2';

const program = (
    sourceFile = 'tests/fixtures/categorical-dependent-eta.ts'
) => new CoreCategoricalProgram({ sourceFile });

const lambdapiRoot = resolve(__dirname, '..', 'emdash2');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe(
    'TypeScript v3.2 USABILITY-2A1 dependent categorical eta',
    () => {
        it(
            'lowers λ k :^n K. s[k] once through an indexed classifier',
            () => {
                const emdash = program();
                const K = emdash.category('K', { line: 1 });
                const E = emdash.displayedFamily('E', K, { line: 2 });
                const s = emdash.section('s', E, { line: 3 });
                let callbackCount = 0;

                const eta = emdash.dependentLambda(
                    'k',
                    E,
                    k => {
                        callbackCount += 1;
                        return emdash.apply(s, k, {
                            expectedShape: 'dependent-object',
                            source: { line: 6, column: 26 }
                        });
                    },
                    {
                        variation: 'natural',
                        dependency: 'displayed',
                        source: { line: 6, column: 13 }
                    }
                );
                const inspection = emdash.inspect(eta);
                const result = emdash.compile(eta);

                assert.equal(callbackCount, 1);
                assert.equal(result.explicitCore, '(free "s")');
                assert.equal(
                    result.explicitInferredType,
                    result.explicitExpectedType
                );
                assert.equal(result.surfaceType.tag, 'dependent-section');
                assert.deepEqual(
                    result.dependentPrerequisites,
                    ['section-object-evaluation']
                );
                assert.deepEqual(result.structuralPrerequisites, []);
                assert.equal(inspection.usage.length, 0);
                assert.equal(inspection.abstractions.length, 1);

                const evidence = inspection.abstractions[0];
                assert.equal(
                    evidence.rule,
                    'categorical.dependent-eta'
                );
                assert.equal(evidence.variation, 'natural');
                assert.equal(evidence.dependency, 'displayed');
                assert.equal(evidence.body.tag, 'typed-application');
                if (evidence.body.tag !== 'typed-application') {
                    assert.fail('Expected a retained section application');
                }
                assert.equal(
                    evidence.body.target,
                    'section-object-evaluation'
                );
                assert.equal(evidence.body.type.tag, 'indexed-object');
                if (evidence.body.type.tag !== 'indexed-object') {
                    assert.fail('Expected an indexed fibre classifier');
                }
                assert.equal(evidence.body.type.index, 0);
                assert.equal(evidence.body.argument.tag, 'slot-reference');
                if (evidence.body.argument.tag !== 'slot-reference') {
                    assert.fail('Expected the locally nameless base slot');
                }
                assert.equal(evidence.body.argument.index, 0);
                assert.equal(evidence.body.argument.hint, 'k');
                assert.deepEqual(
                    evidence.dependentPrerequisites,
                    ['section-object-evaluation']
                );
                assert.equal(result.productionLambdapiDependency, false);
                assertDeepFrozen(inspection);
            }
        );

        it('is invariant under binder hints and source provenance', () => {
            const compile = (
                hint: string,
                line: number
            ) => {
                const emdash = program(`eta-${hint}.ts`);
                const K = emdash.category('K', { line: 1 });
                const E = emdash.displayedFamily('E', K, { line: 2 });
                const s = emdash.section('s', E, { line: 3 });
                const eta = emdash.dependentLambda(
                    hint,
                    E,
                    k => emdash.apply(s, k, {
                        expectedShape: 'dependent-object',
                        source: { line: line + 1 }
                    }),
                    { source: { line } }
                );
                return emdash.compile(eta);
            };

            const first = compile('k', 10);
            const second = compile('renamed_index', 40);
            assert.equal(first.explicitCore, second.explicitCore);
            assert.equal(
                first.explicitExpectedType,
                second.explicitExpectedType
            );
            assert.equal(
                first.explicitInferredType,
                second.explicitInferredType
            );
        });

        it('selects the frozen natural/indexed abstraction row', () => {
            const selected = selectCoreCategoricalAbstraction({
                requestedLayer: 'categorical',
                expectedClassifier: 'displayed-or-indexed-family'
            });
            assert.equal(selected.id, 'natural-indexed-abstraction');
            assert.equal(selected.variation, 'natural');
            assert.equal(selected.lowering, 'categorical-contextual-ir');
            assert.equal(selected.implementationStage, 'USABILITY-2A');
        });

        it('rejects a wrong family and non-natural binder modes', () => {
            const emdash = program('dependent-eta-negative.ts');
            const K = emdash.category('K', { line: 1 });
            const E = emdash.displayedFamily('E', K, { line: 2 });
            const D = emdash.displayedFamily('D', K, { line: 3 });
            const d = emdash.section('d', D, { line: 4 });

            assert.throws(
                () => emdash.dependentLambda(
                    'k',
                    E,
                    k => emdash.apply(d, k, {
                        expectedShape: 'dependent-object',
                        source: { line: 10 }
                    }),
                    { source: { line: 9 } }
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'CLASSIFIER_ARGUMENT_MISMATCH' &&
                    /requested family/u.test(error.message)
            );

            assert.throws(
                () => emdash.dependentLambda(
                    'k',
                    E,
                    k => emdash.apply(d, k, {
                        expectedShape: 'dependent-object'
                    }),
                    {
                        variation: 'functorial',
                        source: { line: 20 }
                    }
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'CLASSIFIER_ARGUMENT_MISMATCH' &&
                    /requires natural variation/u.test(error.message)
            );
        });

        it('does not let an indexed callback term escape its scope', () => {
            const emdash = program('dependent-eta-escape.ts');
            const K = emdash.category('K', { line: 1 });
            const E = emdash.displayedFamily('E', K, { line: 2 });
            const s = emdash.section('s', E, { line: 3 });
            let escaped: CoreCategoricalTerm | undefined;

            emdash.dependentLambda(
                'k',
                E,
                k => {
                    escaped = emdash.apply(s, k, {
                        expectedShape: 'dependent-object'
                    });
                    return escaped;
                }
            );
            assert.ok(escaped);
            assert.throws(
                () => emdash.inspect(escaped as CoreCategoricalTerm),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'ESCAPED_SLOT'
            );
        });

        it('keeps indexed classifiers out of closed category APIs', () => {
            const emdash = program('dependent-eta-boundary.ts');
            const K = emdash.category('K', { line: 1 });
            const E = emdash.displayedFamily('E', K, { line: 2 });
            const s = emdash.section('s', E, { line: 3 });

            assert.throws(
                () => emdash.dependentLambda(
                    'k',
                    E,
                    k => {
                        const sk = emdash.apply(s, k, {
                            expectedShape: 'dependent-object'
                        });
                        emdash.fibre(E, sk, { line: 10 });
                        return sk;
                    }
                ),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'EXPECTED_CATEGORY_OBJECT' &&
                    /open indexed object/u.test(error.message)
            );

            assert.throws(
                () => emdash.dependentLambda(
                    'k',
                    E,
                    k => {
                        const sk = emdash.apply(s, k, {
                            expectedShape: 'dependent-object'
                        });
                        emdash.hom('bad', K, sk, sk, { line: 20 });
                        return sk;
                    }
                ),
                error =>
                    error instanceof CoreCategoricalProgramError &&
                    error.code === 'EXPECTED_CATEGORY_OBJECT' &&
                    /open indexed endpoint/u.test(error.message)
            );
        });

        it('reports the first untransferred section-arrow action', () => {
            const emdash = program('dependent-arrow-negative.ts');
            const K = emdash.category('K', { line: 1 });
            const E = emdash.displayedFamily('E', K, { line: 2 });
            const x = emdash.object('x', K, { line: 3 });
            const y = emdash.object('y', K, { line: 4 });
            const p = emdash.hom('p', K, x, y, { line: 5 });
            const s = emdash.section('s', E, { line: 6 });

            let captured: unknown;
            try {
                emdash.apply(s, p, {
                    expectedShape: 'dependent-arrow',
                    source: {
                        line: 31,
                        column: 7,
                        detail: 'dependent section action at p'
                    }
                });
            } catch (error: unknown) {
                captured = error;
            }
            const normalized =
                coreCategoricalDiagnosticFromError(captured);
            assert.equal(
                normalized?.code,
                'UNAVAILABLE_DEPENDENT_ACTION'
            );
            assert.equal(
                normalized?.location,
                'dependent-arrow-negative.ts:31:7'
            );
            assert.match(
                normalized?.message ?? '',
                /piapp1_fapp0 transfer/u
            );
        });

        it(
            'matches the active Pi-category result and component signatures',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_CATEGORICAL_DEPENDENT_ETA_PROBES !==
                    '1'
            },
            () => {
                const header = [
                    'require open emdash.emdash3_2;',
                    'symbol eta_K : Cat;',
                    'symbol eta_E : τ (Catd eta_K);',
                    'symbol eta_D : τ (Catd eta_K);',
                    'symbol eta_x : τ (Obj eta_K);',
                    'symbol eta_s : τ (Obj (Pi_cat eta_E));'
                ];
                const positive = checkLambdapiProbe(
                    {
                        source: [
                            ...header,
                            'symbol eta_result : τ (Obj (Pi_cat eta_E)) ' +
                                '≔ eta_s;',
                            'symbol eta_component : τ (Obj ' +
                                '(Fibre_cat eta_E eta_x)) ' +
                                '≔ @piapp0 eta_K eta_E eta_result eta_x;'
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
                            'symbol eta_wrong : τ (Obj (Pi_cat eta_D)) ' +
                                '≔ eta_s;'
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
