/**
 * Focused USABILITY-DEPENDENT-1A evidence for the approved non-eta
 * displayed section-composition witness.
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
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_PREREQUISITES,
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_RUNTIME_MODULE,
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS,
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_MODULE,
    CORE_CATEGORICAL_DEPENDENT_CONTINUATION_APPLICATION,
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_PROGRAM_REVISION,
    CoreCategoricalFrontendError,
    CoreCategoricalProgram,
    CoreCategoricalTerm,
    checkLambdapiProbe,
    compileCoreCategoricalDependentCompositionTransfer
} from '../src/v3_2';

const program = (
    sourceFile = 'tests/fixtures/categorical-dependent-composition.ts'
) => new CoreCategoricalProgram({
    sourceFile,
    profile: 'usability-dependent-1a'
});

const lambdapiRoot = resolve(__dirname, '..', 'emdash2');

const composition = (
    emdash: CoreCategoricalProgram,
    binderName = 'k'
) => {
    const K = emdash.category('K', { line: 1 });
    const E = emdash.displayedFamily('E', K, { line: 2 });
    const D = emdash.displayedFamily('D', K, { line: 3 });
    const FF = emdash.displayedFunctor('FF', E, D, { line: 4 });
    const s = emdash.section('s', E, { line: 5 });
    let callbackCount = 0;
    const term = emdash.dependentLambda(
        binderName,
        D,
        k => {
            callbackCount++;
            const FFk = emdash.apply(FF, k, {
                expectedShape: 'fibre-functor',
                source: { line: 8, column: 21 }
            });
            const sk = emdash.apply(s, k, {
                expectedShape: 'dependent-object',
                source: { line: 8, column: 27 }
            });
            return emdash.apply(FFk, sk, {
                expectedShape: 'object-value',
                source: { line: 8, column: 24 }
            });
        },
        {
            variation: 'natural',
            dependency: 'displayed',
            source: { line: 8, column: 1 }
        }
    );
    return {
        K,
        E,
        D,
        FF,
        s,
        term,
        callbackCount
    };
};

describe(
    'TypeScript v3.2 USABILITY-DEPENDENT-1A section composition',
    () => {
        it('transfers only the exact active declaration/runtime closure', () => {
            assert.equal(
                CORE_CATEGORICAL_DEPENDENT_COMPOSITION_PROGRAM_REVISION,
                'USABILITY-DEPENDENT-1A-CATEGORICAL-PROGRAM-1'
            );
            assert.deepEqual(
                CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_MODULE
                    .declarations.map(entry => entry.symbol.name),
                ['Terminal_cat', 'comp_fapp0']
            );
            assert.deepEqual(
                CORE_CATEGORICAL_DEPENDENT_COMPOSITION_RUNTIME_MODULE
                    .runtimeRules.map(rule => rule.id),
                [
                    'categorical.displayed-hom-category.reduce',
                    'categorical.displayed-hom-classifier.reduce',
                    'categorical.section-object-classifier.reduce'
                ]
            );
            assert.deepEqual(
                CORE_CATEGORICAL_DEPENDENT_COMPOSITION_RUNTIME_MODULE
                    .runtimeRules.map(rule => rule.sourceOwner.name),
                ['Hom_cat', 'Hom', 'Obj']
            );
            assert.equal(
                CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_MODULE
                    .proofRules.length,
                0
            );
            assert.equal(
                CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_BOUNDARY
                    .newIntrinsicCoreOwners,
                0
            );
            assert.equal(
                CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_BOUNDARY
                    .newMathematicalRules,
                0
            );
            assert.equal(
                CORE_CATEGORICAL_DEPENDENT_COMPOSITION_TRANSFER_BOUNDARY
                    .classifierRulesAreInstalledAtStableCoreHeads,
                true
            );
            assert.deepEqual(
                CORE_CATEGORICAL_DEPENDENT_COMPOSITION_PREREQUISITES
                    .map(entry => entry.id),
                [
                    'terminal-category',
                    'generic-category-composition',
                    'displayed-hom-classifier-reduction',
                    'section-object-classifier-reduction'
                ]
            );
            assert.deepEqual(
                Object.values(
                    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS
                ).map(symbol => symbol.name),
                ['Terminal_cat', 'comp_fapp0']
            );

            const compiled =
                compileCoreCategoricalDependentCompositionTransfer();
            assert.deepEqual(
                compiled.compiled.declarations.map(declaration => [
                    declaration.symbol.name,
                    declaration.status
                ]),
                [
                    ['Terminal_cat', 'installed-opaque'],
                    ['comp_fapp0', 'installed-opaque']
                ]
            );
            assert.deepEqual(
                compiled.runtime.ruleIds,
                [
                    'categorical.displayed-hom-category.reduce',
                    'categorical.displayed-hom-classifier.reduce',
                    'categorical.section-object-classifier.reduce'
                ]
            );
            assert.equal(
                compiled.composedRuntime.ruleIds.filter(id =>
                    id === 'categorical.displayed-hom-category.reduce'
                ).length,
                1
            );
        });

        it('keeps the continuation judgment outside the frozen partition', () => {
            assert.deepEqual(
                CORE_CATEGORICAL_DEPENDENT_CONTINUATION_APPLICATION,
                {
                    id: 'indexed-fibre-functor.object',
                    layer: 'categorical',
                    subjectClassifier: 'indexed-fibre-functor',
                    subjectForm: 'term',
                    argumentDimension: 'object',
                    expectedShape: 'object-value',
                    dependency: 'displayed',
                    target: 'indexed-fibre-functor-object',
                    consumesSubjectTerm: true,
                    implementationStatus: 'reviewed-continuation',
                    surfaceDisposition: 'eligible',
                    rule:
                        'A displayed functor projected at the same ' +
                        'contextual base index acts on an indexed object of ' +
                        'its source family.'
                }
            );
        });

        it('reifies FF[k](s[k]) once and lowers to generic Catd composition', () => {
            const emdash = program();
            const witness = composition(emdash);
            assert.equal(witness.callbackCount, 1);

            const inspection = emdash.inspect(witness.term);
            const evidence = inspection.abstractions.at(-1);
            assert.equal(
                evidence?.rule,
                'categorical.dependent-section-composition'
            );
            assert.equal(evidence?.body.tag, 'typed-application');
            if (
                evidence?.body.tag !== 'typed-application' ||
                evidence.body.subject.type.tag !== 'indexed-functor' ||
                evidence.body.argument.tag !== 'typed-application' ||
                evidence.body.argument.type.tag !== 'indexed-object'
            ) {
                assert.fail('Composition evidence lost indexed classifiers');
            }
            assert.equal(evidence.body.judgmentId,
                'indexed-fibre-functor.object');
            assert.equal(evidence.body.subject.type.index, 0);
            assert.equal(evidence.body.argument.type.index, 0);
            assert.equal(evidence.result.tag, 'explicit-core-term');
            assert.equal(Object.isFrozen(evidence.body), true);

            const compiled = emdash.compile(witness.term);
            assert.equal(
                compiled.explicitCore,
                '(call ' +
                '(free "emdash.categorical.' +
                'generic-category-composition") ' +
                '(implicit (owner "displayed-category-category" ' +
                '(explicit (free "K")))) ' +
                '(implicit (owner "constant-displayed-family" ' +
                '(explicit (free "K")) ' +
                '(explicit (free "emdash.categorical.' +
                'terminal-category")))) ' +
                '(implicit (free "E")) ' +
                '(implicit (free "D")) ' +
                '(explicit (free "FF")) ' +
                '(explicit (free "s")))'
            );
            assert.equal(compiled.surfaceType.tag, 'dependent-section');
            if (compiled.surfaceType.tag !== 'dependent-section') {
                assert.fail('Composition result is not a section');
            }
            assert.deepEqual(
                compiled.dependentPrerequisites,
                [
                    'displayed-functor-fibre',
                    'section-object-evaluation',
                    'generic-category-composition',
                    'terminal-category',
                    'displayed-hom-classifier-reduction',
                    'section-object-classifier-reduction'
                ]
            );
            assert.deepEqual(compiled.structuralPrerequisites, []);
            assert.equal(compiled.productionLambdapiDependency, false);
        });

        it('is alpha- and provenance-invariant after binder elimination', () => {
            const first = program('composition-a.ts');
            const second = program('composition-b.ts');
            const left = first.compile(
                composition(first, 'k').term
            );
            const right = second.compile(
                composition(second, 'renamedIndex').term
            );
            assert.equal(left.explicitCore, right.explicitCore);
            assert.equal(
                left.explicitInferredType,
                right.explicitInferredType
            );
            assert.equal(
                left.explicitExpectedType,
                right.explicitExpectedType
            );
        });

        it('preserves the reviewed eta-only default profile', () => {
            const emdash = new CoreCategoricalProgram();
            const K = emdash.category('K');
            const E = emdash.displayedFamily('E', K);
            const D = emdash.displayedFamily('D', K);
            const FF = emdash.displayedFunctor('FF', E, D);
            const s = emdash.section('s', E);

            assert.throws(
                () => emdash.dependentLambda(
                    'k',
                    D,
                    k => emdash.apply(
                        emdash.apply(FF, k, {
                            expectedShape: 'fibre-functor'
                        }),
                        emdash.apply(s, k, {
                            expectedShape: 'dependent-object'
                        })
                    )
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'UNAVAILABLE_DISPLAYED_ACTION' &&
                    /USABILITY-2A1 eta envelope/u.test(error.message)
            );
        });

        it('fails closed on wrong base and wrong source family', () => {
            const emdash = program('composition-mismatch.ts');
            const K = emdash.category('K');
            const L = emdash.category('L');
            const E = emdash.displayedFamily('E', K);
            const D = emdash.displayedFamily('D', K);
            const Q = emdash.displayedFamily('Q', K);
            const EL = emdash.displayedFamily('EL', L);
            const DL = emdash.displayedFamily('DL', L);
            const FF = emdash.displayedFunctor('FF', E, D);
            const GGL = emdash.displayedFunctor('GGL', EL, DL);
            const q = emdash.section('q', Q);

            assert.throws(
                () => emdash.dependentLambda(
                    'k',
                    D,
                    k => emdash.apply(GGL, k, {
                        expectedShape: 'fibre-functor'
                    })
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'CLASSIFIER_ARGUMENT_MISMATCH' &&
                    /base category/u.test(error.message)
            );

            assert.throws(
                () => emdash.dependentLambda(
                    'k',
                    D,
                    k => emdash.apply(
                        emdash.apply(FF, k, {
                            expectedShape: 'fibre-functor'
                        }),
                        emdash.apply(q, k, {
                            expectedShape: 'dependent-object'
                        })
                    )
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'CLASSIFIER_ARGUMENT_MISMATCH' &&
                    /source family/u.test(error.message)
            );
        });

        it('rejects foreign, escaped, and unsupported indexed forms', () => {
            const emdash = program('composition-scope.ts');
            const foreign = program('composition-foreign.ts');
            const K = emdash.category('K');
            const E = emdash.displayedFamily('E', K);
            const D = emdash.displayedFamily('D', K);
            const Q = emdash.displayedFamily('Q', K);
            const FF = emdash.displayedFunctor('FF', E, D);
            const GG = emdash.displayedFunctor('GG', D, Q);
            const s = emdash.section('s', E);
            const foreignK = foreign.category('ForeignK');
            const foreignE = foreign.displayedFamily(
                'ForeignE',
                foreignK
            );
            const foreignS = foreign.section('foreignS', foreignE);
            let escaped: CoreCategoricalTerm | undefined;

            assert.throws(
                () => emdash.dependentLambda(
                    'k',
                    D,
                    k => emdash.apply(foreignS, k, {
                        expectedShape: 'dependent-object'
                    })
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'FOREIGN_TERM'
            );

            emdash.dependentLambda(
                'k',
                D,
                k => {
                    escaped = emdash.apply(FF, k, {
                        expectedShape: 'fibre-functor'
                    });
                    return emdash.apply(
                        escaped,
                        emdash.apply(s, k, {
                            expectedShape: 'dependent-object'
                        })
                    );
                }
            );
            assert.ok(escaped);
            assert.throws(
                () => emdash.inspect(escaped as CoreCategoricalTerm),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'ESCAPED_SLOT'
            );

            assert.throws(
                () => emdash.dependentLambda(
                    'k',
                    Q,
                    k => {
                        const FFsk = emdash.apply(
                            emdash.apply(FF, k, {
                                expectedShape: 'fibre-functor'
                            }),
                            emdash.apply(s, k, {
                                expectedShape: 'dependent-object'
                            })
                        );
                        return emdash.apply(
                            emdash.apply(GG, k, {
                                expectedShape: 'fibre-functor'
                            }),
                            FFsk
                        );
                    }
                ),
                error =>
                    error instanceof CoreCategoricalFrontendError &&
                    error.code === 'UNAVAILABLE_DISPLAYED_ACTION' &&
                    /exact scoped section-composition body/u.test(
                        error.message
                    )
            );
        });

        it(
            'agrees with Lambdapi on whole-section typing and pointwise computation',
            {
                skip:
                    process.env
                        .EMDASH_RUN_LAMBDAPI_CATEGORICAL_DEPENDENT_COMPOSITION_PROBES !==
                    '1'
            },
            () => {
                const result = checkLambdapiProbe(
                    {
                        source: [
                            'require open emdash.emdash3_2;',
                            'symbol comp_K : Cat;',
                            'symbol comp_E : τ (Catd comp_K);',
                            'symbol comp_D : τ (Catd comp_K);',
                            'symbol comp_FF : τ ' +
                                '(Functord comp_E comp_D);',
                            'symbol comp_s : τ ' +
                                '(Obj (Pi_cat comp_E));',
                            'symbol comp_k : τ (Obj comp_K);',
                            'symbol comp_result : τ ' +
                                '(Obj (Pi_cat comp_D)) ≔',
                            '  @comp_fapp0',
                            '    (@Catd_cat comp_K)',
                            '    (@Const_catd comp_K Terminal_cat)',
                            '    comp_E',
                            '    comp_D',
                            '    comp_FF',
                            '    comp_s;',
                            'assert ⊢',
                            '  @piapp0 comp_K comp_D comp_result comp_k',
                            '  ≡ @fapp0',
                            '      (Fibre_cat comp_E comp_k)',
                            '      (Fibre_cat comp_D comp_k)',
                            '      (@Fibre_func comp_K comp_E comp_D ' +
                                'comp_FF comp_k)',
                            '      (@piapp0 comp_K comp_E comp_s comp_k);'
                        ].join('\n'),
                        sourceMap: []
                    },
                    {
                        packageRoot: lambdapiRoot,
                        timeoutMs: 30_000
                    }
                );
                assert.equal(result.accepted, true, result.diagnostics);
                assert.equal(result.timedOut, false);
            }
        );
    }
);
