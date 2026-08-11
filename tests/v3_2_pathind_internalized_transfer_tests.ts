/**
 * Focused qualification evidence for the root-only internalized PathInd
 * transfer. The active Lambdapi development remains the mathematical
 * authority; this file qualifies the reviewed TypeScript transfer boundary.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    createCoreLfChecker
} from '../src/v3_2/lf_checker';
import {
    CoreLfDeclarationEnvironment
} from '../src/v3_2/lf_declarations';
import {
    KernelExpression,
    Plicity,
    binderMode,
    kernelApplication,
    kernelCall,
    kernelFree,
    provenance
} from '../src/v3_2/kernel';
import {
    CORE_PATHIND_INTERNALIZED_1D_BASE_RUNTIME_MODULE,
    CORE_PATHIND_INTERNALIZED_1D_BASE_RUNTIME_POLICY,
    CORE_PATHIND_INTERNALIZED_1D_PREFIX_LIBRARY_MODULE,
    CORE_PATHIND_INTERNALIZED_1D_PREFIX_LIBRARY_POLICY,
    CORE_PATHIND_INTERNALIZED_1D_PRELUDE_MODULE,
    CORE_PATHIND_INTERNALIZED_1D_PRELUDE_POLICY,
    CORE_PATHIND_INTERNALIZED_1D_REVISION,
    CORE_PATHIND_INTERNALIZED_1D_SIGMA_MODULE,
    CORE_PATHIND_INTERNALIZED_1D_SIGMA_POLICY,
    CORE_PATHIND_INTERNALIZED_1D_SOURCE_FIBRE_RUNTIME_MODULE,
    CORE_PATHIND_INTERNALIZED_1D_SOURCE_FIBRE_RUNTIME_POLICY,
    CORE_PATHIND_INTERNALIZED_1D_SUFFIX_LIBRARY_MODULE,
    CORE_PATHIND_INTERNALIZED_1D_SUFFIX_LIBRARY_POLICY,
    CORE_PATHIND_INTERNALIZED_1D_SYMBOLS,
    CORE_PATHIND_INTERNALIZED_1D_TRANSFER_BOUNDARY,
    CORE_PATHIND_INTERNALIZED_1D_TRUSTED_MODULE,
    CORE_PATHIND_INTERNALIZED_1D_TRUSTED_POLICY,
    CorePathindInternalizedOrdinaryLibraryCapabilityError,
    assertCorePathindInternalizedOrdinaryLibraryCapability,
    compileCorePathindInternalized1dTransfer
} from '../src/v3_2/pathind_internalized_transfer';
import {
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES
} from '../src/v3_2/pathout_foundation_transfer';
import {
    checkLambdapiProbe
} from '../src/v3_2/probe';

const repositoryRoot = resolve(__dirname, '..');
const nodeProvenance = provenance(
    'derived',
    'PATHOUT-LIBRARY-INTERNALIZED-1D focused witness'
);

interface CallArgument {
    readonly plicity: Plicity;
    readonly value: KernelExpression;
}

const call = (
    name: string,
    arguments_: readonly CallArgument[]
): KernelExpression => kernelCall(
    kernelFree(name, nodeProvenance),
    arguments_,
    nodeProvenance
);

const categoryType = (): KernelExpression => kernelApplication(
    'category-universe',
    [],
    nodeProvenance
);

const decode = (classifier: KernelExpression): KernelExpression =>
    kernelApplication(
        'decode',
        [{ value: classifier }],
        nodeProvenance
    );

const objectClassifier = (base: KernelExpression): KernelExpression =>
    kernelApplication(
        'object-classifier',
        [{ value: base }],
        nodeProvenance
    );

const objectType = (base: KernelExpression): KernelExpression =>
    decode(objectClassifier(base));

const homType = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => decode(kernelApplication(
    'hom-classifier',
    [{ value: base }, { value: source }, { value: target }],
    nodeProvenance
));

const displayedCategory = (base: KernelExpression): KernelExpression =>
    kernelApplication(
        'displayed-category-category',
        [{ value: base }],
        nodeProvenance
    );

const displayedFamilyType = (base: KernelExpression): KernelExpression =>
    objectType(displayedCategory(base));

const pathoutCategory = (
    base: KernelExpression,
    source: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutCategory,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]
);

interface InternalizedFixture {
    readonly compilation: ReturnType<
        typeof compileCorePathindInternalized1dTransfer
    >;
    readonly environment: CoreLfDeclarationEnvironment;
    readonly Z: KernelExpression;
    readonly W: KernelExpression;
    readonly x: KernelExpression;
    readonly y: KernelExpression;
    readonly w: KernelExpression;
    readonly p: KernelExpression;
    readonly E: KernelExpression;
    readonly Ew: KernelExpression;
}

let cachedFixture: InternalizedFixture | undefined;

const fixture = (): InternalizedFixture => {
    if (cachedFixture !== undefined) return cachedFixture;
    const compilation = compileCorePathindInternalized1dTransfer();
    let environment = compilation.compiled.environment;
    const add = (name: string, type: KernelExpression): KernelExpression => {
        environment = environment.extend({
            name,
            type,
            mode: binderMode('explicit', 'functorial'),
            provenance: nodeProvenance,
            transparency: 'opaque'
        });
        return kernelFree(name, nodeProvenance);
    };
    const Z = add('pathind_internalized_test_Z', categoryType());
    const W = add('pathind_internalized_test_W', categoryType());
    const x = add('pathind_internalized_test_x', objectType(Z));
    const y = add('pathind_internalized_test_y', objectType(Z));
    const w = add('pathind_internalized_test_w', objectType(W));
    const p = add('pathind_internalized_test_p', homType(Z, x, y));
    const E = add(
        'pathind_internalized_test_E',
        displayedFamilyType(pathoutCategory(Z, x))
    );
    const Ew = add(
        'pathind_internalized_test_Ew',
        displayedFamilyType(pathoutCategory(W, w))
    );
    cachedFixture = Object.freeze({
        compilation,
        environment,
        Z,
        W,
        x,
        y,
        w,
        p,
        E,
        Ew
    });
    return cachedFixture;
};

const extensionRuleIds = [
    'pathind.internalized.' +
        'path-ind-source-fibre-at-sigma-pair-presentation-fusion',
    'pathind.internalized.' +
        'transported-motive-reflexive-fibre-presentation-fusion',
    'pathind.internalized.' +
        'pathout-pi-transport-post-delta-presentation-fusion',
    'pathind.internalized.' +
        'path-ind-target-fibre-at-sigma-pair-presentation-fusion'
] as const;

describe('PATHOUT-LIBRARY-INTERNALIZED-1D transfer', () => {
    it('seals the reviewed exact 4/13/0/10 root-only boundary', () => {
        const boundary = CORE_PATHIND_INTERNALIZED_1D_TRANSFER_BOUNDARY;
        assert.equal(
            CORE_PATHIND_INTERNALIZED_1D_REVISION,
            'PATHOUT-LIBRARY-INTERNALIZED-1D-TRANSFER-14'
        );
        assert.equal(
            boundary.reviewedAuthorization,
            'PATHOUT-LIBRARY-INTERNALIZED-1D-REVIEWED-14'
        );
        assert.deepEqual(
            [
                boundary.trustedDeclarationCount,
                boundary.runtimeRuleCount,
                boundary.proofRuleCount,
                boundary.transparentDefinitionCount,
                boundary.mathematicalRuntimeProjectionCount,
                boundary.derivedRuntimeSupportRuleCount
            ],
            [4, 13, 0, 10, 5, 8]
        );
        assert.deepEqual(
            [
                boundary.baseRuntimeRuleCount,
                boundary.prefixTransparentDefinitionCount,
                boundary.sourceFibreExtensionRuntimeRuleCount,
                boundary.suffixTransparentDefinitionCount
            ],
            [9, 3, 4, 4]
        );
        assert.deepEqual(
            boundary.runtimeRuleIds.slice(-4),
            extensionRuleIds
        );
        assert.equal(boundary.browserOrPublicPackageExported, false);
        assert.equal(boundary.rootOnlyQualification, true);
        assert.equal(boundary.intrinsicCoreOwnerDelta, 0);
        assert.equal(boundary.checkerBranchDelta, 0);
        assert.equal(boundary.evaluatorBranchDelta, 0);
        assert.equal(boundary.activeLambdapiOwnerDelta, 0);
        assert.equal(boundary.activeLambdapiRuleDelta, 0);
    });

    it('compiles every stage with the reviewed policy and 512-step bound',
        () => {
            const { compilation } = fixture();
            assert.deepEqual(
                [
                    compilation.sigmaCompiled.declarations.length,
                    compilation.preludeCompiled.declarations.length,
                    compilation.trustedCompiled.declarations.length,
                    compilation.baseRuntimeFragment.localProgram.rules.length,
                    compilation.prefixLibraryCompiled.declarations.length,
                    compilation.sourceFibreRuntimeFragment.localProgram
                        .rules.length,
                    compilation.suffixLibraryCompiled.declarations.length
                ],
                [1, 3, 3, 9, 3, 4, 4]
            );
            assert.equal(
                compilation.baseRuntimeFragment.localProgram.rules.every(
                    rule =>
                        rule.subjectValidation.kind === 'typescript-checked'
                ),
                true
            );
            assert.equal(
                compilation.sourceFibreRuntimeFragment.localProgram.rules
                    .every(rule =>
                        rule.subjectValidation.kind === 'typescript-checked'
                    ),
                true
            );
            assert.deepEqual(
                [
                    compilation.sigmaCompiled.comparisonStepLimit,
                    compilation.preludeCompiled.comparisonStepLimit,
                    compilation.trustedCompiled.comparisonStepLimit,
                    compilation.baseRuntimeFragment.localProgram
                        .comparisonStepLimit,
                    compilation.prefixLibraryCompiled.comparisonStepLimit,
                    compilation.sourceFibreRuntimeFragment.localProgram
                        .comparisonStepLimit,
                    compilation.suffixLibraryCompiled.comparisonStepLimit
                ],
                [512, 512, 512, 512, 512, 512, 512]
            );
            assert.deepEqual(
                [
                    CORE_PATHIND_INTERNALIZED_1D_SIGMA_POLICY.entries[0]
                        ?.policy,
                    CORE_PATHIND_INTERNALIZED_1D_PRELUDE_POLICY.entries.every(
                        entry =>
                            entry.policy ===
                            'checked-transparent-definition'
                    ),
                    CORE_PATHIND_INTERNALIZED_1D_TRUSTED_POLICY.entries.every(
                        entry => entry.policy === 'opaque-signature'
                    ),
                    CORE_PATHIND_INTERNALIZED_1D_BASE_RUNTIME_POLICY.entries
                        .every(entry => entry.policy === 'runtime-rewrite'),
                    CORE_PATHIND_INTERNALIZED_1D_PREFIX_LIBRARY_POLICY.entries
                        .every(entry =>
                            entry.policy ===
                            'checked-transparent-definition'
                        ),
                    CORE_PATHIND_INTERNALIZED_1D_SOURCE_FIBRE_RUNTIME_POLICY
                        .entries.every(entry =>
                            entry.policy === 'runtime-rewrite'
                        ),
                    CORE_PATHIND_INTERNALIZED_1D_SUFFIX_LIBRARY_POLICY.entries
                        .every(entry =>
                            entry.policy ===
                            'checked-transparent-definition'
                        )
                ],
                ['opaque-signature', true, true, true, true, true, true]
            );
            for (const module of [
                CORE_PATHIND_INTERNALIZED_1D_SIGMA_MODULE,
                CORE_PATHIND_INTERNALIZED_1D_PRELUDE_MODULE,
                CORE_PATHIND_INTERNALIZED_1D_TRUSTED_MODULE,
                CORE_PATHIND_INTERNALIZED_1D_BASE_RUNTIME_MODULE,
                CORE_PATHIND_INTERNALIZED_1D_PREFIX_LIBRARY_MODULE,
                CORE_PATHIND_INTERNALIZED_1D_SOURCE_FIBRE_RUNTIME_MODULE,
                CORE_PATHIND_INTERNALIZED_1D_SUFFIX_LIBRARY_MODULE
            ]) {
                assert.equal(module.proofRules.length, 0);
            }
        });

    it('fires all four staged presentation rules at their exact redexes',
        () => {
            const witness = fixture();
            const bindings = [
                [witness.Z, witness.x, witness.E],
                [
                    witness.Z,
                    witness.x,
                    witness.y,
                    witness.p,
                    witness.E
                ],
                [
                    witness.Z,
                    witness.x,
                    witness.y,
                    witness.p,
                    witness.E
                ],
                [witness.Z, witness.x, witness.E]
            ];
            extensionRuleIds.forEach((id, index) => {
                const program = witness.compilation
                    .sourceFibreRuntimeFragment.localProgram;
                const rule = program.rule(id);
                assert.ok(rule, `Missing staged runtime rule ${id}`);
                const redex = program.instantiateRuleLeft(
                    rule,
                    bindings[index],
                    nodeProvenance
                );
                const result = witness.compilation.composedRuntime
                    .rewriteHead(redex);
                assert.equal(result.status, 'rewritten');
                if (result.status !== 'rewritten') {
                    assert.fail(`Staged runtime rule ${id} did not fire`);
                }
                assert.equal(result.ruleId, id);
            });
        });

    it('types the primary theorem, total presentation, and target transport',
        () => {
            const witness = fixture();
            const { compilation } = witness;
            const checker = createCoreLfChecker(
                witness.environment,
                8192,
                compilation.composedRuntime
            );
            const primary = compilation.trustedCompiled.application(
                CORE_PATHIND_INTERNALIZED_1D_SYMBOLS
                    .pathInductionTransformation,
                [witness.Z],
                nodeProvenance
            );
            const total = compilation.suffixLibraryCompiled.application(
                CORE_PATHIND_INTERNALIZED_1D_SYMBOLS
                    .pathInductionTotalFunctor,
                [witness.Z],
                nodeProvenance
            );
            const transport = compilation.suffixLibraryCompiled.application(
                CORE_PATHIND_INTERNALIZED_1D_SYMBOLS
                    .pathInductionTargetTransport,
                [
                    witness.Z,
                    witness.x,
                    witness.y,
                    witness.p,
                    witness.E
                ],
                nodeProvenance
            );
            assert.doesNotThrow(() =>
                checker.infer(checker.rootContext, primary)
            );
            assert.doesNotThrow(() =>
                checker.infer(checker.rootContext, total)
            );
            assert.doesNotThrow(() =>
                checker.infer(checker.rootContext, transport)
            );
        });

    it('rejects target transport with a motive over a foreign PathOut',
        () => {
            const witness = fixture();
            const checker = createCoreLfChecker(
                witness.environment,
                8192,
                witness.compilation.composedRuntime
            );
            const transport = witness.compilation.suffixLibraryCompiled
                .application(
                    CORE_PATHIND_INTERNALIZED_1D_SYMBOLS
                        .pathInductionTargetTransport,
                    [
                        witness.Z,
                        witness.x,
                        witness.y,
                        witness.p,
                        witness.Ew
                    ],
                    nodeProvenance
                );
            assert.throws(() =>
                checker.infer(checker.rootContext, transport)
            );
        });

    it('keeps trusted and rewriting capabilities out of ordinary code',
        () => {
            assert.equal(
                assertCorePathindInternalizedOrdinaryLibraryCapability(
                    'checked-transparent-definition'
                ),
                'checked-transparent-definition'
            );
            for (const capability of [
                'opaque-signature',
                'runtime-rewrite',
                'proof-unification'
            ] as const) {
                assert.throws(
                    () =>
                        assertCorePathindInternalizedOrdinaryLibraryCapability(
                            capability
                        ),
                    CorePathindInternalizedOrdinaryLibraryCapabilityError
                );
            }
        });

    it('keeps the qualifying profile out of public/browser barrels', () => {
        for (const relative of [
            'src/v3_2/index.ts',
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/browser.ts'
        ]) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, relative), 'utf8'),
                /pathind_internalized_transfer/u,
                relative
            );
        }
    });

    it(
        'matches all twelve bounded active-Lambdapi assertions',
        {
            skip:
                process.env.EMDASH_RUN_LAMBDAPI_PATHIND_INTERNALIZED_PROBES
                !== '1'
        },
        () => {
            const source = String.raw`require open emdash.emdash3_2;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@PathOutMotives_catd Z)
    (@Const_catd Z Cat_cat)
    x
    (@PathOutReflEval_funcd Z)
    ≡ @pathout_refl_eval_func Z x;

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @tapp0_fapp0
    (@Catd_cat (@PathOut_cat Z x))
    Cat_cat
    (@PathInd_src_catd Z x)
    (@PathInd_tgt_catd Z x)
    E
    (@PathInd_func Z x)
    ≡ @path_ind_func_fapp0 Z x E;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @tdapp0_fapp0
    Z
    (@PathOutMotives_catd Z)
    (@Const_catd Z Cat_cat)
    (@PathOutReflEval_funcd Z)
    (@PathOutPi_funcd Z)
    x
    (@PathInd_transfd Z)
    ≡ @PathInd_func Z x;

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @tapp0_fapp0
    (@Catd_cat (@PathOut_cat Z x))
    Cat_cat
    (@PathInd_src_catd Z x)
    (@PathInd_tgt_catd Z x)
    E
    (@tdapp0_fapp0
      Z
      (@PathOutMotives_catd Z)
      (@Const_catd Z Cat_cat)
      (@PathOutReflEval_funcd Z)
      (@PathOutPi_funcd Z)
      x
      (@PathInd_transfd Z))
    ≡ @path_ind_func_fapp0 Z x E;

assert [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @fapp0
    (Fibre_cat E (@pathout_refl_obj Z x))
    (Pi_cat E)
    (@tapp0_fapp0
      (@Catd_cat (@PathOut_cat Z x))
      Cat_cat
      (@PathInd_src_catd Z x)
      (@PathInd_tgt_catd Z x)
      E
      (@tdapp0_fapp0
        Z
        (@PathOutMotives_catd Z)
        (@Const_catd Z Cat_cat)
        (@PathOutReflEval_funcd Z)
        (@PathOutPi_funcd Z)
        x
        (@PathInd_transfd Z)))
    u
    ≡ @path_ind_sec Z x E u;

assert [K : Cat] (R : τ (Catd K))
  (S T : τ (Functord R (@Const_catd K Cat_cat)))
  (eta : τ (Transfd S T))
  (k : τ (Obj K))
  (r : τ (Obj (Fibre_cat R k))) ⊢
  @tapp0_fapp0
    (@Sigma_cat K R)
    Cat_cat
    (@Sigma_catd_functord_catd K R S)
    (@Sigma_catd_functord_catd K R T)
    (Struct_sigma k r)
    (@Sigma_transfd_funcd K R S T eta)
    ≡ @tapp0_fapp0
        (Fibre_cat R k)
        Cat_cat
        (@Fibre_func K R (@Const_catd K Cat_cat) S k)
        (@Fibre_func K R (@Const_catd K Cat_cat) T k)
        r
        (@tdapp0_fapp0 K R (@Const_catd K Cat_cat) S T k eta);

assert [Z : Cat] (x : τ (Obj Z)) (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @tapp0_fapp0
    (@Sigma_cat Z (@PathOutMotives_catd Z))
    Cat_cat
    (@PathIndSrc_catd Z)
    (@PathIndTgt_catd Z)
    (Struct_sigma x E)
    (@PathInd_funcd Z)
    ≡ @path_ind_func_fapp0 Z x E;

assert [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢
  @fapp0
    (Fibre_cat E (@pathout_refl_obj Z x))
    (Pi_cat E)
    (@tapp0_fapp0
      (@Sigma_cat Z (@PathOutMotives_catd Z))
      Cat_cat
      (@PathIndSrc_catd Z)
      (@PathIndTgt_catd Z)
      (Struct_sigma x E)
      (@PathInd_funcd Z))
    u
    ≡ @path_ind_sec Z x E u;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @PathIndSrc_transport_func Z x y p E
    ≡ @pathout_refl_eval_base_func Z x y p E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @PathIndTgt_transport_func Z x y p E
    ≡ @section_pullback_func
        (@PathOut_cat Z y)
        (@PathOut_cat Z x)
        (@PathOut_transport_func Z x y p)
        E;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y))
  (E : τ (Catd (@PathOut_cat Z x))) ⊢
  @fdapp1_int_cell
    Z
    (@PathOutMotives_catd Z)
    (@Const_catd Z Cat_cat)
    (@PathOutPi_funcd Z)
    x
    y
    p
    E
    ≡ @PathIndTgt_transport_func Z x y p E;

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @tapp0_fapp0
    Z
    Cat_cat
    (@PathOutMotives_catd Z)
    (@Const_catd Z Cat_cat)
    x
    (@PathOutPi_funcd Z)
    ≡ @Pi_func (@PathOut_cat Z x);
`;
            const result = checkLambdapiProbe(
                { source, sourceMap: [] },
                {
                    packageRoot: resolve(repositoryRoot, 'emdash2'),
                    timeoutMs: 20_000,
                    warningsEnabled: false
                }
            );
            assert.equal(result.accepted, true, result.diagnostics);
            assert.equal(result.timedOut, false);
        }
    );
});
