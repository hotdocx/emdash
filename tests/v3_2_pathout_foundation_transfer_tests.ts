/**
 * Focused qualification evidence for PATHOUT-LIBRARY-FOUNDATION-1B.
 */

import assert from 'node:assert/strict';
import {
    readFileSync
} from 'node:fs';
import {
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
} from '../src/v3_2/categorical_fibred_dependent_target_transfer';
import {
    coreCategoricalDependentCompositionCoreName
} from '../src/v3_2/categorical_dependent_composition_transfer';
import {
    coreCategoricalDisplayedNdHigherFoundationCoreName
} from '../src/v3_2/categorical_displayed_nd_higher_foundation_transfer';
import {
    CORE_DIRECTED_1A_PRIMITIVE_NAMES
} from '../src/v3_2/directed_1a';
import {
    CORE_DIRECTED_1B_PRIMITIVE_NAMES
} from '../src/v3_2/directed_1b';
import {
    createCoreLfChecker
} from '../src/v3_2/lf_checker';
import {
    CoreLfDeclarationEnvironment
} from '../src/v3_2/lf_declarations';
import {
    coreLfDefinitionalCompare
} from '../src/v3_2/lf_conversion';
import {
    KernelExpression,
    Plicity,
    binderMode,
    kernelApplication,
    kernelBound,
    kernelCall,
    kernelFree,
    provenance
} from '../src/v3_2/kernel';
import {
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES,
    CORE_PATHOUT_FOUNDATION_1B_LIBRARY_MODULE,
    CORE_PATHOUT_FOUNDATION_1B_LIBRARY_POLICY,
    CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_MODULE,
    CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_POLICY,
    CORE_PATHOUT_FOUNDATION_1B_PROOF_MODULE,
    CORE_PATHOUT_FOUNDATION_1B_RUNTIME_MODULE,
    CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY,
    CorePathoutOrdinaryLibraryCapabilityError,
    assertCorePathoutOrdinaryLibraryCapability,
    compileCorePathoutFoundation1bTransfer
} from '../src/v3_2/pathout_foundation_transfer';
import {
    serializeKernelExpression
} from '../src/v3_2/lambdapi';
import {
    checkLambdapiProbe
} from '../src/v3_2/probe';

const repositoryRoot = resolve(__dirname, '..');
const nodeProvenance = provenance(
    'derived',
    'PATHOUT-LIBRARY-FOUNDATION-1B focused witness'
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

const objectType = (base: KernelExpression): KernelExpression =>
    decode(kernelApplication(
        'object-classifier',
        [{ value: base }],
        nodeProvenance
    ));

const homType = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => decode(kernelApplication(
    'hom-classifier',
    [{ value: base }, { value: source }, { value: target }],
    nodeProvenance
));

const functorObject = (
    source: KernelExpression,
    target: KernelExpression,
    functor: KernelExpression,
    object: KernelExpression
): KernelExpression => kernelApplication(
    'functor-object',
    [
        { value: source },
        { value: target },
        { value: functor },
        { value: object }
    ],
    nodeProvenance
);

const opposite = (base: KernelExpression): KernelExpression => call(
    CORE_CATEGORICAL_FIBRED_DEPENDENT_TARGET_CORE_NAMES
        .oppositeCategory,
    [{ plicity: 'explicit', value: base }]
);

const categoryOfCategories = (): KernelExpression => kernelApplication(
    'category-of-categories',
    [],
    nodeProvenance
);

const identity = (
    base: KernelExpression,
    object: KernelExpression
): KernelExpression => call(
    coreCategoricalDisplayedNdHigherFoundationCoreName(
        'identityArrow'
    ),
    [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: object }
    ]
);

const representable = (
    Z: KernelExpression,
    x: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.representableFamily,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'explicit', value: x }
    ]
);

const representableTransport = (
    Z: KernelExpression,
    x: KernelExpression,
    y: KernelExpression,
    p: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.representableTransport,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'implicit', value: x },
        { plicity: 'implicit', value: y },
        { plicity: 'explicit', value: p }
    ]
);

const representedSourceAction = (
    Z: KernelExpression,
    x: KernelExpression,
    y: KernelExpression,
    p: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.representedSourceAction,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'implicit', value: Z },
        {
            plicity: 'explicit',
            value: identity(categoryOfCategories(), Z)
        },
        { plicity: 'implicit', value: y },
        { plicity: 'implicit', value: x },
        { plicity: 'explicit', value: p }
    ]
);

const pathoutCategory = (
    Z: KernelExpression,
    x: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutCategory,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'explicit', value: x }
    ]
);

const pathoutCategoryFunctor = (
    Z: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutCategoryFunctor,
    [{ plicity: 'implicit', value: Z }]
);

const pathoutTransport = (
    Z: KernelExpression,
    x: KernelExpression,
    y: KernelExpression,
    p: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutTransport,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'implicit', value: x },
        { plicity: 'implicit', value: y },
        { plicity: 'explicit', value: p }
    ]
);

const pathoutObject = (
    Z: KernelExpression,
    x: KernelExpression,
    y: KernelExpression,
    p: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutObject,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'explicit', value: x },
        { plicity: 'explicit', value: y },
        { plicity: 'explicit', value: p }
    ]
);

const pathoutReflexiveObject = (
    Z: KernelExpression,
    x: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutReflexiveObject,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'explicit', value: x }
    ]
);

const pathoutReflexiveArrow = (
    Z: KernelExpression,
    x: KernelExpression,
    y: KernelExpression,
    p: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutReflexiveArrow,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'explicit', value: x },
        { plicity: 'explicit', value: y },
        { plicity: 'explicit', value: p }
    ]
);

const compose = (
    Z: KernelExpression,
    x: KernelExpression,
    y: KernelExpression,
    z: KernelExpression,
    q: KernelExpression,
    p: KernelExpression
): KernelExpression => call(
    coreCategoricalDependentCompositionCoreName(
        'generic-category-composition'
    ),
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'implicit', value: x },
        { plicity: 'implicit', value: y },
        { plicity: 'implicit', value: z },
        { plicity: 'explicit', value: q },
        { plicity: 'explicit', value: p }
    ]
);

interface PathoutFixture {
    readonly environment: CoreLfDeclarationEnvironment;
    readonly runtime: ReturnType<
        typeof compileCorePathoutFoundation1bTransfer
    >['composedRuntime'];
    readonly proofProgram: ReturnType<
        typeof compileCorePathoutFoundation1bTransfer
    >['proofProgram'];
    readonly Z: KernelExpression;
    readonly W: KernelExpression;
    readonly x: KernelExpression;
    readonly y: KernelExpression;
    readonly z: KernelExpression;
    readonly w: KernelExpression;
    readonly p: KernelExpression;
    readonly q: KernelExpression;
    readonly r: KernelExpression;
}

let cachedFixture: PathoutFixture | undefined;

const fixture = (): PathoutFixture => {
    if (cachedFixture !== undefined) return cachedFixture;
    const compilation = compileCorePathoutFoundation1bTransfer();
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
    const Z = add('pathout_test_Z', categoryType());
    const W = add('pathout_test_W', categoryType());
    const x = add('pathout_test_x', objectType(Z));
    const y = add('pathout_test_y', objectType(Z));
    const z = add('pathout_test_z', objectType(Z));
    const w = add('pathout_test_w', objectType(W));
    const p = add('pathout_test_p', homType(Z, x, y));
    const q = add('pathout_test_q', homType(Z, y, z));
    const r = add('pathout_test_r', homType(Z, x, z));
    cachedFixture = Object.freeze({
        environment,
        runtime: compilation.composedRuntime,
        proofProgram: compilation.proofProgram,
        Z,
        W,
        x,
        y,
        z,
        w,
        p,
        q,
        r
    });
    return cachedFixture;
};

const assertDefinitionallyEqual = (
    left: KernelExpression,
    right: KernelExpression,
    witness = fixture()
): void => {
    const result = coreLfDefinitionalCompare(
        witness.environment,
        left,
        right,
        4096,
        undefined,
        witness.runtime
    );
    assert.equal(
        result.status,
        'equal',
        `Expected definitional equality, received ${result.status}`
    );
};

const assertProofTimeEqual = (
    left: KernelExpression,
    right: KernelExpression,
    witness = fixture()
): void => {
    const runtimeOnly = coreLfDefinitionalCompare(
        witness.environment,
        left,
        right,
        4096,
        undefined,
        witness.runtime
    );
    assert.equal(runtimeOnly.status, 'not-equal');
    const result = witness.proofProgram
        .compareUnderOpaqueDeclarationExtension(
            witness.environment,
            witness.runtime,
            left,
            right
        );
    const diagnostic = result.status === 'stuck'
        ? [
            `reason=${result.reason}`,
            `problem=${result.problemId}`,
            `left=${serializeKernelExpression(result.left)}`,
            `right=${serializeKernelExpression(result.right)}`,
            `mismatch=${result.mismatch?.code ?? 'none'}@` +
                `${result.mismatch?.path.join('.') ?? 'none'}`,
            `rules=${result.ruleApplications.map(application =>
                application.ruleId).join(',')}`,
            `trace=${result.trace.map(entry => entry.kind).join(',')}`
        ].join('; ')
        : `status=${result.status}`;
    assert.equal(
        result.status,
        'solved',
        `Expected proof-time equality, ${diagnostic}`
    );
    if (result.status === 'solved') {
        assert.equal(
            result.ruleApplications.some(application =>
                application.ruleId ===
                    'pathout.foundation.' +
                    'precomposition-identity-family'
            ),
            true
        );
    }
};

const infer = (term: KernelExpression) => {
    const witness = fixture();
    const checker = createCoreLfChecker(
        witness.environment,
        4096,
        witness.runtime
    );
    return checker.infer(checker.rootContext, term);
};

describe('PATHOUT-LIBRARY-FOUNDATION-1B transfer', () => {
    it('seals the reviewed exact 5/13/2/9 root-only boundary', () => {
        assert.deepEqual(
            CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                .prerequisiteDeclarationNames,
            [
                'hom_int_precomp_tele_func',
                'hom_int_precomp_func',
                'Sigma_func',
                'hom_postcomp_func',
                'hom_precomp_along_func'
            ]
        );
        assert.deepEqual(
            CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY.runtimeRuleIds,
            [
                'pathout.foundation.represented-hom-capped-action',
                'pathout.foundation.postcomposition-object-action',
                'pathout.foundation.' +
                    'represented-hom-object-action-fusion',
                'pathout.foundation.' +
                    'postcomposition-identity-source-unit',
                'pathout.foundation.precomposition-object-action',
                'pathout.foundation.' +
                    'precomposition-identity-incoming',
                'pathout.foundation.hom-int-precomp-component',
                'pathout.foundation.' +
                    'hom-int-precomp-component-object-fusion',
                'pathout.foundation.hom-int-precomp-full-action',
                'pathout.foundation.hom-int-precomp-capped-action',
                'pathout.foundation.hom-int-precomp-tele-application',
                'pathout.foundation.sigma-func-object',
                'pathout.foundation.sigma-func-capped-action'
            ]
        );
        assert.deepEqual(
            CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY.proofRuleIds,
            [
                'pathout.foundation.precomposition-identity-family',
                'pathout.foundation.' +
                    'hom-int-precomp-projection-order'
            ]
        );
        assert.deepEqual(
            CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                .transparentLibraryDefinitionNames,
            [
                'Rep_catd_func',
                'Rep_catd',
                'Rep_transport_func',
                'PathOut_cat',
                'PathOut_cat_func',
                'PathOut_transport_func',
                'pathout_obj',
                'pathout_refl_obj',
                'pathout_refl_arrow'
            ]
        );
        assert.deepEqual(
            [
                CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                    .prerequisiteDeclarationCount,
                CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                    .runtimeRuleCount,
                CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                    .proofRuleCount,
                CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                    .transparentLibraryDefinitionCount,
                CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                    .generatedProofConstraintCount
            ],
            [5, 13, 2, 9, 4]
        );
        assert.equal(
            CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                .browserOrPublicPackageExported,
            false
        );
        assert.equal(
            CORE_PATHOUT_FOUNDATION_1B_TRANSFER_BOUNDARY
                .intrinsicCoreOwnerDelta,
            0
        );
    });

    it('compiles every entry through the generic transfer engines', () => {
        const compilation = compileCorePathoutFoundation1bTransfer();
        assert.equal(compilation.prerequisiteCompiled.declarations.length, 5);
        assert.equal(compilation.libraryCompiled.declarations.length, 9);
        assert.equal(compilation.runtime.rules.length, 13);
        assert.equal(
            compilation.runtime.rules.every(rule =>
                rule.subjectValidation.kind === 'typescript-checked'
            ),
            true
        );
        assert.deepEqual(compilation.proofProgram.ruleIds, [
            'pathout.foundation.precomposition-identity-family',
            'pathout.foundation.hom-int-precomp-projection-order'
        ]);
        assert.equal(
            compilation.proofProgram.rules[0]?.typingValidation.kind,
            'typescript-checked'
        );
        assert.equal(
            compilation.proofProgram.rules[1]?.typingValidation.kind,
            'external-oracle-required'
        );
        assert.deepEqual(
            CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_POLICY.entries.map(
                entry => entry.policy
            ),
            [
                'opaque-signature',
                'opaque-signature',
                'opaque-signature',
                'opaque-signature',
                'opaque-signature'
            ]
        );
        assert.equal(
            CORE_PATHOUT_FOUNDATION_1B_LIBRARY_POLICY.entries.every(
                entry => entry.policy ===
                    'checked-transparent-definition'
            ),
            true
        );
        assert.equal(
            CORE_PATHOUT_FOUNDATION_1B_RUNTIME_MODULE.runtimeRules.length,
            13
        );
        assert.equal(
            CORE_PATHOUT_FOUNDATION_1B_PROOF_MODULE.proofRules.length,
            2
        );
    });

    it('computes a representable fibre as Hom(Z,x,y)', () => {
        const witness = fixture();
        assertDefinitionallyEqual(
            functorObject(
                witness.Z,
                categoryOfCategories(),
                representable(witness.Z, witness.x),
                witness.y
            ),
            kernelApplication(
                'hom-category',
                [
                    { value: witness.Z },
                    { value: witness.x },
                    { value: witness.y }
                ],
                nodeProvenance
            ),
            witness
        );
    });

    it('computes representable transport by hom_int precomposition', () => {
        const witness = fixture();
        assertDefinitionallyEqual(
            representableTransport(
                witness.Z,
                witness.x,
                witness.y,
                witness.p
            ),
            representedSourceAction(
                witness.Z,
                witness.x,
                witness.y,
                witness.p
            ),
            witness
        );
    });

    it('computes PathOut(x) as the Sigma total of Rep(x)', () => {
        const witness = fixture();
        assertDefinitionallyEqual(
            pathoutCategory(witness.Z, witness.x),
            call(CORE_DIRECTED_1A_PRIMITIVE_NAMES['sigma-category'], [
                { plicity: 'implicit', value: witness.Z },
                {
                    plicity: 'explicit',
                    value: representable(witness.Z, witness.x)
                }
            ]),
            witness
        );
    });

    it('computes the PathOut functor object as PathOut(x)', () => {
        const witness = fixture();
        assertDefinitionallyEqual(
            functorObject(
                opposite(witness.Z),
                categoryOfCategories(),
                pathoutCategoryFunctor(witness.Z),
                witness.x
            ),
            pathoutCategory(witness.Z, witness.x),
            witness
        );
    });

    it('proves general source transport by projection-order unification',
        () => {
        const witness = fixture();
        assertProofTimeEqual(
            functorObject(
                pathoutCategory(witness.Z, witness.y),
                pathoutCategory(witness.Z, witness.x),
                pathoutTransport(
                    witness.Z,
                    witness.x,
                    witness.y,
                    witness.p
                ),
                pathoutObject(
                    witness.Z,
                    witness.y,
                    witness.z,
                    witness.q
                )
            ),
            pathoutObject(
                witness.Z,
                witness.x,
                witness.z,
                compose(
                    witness.Z,
                    witness.x,
                    witness.y,
                    witness.z,
                    witness.q,
                    witness.p
                )
            ),
            witness
        );
    });

    it('computes reflexive source transport to (y,p)', () => {
        const witness = fixture();
        assertDefinitionallyEqual(
            functorObject(
                pathoutCategory(witness.Z, witness.y),
                pathoutCategory(witness.Z, witness.x),
                pathoutTransport(
                    witness.Z,
                    witness.x,
                    witness.y,
                    witness.p
                ),
                pathoutReflexiveObject(witness.Z, witness.y)
            ),
            pathoutObject(
                witness.Z,
                witness.x,
                witness.y,
                witness.p
            ),
            witness
        );
    });

    it('types the canonical arrow from (x,id_x) to (y,p)', () => {
        const witness = fixture();
        const term = pathoutReflexiveArrow(
            witness.Z,
            witness.x,
            witness.y,
            witness.p
        );
        const checker = createCoreLfChecker(
            witness.environment,
            4096,
            witness.runtime
        );
        const expected = homType(
                pathoutCategory(witness.Z, witness.x),
                pathoutReflexiveObject(witness.Z, witness.x),
                pathoutObject(
                    witness.Z,
                    witness.x,
                    witness.y,
                    witness.p
                )
            );
        const checked = checker.check(
            checker.rootContext,
            term,
            expected
        );
        assertDefinitionallyEqual(checked.type, expected, witness);
    });

    it('rejects a representable source object from another category', () => {
        const witness = fixture();
        assert.throws(() => infer(representable(witness.Z, witness.w)));
    });

    it('rejects representable transport with the wrong endpoints', () => {
        const witness = fixture();
        assert.throws(() => infer(representableTransport(
            witness.Z,
            witness.x,
            witness.y,
            witness.q
        )));
    });

    it('rejects a PathOut source object from another category', () => {
        const witness = fixture();
        assert.throws(() => infer(pathoutCategory(
            witness.Z,
            witness.w
        )));
    });

    it('rejects a dependent pair with the wrong fibre component', () => {
        const witness = fixture();
        assert.throws(() => infer(pathoutObject(
            witness.Z,
            witness.x,
            witness.y,
            witness.q
        )));
    });

    it('rejects PathOut transport with the wrong arrow endpoints', () => {
        const witness = fixture();
        assert.throws(() => infer(pathoutTransport(
            witness.Z,
            witness.x,
            witness.y,
            witness.r
        )));
    });

    it('rejects a foreign unscoped term', () => {
        const witness = fixture();
        assert.throws(() => infer(pathoutCategory(
            witness.Z,
            kernelBound(0, nodeProvenance)
        )));
    });

    it('rejects runtime-rule authority from ordinary library code', () => {
        assert.throws(
            () => assertCorePathoutOrdinaryLibraryCapability(
                'runtime-rewrite'
            ),
            CorePathoutOrdinaryLibraryCapabilityError
        );
    });

    it('rejects proof-rule authority from ordinary library code', () => {
        assert.throws(
            () => assertCorePathoutOrdinaryLibraryCapability(
                'proof-unification'
            ),
            CorePathoutOrdinaryLibraryCapabilityError
        );
        assert.equal(
            assertCorePathoutOrdinaryLibraryCapability(
                'checked-transparent-definition'
            ),
            'checked-transparent-definition'
        );
    });

    it('keeps the qualifying profile out of public/browser barrels', () => {
        for (const relative of [
            'src/v3_2/index.ts',
            'src/v3_2/browser.ts',
            'src/v3_2/package_authoring.ts'
        ]) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, relative), 'utf8'),
                /pathout_foundation_transfer/u,
                relative
            );
        }
        assert.equal(
            CORE_PATHOUT_FOUNDATION_1B_PREREQUISITE_MODULE
                .inductives.length,
            0
        );
        assert.equal(
            CORE_PATHOUT_FOUNDATION_1B_LIBRARY_MODULE.runtimeRules.length,
            0
        );
    });

    it(
        'matches all six bounded active-Lambdapi assertions',
        {
            skip:
                process.env.EMDASH_RUN_LAMBDAPI_PATHOUT_FOUNDATION_PROBES !==
                '1'
        },
        () => {
            const source = [
                'require open emdash.emdash3_2;',
                'assert [Z : Cat] (x y : τ (Obj Z))',
                '  (p : τ (Hom Z x y)) ⊢',
                '  @Rep_transport_func Z x y p',
                '    ≡ @hom_int_precomp_func',
                '        Z Z (@id Cat_cat Z) y x p;',
                'assert [K : Cat] (E : τ (Catd K)) ⊢',
                '  @fapp0 (Catd_cat K) Cat_cat (Sigma_func K) E',
                '    ≡ Sigma_cat E;',
                'assert [K : Cat] (E D : τ (Catd K))',
                '  (eta : τ (Functord E D)) ⊢',
                '  @fapp1_fapp0 (Catd_cat K) Cat_cat',
                '    (@Sigma_func K) E D eta',
                '    ≡ @sigma_map_func K E D eta;',
                'assert [Z : Cat] (x : τ (Obj Z)) ⊢',
                '  @fapp0 (Op_cat Z) Cat_cat',
                '    (@PathOut_cat_func Z) x',
                '    ≡ @PathOut_cat Z x;',
                'assert [Z : Cat] (x y : τ (Obj Z))',
                '  (p : τ (Hom Z x y)) ⊢',
                '  @fapp0',
                '    (@PathOut_cat Z y)',
                '    (@PathOut_cat Z x)',
                '    (@PathOut_transport_func Z x y p)',
                '    (@pathout_refl_obj Z y)',
                '    ≡ @pathout_obj Z x y p;',
                'assert [Z : Cat] (x y : τ (Obj Z))',
                '  (p : τ (Hom Z x y)) ⊢',
                '  @pathout_refl_arrow Z x y p',
                '    : τ (Hom',
                '        (@PathOut_cat Z x)',
                '        (@pathout_refl_obj Z x)',
                '        (@pathout_obj Z x y p));'
            ].join('\n');
            const result = checkLambdapiProbe(
                { source: `${source}\n`, sourceMap: [] },
                {
                    packageRoot: resolve(repositoryRoot, 'emdash2'),
                    timeoutMs: 20_000,
                    warningsEnabled: false
                }
            );
            assert.equal(
                result.accepted,
                true,
                result.diagnostics
            );
            assert.equal(result.timedOut, false);
        }
    );
});
