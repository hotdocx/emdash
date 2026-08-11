/**
 * Focused qualification evidence for the root-only PathOut transitivity
 * derived library.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    coreCategoricalFibredStructureCoreName
} from '../src/v3_2/categorical_fibred_structure_transfer';
import {
    CORE_CATEGORICAL_STRUCTURAL_SYMBOLS,
    coreCategoricalStructuralSymbolCoreName
} from '../src/v3_2/categorical_structural_transfer';
import { createCoreLfChecker } from '../src/v3_2/lf_checker';
import { coreLfDefinitionalCompare } from '../src/v3_2/lf_conversion';
import {
    CoreLfDeclarationEnvironment
} from '../src/v3_2/lf_declarations';
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
import { serializeKernelExpression } from '../src/v3_2/lambdapi';
import {
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES
} from '../src/v3_2/pathout_foundation_transfer';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_CORE_NAMES
} from '../src/v3_2/pathind_fixed_source_transfer';
import {
    CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY,
    CORE_PATHOUT_TRANSITIVITY_1E_CORE_NAMES,
    CORE_PATHOUT_TRANSITIVITY_1E_LINKAGE,
    CORE_PATHOUT_TRANSITIVITY_1E_MODULE,
    CORE_PATHOUT_TRANSITIVITY_1E_POLICY,
    CORE_PATHOUT_TRANSITIVITY_1E_REVISION,
    CORE_PATHOUT_TRANSITIVITY_1E_RUNTIME_MODULE,
    CORE_PATHOUT_TRANSITIVITY_1E_RUNTIME_POLICY,
    CORE_PATHOUT_TRANSITIVITY_1E_SYMBOLS,
    CorePathoutTransitivityOrdinaryLibraryCapabilityError,
    assertCorePathoutTransitivityOrdinaryLibraryCapability,
    compileCorePathoutTransitivity1eInheritedProof,
    compileCorePathoutTransitivity1eTransfer
} from '../src/v3_2/pathout_transitivity_transfer';
import { checkLambdapiProbe } from '../src/v3_2/probe';

const repositoryRoot = resolve(__dirname, '..');
const nodeProvenance = provenance(
    'derived',
    'PATHOUT-LIBRARY-TRANSITIVITY-1E focused witness'
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

const linkedCoreName = (backendName: string): string => {
    const link = CORE_PATHOUT_TRANSITIVITY_1E_LINKAGE.entries.find(
        entry =>
            entry.kind === 'free-declaration' &&
            entry.backendName === backendName
    );
    if (link === undefined || link.kind !== 'free-declaration') {
        throw new Error(`No transitivity link for ${backendName}`);
    }
    return link.coreName;
};

const categoryType = (): KernelExpression => kernelApplication(
    'category-universe',
    [],
    nodeProvenance
);

const categoryOfCategories = (): KernelExpression => kernelApplication(
    'category-of-categories',
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

const displayedFunctorType = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => decode(call(
    linkedCoreName('Functord'),
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]
));

const homCategory = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => kernelApplication(
    'hom-category',
    [{ value: base }, { value: source }, { value: target }],
    nodeProvenance
);

const displayedFunctorCategory = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => call(
    linkedCoreName('Functord_cat'),
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]
);

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

const functorHomCapped = (
    source: KernelExpression,
    target: KernelExpression,
    functor: KernelExpression,
    sourceObject: KernelExpression,
    targetObject: KernelExpression,
    arrow: KernelExpression
): KernelExpression => kernelApplication(
    'functor-hom-capped',
    [
        { value: source },
        { value: target },
        { value: functor },
        { value: sourceObject },
        { value: targetObject },
        { value: arrow }
    ],
    nodeProvenance
);

const fibre = (
    base: KernelExpression,
    family: KernelExpression,
    point: KernelExpression
): KernelExpression => functorObject(
    base,
    categoryOfCategories(),
    family,
    point
);

const sectionCategory = (
    base: KernelExpression,
    family: KernelExpression
): KernelExpression => kernelApplication(
    'section-category',
    [{ value: base }, { value: family }],
    nodeProvenance
);

const component = (
    base: KernelExpression,
    sourceFamily: KernelExpression,
    targetFamily: KernelExpression,
    point: KernelExpression,
    displayedFunctor: KernelExpression
): KernelExpression => kernelApplication(
    'transfor-component-capped',
    [
        { value: base },
        { value: categoryOfCategories() },
        { value: sourceFamily },
        { value: targetFamily },
        { value: point },
        { value: displayedFunctor }
    ],
    nodeProvenance
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

const compositionTarget = (
    Z: KernelExpression,
    x: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_TRANSITIVITY_1E_CORE_NAMES.CompTarget_catd,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'explicit', value: x }
    ]
);

const compositionTargetAction = (
    Z: KernelExpression,
    x: KernelExpression,
    a: KernelExpression,
    b: KernelExpression,
    p: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_TRANSITIVITY_1E_CORE_NAMES.CompTarget_fapp1_func,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'implicit', value: x },
        { plicity: 'implicit', value: a },
        { plicity: 'implicit', value: b },
        { plicity: 'explicit', value: p }
    ]
);

const compositionMotive = (
    Z: KernelExpression,
    x: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_TRANSITIVITY_1E_CORE_NAMES.CompMotive_catd,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'explicit', value: x }
    ]
);

const pathCompositionSection = (
    Z: KernelExpression,
    x: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_TRANSITIVITY_1E_CORE_NAMES.path_comp_sec,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'explicit', value: x }
    ]
);

const pathCompositionFunctor = (
    Z: KernelExpression,
    x: KernelExpression,
    y: KernelExpression,
    p: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_TRANSITIVITY_1E_CORE_NAMES.path_comp_func,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'implicit', value: x },
        { plicity: 'implicit', value: y },
        { plicity: 'explicit', value: p }
    ]
);

const displayedIdentity = (
    Z: KernelExpression,
    family: KernelExpression
): KernelExpression => call(
    coreCategoricalFibredStructureCoreName('displayed-identity'),
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'implicit', value: family }
    ]
);

const pathInductionSection = (
    Z: KernelExpression,
    x: KernelExpression,
    motive: KernelExpression,
    datum: KernelExpression
): KernelExpression => call(
    CORE_PATHIND_FIXED_SOURCE_1C_CORE_NAMES.pathInductionSection,
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'explicit', value: x },
        { plicity: 'explicit', value: motive },
        { plicity: 'explicit', value: datum }
    ]
);

const identityFunctor = (Z: KernelExpression): KernelExpression => call(
    coreCategoricalStructuralSymbolCoreName(
        CORE_CATEGORICAL_STRUCTURAL_SYMBOLS.identityFunctor
    ),
    [{ plicity: 'implicit', value: Z }]
);

const stablePrecomposition = (
    Z: KernelExpression,
    x: KernelExpression,
    y: KernelExpression,
    z: KernelExpression,
    p: KernelExpression,
    q: KernelExpression
): KernelExpression => call(
    coreCategoricalFibredStructureCoreName('precomposition-action'),
    [
        { plicity: 'implicit', value: Z },
        { plicity: 'implicit', value: Z },
        { plicity: 'explicit', value: identityFunctor(Z) },
        { plicity: 'explicit', value: z },
        { plicity: 'implicit', value: x },
        { plicity: 'implicit', value: y },
        { plicity: 'explicit', value: p },
        { plicity: 'explicit', value: q }
    ]
);

interface TransitivityFixture {
    readonly compilation: ReturnType<
        typeof compileCorePathoutTransitivity1eTransfer
    >;
    readonly environment: CoreLfDeclarationEnvironment;
    readonly Z: KernelExpression;
    readonly W: KernelExpression;
    readonly x: KernelExpression;
    readonly y: KernelExpression;
    readonly z: KernelExpression;
    readonly w: KernelExpression;
    readonly p: KernelExpression;
    readonly q: KernelExpression;
    readonly s: KernelExpression;
}

let cachedFixture: TransitivityFixture | undefined;

const fixture = (): TransitivityFixture => {
    if (cachedFixture !== undefined) return cachedFixture;
    const compilation = compileCorePathoutTransitivity1eTransfer();
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
    const Z = add('pathout_transitivity_test_Z', categoryType());
    const W = add('pathout_transitivity_test_W', categoryType());
    const x = add('pathout_transitivity_test_x', objectType(Z));
    const y = add('pathout_transitivity_test_y', objectType(Z));
    const z = add('pathout_transitivity_test_z', objectType(Z));
    const w = add('pathout_transitivity_test_w', objectType(W));
    const p = add('pathout_transitivity_test_p', homType(Z, x, y));
    const q = add('pathout_transitivity_test_q', homType(Z, y, z));
    const s = add('pathout_transitivity_test_s', homType(W, w, w));
    cachedFixture = Object.freeze({
        compilation,
        environment,
        Z,
        W,
        x,
        y,
        z,
        w,
        p,
        q,
        s
    });
    return cachedFixture;
};

const assertDefinitionallyEqual = (
    left: KernelExpression,
    right: KernelExpression,
    witness: TransitivityFixture
): void => {
    const result = coreLfDefinitionalCompare(
        witness.environment,
        left,
        right,
        8192,
        undefined,
        witness.compilation.composedRuntime
    );
    const diagnostic = result.status === 'not-equal'
        ? [
            `left=${serializeKernelExpression(result.normalizedLeft)}`,
            `right=${serializeKernelExpression(result.normalizedRight)}`,
            `mismatch=${result.mismatch.code}@` +
                result.mismatch.path.join('.')
        ].join('; ')
        : `status=${result.status}`;
    assert.equal(
        result.status,
        'equal',
        `Expected definitional equality, ${diagnostic}`
    );
};

describe('PATHOUT-LIBRARY-TRANSITIVITY-1E transfer', () => {
    it('seals the reviewed exact corrected 0/1/0/5 boundary', () => {
        const boundary = CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY;
        assert.equal(
            CORE_PATHOUT_TRANSITIVITY_1E_REVISION,
            'PATHOUT-LIBRARY-TRANSITIVITY-1E-TRANSFER-4'
        );
        assert.deepEqual(
            [
                boundary.reviewedAuthorization,
                boundary.proposalCheckpoint,
                boundary.reviewCheckpoint,
                boundary.exactBoundary
            ],
            [
                'PATHOUT-LIBRARY-TRANSITIVITY-1E-REVIEWED-4',
                '2498053',
                'fc9a323',
                '0/1/0/5'
            ]
        );
        assert.deepEqual(
            [
                boundary.trustedDeclarationCount,
                boundary.runtimeRuleCount,
                boundary.proofRuleCount,
                boundary.transparentDefinitionCount,
                boundary.inheritedProofProviderCount,
                boundary.requiredExistingProviderCount,
                boundary.typedLibraryConsumerCount,
                boundary.selectedDefinitionalObservationCount,
                boundary.selectedRuntimeDefinitionalObservationCount,
                boundary.selectedInheritedProofTimeObservationCount,
                boundary.negativeConsumerCount,
                boundary.boundedOracleAssertionCount
            ],
            [0, 1, 0, 5, 1, 11, 2, 8, 7, 1, 8, 8]
        );
        assert.deepEqual(boundary.runtimeRuleIds, [
            'pathout.transitivity.' +
                'fixed-source-selected-component-' +
                'consumer-parent-fusion'
        ]);
        assert.deepEqual(boundary.inheritedProofProviderIds, [
            'stress.sigma-pi.uncurrying'
        ]);
        assert.deepEqual(boundary.transparentDefinitionNames, [
            'CompTarget_catd',
            'CompTarget_fapp1_func',
            'CompMotive_catd',
            'path_comp_sec',
            'path_comp_func'
        ]);
        assert.equal(
            boundary.sourceInjectiveModifierRecordedAsMetadata,
            true
        );
        assert.equal(
            boundary.typescriptInjectivityOrUnificationBehaviorAdded,
            false
        );
        assert.equal(boundary.v2PreDeltaLocalSupportRetained, false);
        assert.equal(
            boundary.v3StablePostCompTargetDeltaLocalSupportRetained,
            false
        );
        assert.equal(
            boundary.v4OriginalConsumerParentLocalSupportSelected,
            true
        );
        assert.equal(
            boundary.localSupportRuleMatchesBeforeDescendantDelta,
            true
        );
        assert.equal(boundary.browserOrPublicPackageExported, false);
    });

    it('compiles five definitions then one subject-checked local support',
        () => {
            const { compilation } = fixture();
            assert.equal(compilation.compiled.declarations.length, 5);
            assert.equal(compilation.compiled.comparisonStepLimit, 512);
            assert.equal(
                CORE_PATHOUT_TRANSITIVITY_1E_MODULE.runtimeRules.length,
                0
            );
            assert.equal(
                CORE_PATHOUT_TRANSITIVITY_1E_MODULE.proofRules.length,
                0
            );
            assert.equal(
                CORE_PATHOUT_TRANSITIVITY_1E_RUNTIME_MODULE
                    .runtimeRules.length,
                1
            );
            assert.equal(
                CORE_PATHOUT_TRANSITIVITY_1E_RUNTIME_MODULE
                    .proofRules.length,
                0
            );
            assert.equal(compilation.runtime.rules.length, 1);
            assert.equal(
                compilation.runtime.rules[0]?.subjectValidation.kind,
                'typescript-checked'
            );
            assert.equal(compilation.runtime.comparisonStepLimit, 512);
            assert.equal(
                CORE_PATHOUT_TRANSITIVITY_1E_RUNTIME_POLICY.entries[0]
                    ?.policy,
                'runtime-rewrite'
            );
            assert.equal(
                CORE_PATHOUT_TRANSITIVITY_1E_POLICY.entries.every(entry =>
                    entry.policy === 'checked-transparent-definition'
                ),
                true
            );
            const localNames = new Set(
                Object.values(CORE_PATHOUT_TRANSITIVITY_1E_CORE_NAMES)
            );
            const localLinkNames =
                CORE_PATHOUT_TRANSITIVITY_1E_LINKAGE.entries.flatMap(
                    entry =>
                        entry.kind === 'free-declaration' &&
                        localNames.has(entry.coreName)
                            ? [entry.coreName]
                            : []
                );
            assert.equal(localLinkNames.length, 5);
            assert.equal(
                CORE_PATHOUT_TRANSITIVITY_1E_MODULE.declarations[0]
                    ?.modifiers.rigidity,
                'injective'
            );
        });

    it('fires the exact complete-parent support at its staged redex', () => {
        const w = fixture();
        const id = CORE_PATHOUT_TRANSITIVITY_1E_BOUNDARY.runtimeRuleIds[0];
        assert.ok(id);
        const program = w.compilation.runtimeFragment.localProgram;
        const rule = program.rule(id);
        assert.ok(rule, `Missing local transitivity runtime rule ${id}`);
        const redex = program.instantiateRuleLeft(
            rule,
            [w.Z, w.x, w.y, w.p],
            nodeProvenance
        );
        const result = w.compilation.composedRuntime.rewriteHead(redex);
        assert.equal(result.status, 'rewritten');
        if (result.status !== 'rewritten') {
            assert.fail(`Local transitivity runtime rule ${id} did not fire`);
        }
        assert.equal(result.ruleId, id);
    });

    it('computes three observations and proves the Sigma/Pi observation',
        () => {
        const w = fixture();
        const repX = representable(w.Z, w.x);
        const repY = representable(w.Z, w.y);
        const target = compositionTarget(w.Z, w.x);
        const motive = compositionMotive(w.Z, w.x);
        const targetFibre = displayedFunctorCategory(w.Z, repY, repX);
        assertDefinitionallyEqual(
            fibre(w.Z, target, w.y),
            targetFibre,
            w
        );
        assertDefinitionallyEqual(
            fibre(
                pathoutCategory(w.Z, w.x),
                motive,
                pathoutObject(w.Z, w.x, w.y, w.p)
            ),
            targetFibre,
            w
        );
        const sectionCategoryComparison = coreLfDefinitionalCompare(
            w.environment,
            sectionCategory(pathoutCategory(w.Z, w.x), motive),
            displayedFunctorCategory(w.Z, repX, target),
            8192,
            undefined,
            w.compilation.composedRuntime
        );
        assert.equal(sectionCategoryComparison.status, 'not-equal');
        if (sectionCategoryComparison.status !== 'not-equal') {
            assert.fail('Sigma/Pi category presentations collapsed at runtime');
        }
        assert.equal(sectionCategoryComparison.mismatch.code, 'TAG_MISMATCH');
        const inherited = compileCorePathoutTransitivity1eInheritedProof(
            w.compilation,
            w.environment
        );
        assert.deepEqual(inherited.proofProgram.ruleIds, [
            'stress.sigma-pi.uncurrying'
        ]);
        const proofResult = inherited.proofProgram.compare(
            sectionCategoryComparison.normalizedLeft,
            sectionCategoryComparison.normalizedRight
        );
        assert.equal(proofResult.status, 'solved');
        if (proofResult.status !== 'solved') {
            assert.fail('Inherited Sigma/Pi proof provider did not solve');
        }
        assert.deepEqual(
            proofResult.ruleApplications.map(application =>
                application.ruleId
            ),
            ['stress.sigma-pi.uncurrying']
        );
        assertDefinitionallyEqual(
            pathInductionSection(
                w.Z,
                w.x,
                motive,
                displayedIdentity(w.Z, repX)
            ),
            pathCompositionSection(w.Z, w.x),
            w
        );
    });

    it('computes the final four observations to stable precomposition',
        () => {
            const w = fixture();
            const repX = representable(w.Z, w.x);
            const repY = representable(w.Z, w.y);
            const target = compositionTarget(w.Z, w.x);
            const pathFunctor = pathCompositionFunctor(
                w.Z,
                w.x,
                w.y,
                w.p
            );
            const sectionComponent = component(
                w.Z,
                repX,
                target,
                w.y,
                pathCompositionSection(w.Z, w.x)
            );
            const selectedPathFunctor = functorObject(
                homCategory(w.Z, w.x, w.y),
                displayedFunctorCategory(w.Z, repY, repX),
                sectionComponent,
                w.p
            );
            assertDefinitionallyEqual(
                functorHomCapped(
                    w.Z,
                    categoryOfCategories(),
                    target,
                    w.x,
                    w.y,
                    w.p
                ),
                compositionTargetAction(
                    w.Z,
                    w.x,
                    w.x,
                    w.y,
                    w.p
                ),
                w
            );
            assertDefinitionallyEqual(selectedPathFunctor, pathFunctor, w);
            const pathComponent = functorObject(
                homCategory(w.Z, w.y, w.z),
                homCategory(w.Z, w.x, w.z),
                component(w.Z, repY, repX, w.z, pathFunctor),
                w.q
            );
            assertDefinitionallyEqual(
                pathComponent,
                stablePrecomposition(
                    w.Z,
                    w.x,
                    w.y,
                    w.z,
                    w.p,
                    w.q
                ),
                w
            );
            const expandedComponent = functorObject(
                homCategory(w.Z, w.y, w.z),
                homCategory(w.Z, w.x, w.z),
                component(w.Z, repY, repX, w.z, selectedPathFunctor),
                w.q
            );
            assertDefinitionallyEqual(
                expandedComponent,
                stablePrecomposition(
                    w.Z,
                    w.x,
                    w.y,
                    w.z,
                    w.p,
                    w.q
                ),
                w
            );
        });

    it('types both named transitivity library consumers', () => {
        const w = fixture();
        const checker = createCoreLfChecker(
            w.environment,
            8192,
            w.compilation.composedRuntime
        );
        const section = w.compilation.compiled.application(
            CORE_PATHOUT_TRANSITIVITY_1E_SYMBOLS.pathCompositionSection,
            [w.Z, w.x],
            nodeProvenance
        );
        const functor = w.compilation.compiled.application(
            CORE_PATHOUT_TRANSITIVITY_1E_SYMBOLS.pathCompositionFunctor,
            [w.Z, w.x, w.y, w.p],
            nodeProvenance
        );
        assert.doesNotThrow(() => checker.check(
            checker.rootContext,
            section,
            objectType(displayedFunctorCategory(
                w.Z,
                representable(w.Z, w.x),
                compositionTarget(w.Z, w.x)
            ))
        ));
        assert.doesNotThrow(() => checker.check(
            checker.rootContext,
            functor,
            displayedFunctorType(
                w.Z,
                representable(w.Z, w.y),
                representable(w.Z, w.x)
            )
        ));
    });

    it('rejects all eight foreign-base and wrong-endpoint consumers', () => {
        const w = fixture();
        const checker = createCoreLfChecker(
            w.environment,
            8192,
            w.compilation.composedRuntime
        );
        const infer = (term: KernelExpression): void => {
            checker.infer(checker.rootContext, term);
        };
        const invalid = [
            compositionTarget(w.Z, w.w),
            compositionMotive(w.Z, w.w),
            pathCompositionSection(w.Z, w.w),
            compositionTargetAction(w.Z, w.x, w.x, w.y, w.q),
            compositionTargetAction(w.Z, w.w, w.x, w.y, w.p),
            pathCompositionFunctor(w.Z, w.x, w.y, w.q),
            pathCompositionFunctor(w.W, w.w, w.w, w.p),
            compositionTarget(w.Z, kernelBound(0, nodeProvenance))
        ];
        assert.equal(invalid.length, 8);
        invalid.forEach(term => assert.throws(() => infer(term)));
    });

    it('keeps rule authority and public presentation closed', () => {
        assert.equal(
            assertCorePathoutTransitivityOrdinaryLibraryCapability(
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
                    assertCorePathoutTransitivityOrdinaryLibraryCapability(
                        capability
                    ),
                CorePathoutTransitivityOrdinaryLibraryCapabilityError
            );
        }
        for (const relative of [
            'src/v3_2/index.ts',
            'src/v3_2/package_core.ts',
            'src/v3_2/package_authoring.ts',
            'src/v3_2/package_workspace.ts',
            'src/v3_2/browser.ts'
        ]) {
            assert.doesNotMatch(
                readFileSync(resolve(repositoryRoot, relative), 'utf8'),
                /pathout_transitivity_transfer/u,
                relative
            );
        }
    });

    it(
        'matches all eight bounded active-Lambdapi assertions',
        {
            skip:
                process.env.EMDASH_RUN_LAMBDAPI_PATHOUT_TRANSITIVITY_PROBES
                !== '1'
        },
        () => {
            const source = String.raw`require open emdash.emdash3_2;

assert [Z : Cat] (x y : τ (Obj Z)) ⊢
  Fibre_cat (@CompTarget_catd Z x) y
    ≡ @Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x);

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  Fibre_cat (@CompMotive_catd Z x) (@pathout_obj Z x y p)
    ≡ @Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x);

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @eq_refl Cat_grpd
    (@Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x))
  : τ (@= Cat_grpd
      (@Pi_cat (@PathOut_cat Z x) (@CompMotive_catd Z x))
      (@Functord_cat Z (@Rep_catd Z x) (@CompTarget_catd Z x)));

assert [Z : Cat] (x : τ (Obj Z)) ⊢
  @path_ind_sec
    Z x (@CompMotive_catd Z x) (@id_funcd Z (@Rep_catd Z x))
    ≡ @path_comp_sec Z x;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @fapp1_fapp0 Z Cat_cat (@CompTarget_catd Z x) x y p
    ≡ @CompTarget_fapp1_func Z x x y p;

assert [Z : Cat] (x y : τ (Obj Z)) (p : τ (Hom Z x y)) ⊢
  @fapp0
    (Hom_cat Z x y)
    (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
    (@tapp0_fapp0 Z Cat_cat (@Rep_catd Z x)
      (@CompTarget_catd Z x) y (@path_comp_sec Z x))
    p
    ≡ @path_comp_func Z x y p;

assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y)) (q : τ (Hom Z y z)) ⊢
  @fapp0
    (Hom_cat Z y z)
    (Hom_cat Z x z)
    (@tapp0_fapp0 Z Cat_cat (@Rep_catd Z y)
      (@Rep_catd Z x) z (@path_comp_func Z x y p))
    q
    ≡ @hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q;

assert [Z : Cat] (x y z : τ (Obj Z))
  (p : τ (Hom Z x y)) (q : τ (Hom Z y z)) ⊢
  @fapp0
    (Hom_cat Z y z)
    (Hom_cat Z x z)
    (@tapp0_fapp0 Z Cat_cat (@Rep_catd Z y) (@Rep_catd Z x) z
      (@fapp0
        (Hom_cat Z x y)
        (@Functord_cat Z (@Rep_catd Z y) (@Rep_catd Z x))
        (@tapp0_fapp0 Z Cat_cat (@Rep_catd Z x)
          (@CompTarget_catd Z x) y (@path_comp_sec Z x))
        p))
    q
    ≡ @hom_precomp_along_fapp0 Z Z (@id_func Z) z x y p q;
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
