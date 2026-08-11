/**
 * Focused qualification evidence for PATHIND-TRUSTED-PROFILE-1C.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_LINKAGE
} from '../src/v3_2/categorical_displayed_chain_transfer';
import {
    CORE_CATEGORICAL_FIBRED_BINDER_CORE_NAMES
} from '../src/v3_2/categorical_fibred_binder_transfer';
import {
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CORE_NAMES
} from '../src/v3_2/categorical_fibred_weaken_reindex_transfer';
import {
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_CORE_NAMES
} from '../src/v3_2/categorical_displayed_nd_higher_foundation_transfer';
import {
    CORE_CATEGORICAL_MIXED_ACTION_CORE_NAMES
} from '../src/v3_2/categorical_mixed_action_transfer';
import {
    CORE_DIRECTED_1B_PRIMITIVE_NAMES
} from '../src/v3_2/directed_1b';
import {
    createCoreLfChecker
} from '../src/v3_2/lf_checker';
import {
    coreLfDefinitionalCompare
} from '../src/v3_2/lf_conversion';
import {
    CoreLfDeclarationEnvironment
} from '../src/v3_2/lf_declarations';
import {
    KernelExpression,
    Plicity,
    binderMode,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    provenance
} from '../src/v3_2/kernel';
import {
    CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_MODULE,
    CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_POLICY,
    CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_MODULE,
    CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_POLICY,
    CORE_PATHIND_FIXED_SOURCE_1C_RUNTIME_MODULE,
    CORE_PATHIND_FIXED_SOURCE_1C_RUNTIME_POLICY,
    CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY,
    CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_MODULE,
    CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_POLICY,
    CorePathindOrdinaryLibraryCapabilityError,
    assertCorePathindOrdinaryLibraryCapability,
    compileCorePathindFixedSource1cTransfer,
    corePathindFixedSource1cCoreName
} from '../src/v3_2/pathind_fixed_source_transfer';
import {
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES
} from '../src/v3_2/pathout_foundation_transfer';
import {
    checkLambdapiProbe
} from '../src/v3_2/probe';
import {
    serializeKernelExpression
} from '../src/v3_2/lambdapi';

const repositoryRoot = resolve(__dirname, '..');
const nodeProvenance = provenance(
    'derived',
    'PATHIND-TRUSTED-PROFILE-1C focused witness'
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

const displayedChainPrerequisiteCoreName = (
    backendName: 'Functord_cat' | 'Terminal_cat'
): string => {
    const entry =
        CORE_CATEGORICAL_DISPLAYED_CHAIN_PREREQUISITE_LINKAGE.entries.find(
            candidate =>
                candidate.kind === 'free-declaration' &&
                candidate.backendName === backendName
        );
    if (entry === undefined || entry.kind !== 'free-declaration') {
        throw new Error(
            `Missing displayed-chain prerequisite ${backendName}`
        );
    }
    return entry.coreName;
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

const terminalCategory = (): KernelExpression => kernelFree(
    displayedChainPrerequisiteCoreName('Terminal_cat'),
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

const displayedFunctorCategory = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => call(
    displayedChainPrerequisiteCoreName('Functord_cat'),
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]
);

const transforCategory = (
    source: KernelExpression,
    target: KernelExpression,
    left: KernelExpression,
    right: KernelExpression
): KernelExpression => kernelApplication(
    'transfor-category',
    [
        { value: source },
        { value: target },
        { value: left },
        { value: right }
    ],
    nodeProvenance
);

const homCategory = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression
): KernelExpression => kernelApplication(
    'hom-category',
    [{ value: base }, { value: source }, { value: target }],
    nodeProvenance
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

const constantFamily = (
    base: KernelExpression,
    value: KernelExpression
): KernelExpression => kernelApplication(
    'constant-displayed-family',
    [{ value: base }, { value }],
    nodeProvenance
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

const pointFunctor = (
    target: KernelExpression,
    point: KernelExpression
): KernelExpression => call(
    CORE_CATEGORICAL_FIBRED_WEAKEN_REINDEX_CORE_NAMES.pointFunctor,
    [
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: point }
    ]
);

const identity = (
    base: KernelExpression,
    object: KernelExpression
): KernelExpression => call(
    CORE_CATEGORICAL_DISPLAYED_ND_HIGHER_FOUNDATION_CORE_NAMES
        .identityArrow,
    [
        { plicity: 'explicit', value: base },
        { plicity: 'explicit', value: object }
    ]
);

const sigmaPair = (
    base: KernelExpression,
    family: KernelExpression,
    first: KernelExpression,
    second: KernelExpression
): KernelExpression => {
    const point = kernelBound(0, nodeProvenance);
    const familyClassifier = kernelLambda(
        kernelBinder(
            'pairPoint',
            objectType(base),
            binderMode('explicit', 'functorial'),
            nodeProvenance
        ),
        objectClassifier(fibre(base, family, point)),
        nodeProvenance
    );
    return call(
        CORE_DIRECTED_1B_PRIMITIVE_NAMES['dependent-pair'],
        [
            {
                plicity: 'implicit',
                value: objectClassifier(base)
            },
            { plicity: 'implicit', value: familyClassifier },
            { plicity: 'explicit', value: first },
            { plicity: 'explicit', value: second }
        ]
    );
};

const representable = (
    base: KernelExpression,
    source: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.representableFamily,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]
);

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

const pathoutObject = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression,
    arrow: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutObject,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target },
        { plicity: 'explicit', value: arrow }
    ]
);

const pathoutReflexiveObject = (
    base: KernelExpression,
    source: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutReflexiveObject,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]
);

const pathoutReflexiveArrow = (
    base: KernelExpression,
    source: KernelExpression,
    target: KernelExpression,
    arrow: KernelExpression
): KernelExpression => call(
    CORE_PATHOUT_FOUNDATION_1B_CORE_NAMES.pathoutReflexiveArrow,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target },
        { plicity: 'explicit', value: arrow }
    ]
);

const fibreCovariantTarget = (
    base: KernelExpression,
    family: KernelExpression
): KernelExpression => call(
    corePathindFixedSource1cCoreName('fibreCovariantTarget'),
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family }
    ]
);

const fibreCovariantTransformation = (
    base: KernelExpression,
    family: KernelExpression,
    source: KernelExpression,
    datum: KernelExpression
): KernelExpression => call(
    corePathindFixedSource1cCoreName('fibreCovariantTransformation'),
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: datum }
    ]
);

const fibreCovariantAction = (
    base: KernelExpression,
    family: KernelExpression,
    source: KernelExpression,
    target: KernelExpression,
    datum: KernelExpression
): KernelExpression => call(
    CORE_CATEGORICAL_MIXED_ACTION_CORE_NAMES.covariantFibreAction,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: family },
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: datum }
    ]
);

const pathInductionSection = (
    base: KernelExpression,
    source: KernelExpression,
    motive: KernelExpression,
    datum: KernelExpression
): KernelExpression => call(
    corePathindFixedSource1cCoreName('pathInductionSection'),
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: motive },
        { plicity: 'explicit', value: datum }
    ]
);

const pathInductionComponentFunctor = (
    base: KernelExpression,
    source: KernelExpression,
    motive: KernelExpression
): KernelExpression => call(
    corePathindFixedSource1cCoreName(
        'pathInductionComponentFunctor'
    ),
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: motive }
    ]
);

const pathoutReflexiveArrowSection = (
    base: KernelExpression,
    source: KernelExpression
): KernelExpression => call(
    corePathindFixedSource1cCoreName('pathoutReflexiveArrowSection'),
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: source }
    ]
);

const sigmaProjectionPullback = (
    base: KernelExpression,
    sourceFamily: KernelExpression,
    targetFamily: KernelExpression
): KernelExpression => call(
    CORE_CATEGORICAL_FIBRED_BINDER_CORE_NAMES.sigmaProjectionPullback,
    [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: sourceFamily },
        { plicity: 'explicit', value: targetFamily }
    ]
);

interface PathindFixture {
    readonly environment: CoreLfDeclarationEnvironment;
    readonly runtime: ReturnType<
        typeof compileCorePathindFixedSource1cTransfer
    >['composedRuntime'];
    readonly Z: KernelExpression;
    readonly W: KernelExpression;
    readonly x: KernelExpression;
    readonly y: KernelExpression;
    readonly w: KernelExpression;
    readonly p: KernelExpression;
    readonly E: KernelExpression;
    readonly D: KernelExpression;
    readonly Ew: KernelExpression;
    readonly u: KernelExpression;
    readonly v: KernelExpression;
    readonly uD: KernelExpression;
    readonly uw: KernelExpression;
}

let cachedFixture: PathindFixture | undefined;

const fixture = (): PathindFixture => {
    if (cachedFixture !== undefined) return cachedFixture;
    const compilation = compileCorePathindFixedSource1cTransfer();
    let environment = compilation.compiled.environment;
    const add = (name: string, type: KernelExpression): KernelExpression => {
        const declaration = {
            name,
            type,
            mode: binderMode('explicit', 'functorial'),
            provenance: nodeProvenance,
            transparency: 'opaque' as const
        };
        environment = environment.extend(declaration);
        return kernelFree(name, nodeProvenance);
    };
    const Z = add('pathind_test_Z', categoryType());
    const W = add('pathind_test_W', categoryType());
    const x = add('pathind_test_x', objectType(Z));
    const y = add('pathind_test_y', objectType(Z));
    const w = add('pathind_test_w', objectType(W));
    const p = add('pathind_test_p', homType(Z, x, y));
    const pathout = pathoutCategory(Z, x);
    const foreignPathout = pathoutCategory(W, w);
    const reflexive = pathoutReflexiveObject(Z, x);
    const point = pathoutObject(Z, x, y, p);
    const foreignReflexive = pathoutReflexiveObject(W, w);
    const E = add('pathind_test_E', displayedFamilyType(pathout));
    const D = add('pathind_test_D', displayedFamilyType(Z));
    const Ew = add(
        'pathind_test_Ew',
        displayedFamilyType(foreignPathout)
    );
    const u = add('pathind_test_u', objectType(fibre(
        pathout,
        E,
        reflexive
    )));
    const v = add('pathind_test_v', objectType(fibre(
        pathout,
        E,
        point
    )));
    const uD = add('pathind_test_uD', objectType(fibre(Z, D, x)));
    const uw = add('pathind_test_uw', objectType(fibre(
        foreignPathout,
        Ew,
        foreignReflexive
    )));
    cachedFixture = Object.freeze({
        environment,
        runtime: compilation.composedRuntime,
        Z,
        W,
        x,
        y,
        w,
        p,
        E,
        D,
        Ew,
        u,
        v,
        uD,
        uw
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
        8192,
        undefined,
        witness.runtime
    );
    const diagnostic = result.status === 'not-equal'
        ? [
            `mismatch=${result.mismatch.code}@` +
                result.mismatch.path.join('.'),
            `left=${serializeKernelExpression(result.normalizedLeft)}`,
            `right=${serializeKernelExpression(result.normalizedRight)}`,
            `rules=${result.trace
                .flatMap(entry => entry.reduction.kind === 'runtime'
                    ? [entry.reduction.ruleId]
                    : [])
                .join(',')}`
        ].join('; ')
        : `status=${result.status}`;
    assert.equal(
        result.status,
        'equal',
        `Expected definitional equality, ${diagnostic}`
    );
};

const infer = (term: KernelExpression) => {
    const witness = fixture();
    const checker = createCoreLfChecker(
        witness.environment,
        8192,
        witness.runtime
    );
    return checker.infer(checker.rootContext, term);
};

describe('PATHIND-TRUSTED-PROFILE-1C transfer', () => {
    it('seals the reviewed exact 5/12/0/6 root-only boundary', () => {
        assert.deepEqual(
            CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                .trustedDeclarationNames,
            [
                'fib_cov_int',
                'fib_cov_src_func',
                'fib_cov_transf',
                'path_ind_sec',
                'path_ind_func_fapp0'
            ]
        );
        assert.deepEqual(
            CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY.runtimeRuleIds,
            [
                'pathind.fixed-source.contravariant-representable-object',
                'pathind.fixed-source.displayed-functor-object',
                'pathind.fixed-source.displayed-hom-object-fusion',
                'pathind.fixed-source.transfor-classifier-delta',
                'pathind.fixed-source.fib-cov-target-section-fusion',
                'pathind.fixed-source.' +
                    'fixed-evaluation-post-delta-presentation-fusion',
                'pathind.fixed-source.fib-cov-package-component',
                'pathind.fixed-source.fib-cov-component-object',
                'pathind.fixed-source.fib-cov-section-point',
                'pathind.fixed-source.path-ind-section-object-action',
                'pathind.fixed-source.path-ind-point-computation',
                'pathind.fixed-source.' +
                    'path-ind-sigma-pullback-computation'
            ]
        );
        assert.deepEqual(
            CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                .transparentDefinitionNames,
            [
                'FibCov_target_catd',
                'pathout_refl_eval_func',
                'pathout_refl_eval_base_func',
                'pathout_refl_arrow_sec',
                'PathInd_src_catd',
                'PathInd_tgt_catd'
            ]
        );
        assert.deepEqual(
            [
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .trustedDeclarationCount,
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .runtimeRuleCount,
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .proofRuleCount,
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .transparentDefinitionCount,
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .typedLibraryConsumerCount,
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .negativeConsumerCount,
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .selectedRuntimeObservationCount,
                CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                    .boundedOracleAssertionCount
            ],
            [5, 12, 0, 6, 1, 8, 5, 9]
        );
        assert.equal(
            CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                .reviewedAuthorization,
            'PATHIND-TRUSTED-PROFILE-1C-REVIEWED-8'
        );
        assert.equal(
            CORE_PATHIND_FIXED_SOURCE_1C_TRANSFER_BOUNDARY
                .browserOrPublicPackageExported,
            false
        );
    });

    it('compiles every entry through the generic transfer engines', () => {
        const compilation = compileCorePathindFixedSource1cTransfer();
        assert.deepEqual(
            [
                compilation.fibreTargetCompiled.declarations.length,
                compilation.trustedCompiled.declarations.length,
                compilation.libraryCompiled.declarations.length,
                compilation.runtime.rules.length
            ],
            [1, 5, 5, 12]
        );
        assert.equal(
            compilation.runtime.rules.every(rule =>
                rule.subjectValidation.kind === 'typescript-checked'
            ),
            true
        );
        assert.deepEqual(
            CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_POLICY.entries.map(
                entry => entry.policy
            ),
            ['checked-transparent-definition']
        );
        assert.equal(
            CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_POLICY.entries.every(
                entry => entry.policy === 'opaque-signature'
            ),
            true
        );
        assert.equal(
            CORE_PATHIND_FIXED_SOURCE_1C_RUNTIME_POLICY.entries.every(
                entry => entry.policy === 'runtime-rewrite'
            ),
            true
        );
        assert.equal(
            CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_POLICY.entries.every(
                entry => entry.policy ===
                    'checked-transparent-definition'
            ),
            true
        );
        assert.deepEqual(
            [
                CORE_PATHIND_FIXED_SOURCE_1C_FIBRE_TARGET_MODULE
                    .proofRules.length,
                CORE_PATHIND_FIXED_SOURCE_1C_TRUSTED_MODULE
                    .proofRules.length,
                CORE_PATHIND_FIXED_SOURCE_1C_RUNTIME_MODULE
                    .proofRules.length,
                CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_MODULE
                    .proofRules.length
            ],
            [0, 0, 0, 0]
        );
    });

    it('projects displayed-functor objects to transfor objects', () => {
        const witness = fixture();
        assertDefinitionallyEqual(
            objectType(displayedFunctorCategory(
                witness.Z,
                witness.D,
                witness.D
            )),
            objectType(transforCategory(
                witness.Z,
                categoryOfCategories(),
                witness.D,
                witness.D
            )),
            witness
        );
    });

    it('computes FibCov target objects as Hom(Catd(Z),Rep(x),D) objects',
        () => {
            const witness = fixture();
            assertDefinitionallyEqual(
                objectType(fibre(
                    witness.Z,
                    fibreCovariantTarget(witness.Z, witness.D),
                    witness.x
                )),
                objectType(homCategory(
                    displayedCategory(witness.Z),
                    representable(witness.Z, witness.x),
                    witness.D
                )),
                witness
            );
        });

    it('computes the PathInd component object to path_ind_sec', () => {
        const witness = fixture();
        const pathout = pathoutCategory(witness.Z, witness.x);
        const reflexive = pathoutReflexiveObject(witness.Z, witness.x);
        assertDefinitionallyEqual(
            functorObject(
                fibre(pathout, witness.E, reflexive),
                sectionCategory(pathout, witness.E),
                pathInductionComponentFunctor(
                    witness.Z,
                    witness.x,
                    witness.E
                ),
                witness.u
            ),
            pathInductionSection(
                witness.Z,
                witness.x,
                witness.E,
                witness.u
            ),
            witness
        );
    });

    it('computes a PathInd section point by transport along rho', () => {
        const witness = fixture();
        const pathout = pathoutCategory(witness.Z, witness.x);
        const reflexive = pathoutReflexiveObject(witness.Z, witness.x);
        const point = pathoutObject(
            witness.Z,
            witness.x,
            witness.y,
            witness.p
        );
        const literalPoint = sigmaPair(
            witness.Z,
            representable(witness.Z, witness.x),
            witness.y,
            witness.p
        );
        const rho = pathoutReflexiveArrow(
            witness.Z,
            witness.x,
            witness.y,
            witness.p
        );
        const targetFibre = fibre(pathout, witness.E, point);
        const transported = functorObject(
            homCategory(pathout, reflexive, point),
            targetFibre,
            fibreCovariantAction(
                pathout,
                witness.E,
                reflexive,
                point,
                witness.u
            ),
            rho
        );
        const reduced = witness.runtime.rewriteHead(component(
            pathout,
            constantFamily(pathout, terminalCategory()),
            witness.E,
            literalPoint,
            pathInductionSection(
                witness.Z,
                witness.x,
                witness.E,
                witness.u
            )
        ));
        assert.equal(reduced.status, 'rewritten');
        if (reduced.status !== 'rewritten') {
            assert.fail('The fixed-source point rule did not fire');
        }
        assert.equal(
            reduced.ruleId,
            'pathind.fixed-source.path-ind-point-computation'
        );
        assert.equal(
            kernelExpressionEquals(
                reduced.after,
                pointFunctor(targetFibre, transported)
            ),
            true
        );
    });

    it('folds the Sigma-pullback motive to fib_cov_transf', () => {
        const witness = fixture();
        assertDefinitionallyEqual(
            pathInductionSection(
                witness.Z,
                witness.x,
                sigmaProjectionPullback(
                    witness.Z,
                    representable(witness.Z, witness.x),
                    witness.D
                ),
                witness.uD
            ),
            fibreCovariantTransformation(
                witness.Z,
                witness.D,
                witness.x,
                witness.uD
            ),
            witness
        );
    });

    it('types the rho-section consumer and exposes transport along rho',
        () => {
            const witness = fixture();
            const pathout = pathoutCategory(witness.Z, witness.x);
            const reflexive = pathoutReflexiveObject(witness.Z, witness.x);
            const point = pathoutObject(
                witness.Z,
                witness.x,
                witness.y,
                witness.p
            );
            const literalPoint = sigmaPair(
                witness.Z,
                representable(witness.Z, witness.x),
                witness.y,
                witness.p
            );
            const rho = pathoutReflexiveArrow(
                witness.Z,
                witness.x,
                witness.y,
                witness.p
            );
            const motive = representable(pathout, reflexive);
            const section = pathoutReflexiveArrowSection(
                witness.Z,
                witness.x
            );
            const expandedSection = pathInductionSection(
                witness.Z,
                witness.x,
                motive,
                identity(pathout, reflexive)
            );
            const expectedType = objectType(sectionCategory(
                pathout,
                motive
            ));
            const checker = createCoreLfChecker(
                witness.environment,
                8192,
                witness.runtime
            );
            const checked = checker.check(
                checker.rootContext,
                section,
                expectedType
            );
            assertDefinitionallyEqual(checked.type, expectedType, witness);
            assertDefinitionallyEqual(
                section,
                expandedSection,
                witness
            );
            const reduced = witness.runtime.rewriteHead(component(
                pathout,
                constantFamily(pathout, terminalCategory()),
                motive,
                literalPoint,
                expandedSection
            ));
            assert.equal(reduced.status, 'rewritten');
            if (reduced.status !== 'rewritten') {
                assert.fail('The expanded rho-section point did not fire');
            }
            assert.equal(
                reduced.ruleId,
                'pathind.fixed-source.path-ind-point-computation'
            );
            const targetFibre = fibre(pathout, motive, point);
            const transported = functorObject(
                homCategory(pathout, reflexive, point),
                targetFibre,
                fibreCovariantAction(
                    pathout,
                    motive,
                    reflexive,
                    point,
                    identity(pathout, reflexive)
                ),
                rho
            );
            assert.equal(
                kernelExpressionEquals(
                    reduced.after,
                    pointFunctor(targetFibre, transported)
                ),
                true
            );
            const runtimeOnlyRho = coreLfDefinitionalCompare(
                witness.environment,
                reduced.after,
                pointFunctor(
                    homCategory(pathout, reflexive, point),
                    rho
                ),
                8192,
                undefined,
                witness.runtime
            );
            assert.equal(runtimeOnlyRho.status, 'not-equal');
        });

    it('rejects a source object from the wrong PathOut category', () => {
        const witness = fixture();
        assert.throws(() => infer(pathInductionSection(
            witness.Z,
            witness.w,
            witness.Ew,
            witness.uw
        )));
    });

    it('rejects a motive over the wrong PathOut base', () => {
        const witness = fixture();
        assert.throws(() => infer(pathInductionSection(
            witness.Z,
            witness.x,
            witness.Ew,
            witness.uw
        )));
    });

    it('rejects a datum from a non-reflexive fibre', () => {
        const witness = fixture();
        assert.throws(() => infer(pathInductionSection(
            witness.Z,
            witness.x,
            witness.E,
            witness.v
        )));
    });

    it('rejects section evaluation at a foreign PathOut object', () => {
        const witness = fixture();
        const pathout = pathoutCategory(witness.Z, witness.x);
        assert.throws(() => infer(component(
            pathout,
            constantFamily(pathout, terminalCategory()),
            witness.E,
            pathoutReflexiveObject(witness.W, witness.w),
            pathInductionSection(
                witness.Z,
                witness.x,
                witness.E,
                witness.u
            )
        )));
    });

    it('rejects a Sigma-pullback motive at the wrong representable',
        () => {
            const witness = fixture();
            assert.throws(() => infer(pathInductionSection(
                witness.Z,
                witness.x,
                sigmaProjectionPullback(
                    witness.Z,
                    representable(witness.Z, witness.y),
                    witness.D
                ),
                witness.uD
            )));
        });

    it('rejects a foreign scoped source term', () => {
        const witness = fixture();
        assert.throws(() => infer(pathInductionSection(
            witness.Z,
            kernelBound(0, nodeProvenance),
            witness.E,
            witness.u
        )));
    });

    it('rejects runtime-rule authority from ordinary library code', () => {
        assert.throws(
            () => assertCorePathindOrdinaryLibraryCapability(
                'runtime-rewrite'
            ),
            CorePathindOrdinaryLibraryCapabilityError
        );
    });

    it('rejects opaque authority from ordinary library code', () => {
        assert.throws(
            () => assertCorePathindOrdinaryLibraryCapability(
                'opaque-signature'
            ),
            CorePathindOrdinaryLibraryCapabilityError
        );
        assert.equal(
            assertCorePathindOrdinaryLibraryCapability(
                'checked-transparent-definition'
            ),
            'checked-transparent-definition'
        );
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
                /pathind_fixed_source_transfer/u,
                relative
            );
        }
        assert.equal(
            CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_MODULE
                .runtimeRules.length,
            0
        );
        assert.equal(
            CORE_PATHIND_FIXED_SOURCE_1C_LIBRARY_MODULE
                .proofRules.length,
            0
        );
    });

    it(
        'matches all nine bounded active-Lambdapi assertions',
        {
            skip:
                process.env.EMDASH_RUN_LAMBDAPI_PATHIND_FIXED_PROBES !==
                '1'
        },
        () => {
            const source = [
                'require open emdash.emdash3_2;',
                'assert [K : Cat] (E D : τ (Catd K)) ⊢',
                '  Obj (@Functord_cat K E D)',
                '    ≡ Obj (@Transf_cat K Cat_cat E D);',
                'assert [K : Cat] (E : τ (Catd K))',
                '  (x : τ (Obj K)) ⊢',
                '  Fibre_cat (@FibCov_target_catd K E) x',
                '    ≡ @Hom_cat (@Catd_cat K) (@Rep_catd K x) E;',
                'assert [K : Cat] (E : τ (Catd K)) ⊢',
                '  @FibCov_target_catd K E',
                '    ≡ @hom_con',
                '        (@Catd_cat K)',
                '        E',
                '        (Op_cat K)',
                '        (@hom_int K K (@id_func K));',
                'assert [K : Cat] (E : τ (Catd K))',
                '  (x : τ (Obj K)) ⊢',
                '  @tapp0_fapp0 K Cat_cat E',
                '    (@FibCov_target_catd K E) x (@fib_cov_int K E)',
                '    ≡ @fib_cov_src_func K E x;',
                'assert [K : Cat] (E : τ (Catd K))',
                '  (x : τ (Obj K))',
                '  (u : τ (Obj (Fibre_cat E x))) ⊢',
                '  fapp0 (@fib_cov_src_func K E x) u',
                '    ≡ @fib_cov_transf K E x u;',
                'assert [K : Cat] (E : τ (Catd K))',
                '  (x y : τ (Obj K))',
                '  (u : τ (Obj (Fibre_cat E x))) ⊢',
                '  @tapp0_fapp0 K Cat_cat',
                '    (@Rep_catd K x) E y (@fib_cov_transf K E x u)',
                '    ≡ @fib_cov_tapp0_func K E x y u;',
                'assert [Z : Cat] (x : τ (Obj Z))',
                '  (E : τ (Catd (@PathOut_cat Z x)))',
                '  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x)))) ⊢',
                '  @fapp0',
                '    (Fibre_cat E (@pathout_refl_obj Z x))',
                '    (Pi_cat E)',
                '    (@path_ind_func_fapp0 Z x E)',
                '    u',
                '    ≡ @path_ind_sec Z x E u;',
                'assert [Z : Cat] (D : τ (Catd Z))',
                '  (x : τ (Obj Z))',
                '  (u : τ (Obj (Fibre_cat D x))) ⊢',
                '  @path_ind_sec Z x',
                '    (@Sigma_proj1_pullback_catd Z (@Rep_catd Z x) D)',
                '    u',
                '    ≡ @fib_cov_transf Z D x u;',
                'assert [Z : Cat] (x y : τ (Obj Z))',
                '  (p : τ (Hom Z x y)) ⊢',
                '  @piapp0',
                '    (@PathOut_cat Z x)',
                '    (@Rep_catd',
                '      (@PathOut_cat Z x)',
                '      (@pathout_refl_obj Z x))',
                '    (@pathout_refl_arrow_sec Z x)',
                '    (@pathout_obj Z x y p)',
                '    ≡ @pathout_refl_arrow Z x y p;'
            ].join('\n');
            const result = checkLambdapiProbe(
                { source: `${source}\n`, sourceMap: [] },
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
