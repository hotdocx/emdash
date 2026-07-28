/**
 * FIBRED-BINDER-1 transfer closure for direct displayed-functor abstraction.
 *
 * The exact SCALE-STRESS-2A Catd/Sigma-projection declarations and
 * Sigma/Pi proof rule are compiled unchanged on top of FIBRED-STRUCTURE-1A.
 * This promotes no new mathematical declaration or rule: it reuses the
 * already-active authority in the first root-only usability consumer.
 */

import {
    CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT,
    validateCoreCategoricalFibredBinderContract
} from './categorical_fibred_binder_contract';
import {
    CoreCategoricalFibredStructureCompilation,
    CORE_CATEGORICAL_FIBRED_STRUCTURE_SOURCE_SHA256,
    compileCoreCategoricalFibredStructureTransfer
} from './categorical_fibred_structure_transfer';
import {
    CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS
} from './categorical_dependent_composition_transfer';
import {
    CORE_DIRECTED_1A_PRIMITIVE_NAMES
} from './directed_1a';
import {
    coreDirectedContinuationTransferSymbol
} from './directed_continuation_transfer';
import {
    KernelExpression,
    Provenance,
    kernelApplication,
    kernelCall,
    kernelFree
} from './kernel';
import {
    CoreLfDeclarationEnvironment
} from './lf_declarations';
import {
    CoreLfModuleSpec,
    CoreLfTransferBuilderExpression,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferRuntimeRule,
    CoreLfTransferScopedBuilder,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    CoreLfCompiledDeclarationModule
} from './lf_transfer_compiler';
import {
    CoreLfCompiledMixedModule,
    CoreLfMixedProofPhase,
    compileCoreLfMixedPhases
} from './lf_transfer_mixed';
import {
    CoreLfCompiledProofProgram,
    CoreLfComposedProofProgram,
    compileCoreLfProofProgram
} from './lf_transfer_proof';
import {
    CoreLfCompiledRuntimeFragment,
    CoreLfCompiledRuntimeProgram,
    CoreLfComposedRuntimeProgram,
    compileCoreLfRuntimeFragment
} from './lf_transfer_runtime';
import {
    CORE_LF_SCALE_STRESS_2A_LINKAGE,
    CORE_LF_SCALE_STRESS_2A_MODULE,
    CORE_LF_SCALE_STRESS_2A_PLAN
} from './scale_stress_2_representation';

export const CORE_CATEGORICAL_FIBRED_BINDER_TRANSFER_REVISION =
    'FIBRED-BINDER-1-EXISTING-SIGMA-PI-CLOSURE-1' as const;

const MODULE_ID = 'emdash.emdash3_2';

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const decodeOwner =
    coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const functorClassifier =
    coreDirectedContinuationTransferSymbol('functor-classifier');
const categoryOfCategories =
    coreDirectedContinuationTransferSymbol(
        'category-of-categories'
    );
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-category-category'
    );
const displayedFunctorCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-functor-category'
    );
const functorObject =
    coreDirectedContinuationTransferSymbol('functor-object');
const transforComponentCapped =
    coreDirectedContinuationTransferSymbol(
        'transfor-component-capped'
    );
const {
    genericComposition
} = CORE_CATEGORICAL_DEPENDENT_COMPOSITION_SYMBOLS;

interface BuilderArgument {
    readonly plicity: 'explicit' | 'implicit';
    readonly value: CoreLfTransferBuilderExpression;
}

const call = (
    builder: CoreLfTransferScopedBuilder,
    callee: CoreLfTransferBuilderExpression,
    arguments_: readonly BuilderArgument[]
): CoreLfTransferBuilderExpression =>
    builder.call(callee, arguments_);

const globalCall = (
    builder: CoreLfTransferScopedBuilder,
    symbol: Parameters<CoreLfTransferScopedBuilder['global']>[0],
    arguments_: readonly BuilderArgument[]
): CoreLfTransferBuilderExpression =>
    call(builder, builder.global(symbol), arguments_);

const decode = (
    builder: CoreLfTransferScopedBuilder,
    classifier: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, decodeOwner, [{
        plicity: 'explicit',
        value: classifier
    }]);

const objectType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, objectClassifier, [{
        plicity: 'explicit',
        value: base
    }]));

const functorType = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, globalCall(builder, functorClassifier, [
        { plicity: 'explicit', value: source },
        { plicity: 'explicit', value: target }
    ]));

const displayedCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedCategoryCategory, [
        { plicity: 'explicit', value: base }
    ]);

const displayedFamilyType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    objectType(builder, displayedCategoryAt(builder, base));

const displayedFunctorType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    sourceFamily: CoreLfTransferBuilderExpression,
    targetFamily: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    objectType(
        builder,
        globalCall(builder, displayedFunctorCategory, [
            { plicity: 'implicit', value: base },
            { plicity: 'explicit', value: sourceFamily },
            { plicity: 'explicit', value: targetFamily }
        ])
    );

const fapp0At = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    functor: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, functorObject, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: functor },
        { plicity: 'explicit', value: object }
    ]);

const tapp0At = (
    builder: CoreLfTransferScopedBuilder,
    source: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    sourceFunctor: CoreLfTransferBuilderExpression,
    targetFunctor: CoreLfTransferBuilderExpression,
    object: CoreLfTransferBuilderExpression,
    transfor: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, transforComponentCapped, [
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: target },
        { plicity: 'implicit', value: sourceFunctor },
        { plicity: 'implicit', value: targetFunctor },
        { plicity: 'explicit', value: object },
        { plicity: 'explicit', value: transfor }
    ]);

const composeAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    source: CoreLfTransferBuilderExpression,
    middle: CoreLfTransferBuilderExpression,
    target: CoreLfTransferBuilderExpression,
    outer: CoreLfTransferBuilderExpression,
    inner: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, genericComposition, [
        { plicity: 'implicit', value: base },
        { plicity: 'implicit', value: source },
        { plicity: 'implicit', value: middle },
        { plicity: 'implicit', value: target },
        { plicity: 'explicit', value: outer },
        { plicity: 'explicit', value: inner }
    ]);

const componentCompositionRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const E = builder.capture('E');
    const D = builder.capture('D');
    const C = builder.capture('C');
    const x = builder.capture('x');
    const FF = builder.capture('FF');
    const GG = builder.capture('GG');
    const cat = builder.global(categoryOfCategories);
    const catd = displayedCategoryAt(builder, K);
    const Ex = fapp0At(builder, K, cat, E, x);
    const Dx = fapp0At(builder, K, cat, D, x);
    const Cx = fapp0At(builder, K, cat, C, x);
    return {
        order: 0,
        id: 'categorical.displayed-functor-composition.point',
        groupId: 'categorical.displayed-functor-composition',
        clauseOrder: 0,
        sourceOwner: transforComponentCapped,
        variables: [
            {
                name: 'K',
                type: builder.template(builder.global(category))
            },
            {
                name: 'E',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'D',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'C',
                type: builder.template(displayedFamilyType(builder, K))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, K))
            },
            {
                name: 'FF',
                type: builder.template(
                    displayedFunctorType(builder, K, D, C)
                )
            },
            {
                name: 'GG',
                type: builder.template(
                    displayedFunctorType(builder, K, E, D)
                )
            }
        ],
        left: builder.pattern(tapp0At(
            builder,
            K,
            cat,
            E,
            C,
            x,
            composeAt(
                builder,
                catd,
                E,
                D,
                C,
                FF,
                GG
            )
        )),
        right: builder.template(composeAt(
            builder,
            cat,
            Ex,
            Dx,
            Cx,
            tapp0At(builder, K, cat, D, C, x, FF),
            tapp0At(builder, K, cat, E, D, x, GG)
        )),
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            sourceFragment:
                'rule @tapp0_fapp0 $K Cat_cat $E $C $x ' +
                '(@comp_fapp0 (@Catd_cat $K) $E $D $C $FF $GG)'
        }
    };
};

const functorCompositionObjectRule =
(): CoreLfTransferRuntimeRule => {
    const builder = new CoreLfTransferScopedBuilder();
    const A = builder.capture('A');
    const B = builder.capture('B');
    const C = builder.capture('C');
    const F = builder.capture('F');
    const G = builder.capture('G');
    const x = builder.capture('x');
    const cat = builder.global(categoryOfCategories);
    return {
        order: 1,
        id: 'categorical.functor-composition.object',
        groupId: 'categorical.functor-composition',
        clauseOrder: 0,
        sourceOwner: functorObject,
        variables: [
            {
                name: 'A',
                type: builder.template(builder.global(category))
            },
            {
                name: 'B',
                type: builder.template(builder.global(category))
            },
            {
                name: 'C',
                type: builder.template(builder.global(category))
            },
            {
                name: 'F',
                type: builder.template(functorType(builder, B, C))
            },
            {
                name: 'G',
                type: builder.template(functorType(builder, A, B))
            },
            {
                name: 'x',
                type: builder.template(objectType(builder, A))
            }
        ],
        left: builder.pattern(fapp0At(
            builder,
            A,
            C,
            composeAt(builder, cat, A, B, C, F, G),
            x
        )),
        right: builder.template(fapp0At(
            builder,
            B,
            C,
            F,
            fapp0At(builder, A, B, G, x)
        )),
        provenance: {
            authorityPath: 'emdash2/emdash3_2.lp',
            sourceFragment:
                'rule @fapp0 $A $C ' +
                '(@comp_fapp0 Cat_cat $A $B $C $F $G) $x'
        }
    };
};

const binderRuntimeRules = Object.freeze([
    componentCompositionRule(),
    functorCompositionObjectRule()
]);

export const CORE_CATEGORICAL_FIBRED_BINDER_RUNTIME_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision:
        'FIBRED-BINDER-1-EXISTING-POINTWISE-COMPOSITION-RUNTIME-1',
    moduleId: MODULE_ID,
    fragmentId: 'fibred-binder-1-pointwise-composition-runtime',
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceSha256:
        CORE_CATEGORICAL_FIBRED_STRUCTURE_SOURCE_SHA256,
    dependencies: [],
    externalSymbols: [
        category,
        decodeOwner,
        objectClassifier,
        functorClassifier,
        categoryOfCategories,
        displayedCategoryCategory,
        displayedFunctorCategory,
        functorObject,
        transforComponentCapped,
        genericComposition
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: [],
    inductives: [],
    runtimeRules: binderRuntimeRules,
    proofRules: []
});

export const CORE_CATEGORICAL_FIBRED_BINDER_RUNTIME_POLICY:
CoreLfTransferPolicyOverlay = createCoreLfTransferPolicyOverlay(
    CORE_CATEGORICAL_FIBRED_BINDER_RUNTIME_MODULE,
    {
        revision:
            'FIBRED-BINDER-1-EXISTING-POINTWISE-' +
            'COMPOSITION-RUNTIME-POLICY-1',
        moduleRevision:
            CORE_CATEGORICAL_FIBRED_BINDER_RUNTIME_MODULE.revision,
        entries: binderRuntimeRules.map((rule, order) => ({
            order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence:
                'Exact active pointwise composition computation required ' +
                'by the displayed composition consumer'
        }))
    }
);

const sigmaProjectionPullback =
    CORE_LF_SCALE_STRESS_2A_MODULE.declarations[1].symbol;

const localCoreName = (
    symbol: typeof sigmaProjectionPullback
): string => {
    const link = CORE_LF_SCALE_STRESS_2A_LINKAGE.entries.find(
        candidate =>
            candidate.symbol.moduleId === symbol.moduleId &&
            candidate.symbol.name === symbol.name
    );
    if (link === undefined || link.kind !== 'free-declaration') {
        throw new Error(
            `FIBRED-BINDER-1 has no free Core link for ` +
            `${symbol.moduleId}.${symbol.name}`
        );
    }
    return link.coreName;
};

export const CORE_CATEGORICAL_FIBRED_BINDER_CORE_NAMES =
Object.freeze({
    displayedFamilyClassifier: localCoreName(
        CORE_LF_SCALE_STRESS_2A_MODULE.declarations[0].symbol
    ),
    sigmaProjectionPullback:
        localCoreName(sigmaProjectionPullback)
});

const proofPhase = CORE_LF_SCALE_STRESS_2A_PLAN.phases.find(
    (
        phase
    ): phase is CoreLfMixedProofPhase => phase.kind === 'proof'
);

if (proofPhase === undefined) {
    throw new Error(
        'FIBRED-BINDER-1 lost the SCALE-STRESS-2A proof phase'
    );
}

export interface CoreCategoricalFibredBinderClassifiers {
    readonly direct: KernelExpression;
    readonly nested: KernelExpression;
}

/**
 * Construct both stable classifier presentations without identifying them.
 */
export function coreCategoricalFibredBinderClassifiers(
    base: KernelExpression,
    sourceFamily: KernelExpression,
    targetFamily: KernelExpression,
    nodeProvenance: Provenance
): CoreCategoricalFibredBinderClassifiers {
    const sigma = kernelCall(
        kernelFree(
            CORE_DIRECTED_1A_PRIMITIVE_NAMES['sigma-category'],
            nodeProvenance
        ),
        [
            { plicity: 'implicit', value: base },
            { plicity: 'explicit', value: sourceFamily }
        ],
        nodeProvenance
    );
    const pullback = kernelCall(
        kernelFree(
            CORE_CATEGORICAL_FIBRED_BINDER_CORE_NAMES
                .sigmaProjectionPullback,
            nodeProvenance
        ),
        [
            { plicity: 'implicit', value: base },
            { plicity: 'explicit', value: sourceFamily },
            { plicity: 'explicit', value: targetFamily }
        ],
        nodeProvenance
    );
    return Object.freeze({
        direct: kernelCall(
            kernelFree(
                CORE_DIRECTED_1A_PRIMITIVE_NAMES[
                    'displayed-functor-category'
                ],
                nodeProvenance
            ),
            [
                { plicity: 'implicit', value: base },
                { plicity: 'explicit', value: sourceFamily },
                { plicity: 'explicit', value: targetFamily }
            ],
            nodeProvenance
        ),
        nested: kernelApplication(
            'section-category',
            [
                { value: sigma },
                { value: pullback }
            ],
            nodeProvenance
        )
    });
}

export const CORE_CATEGORICAL_FIBRED_BINDER_TRANSFER_BOUNDARY =
Object.freeze({
    status: 'root-only-existing-authority-binder-closure',
    contractRevision:
        CORE_CATEGORICAL_FIBRED_BINDER_CONTRACT.revision,
    reusedRepresentation:
        'SCALE-STRESS-2A-REPRESENTATION-1',
    declarationNames: Object.freeze([
        'Catd',
        'Sigma_proj1_pullback_catd'
    ]),
    proofRuleIds: Object.freeze([
        'stress.sigma-pi.uncurrying'
    ]),
    declarationCount: 2,
    proofRuleCount: 1,
    runtimeRuleCount: 2,
    transferredRuntimeRuleIds: Object.freeze([
        'categorical.displayed-functor-composition.point',
        'categorical.functor-composition.object'
    ]),
    newMathematicalOwnerCount: 0,
    newMathematicalRuntimeRuleCount: 0,
    newMathematicalProofRuleCount: 0,
    proofTimeComparisonInstalled: true,
    runtimeClassifierCollapseInstalled: false,
    doesNotProvide: Object.freeze([
        'new-kernel-owner-or-rule',
        'runtime-Pi-to-Functord-collapse',
        'displayed-transfor-binder',
        'general-dependent-displayed-bracket',
        'browser-profile',
        'bulk-transfer'
    ])
});

export interface CoreCategoricalFibredBinderCompilation {
    readonly prerequisite:
        CoreCategoricalFibredStructureCompilation;
    readonly mixed: CoreLfCompiledMixedModule;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext:
        CoreLfCompiledMixedModule['declarations'];
    readonly proofProgram:
        CoreLfCompiledProofProgram | CoreLfComposedProofProgram;
    readonly runtimeFragment: CoreLfCompiledRuntimeFragment;
    readonly runtime: CoreLfCompiledRuntimeProgram;
    readonly composedRuntime: CoreLfComposedRuntimeProgram;
}

export function compileCoreCategoricalFibredBinderTransfer():
CoreCategoricalFibredBinderCompilation {
    validateCoreCategoricalFibredBinderContract();
    const prerequisite =
        compileCoreCategoricalFibredStructureTransfer();
    const runtimeFragment = compileCoreLfRuntimeFragment(
        CORE_CATEGORICAL_FIBRED_BINDER_RUNTIME_MODULE,
        CORE_CATEGORICAL_FIBRED_BINDER_RUNTIME_POLICY,
        prerequisite.declarationContext,
        {
            dependencies: [{
                relation: 'earlier-fragment',
                fragment: prerequisite.runtimeFragment
            }]
        }
    );
    const mixed = compileCoreLfMixedPhases(
        CORE_LF_SCALE_STRESS_2A_PLAN,
        CORE_LF_SCALE_STRESS_2A_LINKAGE,
        {
            initialDeclarations: prerequisite.declarationContext,
            initialCheckingRuntime: runtimeFragment.runtime
        }
    );
    const declarationPhases = mixed.phases.filter(
        phase => phase.kind === 'declaration'
    );
    const compiled =
        declarationPhases.at(-1)?.declarations;
    const proofProgram = mixed.proofProgram;
    if (compiled === undefined || proofProgram === undefined) {
        throw new Error(
            'FIBRED-BINDER-1 did not compile its declaration/proof closure'
        );
    }
    return Object.freeze({
        prerequisite,
        mixed,
        compiled,
        declarationContext: mixed.declarations,
        proofProgram,
        runtimeFragment,
        runtime: runtimeFragment.localProgram,
        composedRuntime: runtimeFragment.runtime
    });
}

/**
 * Recheck the exact proof rule in a descendant user declaration
 * environment. The qualified authority declarations still come from the
 * immutable transfer context; only user assumptions are added.
 */
export function compileCoreCategoricalFibredBinderProof(
    compilation: CoreCategoricalFibredBinderCompilation,
    environment: CoreLfDeclarationEnvironment
): CoreLfCompiledProofProgram {
    return compileCoreLfProofProgram(
        proofPhase.module,
        proofPhase.policy,
        {
            environment,
            declaration: symbol =>
                compilation.declarationContext.declaration(symbol)
        },
        {
            runtimeProgram: compilation.composedRuntime
        }
    );
}
