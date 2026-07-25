/**
 * Representation-only SCALE-STRESS-2A transfer of the active Sigma/Pi
 * uncurrying comparison.
 *
 * This compiles one isolated proof-time program against the reviewed
 * 29-signature continuation. Generic source-ordered checking aliases let
 * the standalone validator use an earlier generated base equality while
 * checking later dependent generated constraints.
 */

import {
    CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE,
    compileCoreDirectedContinuationTransferWithRuntime,
    coreDirectedContinuationTransferSymbol
} from './directed_continuation_transfer';
import {
    CoreDirected1bRuntimeProgram
} from './directed_1b';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferBuilderExpression,
    CoreLfTransferExpression,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferScopedBuilder,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreLfTransferExplicitBody,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import {
    CoreLfTransferDeclarationLink
} from './lf_transfer_compiler';
import {
    CoreLfCompiledMixedModule,
    CoreLfMixedDeclarationLinkage,
    CoreLfMixedPhasePlan,
    compileCoreLfMixedPhases,
    createCoreLfMixedDeclarationLinkage,
    planCoreLfMixedPhases
} from './lf_transfer_mixed';
import { binderMode } from './kernel';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';
import {
    CORE_LF_SCALE_STRESS_2_UNCURRYING_ACQUISITION
} from './scale_stress_2_acquisition';

const moduleId = 'emdash.emdash3_2';

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const groupoid =
    coreDirectedContinuationTransferSymbol('groupoid-universe');
const decodeOwner =
    coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');
const displayedCategoryCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-category-category'
    );
const sectionCategory =
    coreDirectedContinuationTransferSymbol('section-category');
const sigmaCategory =
    coreDirectedContinuationTransferSymbol('sigma-category');
const displayedFunctorCategory =
    coreDirectedContinuationTransferSymbol(
        'displayed-functor-category'
    );

const displayedFamilyClassifier =
    coreLfQualifiedSymbol(moduleId, 'Catd');
const sigmaProjectionPullback =
    coreLfQualifiedSymbol(moduleId, 'Sigma_proj1_pullback_catd');

const implicitMode = binderMode('implicit', 'functorial');
const explicitMode = binderMode('explicit', 'functorial');

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
    symbol: CoreLfQualifiedSymbol,
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

const displayedFamilies = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, displayedFamilyClassifier, [{
        plicity: 'explicit',
        value: base
    }]);

const source = (
    sourceFragment: string,
    canonicalCommandOrdinal: number
) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment,
    canonicalCommandOrdinal
});

const publicModifiers = (
    rigidity: 'ordinary' | 'constant' | 'injective',
    sourceOpacity: 'transparent' | 'opaque'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity
});

const catdType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        _K => builder.global(groupoid),
        explicitMode
    ));
};

const catdBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'K',
        builder.global(category),
        K => globalCall(builder, objectClassifier, [{
            plicity: 'explicit',
            value: globalCall(
                builder,
                displayedCategoryCategory,
                [{
                    plicity: 'explicit',
                    value: K
                }]
            )
        }]),
        explicitMode
    ));
};

const sigmaProjectionPullbackType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'K',
        builder.global(category),
        K => builder.pi(
            'R',
            decode(builder, displayedFamilies(builder, K)),
            R => builder.pi(
                'D',
                decode(builder, displayedFamilies(builder, K)),
                _D => decode(
                    builder,
                    displayedFamilies(
                        builder,
                        globalCall(builder, sigmaCategory, [
                            {
                                plicity: 'implicit',
                                value: K
                            },
                            {
                                plicity: 'explicit',
                                value: R
                            }
                        ])
                    )
                ),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const sigmaUncurryingProofRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const K = builder.capture('K');
    const R = builder.capture('R');
    const D = builder.capture('D');
    const K2 = builder.capture('K2');
    const R2 = builder.capture('R2');
    const D2 = builder.capture('D2');
    const familyType = (
        base: CoreLfTransferBuilderExpression
    ): CoreLfTransferBuilderExpression =>
        decode(builder, displayedFamilies(builder, base));
    const sigmaTotal = globalCall(builder, sigmaCategory, [
        { plicity: 'implicit', value: K },
        { plicity: 'explicit', value: R }
    ]);
    const pullback = globalCall(
        builder,
        sigmaProjectionPullback,
        [
            { plicity: 'implicit', value: K },
            { plicity: 'explicit', value: R },
            { plicity: 'explicit', value: D }
        ]
    );
    return {
        order: 2,
        id: 'stress.sigma-pi.uncurrying',
        sourceOwner: sectionCategory,
        variables: [
            {
                name: 'K',
                role: 'matched' as const,
                type: builder.template(builder.global(category))
            },
            {
                name: 'R',
                role: 'matched' as const,
                type: builder.template(familyType(K))
            },
            {
                name: 'D',
                role: 'matched' as const,
                type: builder.template(familyType(K))
            },
            {
                name: 'K2',
                role: 'matched' as const,
                type: builder.template(builder.global(category))
            },
            {
                name: 'R2',
                role: 'matched' as const,
                type: builder.template(familyType(K2))
            },
            {
                name: 'D2',
                role: 'matched' as const,
                type: builder.template(familyType(K2))
            }
        ],
        problem: {
            left: builder.pattern(globalCall(
                builder,
                sectionCategory,
                [
                    {
                        plicity: 'implicit',
                        value: sigmaTotal
                    },
                    {
                        plicity: 'explicit',
                        value: pullback
                    }
                ]
            )),
            right: builder.pattern(globalCall(
                builder,
                displayedFunctorCategory,
                [
                    { plicity: 'implicit', value: K2 },
                    { plicity: 'explicit', value: R2 },
                    { plicity: 'explicit', value: D2 }
                ]
            ))
        },
        /*
         * Preserve handwritten source order. The base constraint must be
         * solved before the later family constraints become homogeneous.
         */
        generatedConstraints: [
            {
                left: builder.template(K),
                right: builder.template(K2)
            },
            {
                left: builder.template(R),
                right: builder.template(R2)
            },
            {
                left: builder.template(D),
                right: builder.template(D2)
            }
        ],
        provenance: source(
            'unif_rule @Pi_cat (@Sigma_cat $K $R) ' +
                '(@Sigma_proj1_pullback_catd $K $R $D) ≡ ' +
                "@Functord_cat $K' $R' $D' ↪ " +
                "[ $K ≡ $K'; $R ≡ $R'; $D ≡ $D' ];",
            995
        )
    };
};

export const CORE_LF_SCALE_STRESS_2A_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'SCALE-STRESS-2A-REPRESENTATION-1',
    moduleId,
    fragmentId: 'scale-stress-2a-sigma-pi-uncurrying',
    authorityPath:
        CORE_LF_SCALE_STRESS_2_UNCURRYING_ACQUISITION.authorityPath,
    sourceSha256:
        CORE_LF_SCALE_STRESS_2_UNCURRYING_ACQUISITION.sourceSha256,
    canonicalExport: {
        exporterVersion:
            CORE_LF_SCALE_STRESS_2_UNCURRYING_ACQUISITION
                .canonicalExport.exporterVersion,
        sha256:
            CORE_LF_SCALE_STRESS_2_UNCURRYING_ACQUISITION
                .canonicalExport.sha256
    },
    dependencies: [],
    externalSymbols: [
        category,
        groupoid,
        decodeOwner,
        objectClassifier,
        displayedCategoryCategory,
        sectionCategory,
        sigmaCategory,
        displayedFunctorCategory
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations: [
        {
            order: 0,
            symbol: displayedFamilyClassifier,
            type: catdType(),
            body: coreLfTransferExplicitBody(catdBody()),
            modifiers: publicModifiers('injective', 'transparent'),
            provenance: source(
                'injective symbol Catd (K : Cat) : Grpd ' +
                    '≔ Obj (Catd_cat K);',
                389
            )
        },
        {
            order: 1,
            symbol: sigmaProjectionPullback,
            type: sigmaProjectionPullbackType(),
            body: coreLfTransferAbsentBody(),
            modifiers: publicModifiers('injective', 'opaque'),
            provenance: source(
                'injective symbol Sigma_proj1_pullback_catd ' +
                    '[K : Cat] (R D : τ (Catd K)) : ' +
                    'τ (Catd (@Sigma_cat K R));',
                991
            )
        }
    ],
    inductives: [],
    runtimeRules: [],
    proofRules: [sigmaUncurryingProofRule()]
});

export const CORE_LF_SCALE_STRESS_2A_POLICY:
CoreLfTransferPolicyOverlay =
    createCoreLfTransferPolicyOverlay(
        CORE_LF_SCALE_STRESS_2A_MODULE,
        {
            revision: 'SCALE-STRESS-2A-POLICY-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_2A_MODULE.revision,
            entries: [
                {
                    order: 0,
                    target: {
                        kind: 'declaration',
                        symbol: displayedFamilyClassifier
                    },
                    policy: 'checked-transparent-definition',
                    evidence:
                        'Exact active Catd definition, isolated stress only'
                },
                {
                    order: 1,
                    target: {
                        kind: 'declaration',
                        symbol: sigmaProjectionPullback
                    },
                    policy: 'opaque-signature',
                    evidence:
                        'Exact active stable owner, isolated stress only'
                },
                {
                    order: 2,
                    target: {
                        kind: 'proof-rule',
                        id: 'stress.sigma-pi.uncurrying'
                    },
                    policy: 'proof-unification',
                    evidence:
                        'Exact active proof rule in an unregistered ' +
                        'qualification program'
                }
            ]
        }
    );

export const CORE_LF_SCALE_STRESS_2A_PLAN:
CoreLfMixedPhasePlan = planCoreLfMixedPhases(
    CORE_LF_SCALE_STRESS_2A_MODULE,
    CORE_LF_SCALE_STRESS_2A_POLICY
);

const externalLink = (
    symbol: CoreLfQualifiedSymbol,
    order: number
): CoreLfTransferDeclarationLink => {
    const link =
        CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries.find(
            candidate =>
                candidate.symbol.moduleId === symbol.moduleId &&
                candidate.symbol.name === symbol.name
        );
    if (link === undefined) {
        throw new Error(
            `Reviewed continuation has no link for ` +
                `${symbol.moduleId}.${symbol.name}`
        );
    }
    return Object.freeze({
        ...link,
        order,
        symbol: Object.freeze({ ...link.symbol })
    });
};

const externalSymbols =
    CORE_LF_SCALE_STRESS_2A_MODULE.externalSymbols.map(
        external => external.symbol
    );

export const CORE_LF_SCALE_STRESS_2A_LINKAGE:
CoreLfMixedDeclarationLinkage =
    createCoreLfMixedDeclarationLinkage(
        CORE_LF_SCALE_STRESS_2A_PLAN,
        {
            revision: 'SCALE-STRESS-2A-LINKAGE-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_2A_MODULE.revision,
            entries: [
                ...externalSymbols.map(externalLink),
                {
                    order: externalSymbols.length,
                    symbol: displayedFamilyClassifier,
                    kind: 'free-declaration',
                    coreName: 'emdash_v3_2_scale_stress_2_Catd',
                    backendName: 'Catd'
                },
                {
                    order: externalSymbols.length + 1,
                    symbol: sigmaProjectionPullback,
                    kind: 'free-declaration',
                    coreName:
                        'emdash_v3_2_scale_stress_2_' +
                        'Sigma_proj1_pullback_catd',
                    backendName: 'Sigma_proj1_pullback_catd'
                }
            ]
        }
    );

export interface CoreLfScaleStress2aCompilation {
    readonly initialDeclarations:
        ReturnType<
            typeof compileCoreDirectedContinuationTransferWithRuntime
        >;
    readonly compiled: CoreLfCompiledMixedModule;
}

export function compileCoreLfScaleStress2aRepresentation():
CoreLfScaleStress2aCompilation {
    validateCoreLfScaleEngineReview();
    const initialCheckingRuntime =
        CoreDirected1bRuntimeProgram.create();
    const initialDeclarations =
        compileCoreDirectedContinuationTransferWithRuntime(
            initialCheckingRuntime
        );
    const compiled = compileCoreLfMixedPhases(
        CORE_LF_SCALE_STRESS_2A_PLAN,
        CORE_LF_SCALE_STRESS_2A_LINKAGE,
        {
            initialDeclarations,
            initialCheckingRuntime
        }
    );
    return Object.freeze({
        initialDeclarations,
        compiled
    });
}
