/**
 * Representation-only SCALE-STRESS-3A1 transfer of the first profunctor
 * opacity boundary.
 *
 * The selected fragment deliberately contains a non-contiguous dependency
 * chain. `Prof` and `ProfComparison` are checked transparent definitions,
 * while `DefIso`, `Prof_cat`, and `Prof_tensor` remain exact opaque
 * signatures. No profunctor action rule is selected or activated here.
 */

import {
    CoreDirected1bRuntimeProgram
} from './directed_1b';
import {
    CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE,
    compileCoreDirectedContinuationTransferWithRuntime,
    coreDirectedContinuationTransferSymbol
} from './directed_continuation_transfer';
import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferBuilderExpression,
    CoreLfTransferDeclaration,
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
    CoreLfCompiledDeclarationModule,
    CoreLfTransferDeclarationLinkage,
    CoreLfTransferDeclarationLink,
    compileCoreLfDeclarations,
    createCoreLfTransferDeclarationLinkage
} from './lf_transfer_compiler';
import {
    CoreLfMixedDeclarationContext
} from './lf_transfer_mixed';
import { binderMode } from './kernel';
import {
    validateCoreLfScaleEngineReview
} from './scale_engine_review';
import {
    CORE_LF_SCALE_STRESS_3_PROFUNCTOR_BOUNDARY_ACQUISITION
} from './scale_stress_3_acquisition';

const moduleId = 'emdash.emdash3_2';

const category =
    coreDirectedContinuationTransferSymbol('category-universe');
const groupoid =
    coreDirectedContinuationTransferSymbol('groupoid-universe');
const decodeOwner =
    coreDirectedContinuationTransferSymbol('decode');
const objectClassifier =
    coreDirectedContinuationTransferSymbol('object-classifier');

export const CORE_LF_SCALE_STRESS_3A1_SYMBOLS = Object.freeze({
    definitionalIsomorphism:
        coreLfQualifiedSymbol(moduleId, 'DefIso'),
    profunctorCategory:
        coreLfQualifiedSymbol(moduleId, 'Prof_cat'),
    profunctorClassifier:
        coreLfQualifiedSymbol(moduleId, 'Prof'),
    profunctorComparison:
        coreLfQualifiedSymbol(moduleId, 'ProfComparison'),
    profunctorTensor:
        coreLfQualifiedSymbol(moduleId, 'Prof_tensor')
});

const {
    definitionalIsomorphism,
    profunctorCategory,
    profunctorClassifier,
    profunctorComparison,
    profunctorTensor
} = CORE_LF_SCALE_STRESS_3A1_SYMBOLS;

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

const objectClassifierAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, objectClassifier, [{
        plicity: 'explicit',
        value: base
    }]);

const objectType = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(builder, objectClassifierAt(builder, base));

const profunctorCategoryAt = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, profunctorCategory, [
        { plicity: 'explicit', value: sourceCategory },
        { plicity: 'explicit', value: targetCategory }
    ]);

const profunctorClassifierAt = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, profunctorClassifier, [
        { plicity: 'explicit', value: sourceCategory },
        { plicity: 'explicit', value: targetCategory }
    ]);

const profunctorType = (
    builder: CoreLfTransferScopedBuilder,
    sourceCategory: CoreLfTransferBuilderExpression,
    targetCategory: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    decode(
        builder,
        profunctorClassifierAt(
            builder,
            sourceCategory,
            targetCategory
        )
    );

const definitionalIsomorphismAt = (
    builder: CoreLfTransferScopedBuilder,
    base: CoreLfTransferBuilderExpression,
    left: CoreLfTransferBuilderExpression,
    right: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, definitionalIsomorphism, [
        { plicity: 'implicit', value: base },
        { plicity: 'explicit', value: left },
        { plicity: 'explicit', value: right }
    ]);

const definitionalIsomorphismType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'C',
        builder.global(category),
        C => builder.pi(
            'x',
            objectType(builder, C),
            _x => builder.pi(
                'y',
                objectType(builder, C),
                _y => builder.global(groupoid),
                explicitMode
            ),
            explicitMode
        ),
        implicitMode
    ));
};

const profunctorCategoryType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        _A => builder.pi(
            'B',
            builder.global(category),
            _B => builder.global(category),
            explicitMode
        ),
        explicitMode
    ));
};

const profunctorClassifierType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        _A => builder.pi(
            'B',
            builder.global(category),
            _B => builder.global(groupoid),
            explicitMode
        ),
        explicitMode
    ));
};

const profunctorClassifierBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'A',
        builder.global(category),
        A => builder.lam(
            'B',
            builder.global(category),
            B => objectClassifierAt(
                builder,
                profunctorCategoryAt(builder, A, B)
            ),
            explicitMode
        ),
        explicitMode
    ));
};

const profunctorComparisonType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'P',
                profunctorType(builder, A, B),
                _P => builder.pi(
                    'Q',
                    profunctorType(builder, A, B),
                    _Q => builder.global(groupoid),
                    explicitMode
                ),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const profunctorComparisonBody =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.lam(
        'A',
        builder.global(category),
        A => builder.lam(
            'B',
            builder.global(category),
            B => builder.lam(
                'P',
                profunctorType(builder, A, B),
                P => builder.lam(
                    'Q',
                    profunctorType(builder, A, B),
                    Q => definitionalIsomorphismAt(
                        builder,
                        profunctorCategoryAt(builder, A, B),
                        P,
                        Q
                    ),
                    explicitMode
                ),
                explicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const profunctorTensorType =
(): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(category),
        A => builder.pi(
            'B',
            builder.global(category),
            B => builder.pi(
                'X',
                builder.global(category),
                X => builder.pi(
                    'R',
                    profunctorType(builder, A, B),
                    _R => builder.pi(
                        'S',
                        profunctorType(builder, B, X),
                        _S => profunctorType(builder, A, X),
                        explicitMode
                    ),
                    explicitMode
                ),
                implicitMode
            ),
            implicitMode
        ),
        implicitMode
    ));
};

const source = (
    sourceFragment: string,
    canonicalCommandOrdinal: number
) => ({
    authorityPath: 'emdash2/emdash3_2.lp',
    sourceFragment,
    canonicalCommandOrdinal
});

const publicModifiers = (
    rigidity: 'ordinary' | 'injective',
    sourceOpacity: 'transparent' | 'opaque'
) => ({
    visibility: 'public' as const,
    rigidity,
    sourceOpacity
});

const declarations: readonly CoreLfTransferDeclaration[] = [
    {
        order: 0,
        symbol: definitionalIsomorphism,
        type: definitionalIsomorphismType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol DefIso',
            577
        )
    },
    {
        order: 1,
        symbol: profunctorCategory,
        type: profunctorCategoryType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('injective', 'opaque'),
        provenance: source(
            'injective symbol Prof_cat (A B : Cat) : Cat;',
            1198
        )
    },
    {
        order: 2,
        symbol: profunctorClassifier,
        type: profunctorClassifierType(),
        body: coreLfTransferExplicitBody(
            profunctorClassifierBody()
        ),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol Prof (A B : Cat) : Grpd',
            1202
        )
    },
    {
        order: 3,
        symbol: profunctorComparison,
        type: profunctorComparisonType(),
        body: coreLfTransferExplicitBody(
            profunctorComparisonBody()
        ),
        modifiers: publicModifiers('ordinary', 'transparent'),
        provenance: source(
            'symbol ProfComparison\n  [A B : Cat]',
            1232
        )
    },
    {
        order: 4,
        symbol: profunctorTensor,
        type: profunctorTensorType(),
        body: coreLfTransferAbsentBody(),
        modifiers: publicModifiers('ordinary', 'opaque'),
        provenance: source(
            'symbol Prof_tensor [A B X : Cat]',
            1262
        )
    }
];

export const CORE_LF_SCALE_STRESS_3A1_MODULE:
CoreLfModuleSpec = createCoreLfModuleSpec({
    revision: 'SCALE-STRESS-3A1-PROFUNCTOR-BOUNDARY-1',
    moduleId,
    fragmentId: 'scale-stress-3a1-profunctor-boundary',
    authorityPath:
        CORE_LF_SCALE_STRESS_3_PROFUNCTOR_BOUNDARY_ACQUISITION
            .authorityPath,
    sourceSha256:
        CORE_LF_SCALE_STRESS_3_PROFUNCTOR_BOUNDARY_ACQUISITION
            .sourceSha256,
    canonicalExport: {
        exporterVersion:
            CORE_LF_SCALE_STRESS_3_PROFUNCTOR_BOUNDARY_ACQUISITION
                .canonicalExport.exporterVersion,
        sha256:
            CORE_LF_SCALE_STRESS_3_PROFUNCTOR_BOUNDARY_ACQUISITION
                .canonicalExport.sha256
    },
    dependencies: [],
    externalSymbols: [
        category,
        groupoid,
        decodeOwner,
        objectClassifier
    ].map(symbol => ({
        symbol,
        availability: 'earlier-fragment' as const
    })),
    declarations,
    inductives: [],
    runtimeRules: [],
    proofRules: []
});

export const CORE_LF_SCALE_STRESS_3A1_POLICY:
CoreLfTransferPolicyOverlay =
    createCoreLfTransferPolicyOverlay(
        CORE_LF_SCALE_STRESS_3A1_MODULE,
        {
            revision:
                'SCALE-STRESS-3A1-PROFUNCTOR-BOUNDARY-POLICY-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_3A1_MODULE.revision,
            entries: declarations.map((declaration, order) => ({
                order,
                target: {
                    kind: 'declaration' as const,
                    symbol: declaration.symbol
                },
                policy:
                    declaration.symbol === profunctorClassifier ||
                    declaration.symbol === profunctorComparison
                        ? 'checked-transparent-definition' as const
                        : 'opaque-signature' as const,
                evidence:
                    'Exact active profunctor boundary declaration in ' +
                    'isolated SCALE-STRESS-3A1 evidence'
            }))
        }
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
    CORE_LF_SCALE_STRESS_3A1_MODULE.externalSymbols.map(
        external => external.symbol
    );

export const CORE_LF_SCALE_STRESS_3A1_LINKAGE:
CoreLfTransferDeclarationLinkage =
    createCoreLfTransferDeclarationLinkage(
        CORE_LF_SCALE_STRESS_3A1_MODULE,
        {
            revision:
                'SCALE-STRESS-3A1-PROFUNCTOR-BOUNDARY-LINKAGE-1',
            moduleRevision:
                CORE_LF_SCALE_STRESS_3A1_MODULE.revision,
            entries: [
                ...externalSymbols.map(externalLink),
                ...declarations.map((declaration, index) => ({
                    order: externalSymbols.length + index,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `emdash_v3_2_scale_stress_3a1_` +
                        declaration.symbol.name,
                    backendName: declaration.symbol.name
                }))
            ]
        }
    );

export const CORE_LF_SCALE_STRESS_3A1_BOUNDARY = Object.freeze({
    semanticStatus: 'isolated-representation-only',
    selectedTransparentBodies: Object.freeze([
        profunctorClassifier,
        profunctorComparison
    ]),
    selectedOpaquePrimitives: Object.freeze([
        definitionalIsomorphism,
        profunctorCategory,
        profunctorTensor
    ]),
    doesNotProvide: Object.freeze([
        'active-policy-selection',
        'profunctor-comparison-push-pull',
        'profunctor-tensor-map-or-functor',
        'profunctor-action-runtime-rules',
        'protected-module-visibility',
        'proof-heavy-extension',
        'WalkingEnd-HIT',
        'browser-api',
        'mechanical-transfer-qualification'
    ])
});

export interface CoreLfScaleStress3a1Compilation {
    readonly initialDeclarations:
        ReturnType<
            typeof compileCoreDirectedContinuationTransferWithRuntime
        >;
    readonly compiled: CoreLfCompiledDeclarationModule;
    readonly declarationContext: CoreLfMixedDeclarationContext;
}

export function compileCoreLfScaleStress3a1Representation():
CoreLfScaleStress3a1Compilation {
    validateCoreLfScaleEngineReview();
    const initialCheckingRuntime =
        CoreDirected1bRuntimeProgram.create();
    const initialDeclarations =
        compileCoreDirectedContinuationTransferWithRuntime(
            initialCheckingRuntime
        );
    const compiled = compileCoreLfDeclarations(
        CORE_LF_SCALE_STRESS_3A1_MODULE,
        CORE_LF_SCALE_STRESS_3A1_POLICY,
        CORE_LF_SCALE_STRESS_3A1_LINKAGE,
        {
            initialEnvironment: initialDeclarations.environment,
            runtimeProgram: initialCheckingRuntime
        }
    );
    const declarationContext = new CoreLfMixedDeclarationContext(
        initialDeclarations,
        [compiled]
    );
    return Object.freeze({
        initialDeclarations,
        compiled,
        declarationContext
    });
}
