/**
 * SCALE-INDUCTIVE-1B1 generated-owner contract proposal.
 *
 * The active `τΣ_` binders occur after the inductive name. Lambdapi's
 * generated eliminator therefore varies over them in its motive: they are
 * indices, not fixed prefix parameters. Signature erasure could safely
 * conflate the two, but generated-owner semantics cannot.
 *
 * This proposal records the exact correction and demonstrates that one
 * explicitly typed generated-owner continuation can already pass through the
 * generic declaration, mixed-phase, runtime, and conversion engines. It does
 * not yet change the shared inductive compiler.
 */

import {
    CoreLfModuleSpec,
    CoreLfQualifiedSymbol,
    CoreLfTransferBuilderExpression,
    CoreLfTransferExpression,
    CoreLfTransferInductiveBlock,
    CoreLfTransferScopedBuilder,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay
} from './lf_transfer';
import { binderMode } from './kernel';
import {
    createCoreLfTransferDeclarationLinkage
} from './lf_transfer_compiler';
import {
    compileCoreLfInductiveSignatures,
    lowerCoreLfInductiveSignatures
} from './lf_transfer_inductive';
import {
    CoreLfCompiledMixedModule,
    compileCoreLfMixedPhases,
    createCoreLfMixedDeclarationLinkage,
    planCoreLfMixedPhases
} from './lf_transfer_mixed';
import {
    CORE_LF_SCALE_STRESS_1_REPRESENTATION
} from './scale_stress_1_representation';

export const CORE_LF_SCALE_INDUCTIVE_1B1_REVISION =
    'SCALE-INDUCTIVE-1B1-PROPOSAL-1' as const;

const DECISION_QUESTION =
    'Approve H-DTTLF-SCALE-INDUCTIVE-01/D-DTTLF-SCALE-INDUCTIVE-001 as proposed.' as const;

const coreModuleId = 'emdash.emdash3_2';

const coreSymbol = (name: string): CoreLfQualifiedSymbol =>
    coreLfQualifiedSymbol(coreModuleId, name);

const grpd = coreSymbol('Grpd');
const tau = coreSymbol('τ');
const tauSigma = coreSymbol('τΣ_');
const structSigma = coreSymbol('Struct_sigma');
const generatedIndTauSigma = coreSymbol('ind_τΣ_');
const generatedSigmaFst =
    coreSymbol('scale_generated_sigma_fst');

const explicitMode = binderMode('explicit', 'functorial');
const implicitMode = binderMode('implicit', 'functorial');

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

const applyExplicit = (
    builder: CoreLfTransferScopedBuilder,
    callee: CoreLfTransferBuilderExpression,
    values: readonly CoreLfTransferBuilderExpression[]
): CoreLfTransferBuilderExpression =>
    call(
        builder,
        callee,
        values.map(value => ({ plicity: 'explicit', value }))
    );

const decode = (
    builder: CoreLfTransferScopedBuilder,
    classifier: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, tau, [{
        plicity: 'explicit',
        value: classifier
    }]);

const familyType = (
    builder: CoreLfTransferScopedBuilder,
    A: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    builder.pi(
        'x',
        decode(builder, A),
        _ => builder.global(grpd)
    );

const sigmaType = (
    builder: CoreLfTransferScopedBuilder,
    A: CoreLfTransferBuilderExpression,
    P: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, tauSigma, [
        { plicity: 'implicit', value: A },
        { plicity: 'explicit', value: P }
    ]);

const sigmaConstructor = (
    builder: CoreLfTransferScopedBuilder,
    A: CoreLfTransferBuilderExpression,
    P: CoreLfTransferBuilderExpression,
    x: CoreLfTransferBuilderExpression,
    u: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    globalCall(builder, structSigma, [
        { plicity: 'implicit', value: A },
        { plicity: 'implicit', value: P },
        { plicity: 'explicit', value: x },
        { plicity: 'explicit', value: u }
    ]);

const generatedMotiveType = (
    builder: CoreLfTransferScopedBuilder
): CoreLfTransferBuilderExpression =>
    builder.pi(
        'A',
        builder.global(grpd),
        A => builder.pi(
            'P',
            familyType(builder, A),
            P => builder.pi(
                's',
                sigmaType(builder, A, P),
                _ => builder.global(grpd)
            )
        )
    );

const generatedBranchType = (
    builder: CoreLfTransferScopedBuilder,
    motive: CoreLfTransferBuilderExpression
): CoreLfTransferBuilderExpression =>
    builder.pi(
        'A',
        builder.global(grpd),
        A => builder.pi(
            'P',
            familyType(builder, A),
            P => builder.pi(
                'x',
                decode(builder, A),
                x => builder.pi(
                    'u',
                    decode(
                        builder,
                        applyExplicit(builder, P, [x])
                    ),
                    u => decode(
                        builder,
                        applyExplicit(builder, motive, [
                            A,
                            P,
                            sigmaConstructor(builder, A, P, x, u)
                        ])
                    )
                )
            )
        )
    );

const generatedIndTauSigmaType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'motive',
        generatedMotiveType(builder),
        motive => builder.pi(
            'Struct_sigma',
            generatedBranchType(builder, motive),
            _branch => builder.pi(
                'A',
                builder.global(grpd),
                A => builder.pi(
                    'P',
                    familyType(builder, A),
                    P => builder.pi(
                        's',
                        sigmaType(builder, A, P),
                        s => decode(
                            builder,
                            applyExplicit(builder, motive, [A, P, s])
                        )
                    )
                )
            )
        )
    ));
};

const generatedSigmaFstType = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'A',
        builder.global(grpd),
        A => builder.pi(
            'P',
            familyType(builder, A),
            P => builder.pi(
                's',
                sigmaType(builder, A, P),
                _ => decode(builder, A)
            )
        )
    ));
};

const generatedSigmaFstBody = (): CoreLfTransferExpression => {
    const builder = new CoreLfTransferScopedBuilder();
    const motive = builder.lam(
        'A',
        builder.global(grpd),
        A => builder.lam(
            'P',
            familyType(builder, A),
            _P => builder.lam(
                's',
                sigmaType(builder, A, _P),
                _s => A
            )
        )
    );
    const branch = builder.lam(
        'A',
        builder.global(grpd),
        A => builder.lam(
            'P',
            familyType(builder, A),
            P => builder.lam(
                'x',
                decode(builder, A),
                x => builder.lam(
                    'u',
                    decode(
                        builder,
                        applyExplicit(builder, P, [x])
                    ),
                    _u => x
                )
            )
        )
    );
    return builder.term(builder.lam(
        'A',
        builder.global(grpd),
        A => builder.lam(
            'P',
            familyType(builder, A),
            P => builder.lam(
                's',
                sigmaType(builder, A, P),
                s => applyExplicit(
                    builder,
                    builder.global(generatedIndTauSigma),
                    [motive, branch, A, P, s]
                )
            )
        )
    ));
};

const generatedBetaRule = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const motive = builder.capture('motive');
    const branch = builder.capture('branch');
    const A = builder.capture('A');
    const P = builder.capture('P');
    const x = builder.capture('x');
    const u = builder.capture('u');
    return {
        order: 2,
        id: 'inductive.generated.tau-sigma-beta',
        groupId: 'inductive.generated.tau-sigma',
        clauseOrder: 0,
        sourceOwner: generatedIndTauSigma,
        variables: [
            {
                name: 'motive',
                type: builder.template(generatedMotiveType(builder))
            },
            {
                name: 'branch',
                type: builder.template(
                    generatedBranchType(builder, motive)
                )
            },
            {
                name: 'A',
                type: builder.template(builder.global(grpd))
            },
            {
                name: 'P',
                type: builder.template(familyType(builder, A))
            },
            {
                name: 'x',
                type: builder.template(decode(builder, A))
            },
            {
                name: 'u',
                type: builder.template(decode(
                    builder,
                    applyExplicit(builder, P, [x])
                ))
            }
        ],
        /*
         * Lambdapi's printed rule uses fresh constructor-parameter pattern
         * variables and recovers their equality from typing. The explicit
         * Core rule repeats A/P, making that well-typed guard structural.
         */
        left: builder.pattern(applyExplicit(
            builder,
            builder.global(generatedIndTauSigma),
            [
                motive,
                branch,
                A,
                P,
                sigmaConstructor(builder, A, P, x, u)
            ]
        )),
        right: builder.template(
            applyExplicit(builder, branch, [A, P, x, u])
        ),
        provenance: {
            authorityPath: proposalSource.authorityPath,
            sourceFragment:
                'generated rule ind_τΣ_ ... ' +
                '(Struct_sigma ...) ↪ ...;'
        }
    };
};

const sourceSigmaBlock = (): CoreLfTransferInductiveBlock => {
    const block =
        CORE_LF_SCALE_STRESS_1_REPRESENTATION.core.module.inductives
            .find(candidate =>
                candidate.symbol.moduleId === tauSigma.moduleId &&
                candidate.symbol.name === tauSigma.name
            );
    if (block === undefined) {
        throw new Error("Missing acquired τΣ_ inductive block");
    }
    return block;
};

/**
 * Reclassify the two inline head binders as eliminator-varying indices.
 *
 * The constructor explicitly rebinds those indices with its source plicity,
 * so the 1A-erased head and constructor declaration types remain unchanged.
 */
export const correctedTauSigmaBlock = ():
CoreLfTransferInductiveBlock => {
    const block = sourceSigmaBlock();
    const constructor = block.constructors[0];
    if (
        block.parameters.length !== 2 ||
        block.indices.length !== 0 ||
        constructor === undefined ||
        constructor.parameterModes?.length !== 2
    ) {
        throw new Error(
            'Acquired τΣ_ block no longer matches the measured 1A shape'
        );
    }
    const reboundIndices = block.parameters.map((parameter, index) => ({
        ...parameter,
        mode: constructor.parameterModes![index]
    }));
    return {
        ...block,
        parameters: [],
        indices: block.parameters,
        constructors: [{
            ...constructor,
            parameterModes: undefined,
            binders: [
                ...reboundIndices,
                ...constructor.binders
            ]
        }]
    };
};

const proposalSource = sourceSigmaBlock().provenance;

const sourceClassifiedSignatureModule = createCoreLfModuleSpec({
    revision: 'SCALE-INDUCTIVE-1B1-TAU-SIGMA-SOURCE-CLASSIFICATION-1',
    moduleId: coreModuleId,
    fragmentId: 'scale-inductive-1b1-tau-sigma-source-classification',
    authorityPath: proposalSource.authorityPath,
    sourceSha256:
        CORE_LF_SCALE_STRESS_1_REPRESENTATION.core.module.sourceSha256,
    dependencies: [],
    externalSymbols: [
        { symbol: grpd, availability: 'existing-core' },
        { symbol: tau, availability: 'existing-core' }
    ],
    declarations: [],
    inductives: [sourceSigmaBlock()],
    runtimeRules: [],
    proofRules: []
});

const signatureModule = createCoreLfModuleSpec({
    revision: 'SCALE-INDUCTIVE-1B1-TAU-SIGMA-SIGNATURE-1',
    moduleId: coreModuleId,
    fragmentId: 'scale-inductive-1b1-tau-sigma-signature',
    authorityPath: proposalSource.authorityPath,
    sourceSha256:
        CORE_LF_SCALE_STRESS_1_REPRESENTATION.core.module.sourceSha256,
    dependencies: [],
    externalSymbols: [
        { symbol: grpd, availability: 'existing-core' },
        { symbol: tau, availability: 'existing-core' }
    ],
    declarations: [],
    inductives: [correctedTauSigmaBlock()],
    runtimeRules: [],
    proofRules: []
});

const sourceClassifiedSignaturePolicy =
    createCoreLfTransferPolicyOverlay(
        sourceClassifiedSignatureModule,
        {
            revision:
                'SCALE-INDUCTIVE-1B1-TAU-SIGMA-' +
                'SOURCE-CLASSIFICATION-POLICY-1',
            moduleRevision: sourceClassifiedSignatureModule.revision,
            entries: [{
                order: 0,
                target: {
                    kind: 'inductive',
                    symbol: tauSigma
                },
                policy: 'opaque-signature',
                evidence: '1A erased-signature comparison only'
            }]
        }
    );

const signaturePolicy = createCoreLfTransferPolicyOverlay(
    signatureModule,
    {
        revision: 'SCALE-INDUCTIVE-1B1-TAU-SIGMA-SIGNATURE-POLICY-1',
        moduleRevision: signatureModule.revision,
        entries: [{
            order: 0,
            target: {
                kind: 'inductive',
                symbol: tauSigma
            },
            policy: 'opaque-signature',
            evidence:
                'isolated executable proposal; no product registration'
        }]
    }
);

const contractModule = createCoreLfModuleSpec({
    revision: 'SCALE-INDUCTIVE-1B1-TAU-SIGMA-CONTRACT-1',
    moduleId: coreModuleId,
    fragmentId: 'scale-inductive-1b1-tau-sigma-contract',
    authorityPath: proposalSource.authorityPath,
    sourceSha256: signatureModule.sourceSha256,
    dependencies: [],
    externalSymbols: [
        { symbol: grpd, availability: 'existing-core' },
        { symbol: tau, availability: 'existing-core' },
        { symbol: tauSigma, availability: 'earlier-fragment' },
        { symbol: structSigma, availability: 'earlier-fragment' }
    ],
    declarations: [
        {
            order: 0,
            symbol: generatedIndTauSigma,
            type: generatedIndTauSigmaType(),
            body: coreLfTransferAbsentBody(),
            modifiers: {
                visibility: 'public',
                rigidity: 'ordinary',
                sourceOpacity: 'opaque',
                generatedBy: tauSigma
            },
            provenance: {
                authorityPath: proposalSource.authorityPath,
                sourceFragment: 'generated print ind_τΣ_;'
            }
        },
        {
            order: 1,
            symbol: generatedSigmaFst,
            type: generatedSigmaFstType(),
            body: {
                kind: 'explicit-term',
                term: generatedSigmaFstBody()
            },
            modifiers: {
                visibility: 'private',
                rigidity: 'ordinary',
                sourceOpacity: 'transparent'
            },
            provenance: {
                authorityPath: proposalSource.authorityPath,
                sourceFragment:
                    'proposal witness ind_τΣ_ ' +
                    '(λ A P _, A) (λ A P x _, x)'
            }
        }
    ],
    inductives: [],
    runtimeRules: [generatedBetaRule()],
    proofRules: []
});

const contractPolicy = createCoreLfTransferPolicyOverlay(
    contractModule,
    {
        revision: 'SCALE-INDUCTIVE-1B1-TAU-SIGMA-CONTRACT-POLICY-1',
        moduleRevision: contractModule.revision,
        entries: [
            {
                order: 0,
                target: {
                    kind: 'declaration',
                    symbol: generatedIndTauSigma
                },
                policy: 'opaque-signature',
                evidence:
                    'exact printed generated-owner type, proposal only'
            },
            {
                order: 1,
                target: {
                    kind: 'declaration',
                    symbol: generatedSigmaFst
                },
                policy: 'checked-transparent-definition',
                evidence:
                    'first explicit code-universe generated-owner consumer'
            },
            {
                order: 2,
                target: {
                    kind: 'runtime-rule',
                    id: 'inductive.generated.tau-sigma-beta'
                },
                policy: 'runtime-rewrite',
                evidence:
                    'exact constructor computation contract, proposal only'
            }
        ]
    }
);

const contractPlan = planCoreLfMixedPhases(
    contractModule,
    contractPolicy
);

const contractLinkage = createCoreLfMixedDeclarationLinkage(
    contractPlan,
    {
        revision: 'SCALE-INDUCTIVE-1B1-TAU-SIGMA-CONTRACT-LINKAGE-1',
        moduleRevision: contractModule.revision,
        entries: [
            {
                order: 0,
                symbol: grpd,
                kind: 'core-owner',
                owner: 'groupoid-universe'
            },
            {
                order: 1,
                symbol: tau,
                kind: 'core-owner',
                owner: 'decode'
            },
            {
                order: 2,
                symbol: tauSigma,
                kind: 'free-declaration',
                coreName: 'scale_inductive_tau_sigma',
                backendName: 'τΣ_'
            },
            {
                order: 3,
                symbol: structSigma,
                kind: 'free-declaration',
                coreName: 'scale_inductive_struct_sigma',
                backendName: 'Struct_sigma'
            },
            {
                order: 4,
                symbol: generatedIndTauSigma,
                kind: 'free-declaration',
                coreName: 'scale_inductive_ind_tau_sigma',
                backendName: 'ind_τΣ_'
            },
            {
                order: 5,
                symbol: generatedSigmaFst,
                kind: 'free-declaration',
                coreName: 'scale_inductive_generated_sigma_fst',
                backendName: 'scale_generated_sigma_fst'
            }
        ]
    }
);

/**
 * The correction changes eliminator semantics, not the already checked 1A
 * head/constructor declarations.
 */
export function tauSigmaErasedSignaturesRemainIdentical(): boolean {
    const before = lowerCoreLfInductiveSignatures(
        sourceClassifiedSignatureModule,
        sourceClassifiedSignaturePolicy
    ).module.declarations;
    const after = lowerCoreLfInductiveSignatures(
        signatureModule,
        signaturePolicy
    ).module.declarations;
    return JSON.stringify(
        before.map(declaration => ({
            symbol: declaration.symbol,
            type: declaration.type,
            modifiers: declaration.modifiers
        }))
    ) === JSON.stringify(
        after.map(declaration => ({
            symbol: declaration.symbol,
            type: declaration.type,
            modifiers: declaration.modifiers
        }))
    );
}

export const CORE_LF_SCALE_INDUCTIVE_1B1_SYMBOLS = Object.freeze({
    grpd,
    tau,
    tauSigma,
    structSigma,
    generatedIndTauSigma,
    generatedSigmaFst
});

export interface CoreLfScaleInductive1b1Compilation {
    readonly signatureModule: CoreLfModuleSpec;
    readonly contract: CoreLfCompiledMixedModule;
}

/**
 * Compile the proposal through existing generic engines.
 *
 * This is feasibility evidence, not the reviewed generic association and
 * positivity validator proposed below.
 */
export function compileCoreLfScaleInductive1b1Proposal():
CoreLfScaleInductive1b1Compilation {
    const lowering = lowerCoreLfInductiveSignatures(
        signatureModule,
        signaturePolicy
    );
    const declarations = lowering.module.declarations;
    const signatureLinkage = createCoreLfTransferDeclarationLinkage(
        lowering.module,
        {
            revision:
                'SCALE-INDUCTIVE-1B1-TAU-SIGMA-SIGNATURE-LINKAGE-1',
            moduleRevision: lowering.module.revision,
            entries: [
                {
                    order: 0,
                    symbol: grpd,
                    kind: 'core-owner',
                    owner: 'groupoid-universe'
                },
                {
                    order: 1,
                    symbol: tau,
                    kind: 'core-owner',
                    owner: 'decode'
                },
                {
                    order: 2,
                    symbol: declarations[0].symbol,
                    kind: 'free-declaration',
                    coreName: 'scale_inductive_tau_sigma',
                    backendName: 'τΣ_'
                },
                {
                    order: 3,
                    symbol: declarations[1].symbol,
                    kind: 'free-declaration',
                    coreName: 'scale_inductive_struct_sigma',
                    backendName: 'Struct_sigma'
                }
            ]
        }
    );
    const signature = compileCoreLfInductiveSignatures(
        lowering,
        signatureLinkage
    );
    const contract = compileCoreLfMixedPhases(
        contractPlan,
        contractLinkage,
        { initialDeclarations: signature }
    );
    return Object.freeze({
        signatureModule,
        contract
    });
}

export interface CoreLfScaleInductive1b1Proposal {
    readonly revision: typeof CORE_LF_SCALE_INDUCTIVE_1B1_REVISION;
    readonly row: 'SCALE-INDUCTIVE-1B1';
    readonly parent: 'SCALE-INDUCTIVE-1B';
    readonly status: 'proposal-awaiting-separate-review';
    readonly measuredAuthority: {
        readonly sourceInductive:
            'inductive τΣ_ [a : Grpd] (P : τ a → Grpd) : TYPE';
        readonly generatedMotiveShape:
            'Π A P s, Grpd';
        readonly generatedRuleCount: 1;
        readonly generatedConsumer:
            'ind_τΣ_ (λ A P _, A) (λ A P x _, x)';
        readonly liveLambdapiAccepted: true;
    };
    readonly representationCorrection: {
        readonly inlineBinders: 'indices';
        readonly prefixBinders: 'parameters';
        readonly correctedIndices: readonly ['a', 'P'];
        readonly correctedParameters: readonly [];
        readonly erasedSignatureDelta: 'none';
        readonly generatedSemanticsDelta: 'required';
    };
    readonly proposedImplementation: readonly [
        'correct-tau-sigma-parameter-index-classification',
        'retain-structurally-identical-erased-head-and-constructor-types',
        'add-generic-explicit-generated-owner-contract-association',
        'check-contract-declaration-and-beta-through-existing-engines',
        'classify-nonrecursive-indexed-strict-positivity',
        'compile-polymorphic-generated-first-projection-consumer'
    ];
    readonly nextBoundary: {
        readonly row: 'SCALE-INDUCTIVE-1B2';
        readonly representative: 'ind_nat';
        readonly responsibilities: readonly [
            'direct-recursive-occurrence-validation',
            'recursive-induction-hypothesis-contract',
            'two-generated-computation-rules',
            'negative-strict-positivity-rejection'
        ];
    };
    readonly doesNotAuthorize: readonly [
        'backend-name-only-generated-owner-trust',
        'automatic-unchecked-eliminator-synthesis',
        'recursive-or-mutual-inductive-graduation',
        'general-higher-order-strict-positivity',
        'implicit-native-TYPE-parameter-encoding',
        'active-profile-or-browser-promotion',
        'Lambdapi-source-change',
        'bulk-parser-or-whole-transfer-graduation',
        'remote-or-history-rewriting-Git-operation'
    ];
    readonly decision: {
        readonly humanGate: 'H-DTTLF-SCALE-INDUCTIVE-01';
        readonly decisionId: 'D-DTTLF-SCALE-INDUCTIVE-001';
        readonly status: 'proposal-only';
        readonly question: typeof DECISION_QUESTION;
    };
}

const deepFreeze = <T>(value: T): T => {
    if (
        value !== null &&
        typeof value === 'object' &&
        !Object.isFrozen(value)
    ) {
        Object.values(value as Record<string, unknown>).forEach(deepFreeze);
        Object.freeze(value);
    }
    return value;
};

const rawProposal: CoreLfScaleInductive1b1Proposal = {
    revision: CORE_LF_SCALE_INDUCTIVE_1B1_REVISION,
    row: 'SCALE-INDUCTIVE-1B1',
    parent: 'SCALE-INDUCTIVE-1B',
    status: 'proposal-awaiting-separate-review',
    measuredAuthority: {
        sourceInductive:
            'inductive τΣ_ [a : Grpd] (P : τ a → Grpd) : TYPE',
        generatedMotiveShape: 'Π A P s, Grpd',
        generatedRuleCount: 1,
        generatedConsumer:
            'ind_τΣ_ (λ A P _, A) (λ A P x _, x)',
        liveLambdapiAccepted: true
    },
    representationCorrection: {
        inlineBinders: 'indices',
        prefixBinders: 'parameters',
        correctedIndices: ['a', 'P'],
        correctedParameters: [],
        erasedSignatureDelta: 'none',
        generatedSemanticsDelta: 'required'
    },
    proposedImplementation: [
        'correct-tau-sigma-parameter-index-classification',
        'retain-structurally-identical-erased-head-and-constructor-types',
        'add-generic-explicit-generated-owner-contract-association',
        'check-contract-declaration-and-beta-through-existing-engines',
        'classify-nonrecursive-indexed-strict-positivity',
        'compile-polymorphic-generated-first-projection-consumer'
    ],
    nextBoundary: {
        row: 'SCALE-INDUCTIVE-1B2',
        representative: 'ind_nat',
        responsibilities: [
            'direct-recursive-occurrence-validation',
            'recursive-induction-hypothesis-contract',
            'two-generated-computation-rules',
            'negative-strict-positivity-rejection'
        ]
    },
    doesNotAuthorize: [
        'backend-name-only-generated-owner-trust',
        'automatic-unchecked-eliminator-synthesis',
        'recursive-or-mutual-inductive-graduation',
        'general-higher-order-strict-positivity',
        'implicit-native-TYPE-parameter-encoding',
        'active-profile-or-browser-promotion',
        'Lambdapi-source-change',
        'bulk-parser-or-whole-transfer-graduation',
        'remote-or-history-rewriting-Git-operation'
    ],
    decision: {
        humanGate: 'H-DTTLF-SCALE-INDUCTIVE-01',
        decisionId: 'D-DTTLF-SCALE-INDUCTIVE-001',
        status: 'proposal-only',
        question: DECISION_QUESTION
    }
};

export const CORE_LF_SCALE_INDUCTIVE_1B1_PROPOSAL =
    deepFreeze(rawProposal);

export type CoreLfScaleInductive1b1ProposalErrorCode =
    | 'INVALID_GENERATED_AUTHORITY'
    | 'PARAMETER_INDEX_BOUNDARY_DRIFT'
    | 'PROPOSAL_BOUNDARY_DRIFT';

export class CoreLfScaleInductive1b1ProposalError extends Error {
    constructor(
        public readonly code:
            CoreLfScaleInductive1b1ProposalErrorCode,
        message: string
    ) {
        super(message);
        this.name = 'CoreLfScaleInductive1b1ProposalError';
    }
}

const fail = (
    code: CoreLfScaleInductive1b1ProposalErrorCode,
    message: string
): never => {
    throw new CoreLfScaleInductive1b1ProposalError(code, message);
};

export function validateCoreLfScaleInductive1b1Proposal(
    proposal: CoreLfScaleInductive1b1Proposal =
        CORE_LF_SCALE_INDUCTIVE_1B1_PROPOSAL
): CoreLfScaleInductive1b1Proposal {
    if (
        proposal.measuredAuthority.generatedRuleCount !== 1 ||
        !proposal.measuredAuthority.liveLambdapiAccepted ||
        proposal.measuredAuthority.generatedMotiveShape !==
            'Π A P s, Grpd'
    ) {
        return fail(
            'INVALID_GENERATED_AUTHORITY',
            'Measured ind_τΣ_ authority drifted'
        );
    }
    if (
        proposal.representationCorrection.inlineBinders !== 'indices' ||
        proposal.representationCorrection.prefixBinders !== 'parameters' ||
        proposal.representationCorrection.correctedIndices.join(',') !==
            'a,P' ||
        proposal.representationCorrection.correctedParameters.length !== 0 ||
        proposal.representationCorrection.erasedSignatureDelta !== 'none'
    ) {
        return fail(
            'PARAMETER_INDEX_BOUNDARY_DRIFT',
            'τΣ_ parameter/index correction drifted'
        );
    }
    if (
        proposal.revision !== CORE_LF_SCALE_INDUCTIVE_1B1_REVISION ||
        proposal.status !== 'proposal-awaiting-separate-review' ||
        proposal.nextBoundary.row !== 'SCALE-INDUCTIVE-1B2' ||
        proposal.nextBoundary.representative !== 'ind_nat' ||
        proposal.decision.status !== 'proposal-only' ||
        proposal.decision.question !== DECISION_QUESTION
    ) {
        return fail(
            'PROPOSAL_BOUNDARY_DRIFT',
            'SCALE-INDUCTIVE-1B1 proposal boundary drifted'
        );
    }
    return proposal;
}
