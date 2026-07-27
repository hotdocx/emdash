/**
 * Focused SCALE-0C tests for generic declaration compilation and the exact
 * reviewed 29-signature migration witness.
 */

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_DIRECTED_CONTINUATION_PROFILE,
    CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE,
    CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE,
    CORE_DIRECTED_CONTINUATION_TRANSFER_POLICY,
    CORE_DIRECTED_GRADUATION_MANIFEST,
    CoreDirected1cCatalog,
    CoreLfDeclarationCompilerError,
    CoreLfModuleSpec,
    CoreLfTransferDeclarationLinkage,
    CoreLfTransferError,
    CoreLfTransferScopedBuilder,
    binderMode,
    compileCoreDirectedContinuationTransfer,
    compileCoreLfDeclarations,
    coreLfDefinitionalCompare,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreLfTransferExplicitBody,
    coreLfTransferTacticBody,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    kernelApplication,
    kernelExpressionEquals,
    kernelFree,
    provenance,
    validateCoreDirectedContinuationTransferEquivalence
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const repositoryRoot = resolve(__dirname, '..');

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const expectCompilerError = (
    action: () => unknown,
    code: CoreLfDeclarationCompilerError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfDeclarationCompilerError &&
            error.code === code
    );
};

const expectTransferError = (
    action: () => unknown,
    code: CoreLfTransferError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfTransferError &&
            error.code === code
    );
};

const moduleId = 'fixture.generic_declarations';
const grpd = coreLfQualifiedSymbol(moduleId, 'Grpd');
const carrier = coreLfQualifiedSymbol(moduleId, 'Carrier');
const identity = coreLfQualifiedSymbol(moduleId, 'identity');

const source = (sourceFragment: string) => ({
    authorityPath: 'tests/fixtures/generic_declarations.lp',
    sourceFragment
});

interface GenericFixture {
    readonly module: CoreLfModuleSpec;
    readonly linkage: CoreLfTransferDeclarationLinkage;
    readonly policy: ReturnType<
        typeof createCoreLfTransferPolicyOverlay
    >;
}

const genericFixture = (): GenericFixture => {
    const types = new CoreLfTransferScopedBuilder();
    const identityType = types.term(types.pi(
        'x',
        types.global(carrier),
        _ => types.global(carrier)
    ));
    const bodies = new CoreLfTransferScopedBuilder();
    const identityBody = bodies.term(bodies.lam(
        'x',
        bodies.global(carrier),
        x => x
    ));
    const module = createCoreLfModuleSpec({
        revision: 'generic-declarations-1',
        moduleId,
        fragmentId: 'intrinsic-opaque-transparent',
        authorityPath: 'tests/fixtures/generic_declarations.lp',
        sourceSha256:
            'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
        dependencies: [],
        externalSymbols: [],
        declarations: [
            {
                order: 0,
                symbol: grpd,
                type: { tag: 'type' },
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'constant',
                    sourceOpacity: 'opaque'
                },
                provenance: source('constant symbol Grpd : TYPE;')
            },
            {
                order: 1,
                symbol: carrier,
                type: { tag: 'type' },
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'opaque'
                },
                provenance: source('symbol Carrier : TYPE;')
            },
            {
                order: 2,
                symbol: identity,
                type: identityType,
                body: coreLfTransferExplicitBody(identityBody),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'transparent'
                },
                provenance: source(
                    'symbol identity (x : Carrier) : Carrier ≔ x;'
                )
            }
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'generic-declarations-policy-1',
        moduleRevision: module.revision,
        entries: [
            {
                order: 0,
                target: { kind: 'declaration', symbol: grpd },
                policy: 'conformance-only',
                evidence: 'fixture intrinsic schema'
            },
            {
                order: 1,
                target: { kind: 'declaration', symbol: carrier },
                policy: 'opaque-signature',
                evidence: 'fixture opaque signature'
            },
            {
                order: 2,
                target: { kind: 'declaration', symbol: identity },
                policy: 'checked-transparent-definition',
                evidence: 'fixture checked definition'
            }
        ]
    });
    const linkage = createCoreLfTransferDeclarationLinkage(module, {
        revision: 'generic-declarations-linkage-1',
        moduleRevision: module.revision,
        entries: [
            {
                order: 0,
                symbol: grpd,
                kind: 'core-owner',
                owner: 'groupoid-universe'
            },
            {
                order: 1,
                symbol: carrier,
                kind: 'free-declaration',
                coreName: 'fixture_Carrier',
                backendName: 'Carrier'
            },
            {
                order: 2,
                symbol: identity,
                kind: 'free-declaration',
                coreName: 'fixture_identity',
                backendName: 'identity'
            }
        ]
    });
    return { module, policy, linkage };
};

describe('SCALE-0C generic LF declaration compiler', () => {
    it('compiles an unrelated intrinsic/opaque/transparent fixture', () => {
        const fixture = genericFixture();
        const compiled = compileCoreLfDeclarations(
            fixture.module,
            fixture.policy,
            fixture.linkage
        );

        assert.deepEqual(
            compiled.declarations.map(declaration => declaration.status),
            [
                'intrinsic-conformance',
                'installed-opaque',
                'installed-transparent'
            ]
        );
        assert.deepEqual(
            compiled.environment.declarations.map(
                declaration => declaration.name
            ),
            ['fixture_Carrier', 'fixture_identity']
        );
        assert.deepEqual(compiled.externalFreeReferences, {
            fixture_Carrier: 'Carrier'
        });
        assert.deepEqual(compiled.externalTransparentDefinitions, {
            fixture_identity: 'identity'
        });
        compiled.createChecker().validateEnvironment();
        compiled.assertEnvironment(compiled.environment);
    });

    it('checks a transparent intrinsic owner through the generic policy path', () => {
        const cat = coreLfQualifiedSymbol(moduleId, 'Cat');
        const opposite = coreLfQualifiedSymbol(moduleId, 'Opp');
        const typeBuilder = new CoreLfTransferScopedBuilder();
        const oppositeType = typeBuilder.term(typeBuilder.pi(
            'A',
            typeBuilder.global(cat),
            _A => typeBuilder.global(cat),
            binderMode('explicit', 'functorial')
        ));
        const bodyBuilder = new CoreLfTransferScopedBuilder();
        const oppositeBody = bodyBuilder.term(bodyBuilder.lam(
            'A',
            bodyBuilder.global(cat),
            A => A,
            binderMode('explicit', 'functorial')
        ));
        const module = createCoreLfModuleSpec({
            revision: 'generic-intrinsic-transparent-1',
            moduleId,
            fragmentId: 'generic-intrinsic-transparent',
            authorityPath:
                'tests/fixtures/generic_declarations.lp',
            sourceSha256:
                'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
            dependencies: [],
            externalSymbols: [{
                symbol: cat,
                availability: 'earlier-fragment'
            }],
            declarations: [{
                order: 0,
                symbol: opposite,
                type: oppositeType,
                body: coreLfTransferExplicitBody(oppositeBody),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'transparent'
                },
                provenance: source(
                    'symbol Opp (A : Cat) : Cat ≔ A;'
                )
            }],
            inductives: [],
            runtimeRules: [],
            proofRules: []
        });
        const policy = createCoreLfTransferPolicyOverlay(module, {
            revision: 'generic-intrinsic-transparent-policy-1',
            moduleRevision: module.revision,
            entries: [{
                order: 0,
                target: {
                    kind: 'declaration',
                    symbol: opposite
                },
                policy: 'checked-transparent-definition',
                evidence: 'unrelated intrinsic delta fixture'
            }]
        });
        const linkage = createCoreLfTransferDeclarationLinkage(module, {
            revision: 'generic-intrinsic-transparent-linkage-1',
            moduleRevision: module.revision,
            entries: [
                {
                    order: 0,
                    symbol: cat,
                    kind: 'core-owner',
                    owner: 'category-universe'
                },
                {
                    order: 1,
                    symbol: opposite,
                    kind: 'core-owner',
                    owner: 'opposite-category'
                }
            ]
        });
        const compiled = compileCoreLfDeclarations(
            module,
            policy,
            linkage
        );

        assert.equal(
            compiled.declaration(opposite)?.status,
            'intrinsic-transparent'
        );
        assert.equal(compiled.environment.declarations.length, 0);
        assert.equal(
            compiled.environment.lookupIntrinsicDefinition(
                'opposite-category'
            )?.declarationName,
            `${moduleId}.Opp`
        );
        compiled.assertEnvironment(compiled.environment);

        const nodeProvenance = provenance(
            'derived',
            'generic intrinsic transparent comparison'
        );
        const A = kernelFree('generic_intrinsic_A', nodeProvenance);
        const result = coreLfDefinitionalCompare(
            compiled.environment,
            kernelApplication(
                'opposite-category',
                [{ value: A }],
                nodeProvenance
            ),
            A,
            2
        );
        assert.equal(result.status, 'equal');
        assert.deepEqual(
            result.trace.map(entry => entry.reduction.kind),
            ['delta', 'beta']
        );
    });

    it('uses prior checked delta definitions without a global registry', () => {
        const alias = coreLfQualifiedSymbol(moduleId, 'Alias');
        const witness = coreLfQualifiedSymbol(moduleId, 'witness');
        const cast = coreLfQualifiedSymbol(moduleId, 'cast');
        const module = createCoreLfModuleSpec({
            revision: 'generic-delta-1',
            moduleId,
            fragmentId: 'prior-delta',
            authorityPath:
                'tests/fixtures/generic_declarations.lp',
            sourceSha256:
                'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
            dependencies: [],
            externalSymbols: [],
            declarations: [
                {
                    order: 0,
                    symbol: carrier,
                    type: { tag: 'type' },
                    body: coreLfTransferAbsentBody(),
                    modifiers: {
                        visibility: 'public',
                        rigidity: 'ordinary',
                        sourceOpacity: 'opaque'
                    },
                    provenance: source('symbol Carrier : TYPE;')
                },
                {
                    order: 1,
                    symbol: alias,
                    type: { tag: 'type' },
                    body: {
                        kind: 'explicit-term',
                        term: { tag: 'global', symbol: carrier }
                    },
                    modifiers: {
                        visibility: 'public',
                        rigidity: 'ordinary',
                        sourceOpacity: 'transparent'
                    },
                    provenance: source('symbol Alias : TYPE ≔ Carrier;')
                },
                {
                    order: 2,
                    symbol: witness,
                    type: { tag: 'global', symbol: carrier },
                    body: coreLfTransferAbsentBody(),
                    modifiers: {
                        visibility: 'public',
                        rigidity: 'ordinary',
                        sourceOpacity: 'opaque'
                    },
                    provenance: source('symbol witness : Carrier;')
                },
                {
                    order: 3,
                    symbol: cast,
                    type: { tag: 'global', symbol: alias },
                    body: {
                        kind: 'explicit-term',
                        term: { tag: 'global', symbol: witness }
                    },
                    modifiers: {
                        visibility: 'public',
                        rigidity: 'ordinary',
                        sourceOpacity: 'opaque'
                    },
                    provenance: source('symbol cast : Alias ≔ witness;')
                }
            ],
            inductives: [],
            runtimeRules: [],
            proofRules: []
        });
        const policies = [
            'opaque-signature',
            'checked-transparent-definition',
            'opaque-signature',
            'theorem-body'
        ] as const;
        const policy = createCoreLfTransferPolicyOverlay(module, {
            revision: 'generic-delta-policy-1',
            moduleRevision: module.revision,
            entries: module.declarations.map((declaration, order) => ({
                order,
                target: {
                    kind: 'declaration' as const,
                    symbol: declaration.symbol
                },
                policy: policies[order],
                evidence: 'generic prior-delta fixture'
            }))
        });
        const linkage = createCoreLfTransferDeclarationLinkage(module, {
            revision: 'generic-delta-linkage-1',
            moduleRevision: module.revision,
            entries: module.declarations.map((declaration, order) => ({
                order,
                symbol: declaration.symbol,
                kind: 'free-declaration' as const,
                coreName: `delta_${declaration.symbol.name}`,
                backendName: declaration.symbol.name
            }))
        });
        const compiled = compileCoreLfDeclarations(
            module,
            policy,
            linkage
        );

        assert.equal(
            compiled.declaration(cast)?.status,
            'installed-theorem'
        );
        assert.equal(
            compiled.environment.lookup('delta_cast')?.transparency,
            'opaque'
        );
        assert.notEqual(
            compiled.environment.lookup('delta_cast')?.body,
            undefined
        );
        compiled.createChecker().validateEnvironment();
    });

    it('requires complete immutable linkage independently of policy', () => {
        const fixture = genericFixture();
        expectCompilerError(
            () => createCoreLfTransferDeclarationLinkage(
                fixture.module,
                {
                    revision: 'missing-linkage-1',
                    moduleRevision: fixture.module.revision,
                    entries: fixture.linkage.entries.slice(0, -1)
                }
            ),
            'INCOMPLETE_LINKAGE'
        );
        assertDeepFrozen(fixture.linkage);
    });

    it('requires exact policy coverage at compilation time', () => {
        const fixture = genericFixture();
        const partial = createCoreLfTransferPolicyOverlay(
            fixture.module,
            {
                revision: 'partial-policy-1',
                moduleRevision: fixture.module.revision,
                entries: fixture.policy.entries.slice(0, -1)
            }
        );
        expectCompilerError(
            () => compileCoreLfDeclarations(
                fixture.module,
                partial,
                fixture.linkage
            ),
            'INCOMPLETE_POLICY'
        );
    });

    it('rejects a forward declaration dependency', () => {
        const builder = new CoreLfTransferScopedBuilder();
        const forwardModule = createCoreLfModuleSpec({
            revision: 'forward-dependency-1',
            moduleId,
            fragmentId: 'forward-dependency',
            authorityPath:
                'tests/fixtures/generic_declarations.lp',
            sourceSha256:
                'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
            dependencies: [],
            externalSymbols: [],
            declarations: [
                {
                    order: 0,
                    symbol: carrier,
                    type: builder.term(builder.global(identity)),
                    body: coreLfTransferAbsentBody(),
                    modifiers: {
                        visibility: 'public',
                        rigidity: 'ordinary',
                        sourceOpacity: 'opaque'
                    },
                    provenance: source('symbol Carrier : identity;')
                },
                {
                    order: 1,
                    symbol: identity,
                    type: { tag: 'type' },
                    body: coreLfTransferAbsentBody(),
                    modifiers: {
                        visibility: 'public',
                        rigidity: 'ordinary',
                        sourceOpacity: 'opaque'
                    },
                    provenance: source('symbol identity : TYPE;')
                }
            ],
            inductives: [],
            runtimeRules: [],
            proofRules: []
        });
        const policy = createCoreLfTransferPolicyOverlay(
            forwardModule,
            {
                revision: 'forward-policy-1',
                moduleRevision: forwardModule.revision,
                entries: forwardModule.declarations.map(
                    (declaration, order) => ({
                        order,
                        target: {
                            kind: 'declaration' as const,
                            symbol: declaration.symbol
                        },
                        policy: 'opaque-signature' as const,
                        evidence: 'forward-reference rejection fixture'
                    })
                )
            }
        );
        const linkage = createCoreLfTransferDeclarationLinkage(
            forwardModule,
            {
                revision: 'forward-linkage-1',
                moduleRevision: forwardModule.revision,
                entries: forwardModule.declarations.map(
                    (declaration, order) => ({
                        order,
                        symbol: declaration.symbol,
                        kind: 'free-declaration' as const,
                        coreName:
                            order === 0
                                ? 'forward_Carrier'
                                : 'forward_identity',
                        backendName: declaration.symbol.name
                    })
                )
            }
        );
        expectCompilerError(
            () => compileCoreLfDeclarations(
                forwardModule,
                policy,
                linkage
            ),
            'UNAVAILABLE_SYMBOL'
        );
    });

    it('rejects intrinsic signature drift and incompatible tactic bodies', () => {
        const fixture = genericFixture();
        const drifted = createCoreLfModuleSpec({
            ...fixture.module,
            revision: 'intrinsic-drift-1',
            declarations: fixture.module.declarations.map(
                (declaration, index) => index === 0
                    ? {
                        ...declaration,
                        type: {
                            tag: 'pi' as const,
                            binder: {
                                hint: 'A',
                                mode: binderMode(
                                    'explicit',
                                    'functorial'
                                ),
                                type: { tag: 'type' as const }
                            },
                            body: { tag: 'type' as const }
                        }
                    }
                    : declaration
            )
        });
        const driftPolicy = createCoreLfTransferPolicyOverlay(
            drifted,
            {
                revision: 'intrinsic-drift-policy-1',
                moduleRevision: drifted.revision,
                entries: fixture.policy.entries
            }
        );
        const driftLinkage = createCoreLfTransferDeclarationLinkage(
            drifted,
            {
                revision: 'intrinsic-drift-linkage-1',
                moduleRevision: drifted.revision,
                entries: fixture.linkage.entries
            }
        );
        expectCompilerError(
            () => compileCoreLfDeclarations(
                drifted,
                driftPolicy,
                driftLinkage
            ),
            'INTRINSIC_SIGNATURE_MISMATCH'
        );

        const tactic = createCoreLfModuleSpec({
            ...fixture.module,
            revision: 'tactic-body-1',
            declarations: fixture.module.declarations.map(
                (declaration, index) => index === 2
                    ? {
                        ...declaration,
                        body: coreLfTransferTacticBody('begin exact x; end')
                    }
                    : declaration
            )
        });
        const tacticPolicy = createCoreLfTransferPolicyOverlay(
            tactic,
            {
                revision: 'tactic-policy-1',
                moduleRevision: tactic.revision,
                entries: fixture.policy.entries
            }
        );
        const tacticLinkage = createCoreLfTransferDeclarationLinkage(
            tactic,
            {
                revision: 'tactic-linkage-1',
                moduleRevision: tactic.revision,
                entries: fixture.linkage.entries
            }
        );
        expectCompilerError(
            () => compileCoreLfDeclarations(
                tactic,
                tacticPolicy,
                tacticLinkage
            ),
            'INCOMPATIBLE_POLICY'
        );
    });
});

describe('SCALE-0C reviewed continuation migration', () => {
    it('pins all 29 signatures and keeps policy separate from linkage', () => {
        assert.equal(
            CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE.declarations.length,
            29
        );
        assert.equal(
            CORE_DIRECTED_CONTINUATION_TRANSFER_POLICY.entries.length,
            29
        );
        assert.equal(
            CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE.entries.length,
            29
        );
        assert.deepEqual(
            CORE_DIRECTED_CONTINUATION_TRANSFER_POLICY.entries.reduce(
                (counts, entry) => ({
                    ...counts,
                    [entry.policy]: (counts[entry.policy] ?? 0) + 1
                }),
                {} as Record<string, number>
            ),
            {
                'conformance-only': 20,
                'opaque-signature': 8,
                'checked-transparent-definition': 1
            }
        );
        assert.equal(
            CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE.runtimeRules.length,
            0
        );
        assert.equal(
            CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE.proofRules.length,
            0
        );
        assertDeepFrozen(CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE);
        assertDeepFrozen(CORE_DIRECTED_CONTINUATION_TRANSFER_POLICY);
        assertDeepFrozen(CORE_DIRECTED_CONTINUATION_TRANSFER_LINKAGE);
    });

    it('matches the reviewed catalog expression-for-expression', () => {
        const compiled = compileCoreDirectedContinuationTransfer();
        validateCoreDirectedContinuationTransferEquivalence(compiled);
        const legacy = CoreDirected1cCatalog.create();

        assert.deepEqual(
            compiled.environment.declarations.map(declaration => ({
                name: declaration.name,
                transparency: declaration.transparency,
                hasBody: declaration.body !== undefined
            })),
            legacy.environment.declarations.map(declaration => ({
                name: declaration.name,
                transparency: declaration.transparency,
                hasBody: declaration.body !== undefined
            }))
        );
        compiled.environment.declarations.forEach(
            (declaration, index) => {
                const previous = legacy.environment.declarations[index];
                assert.equal(
                    kernelExpressionEquals(
                        declaration.type,
                        previous.type
                    ),
                    true
                );
                assert.equal(
                    declaration.body === undefined
                        ? previous.body === undefined
                        : previous.body !== undefined &&
                            kernelExpressionEquals(
                                declaration.body,
                                previous.body
                            ),
                    true
                );
            }
        );
        assert.equal(
            compiled.declarations.length,
            CORE_DIRECTED_CONTINUATION_PROFILE
                .signatureClosure.totalCount
        );
    });

    it('anchors every declaration fragment to the live authority and hashes', () => {
        const authorityPath = resolve(
            repositoryRoot,
            CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE.authorityPath
        );
        const authority = readFileSync(authorityPath, 'utf8');
        const sourceHash =
            `sha256:${createHash('sha256').update(authority).digest('hex')}`;
        assert.equal(
            sourceHash,
            CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE.sourceSha256
        );
        for (
            const declaration of
            CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE.declarations
        ) {
            assert.equal(
                authority.includes(declaration.provenance.sourceFragment),
                true,
                declaration.provenance.sourceFragment
            );
        }
        assert.equal(
            CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE.canonicalExport
                ?.sha256,
            'sha256:61242c1a1c4c6fe032ff9d22ae7292556ff3abd41921ff79352642e3f1790000'
        );
    });

    it('keeps the compiler owner-agnostic and out of the browser graph', () => {
        const compilerSource = readFileSync(
            resolve(
                repositoryRoot,
                'src/v3_2/lf_transfer_compiler.ts'
            ),
            'utf8'
        );
        [
            'sigma-category',
            'displayed-functor-category',
            'section-object-evaluation',
            'CoreDirected'
        ].forEach(forbidden =>
            assert.equal(compilerSource.includes(forbidden), false)
        );
        assert.equal(
            Object.prototype.hasOwnProperty.call(
                browser,
                'compileCoreLfDeclarations'
            ),
            false
        );
        assert.equal(
            Object.prototype.hasOwnProperty.call(
                browser,
                'compileCoreDirectedContinuationTransfer'
            ),
            false
        );
        assert.equal(
            CORE_DIRECTED_GRADUATION_MANIFEST.composition
                .totalOwnerSignatureCount,
            29
        );
    });

    it('does not let the representation layer grant missing policy', () => {
        expectTransferError(
            () => createCoreLfTransferPolicyOverlay(
                CORE_DIRECTED_CONTINUATION_TRANSFER_MODULE,
                {
                    revision: 'foreign-policy-1',
                    moduleRevision: 'not-the-reviewed-module',
                    entries: []
                }
            ),
            'INVALID_POLICY'
        );
    });
});
