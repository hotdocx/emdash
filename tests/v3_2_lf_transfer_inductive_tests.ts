/**
 * Focused SCALE-INDUCTIVE-1A generic signature-lowering tests.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_STRESS_1_REPRESENTATION,
    CoreLfDeclarationCompilerError,
    CoreLfInductiveCompilerError,
    CoreLfModuleSpec,
    CoreLfTransferError,
    CoreLfTransferPolicyOverlay,
    binderMode,
    compileCoreLfInductiveSignatures,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    lowerCoreLfInductiveSignatures
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const repositoryRoot = resolve(__dirname, '..');
const moduleId = 'fixture.inductive';
const pair = coreLfQualifiedSymbol(moduleId, 'Pair');
const makePair = coreLfQualifiedSymbol(moduleId, 'make_pair');
const generatedIndPair =
    coreLfQualifiedSymbol(moduleId, 'ind_Pair');
const usesGenerated =
    coreLfQualifiedSymbol(moduleId, 'uses_generated');

const source = (sourceFragment: string) => ({
    authorityPath: 'tests/fixtures/inductive.lp',
    sourceFragment
});

interface InductiveFixture {
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
}

const pairFixture = (): InductiveFixture => {
    const module = createCoreLfModuleSpec({
        revision: 'inductive-fixture-1',
        moduleId,
        fragmentId: 'dependent-pair',
        authorityPath: 'tests/fixtures/inductive.lp',
        sourceSha256:
            'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
        dependencies: [],
        externalSymbols: [],
        declarations: [],
        inductives: [{
            order: 0,
            symbol: pair,
            parameters: [{
                hint: 'A',
                mode: binderMode('explicit', 'functorial'),
                type: { tag: 'type' }
            }],
            indices: [],
            sort: { tag: 'type' },
            constructors: [{
                order: 0,
                symbol: makePair,
                binders: [
                    {
                        hint: 'first',
                        mode: binderMode('explicit', 'functorial'),
                        type: {
                            tag: 'bound',
                            index: 0
                        }
                    },
                    {
                        hint: 'second',
                        mode: binderMode('explicit', 'functorial'),
                        type: {
                            tag: 'bound',
                            index: 1
                        }
                    }
                ],
                result: {
                    tag: 'call',
                    callee: {
                        tag: 'global',
                        symbol: pair
                    },
                    arguments: [{
                        plicity: 'explicit',
                        value: {
                            tag: 'bound',
                            index: 2
                        }
                    }]
                },
                provenance: source(
                    '| make_pair [A] : A → A → Pair A;'
                )
            }],
            generatedSymbols: [generatedIndPair],
            modifiers: {
                visibility: 'public',
                rigidity: 'injective',
                sourceOpacity: 'opaque'
            },
            provenance: source(
                'inductive Pair (A : TYPE) : TYPE ≔'
            )
        }],
        runtimeRules: [],
        proofRules: []
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'inductive-fixture-policy-1',
        moduleRevision: module.revision,
        entries: [{
            order: 0,
            target: {
                kind: 'inductive',
                symbol: pair
            },
            policy: 'opaque-signature',
            evidence: 'synthetic signature-lowering fixture'
        }]
    });
    return { module, policy };
};

const nullaryFixture = (): InductiveFixture => {
    const fixture = pairFixture();
    const block = fixture.module.inductives[0];
    const module = createCoreLfModuleSpec({
        ...fixture.module,
        revision: 'inductive-nullary-fixture-1',
        fragmentId: 'nullary-pair',
        inductives: [{
            ...block,
            parameters: [],
            constructors: [{
                ...block.constructors[0],
                binders: [],
                result: {
                    tag: 'global',
                    symbol: pair
                }
            }]
        }]
    });
    const policy = createCoreLfTransferPolicyOverlay(module, {
        revision: 'inductive-nullary-fixture-policy-1',
        moduleRevision: module.revision,
        entries: fixture.policy.entries
    });
    return { module, policy };
};

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
    );
};

const expectInductiveError = (
    action: () => unknown,
    code: CoreLfInductiveCompilerError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfInductiveCompilerError &&
            error.code === code
    );
};

const loweredLinkage = (
    fixture: ReturnType<typeof lowerCoreLfInductiveSignatures>
) => createCoreLfTransferDeclarationLinkage(
    fixture.module,
    {
        revision: 'inductive-fixture-linkage-1',
        moduleRevision: fixture.module.revision,
        entries: fixture.module.declarations.map(
            (declaration, order) => ({
                order,
                symbol: declaration.symbol,
                kind: 'free-declaration' as const,
                coreName:
                    declaration.symbol.name === 'Pair'
                        ? 'fixture_Pair'
                        : 'fixture_make_pair',
                backendName: declaration.symbol.name
            })
        )
    }
);

describe('SCALE-INDUCTIVE-1A generic inductive signatures', () => {
    it('lowers a parameterized head and constructor mechanically', () => {
        const fixture = pairFixture();
        const lowering = lowerCoreLfInductiveSignatures(
            fixture.module,
            fixture.policy
        );
        assert.equal(lowering.semanticStatus, 'signature-lowering-only');
        assert.deepEqual(
            lowering.module.declarations.map(declaration => [
                declaration.order,
                declaration.symbol.name,
                declaration.modifiers.rigidity
            ]),
            [
                [0, 'Pair', 'injective'],
                [1, 'make_pair', 'injective']
            ]
        );
        const head = lowering.module.declarations[0].type;
        assert.equal(head.tag, 'pi');
        if (head.tag !== 'pi') return;
        assert.equal(head.binder.hint, 'A');
        assert.equal(head.binder.type.tag, 'type');
        assert.equal(head.body.tag, 'type');

        const constructor = lowering.module.declarations[1].type;
        assert.equal(constructor.tag, 'pi');
        if (
            constructor.tag !== 'pi' ||
            constructor.body.tag !== 'pi' ||
            constructor.body.body.tag !== 'pi'
        ) return;
        assert.equal(constructor.binder.hint, 'A');
        assert.deepEqual(
            constructor.body.binder.type,
            { tag: 'bound', index: 0 }
        );
        assert.deepEqual(
            constructor.body.body.binder.type,
            { tag: 'bound', index: 1 }
        );
        assert.deepEqual(
            lowering.blocks[0].generatedSymbols,
            [generatedIndPair]
        );
        assert.deepEqual(
            lowering.blocks[0].referencedUntypedGeneratedSymbols,
            []
        );
        assertDeepFrozen(lowering);
    });

    it('compiles lowered signatures through the existing LF engine', () => {
        const fixture = nullaryFixture();
        const lowering = lowerCoreLfInductiveSignatures(
            fixture.module,
            fixture.policy
        );
        const compiled = compileCoreLfInductiveSignatures(
            lowering,
            loweredLinkage(lowering)
        );

        assert.deepEqual(
            compiled.declarations.map(declaration => [
                declaration.symbol.name,
                declaration.status
            ]),
            [
                ['Pair', 'installed-opaque'],
                ['make_pair', 'installed-opaque']
            ]
        );
        assert.deepEqual(
            compiled.environment.declarations.map(
                declaration => declaration.name
            ),
            ['fixture_Pair', 'fixture_make_pair']
        );
        compiled.createChecker().validateEnvironment();
        compiled.assertEnvironment(compiled.environment);
    });

    it('rejects implicit native-TYPE parameter encoding', () => {
        const fixture = pairFixture();
        const lowering = lowerCoreLfInductiveSignatures(
            fixture.module,
            fixture.policy
        );
        assert.throws(
            () => compileCoreLfInductiveSignatures(
                lowering,
                loweredLinkage(lowering)
            ),
            error =>
                error instanceof CoreLfDeclarationCompilerError &&
                error.code === 'DECLARATION_CHECK_FAILED' &&
                /checker sort KIND, not TYPE/u.test(error.message)
        );
        assert.ok(
            lowering.doesNotProvide.includes(
                'implicit-native-TYPE-parameter-encoding'
            )
        );
    });

    it('lowers the active dependent Sigma shape without promoting it', () => {
        const stress = CORE_LF_SCALE_STRESS_1_REPRESENTATION.core;
        const block = stress.module.inductives[0];
        assert.deepEqual(block.parameters, []);
        assert.deepEqual(
            block.indices.map(index => [
                index.hint,
                index.mode.plicity
            ]),
            [
                ['a', 'implicit'],
                ['P', 'explicit']
            ]
        );
        const lowering = lowerCoreLfInductiveSignatures(
            stress.module,
            stress.policy
        );
        assert.deepEqual(
            lowering.module.declarations.map(
                declaration => declaration.symbol.name
            ),
            ['τΣ_', 'Struct_sigma']
        );
        assert.ok(
            lowering.policy.entries.every(
                entry => entry.policy === 'conformance-only'
            )
        );
        assert.deepEqual(
            lowering.blocks[0].generatedSymbols.map(
                symbol => symbol.name
            ),
            ['ind_τΣ_']
        );
        assert.deepEqual(
            lowering.blocks[0].referencedUntypedGeneratedSymbols,
            []
        );

        const constructor = lowering.module.declarations[1].type;
        assert.equal(constructor.tag, 'pi');
        if (constructor.tag !== 'pi') return;
        assert.equal(constructor.binder.mode.plicity, 'implicit');
        assert.equal(constructor.body.tag, 'pi');
        if (constructor.body.tag !== 'pi') return;
        assert.equal(
            constructor.body.binder.mode.plicity,
            'implicit'
        );
        assert.equal(
            lowering.doesNotProvide.includes(
                'generated-eliminator-types'
            ),
            true
        );
        assert.equal(
            lowering.doesNotProvide.includes('induction-semantics'),
            true
        );
        assert.equal(
            lowering.doesNotProvide.includes(
                'implicit-native-TYPE-parameter-encoding'
            ),
            true
        );
    });

    it('checks the dependent Sigma signatures under test-only policy', () => {
        const stress = CORE_LF_SCALE_STRESS_1_REPRESENTATION.core;
        const policy = createCoreLfTransferPolicyOverlay(
            stress.module,
            {
                revision: 'stress-sigma-test-policy-1',
                moduleRevision: stress.module.revision,
                entries: [{
                    order: 0,
                    target: {
                        kind: 'inductive',
                        symbol:
                            stress.module.inductives[0].symbol
                    },
                    policy: 'opaque-signature',
                    evidence:
                        'test-only generic signature compiler witness'
                }]
            }
        );
        const lowering = lowerCoreLfInductiveSignatures(
            stress.module,
            policy
        );
        assert.deepEqual(
            lowering.module.externalSymbols.map(
                external => external.symbol.name
            ),
            ['Grpd', 'τ']
        );
        const declarations = lowering.module.declarations;
        const linkage = createCoreLfTransferDeclarationLinkage(
            lowering.module,
            {
                revision: 'stress-sigma-test-linkage-1',
                moduleRevision: lowering.module.revision,
                entries: [
                    {
                        order: 0,
                        symbol:
                            lowering.module.externalSymbols[0].symbol,
                        kind: 'core-owner',
                        owner: 'groupoid-universe'
                    },
                    {
                        order: 1,
                        symbol:
                            lowering.module.externalSymbols[1].symbol,
                        kind: 'core-owner',
                        owner: 'decode'
                    },
                    {
                        order: 2,
                        symbol: declarations[0].symbol,
                        kind: 'free-declaration',
                        coreName: 'stress_tau_sigma',
                        backendName: 'τΣ_'
                    },
                    {
                        order: 3,
                        symbol: declarations[1].symbol,
                        kind: 'free-declaration',
                        coreName: 'stress_struct_sigma',
                        backendName: 'Struct_sigma'
                    }
                ]
            }
        );
        const compiled = compileCoreLfInductiveSignatures(
            lowering,
            linkage
        );
        assert.deepEqual(
            compiled.declarations.map(declaration => declaration.status),
            ['installed-opaque', 'installed-opaque']
        );
        compiled.createChecker().validateEnvironment();
    });

    it('rejects a constructor with the wrong result head', () => {
        const fixture = pairFixture();
        const block = fixture.module.inductives[0];
        const malformed = createCoreLfModuleSpec({
            ...fixture.module,
            revision: 'inductive-wrong-head-1',
            inductives: [{
                ...block,
                constructors: [{
                    ...block.constructors[0],
                    result: {
                        tag: 'global',
                        symbol: makePair
                    }
                }]
            }]
        });
        const policy = createCoreLfTransferPolicyOverlay(malformed, {
            revision: 'inductive-wrong-head-policy-1',
            moduleRevision: malformed.revision,
            entries: fixture.policy.entries
        });
        expectInductiveError(
            () => lowerCoreLfInductiveSignatures(malformed, policy),
            'INVALID_CONSTRUCTOR_RESULT'
        );
    });

    it('requires constructor-local modes to cover every parameter', () => {
        const fixture = pairFixture();
        const block = fixture.module.inductives[0];
        assert.throws(
            () => createCoreLfModuleSpec({
                ...fixture.module,
                revision: 'inductive-parameter-mode-gap-1',
                inductives: [{
                    ...block,
                    constructors: [{
                        ...block.constructors[0],
                        parameterModes: []
                    }]
                }]
            }),
            error =>
                error instanceof CoreLfTransferError &&
                error.code === 'INVALID_EXPRESSION' &&
                /parameter modes/u.test(error.message)
        );
    });

    it('rejects parameter omission, reordering, and plicity drift', () => {
        const fixture = pairFixture();
        const block = fixture.module.inductives[0];
        const variants = [
            {
                tag: 'global' as const,
                symbol: pair
            },
            {
                tag: 'call' as const,
                callee: {
                    tag: 'global' as const,
                    symbol: pair
                },
                arguments: [{
                    plicity: 'explicit' as const,
                    value: {
                        tag: 'bound' as const,
                        index: 1
                    }
                }]
            },
            {
                tag: 'call' as const,
                callee: {
                    tag: 'global' as const,
                    symbol: pair
                },
                arguments: [{
                    plicity: 'implicit' as const,
                    value: {
                        tag: 'bound' as const,
                        index: 2
                    }
                }]
            }
        ];
        variants.forEach((result, index) => {
            const malformed = createCoreLfModuleSpec({
                ...fixture.module,
                revision: `inductive-result-drift-${index}`,
                inductives: [{
                    ...block,
                    constructors: [{
                        ...block.constructors[0],
                        result
                    }]
                }]
            });
            const policy = createCoreLfTransferPolicyOverlay(
                malformed,
                {
                    revision:
                        `inductive-result-drift-policy-${index}`,
                    moduleRevision: malformed.revision,
                    entries: fixture.policy.entries
                }
            );
            expectInductiveError(
                () => lowerCoreLfInductiveSignatures(
                    malformed,
                    policy
                ),
                'INVALID_CONSTRUCTOR_RESULT'
            );
        });
    });

    it('requires exact inductive policy coverage', () => {
        const fixture = pairFixture();
        const incomplete = createCoreLfTransferPolicyOverlay(
            fixture.module,
            {
                revision: 'inductive-incomplete-policy-1',
                moduleRevision: fixture.module.revision,
                entries: []
            }
        );
        expectInductiveError(
            () => lowerCoreLfInductiveSignatures(
                fixture.module,
                incomplete
            ),
            'INCOMPLETE_INDUCTIVE_POLICY'
        );
    });

    it('fails closed when an untyped generated owner is referenced', () => {
        const fixture = pairFixture();
        const module = createCoreLfModuleSpec({
            ...fixture.module,
            revision: 'inductive-generated-reference-1',
            declarations: [{
                order: 1,
                symbol: usesGenerated,
                type: {
                    tag: 'global',
                    symbol: generatedIndPair
                },
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'opaque'
                },
                provenance: source(
                    'symbol uses_generated : ind_Pair;'
                )
            }]
        });
        const policy = createCoreLfTransferPolicyOverlay(module, {
            revision: 'inductive-generated-reference-policy-1',
            moduleRevision: module.revision,
            entries: [
                fixture.policy.entries[0],
                {
                    order: 1,
                    target: {
                        kind: 'declaration',
                        symbol: usesGenerated
                    },
                    policy: 'opaque-signature',
                    evidence: 'generated-owner refusal fixture'
                }
            ]
        });
        const lowering = lowerCoreLfInductiveSignatures(
            module,
            policy
        );
        assert.deepEqual(
            lowering.blocks[0].referencedUntypedGeneratedSymbols,
            [generatedIndPair]
        );
        expectInductiveError(
            () => compileCoreLfInductiveSignatures(
                lowering,
                loweredLinkage(lowering)
            ),
            'UNTYPED_GENERATED_SYMBOL_REFERENCED'
        );
    });

    it('keeps the phase owner-agnostic and outside the browser API', () => {
        const implementation = readFileSync(
            resolve(
                repositoryRoot,
                'src/v3_2/lf_transfer_inductive.ts'
            ),
            'utf8'
        );
        assert.doesNotMatch(
            implementation,
            /τΣ_|Struct_sigma|ind_τΣ_|nat_add|Nat_grpd|Pair/u
        );
        assert.equal(
            'lowerCoreLfInductiveSignatures' in browser,
            false
        );
        assert.equal(
            'compileCoreLfInductiveSignatures' in browser,
            false
        );
    });
});
