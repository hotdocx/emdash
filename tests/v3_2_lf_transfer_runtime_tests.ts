/**
 * Focused SCALE-0D tests for generic runtime compilation and the exact
 * reviewed ten-rule migration witness.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_DIRECTED_CONTINUATION_RUNTIME_SUBJECT_ORACLE,
    CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE,
    CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_POLICY,
    CORE_DIRECTED_GRADUATION_MANIFEST,
    CoreLfCompiledRuntimeProgram,
    CoreLfModuleSpec,
    CoreLfRuntimeCompilerError,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferRuntimeRule,
    CoreLfTransferScopedBuilder,
    compileCoreDirectedContinuationRuntimeTransfer,
    compileCoreLfDeclarations,
    compileCoreLfProofProgram,
    compileCoreLfRuntimeProgram,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    provenance,
    validateCoreDirectedContinuationRuntimeTransferEquivalence
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

const expectRuntimeError = (
    action: () => unknown,
    code: CoreLfRuntimeCompilerError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfRuntimeCompilerError &&
            error.code === code
    );
};

const fixtureModuleId = 'fixture.generic_runtime';
const nat = coreLfQualifiedSymbol(fixtureModuleId, 'Nat');
const zero = coreLfQualifiedSymbol(fixtureModuleId, 'zero');
const identity = coreLfQualifiedSymbol(fixtureModuleId, 'identity');
const beneath = coreLfQualifiedSymbol(fixtureModuleId, 'beneath');
const leftType = coreLfQualifiedSymbol(fixtureModuleId, 'Left');
const rightType = coreLfQualifiedSymbol(fixtureModuleId, 'Right');
const leftHead = coreLfQualifiedSymbol(fixtureModuleId, 'left_head');
const rightValue = coreLfQualifiedSymbol(fixtureModuleId, 'right_value');

const fixtureSource = (sourceFragment: string) => ({
    authorityPath: 'tests/fixtures/generic_runtime.lp',
    sourceFragment
});

const declarationModifiers = {
    visibility: 'public' as const,
    rigidity: 'ordinary' as const,
    sourceOpacity: 'opaque' as const
};

const functionType = (
    argumentType: typeof nat,
    resultType: typeof nat
) => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'x',
        builder.global(argumentType),
        _ => builder.global(resultType)
    ));
};

const beneathType = () => {
    const builder = new CoreLfTransferScopedBuilder();
    const bodyType = builder.pi(
        'y',
        builder.global(nat),
        _ => builder.global(nat)
    );
    return builder.term(builder.pi(
        'f',
        bodyType,
        _ => builder.global(nat)
    ));
};

interface GenericRuntimeFixture {
    readonly declarations: ReturnType<typeof compileCoreLfDeclarations>;
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
}

const runtimePolicy = (
    module: CoreLfModuleSpec,
    revision: string
): CoreLfTransferPolicyOverlay =>
    createCoreLfTransferPolicyOverlay(module, {
        revision,
        moduleRevision: module.revision,
        entries: module.runtimeRules.map((rule, order) => ({
            order,
            target: {
                kind: 'runtime-rule' as const,
                id: rule.id
            },
            policy: 'runtime-rewrite' as const,
            evidence: 'generic runtime fixture'
        }))
    });

const genericRuntimeFixture = (): GenericRuntimeFixture => {
    const declarationModule = createCoreLfModuleSpec({
        revision: 'generic-runtime-declarations-1',
        moduleId: fixtureModuleId,
        fragmentId: 'generic-runtime-declarations',
        authorityPath: 'tests/fixtures/generic_runtime.lp',
        sourceSha256:
            'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
        dependencies: [],
        externalSymbols: [],
        declarations: [
            {
                order: 0,
                symbol: nat,
                type: { tag: 'type' },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: fixtureSource('symbol Nat : TYPE;')
            },
            {
                order: 1,
                symbol: zero,
                type: { tag: 'global', symbol: nat },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: fixtureSource('symbol zero : Nat;')
            },
            {
                order: 2,
                symbol: identity,
                type: functionType(nat, nat),
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: fixtureSource(
                    'symbol identity (x : Nat) : Nat;'
                )
            },
            {
                order: 3,
                symbol: beneath,
                type: beneathType(),
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: fixtureSource(
                    'symbol beneath (f : Nat → Nat) : Nat;'
                )
            }
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const declarationPolicy = createCoreLfTransferPolicyOverlay(
        declarationModule,
        {
            revision: 'generic-runtime-declaration-policy-1',
            moduleRevision: declarationModule.revision,
            entries: declarationModule.declarations.map(
                (declaration, order) => ({
                    order,
                    target: {
                        kind: 'declaration' as const,
                        symbol: declaration.symbol
                    },
                    policy: 'opaque-signature' as const,
                    evidence: 'generic runtime declaration fixture'
                })
            )
        }
    );
    const linkage = createCoreLfTransferDeclarationLinkage(
        declarationModule,
        {
            revision: 'generic-runtime-linkage-1',
            moduleRevision: declarationModule.revision,
            entries: declarationModule.declarations.map(
                (declaration, order) => ({
                    order,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `runtime_fixture_${declaration.symbol.name}`,
                    backendName: declaration.symbol.name
                })
            )
        }
    );
    const declarations = compileCoreLfDeclarations(
        declarationModule,
        declarationPolicy,
        linkage
    );

    const identityPattern = new CoreLfTransferScopedBuilder();
    const identityLeft = identityPattern.pattern(identityPattern.call(
        identityPattern.global(identity),
        [{
            plicity: 'explicit',
            value: identityPattern.capture('x')
        }]
    ));
    const identityTemplate = new CoreLfTransferScopedBuilder();
    const identityRight = identityTemplate.template(
        identityTemplate.capture('x')
    );

    const beneathPattern = new CoreLfTransferScopedBuilder();
    const beneathLeft = beneathPattern.pattern(beneathPattern.call(
        beneathPattern.global(beneath),
        [{
            plicity: 'explicit',
            value: beneathPattern.lam(
                'y',
                beneathPattern.global(nat),
                _ => beneathPattern.capture('x')
            )
        }]
    ));
    const beneathTemplate = new CoreLfTransferScopedBuilder();
    const beneathRight = beneathTemplate.template(
        beneathTemplate.capture('x')
    );

    const module = createCoreLfModuleSpec({
        revision: 'generic-runtime-rules-1',
        moduleId: fixtureModuleId,
        fragmentId: 'generic-runtime-rules',
        authorityPath: 'tests/fixtures/generic_runtime.lp',
        sourceSha256:
            'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
        dependencies: [],
        externalSymbols: [nat, identity, beneath].map(symbol => ({
            symbol,
            availability: 'earlier-fragment' as const
        })),
        declarations: [],
        inductives: [],
        runtimeRules: [
            {
                order: 0,
                id: 'fixture.identity.evaluate',
                groupId: 'fixture.identity.evaluate',
                clauseOrder: 0,
                sourceOwner: identity,
                variables: [{
                    name: 'x',
                    type: { tag: 'global', symbol: nat }
                }],
                left: identityLeft,
                right: identityRight,
                provenance: fixtureSource(
                    'rule identity $x ↪ $x;'
                )
            },
            {
                order: 1,
                id: 'fixture.beneath.evaluate',
                groupId: 'fixture.beneath.evaluate',
                clauseOrder: 0,
                sourceOwner: beneath,
                variables: [{
                    name: 'x',
                    type: { tag: 'global', symbol: nat }
                }],
                left: beneathLeft,
                right: beneathRight,
                provenance: fixtureSource(
                    'rule beneath (λ y, $x) ↪ $x;'
                )
            }
        ],
        proofRules: []
    });
    return {
        declarations,
        module,
        policy: runtimePolicy(module, 'generic-runtime-policy-1')
    };
};

const proofSubjectRuntimeFixture = () => {
    const declarationModule = createCoreLfModuleSpec({
        revision: 'proof-subject-runtime-declarations-1',
        moduleId: fixtureModuleId,
        fragmentId: 'proof-subject-runtime-declarations',
        authorityPath: 'tests/fixtures/generic_runtime.lp',
        sourceSha256:
            'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
        dependencies: [],
        externalSymbols: [],
        declarations: [
            {
                order: 0,
                symbol: leftType,
                type: { tag: 'type' as const },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: fixtureSource('symbol Left : TYPE;')
            },
            {
                order: 1,
                symbol: rightType,
                type: { tag: 'type' as const },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: fixtureSource('symbol Right : TYPE;')
            },
            {
                order: 2,
                symbol: leftHead,
                type: functionType(leftType, leftType),
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: fixtureSource(
                    'symbol left_head (x : Left) : Left;'
                )
            },
            {
                order: 3,
                symbol: rightValue,
                type: { tag: 'global' as const, symbol: rightType },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: fixtureSource(
                    'symbol right_value : Right;'
                )
            }
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const declarationPolicy = createCoreLfTransferPolicyOverlay(
        declarationModule,
        {
            revision: 'proof-subject-runtime-declaration-policy-1',
            moduleRevision: declarationModule.revision,
            entries: declarationModule.declarations.map(
                (declaration, order) => ({
                    order,
                    target: {
                        kind: 'declaration' as const,
                        symbol: declaration.symbol
                    },
                    policy: 'opaque-signature' as const,
                    evidence: 'proof-subject runtime fixture'
                })
            )
        }
    );
    const linkage = createCoreLfTransferDeclarationLinkage(
        declarationModule,
        {
            revision: 'proof-subject-runtime-linkage-1',
            moduleRevision: declarationModule.revision,
            entries: declarationModule.declarations.map(
                (declaration, order) => ({
                    order,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `proof_subject_fixture_${declaration.symbol.name}`,
                    backendName: declaration.symbol.name
                })
            )
        }
    );
    const declarations = compileCoreLfDeclarations(
        declarationModule,
        declarationPolicy,
        linkage
    );

    const proofBuilder = new CoreLfTransferScopedBuilder();
    const proofRule = {
        order: 0,
        id: 'fixture.proof-subject.types',
        sourceOwner: leftType,
        variables: [],
        problem: {
            left: proofBuilder.pattern(proofBuilder.global(leftType)),
            right: proofBuilder.pattern(proofBuilder.global(rightType))
        },
        generatedConstraints: [{
            left: proofBuilder.template(proofBuilder.global(leftType)),
            right: proofBuilder.template(proofBuilder.global(leftType))
        }],
        provenance: fixtureSource(
            'unif_rule Left ≡ Right ↪ [Left ≡ Left];'
        )
    };
    const proofModule = createCoreLfModuleSpec({
        revision: 'proof-subject-runtime-proof-1',
        moduleId: fixtureModuleId,
        fragmentId: 'proof-subject-runtime-proof',
        authorityPath: 'tests/fixtures/generic_runtime.lp',
        sourceSha256:
            'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
        dependencies: [],
        externalSymbols: [leftType, rightType].map(symbol => ({
            symbol,
            availability: 'earlier-fragment' as const
        })),
        declarations: [],
        inductives: [],
        runtimeRules: [],
        proofRules: [proofRule]
    });
    const proofPolicy = createCoreLfTransferPolicyOverlay(
        proofModule,
        {
            revision: 'proof-subject-runtime-proof-policy-1',
            moduleRevision: proofModule.revision,
            entries: [{
                order: 0,
                target: {
                    kind: 'proof-rule' as const,
                    id: proofRule.id
                },
                policy: 'proof-unification' as const,
                evidence: 'proof-subject runtime fixture'
            }]
        }
    );
    const proofProgram = compileCoreLfProofProgram(
        proofModule,
        proofPolicy,
        declarations
    );

    const runtimeBuilder = new CoreLfTransferScopedBuilder();
    const runtimeRule = {
        order: 0,
        id: 'fixture.proof-subject.evaluate',
        groupId: 'fixture.proof-subject.evaluate',
        clauseOrder: 0,
        sourceOwner: leftHead,
        variables: [{
            name: 'x',
            type: runtimeBuilder.template(
                runtimeBuilder.global(leftType)
            )
        }],
        left: runtimeBuilder.pattern(runtimeBuilder.call(
            runtimeBuilder.global(leftHead),
            [{
                plicity: 'explicit' as const,
                value: runtimeBuilder.capture('x')
            }]
        )),
        right: runtimeBuilder.template(
            runtimeBuilder.global(rightValue)
        ),
        provenance: fixtureSource(
            'rule left_head $x ↪ right_value;'
        )
    };
    const module = createCoreLfModuleSpec({
        revision: 'proof-subject-runtime-rules-1',
        moduleId: fixtureModuleId,
        fragmentId: 'proof-subject-runtime-rules',
        authorityPath: 'tests/fixtures/generic_runtime.lp',
        sourceSha256:
            'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
        dependencies: [],
        externalSymbols: [
            leftType,
            leftHead,
            rightValue
        ].map(symbol => ({
            symbol,
            availability: 'earlier-fragment' as const
        })),
        declarations: [],
        inductives: [],
        runtimeRules: [runtimeRule],
        proofRules: []
    });
    return {
        declarations,
        module,
        policy: runtimePolicy(
            module,
            'proof-subject-runtime-policy-1'
        ),
        proofProgram,
        expectation: {
            runtimeRuleId: runtimeRule.id,
            proofRuleIds: [proofRule.id]
        }
    };
};

const replaceRuntimeRules = (
    fixture: GenericRuntimeFixture,
    revision: string,
    runtimeRules: readonly CoreLfTransferRuntimeRule[],
    externalSymbols = fixture.module.externalSymbols
): GenericRuntimeFixture => {
    const module = createCoreLfModuleSpec({
        ...fixture.module,
        revision,
        externalSymbols,
        runtimeRules
    });
    return {
        declarations: fixture.declarations,
        module,
        policy: runtimePolicy(module, `${revision}-policy`)
    };
};

let exactTransfer:
    ReturnType<typeof compileCoreDirectedContinuationRuntimeTransfer> |
    undefined;

const reviewedTransfer = () => {
    exactTransfer ??=
        compileCoreDirectedContinuationRuntimeTransfer();
    return exactTransfer;
};

describe('SCALE-0D generic LF runtime compiler', () => {
    it('strictly checks and executes an unrelated two-rule fixture', () => {
        const fixture = genericRuntimeFixture();
        const runtime = compileCoreLfRuntimeProgram(
            fixture.module,
            fixture.policy,
            fixture.declarations
        );
        assert.deepEqual(
            runtime.rules.map(rule => rule.subjectValidation.kind),
            ['typescript-checked', 'typescript-checked']
        );

        const source = provenance('derived', 'generic runtime witness');
        const witness = kernelFree('runtime_fixture_zero', source);
        const first = runtime.instantiateRuleLeft(
            runtime.rules[0],
            [witness],
            source
        );
        const firstResult = runtime.rewriteHead(first);
        assert.equal(firstResult.status, 'rewritten');
        if (firstResult.status === 'rewritten') {
            assert.equal(firstResult.ruleId, 'fixture.identity.evaluate');
            assert.equal(
                kernelExpressionEquals(firstResult.after, witness),
                true
            );
        }

        const second = runtime.instantiateRuleLeft(
            runtime.rules[1],
            [witness],
            source
        );
        const secondResult = runtime.rewriteHead(second);
        assert.equal(secondResult.status, 'rewritten');
        if (secondResult.status === 'rewritten') {
            assert.equal(secondResult.ruleId, 'fixture.beneath.evaluate');
            assert.equal(
                kernelExpressionEquals(secondResult.after, witness),
                true
            );
        }
    });

    it('matches open ambient terms and binder-independent captures', () => {
        const fixture = genericRuntimeFixture();
        const runtime = compileCoreLfRuntimeProgram(
            fixture.module,
            fixture.policy,
            fixture.declarations
        );
        const source = provenance('derived', 'open runtime witness');
        const openIdentity = kernelBound(0, source);
        const identityLink =
            fixture.declarations.declaration(identity)?.link;
        assert.equal(identityLink?.kind, 'free-declaration');
        if (identityLink?.kind !== 'free-declaration') return;
        const openRedex = kernelCall(
            kernelFree(identityLink.coreName, source),
            [{
                plicity: 'explicit' as const,
                value: openIdentity
            }],
            source
        );
        const rewritten = runtime.rewriteHead(openRedex);
        assert.equal(rewritten.status, 'rewritten');
        if (rewritten.status === 'rewritten') {
            assert.equal(
                kernelExpressionEquals(
                    rewritten.after,
                    openIdentity
                ),
                true
            );
            assert.equal(
                kernelExpressionEquals(
                    rewritten.match.bindings[0],
                    openIdentity
                ),
                true
            );
        }
    });

    it('rejects plicity drift, source-owner drift, and bad groups', () => {
        const fixture = genericRuntimeFixture();
        const first = fixture.module.runtimeRules[0];
        assert.equal(first.left.tag, 'call');
        if (first.left.tag !== 'call') return;
        const badPlicity = replaceRuntimeRules(
            fixture,
            'generic-runtime-bad-plicity-1',
            [{
                ...first,
                left: {
                    ...first.left,
                    arguments: [{
                        ...first.left.arguments[0],
                        plicity: 'implicit'
                    }]
                }
            }]
        );
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                badPlicity.module,
                badPlicity.policy,
                badPlicity.declarations
            ),
            'INVALID_RUNTIME_APPLICATION'
        );

        const foreignOwnerModule = {
            ...fixture.module,
            runtimeRules: [{
                ...first,
                sourceOwner: beneath
            }]
        };
        const foreignOwnerPolicy = runtimePolicy(
            foreignOwnerModule,
            'generic-runtime-foreign-owner-policy-1'
        );
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                foreignOwnerModule,
                foreignOwnerPolicy,
                fixture.declarations
            ),
            'SOURCE_OWNER_MISMATCH'
        );

        const badGroups = replaceRuntimeRules(
            fixture,
            'generic-runtime-bad-group-1',
            fixture.module.runtimeRules.map((rule, order) => ({
                ...rule,
                groupId: 'fixture.grouped',
                clauseOrder: order === 0 ? 0 : 2
            }))
        );
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                badGroups.module,
                badGroups.policy,
                badGroups.declarations
            ),
            'INVALID_RUNTIME_GROUP'
        );
    });

    it('rejects missing policy and a non-preserving strict rule', () => {
        const fixture = genericRuntimeFixture();
        const partialPolicy = createCoreLfTransferPolicyOverlay(
            fixture.module,
            {
                revision: 'generic-runtime-partial-policy-1',
                moduleRevision: fixture.module.revision,
                entries: fixture.policy.entries.slice(0, 1)
            }
        );
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                fixture.module,
                partialPolicy,
                fixture.declarations
            ),
            'INCOMPLETE_RUNTIME_POLICY'
        );

        const first = fixture.module.runtimeRules[0];
        const invalid = replaceRuntimeRules(
            fixture,
            'generic-runtime-invalid-subject-1',
            [{
                ...first,
                right: { tag: 'type' }
            }]
        );
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                invalid.module,
                invalid.policy,
                invalid.declarations
            ),
            'INVALID_RUNTIME_RULE_TYPE'
        );
    });

    it('fails closed on wildcard and higher-order binder capture', () => {
        const fixture = genericRuntimeFixture();
        const wildcardBuilder = new CoreLfTransferScopedBuilder();
        const wildcardLeft = wildcardBuilder.pattern(
            wildcardBuilder.call(
                wildcardBuilder.global(identity),
                [{
                    plicity: 'explicit',
                    value: wildcardBuilder.wildcard()
                }]
            )
        );
        const wildcardTemplate = new CoreLfTransferScopedBuilder();
        const wildcardRight = wildcardTemplate.template(
            wildcardTemplate.global(zero)
        );
        const wildcardRule: CoreLfTransferRuntimeRule = {
            order: 0,
            id: 'fixture.wildcard.evaluate',
            groupId: 'fixture.wildcard.evaluate',
            clauseOrder: 0,
            sourceOwner: identity,
            variables: [],
            left: wildcardLeft,
            right: wildcardRight,
            provenance: fixtureSource(
                'rule identity _ ↪ zero;'
            )
        };
        const wildcard = replaceRuntimeRules(
            fixture,
            'generic-runtime-wildcard-1',
            [wildcardRule],
            [...fixture.module.externalSymbols, {
                symbol: zero,
                availability: 'earlier-fragment'
            }]
        );
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                wildcard.module,
                wildcard.policy,
                wildcard.declarations
            ),
            'UNSUPPORTED_RUNTIME_PATTERN'
        );

        const higherBuilder = new CoreLfTransferScopedBuilder();
        const higherLeft = higherBuilder.pattern(higherBuilder.call(
            higherBuilder.global(beneath),
            [{
                plicity: 'explicit',
                value: higherBuilder.lam(
                    'y',
                    higherBuilder.global(nat),
                    _ => higherBuilder.capture('x', [0])
                )
            }]
        ));
        const higherTemplate = new CoreLfTransferScopedBuilder();
        const higherRight = higherTemplate.template(
            higherTemplate.capture('x')
        );
        const higher = replaceRuntimeRules(
            fixture,
            'generic-runtime-higher-order-1',
            [{
                order: 0,
                id: 'fixture.higher.evaluate',
                groupId: 'fixture.higher.evaluate',
                clauseOrder: 0,
                sourceOwner: beneath,
                variables: [{
                    name: 'x',
                    type: { tag: 'global', symbol: nat }
                }],
                left: higherLeft,
                right: higherRight,
                provenance: fixtureSource(
                    'rule beneath (λ y, $x[y]) ↪ $x;'
                )
            }]
        );
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                higher.module,
                higher.policy,
                higher.declarations
            ),
            'UNSUPPORTED_HIGHER_ORDER_PATTERN'
        );
    });

    it(
        'checks a typed wildcard witness while ignoring that runtime slot',
        () => {
            const fixture = genericRuntimeFixture();
            const pattern = new CoreLfTransferScopedBuilder();
            const left = pattern.pattern(pattern.call(
                pattern.global(identity),
                [{
                    plicity: 'explicit',
                    value: pattern.wildcard(
                        pattern.global(zero)
                    )
                }]
            ));
            const template = new CoreLfTransferScopedBuilder();
            const right = template.template(
                template.global(zero)
            );
            const module = replaceRuntimeRules(
                fixture,
                'generic-runtime-typed-wildcard-1',
                [{
                    order: 0,
                    id: 'fixture.typed-wildcard.evaluate',
                    groupId: 'fixture.typed-wildcard.evaluate',
                    clauseOrder: 0,
                    sourceOwner: identity,
                    variables: [],
                    left,
                    right,
                    provenance: fixtureSource(
                        'rule identity _ ↪ zero;'
                    )
                }],
                [...fixture.module.externalSymbols, {
                    symbol: zero,
                    availability: 'earlier-fragment'
                }]
            );
            const runtime = compileCoreLfRuntimeProgram(
                module.module,
                module.policy,
                module.declarations
            );

            assert.equal(
                runtime.rules[0].subjectValidation.kind,
                'typescript-checked'
            );
            const identityLink =
                fixture.declarations.declaration(identity)?.link;
            const zeroLink =
                fixture.declarations.declaration(zero)?.link;
            assert.equal(identityLink?.kind, 'free-declaration');
            assert.equal(zeroLink?.kind, 'free-declaration');
            if (
                identityLink?.kind !== 'free-declaration' ||
                zeroLink?.kind !== 'free-declaration'
            ) {
                return;
            }
            const nodeProvenance = provenance(
                'derived',
                'typed wildcard runtime redex'
            );
            const redex = kernelCall(
                kernelFree(identityLink.coreName, nodeProvenance),
                [{
                    plicity: 'explicit',
                    value: kernelFree(
                        zeroLink.coreName,
                        nodeProvenance
                    )
                }],
                nodeProvenance
            );
            const rewritten = runtime.rewriteHead(redex);
            assert.equal(rewritten.status, 'rewritten');
            if (rewritten.status !== 'rewritten') return;
            assert.equal(
                rewritten.ruleId,
                'fixture.typed-wildcard.evaluate'
            );
            assert.equal(
                kernelExpressionEquals(
                    rewritten.after,
                    kernelFree(zeroLink.coreName, nodeProvenance)
                ),
                true
            );
            assertDeepFrozen(runtime.rules[0]);
        }
    );

    it('uses exact proof rules only for selected inferred subjects', () => {
        const fixture = proofSubjectRuntimeFixture();
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                fixture.module,
                fixture.policy,
                fixture.declarations
            ),
            'INVALID_RUNTIME_RULE_TYPE'
        );
        const runtime = compileCoreLfRuntimeProgram(
            fixture.module,
            fixture.policy,
            fixture.declarations,
            {
                subjectReductionProof: {
                    program: fixture.proofProgram,
                    rules: [fixture.expectation]
                }
            }
        );
        assert.equal(
            runtime.rules[0].subjectValidation.kind,
            'typescript-proof-checked'
        );
        assert.deepEqual(
            runtime.rules[0].subjectValidation.kind ===
                'typescript-proof-checked'
                ? runtime.rules[0].subjectValidation.proofRuleIds
                : [],
            ['fixture.proof-subject.types']
        );
        assertDeepFrozen(runtime.rules[0].subjectValidation);
    });

    it('makes subject-proof expectations exact and self-invalidating', () => {
        const fixture = proofSubjectRuntimeFixture();
        const generic = genericRuntimeFixture();
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                generic.module,
                generic.policy,
                generic.declarations,
                {
                    subjectReductionProof: {
                        program: fixture.proofProgram,
                        rules: [{
                            runtimeRuleId: 'fixture.identity.evaluate',
                            proofRuleIds: [
                                'fixture.proof-subject.types'
                            ]
                        }]
                    }
                }
            ),
            'INVALID_RUNTIME_SUBJECT_PROOF'
        );
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                fixture.module,
                fixture.policy,
                fixture.declarations,
                {
                    subjectReductionProof: {
                        program: fixture.proofProgram,
                        rules: [{
                            ...fixture.expectation,
                            proofRuleIds: ['fixture.unknown-proof']
                        }]
                    }
                }
            ),
            'INVALID_RUNTIME_SUBJECT_PROOF'
        );
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                fixture.module,
                fixture.policy,
                fixture.declarations,
                {
                    subjectReductionProof: {
                        program: fixture.proofProgram,
                        rules: [fixture.expectation]
                    },
                    subjectReductionOracle: {
                        authorityPath: fixture.module.authorityPath,
                        ruleIds: [fixture.expectation.runtimeRuleId],
                        evidence: 'deliberate overlap'
                    }
                }
            ),
            'INVALID_RUNTIME_SUBJECT_PROOF'
        );

        const foreign = proofSubjectRuntimeFixture();
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                fixture.module,
                fixture.policy,
                fixture.declarations,
                {
                    subjectReductionProof: {
                        program: foreign.proofProgram,
                        rules: [fixture.expectation]
                    }
                }
            ),
            'INVALID_RUNTIME_SUBJECT_PROOF'
        );
    });

    it('makes subject-oracle exceptions exact and self-invalidating', () => {
        const fixture = genericRuntimeFixture();
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                fixture.module,
                fixture.policy,
                fixture.declarations,
                {
                    subjectReductionOracle: {
                        authorityPath: fixture.module.authorityPath,
                        ruleIds: ['fixture.identity.evaluate'],
                        evidence: 'deliberately stale fixture exception'
                    }
                }
            ),
            'INVALID_RUNTIME_SUBJECT_ORACLE'
        );
        expectRuntimeError(
            () => compileCoreLfRuntimeProgram(
                fixture.module,
                fixture.policy,
                fixture.declarations,
                {
                    subjectReductionOracle: {
                        authorityPath: 'tests/fixtures/foreign.lp',
                        ruleIds: [],
                        evidence: 'foreign fixture exception'
                    }
                }
            ),
            'INVALID_RUNTIME_SUBJECT_ORACLE'
        );
    });
});

describe('SCALE-0D reviewed ten-rule runtime migration', () => {
    it('reaches one generic 29-declaration/ten-rule fixed point', () => {
        const transfer = reviewedTransfer();
        const rebuilt =
            compileCoreDirectedContinuationRuntimeTransfer();
        assert.notEqual(transfer, rebuilt);
        assert.equal(
            JSON.stringify(transfer.runtime.rules),
            JSON.stringify(rebuilt.runtime.rules)
        );
        assert.equal(
            transfer.declarations.environment.declarations.length,
            9
        );
        assert.deepEqual(
            transfer.runtime.ruleIds,
            CORE_DIRECTED_GRADUATION_MANIFEST.runtimeRules.map(
                rule => rule.id
            )
        );
        assert.equal(
            transfer.runtime instanceof CoreLfCompiledRuntimeProgram,
            true
        );
        assert.deepEqual(
            transfer.runtime.rules.map(
                rule => rule.checkedWithEarlierRuleIds
            ),
            transfer.runtime.rules.map((_, index) =>
                transfer.runtime.ruleIds.slice(0, index)
            )
        );
    });

    it('preserves the exact standalone subject-reduction boundary', () => {
        const transfer = reviewedTransfer();
        assert.deepEqual(
            transfer.runtime.rules
                .filter(rule =>
                    rule.subjectValidation.kind ===
                        'external-oracle-required'
                )
                .map(rule => rule.id),
            CORE_DIRECTED_CONTINUATION_RUNTIME_SUBJECT_ORACLE.ruleIds
        );
        assert.deepEqual(
            transfer.runtime.rules
                .filter(rule =>
                    rule.subjectValidation.kind ===
                        'typescript-checked'
                )
                .map(rule => rule.id),
            transfer.runtime.ruleIds.slice(0, 6)
        );
        assert.equal(
            CORE_DIRECTED_CONTINUATION_RUNTIME_SUBJECT_ORACLE
                .authorityPath,
            CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE
                .authorityPath
        );
    });

    it('matches all ten legacy rewrites and their exact near misses', () => {
        assert.doesNotThrow(() =>
            validateCoreDirectedContinuationRuntimeTransferEquivalence(
                reviewedTransfer()
            )
        );
    });

    it('pins source/export evidence, policy coverage, and immutability', () => {
        assert.equal(
            CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE
                .runtimeRules.length,
            10
        );
        assert.equal(
            CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_POLICY.entries
                .length,
            10
        );
        assert.equal(
            CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE
                .sourceSha256,
            'sha256:c09f503aff20cb3f9f5b59fcb1dbb4339bdfa853b48931ebd0dcce9b827ef29f'
        );
        assert.equal(
            CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE
                .canonicalExport?.sha256,
            'sha256:91f0deb710b93acc55aa3a6f947505de973b9deaa94d68e1a213037dfcc9c3d3'
        );
        assertDeepFrozen(
            CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_MODULE
        );
        assertDeepFrozen(
            CORE_DIRECTED_CONTINUATION_RUNTIME_TRANSFER_POLICY
        );
        assertDeepFrozen(reviewedTransfer().runtime);
    });

    it('keeps the compiler owner-agnostic and out of the browser API', () => {
        const source = readFileSync(
            resolve(
                repositoryRoot,
                'src/v3_2/lf_transfer_runtime.ts'
            ),
            'utf8'
        );
        assert.doesNotMatch(
            source,
            /sigma|directed|functor-hom|transfor/u
        );
        assert.equal(
            'compileCoreLfRuntimeProgram' in browser,
            false
        );
        assert.equal(
            'compileCoreDirectedContinuationRuntimeTransfer' in browser,
            false
        );
    });
});
