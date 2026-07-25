/**
 * Focused SCALE-0E tests for generic proof-time unification compilation and
 * bounded comparison. All executable rules here are representation-only
 * fixtures; no active emdash proof rule is promoted.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CoreElaborationSession,
    CoreLfCompiledProofProgram,
    CoreLfModuleSpec,
    CoreLfProofCompilerError,
    CoreLfTransferPolicyOverlay,
    CoreLfTransferProofRule,
    CoreLfTransferScopedBuilder,
    KernelExpression,
    compileCoreLfDeclarations,
    compileCoreLfProofProgram,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    createCoreLfModuleSpec,
    createCoreLfTransferDeclarationLinkage,
    createCoreLfTransferPolicyOverlay,
    kernelExpressionEquals,
    kernelFree,
    provenance
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

const expectProofError = (
    action: () => unknown,
    code: CoreLfProofCompilerError['code']
): void => {
    assert.throws(
        action,
        error =>
            error instanceof CoreLfProofCompilerError &&
            error.code === code
    );
};

const fixtureModuleId = 'fixture.generic_proof';
const nat = coreLfQualifiedSymbol(fixtureModuleId, 'Nat');
const code = coreLfQualifiedSymbol(fixtureModuleId, 'Code');
const zero = coreLfQualifiedSymbol(fixtureModuleId, 'zero');
const one = coreLfQualifiedSymbol(fixtureModuleId, 'one');
const leftHead = coreLfQualifiedSymbol(fixtureModuleId, 'left_head');
const rightHead = coreLfQualifiedSymbol(fixtureModuleId, 'right_head');
const bridgeLeft =
    coreLfQualifiedSymbol(fixtureModuleId, 'bridge_left');
const bridgeRight =
    coreLfQualifiedSymbol(fixtureModuleId, 'bridge_right');

const fixtureSource = (sourceFragment: string) => ({
    authorityPath: 'tests/fixtures/generic_proof.lp',
    sourceFragment
});

const declarationModifiers = {
    visibility: 'public' as const,
    rigidity: 'ordinary' as const,
    sourceOpacity: 'opaque' as const
};

const functionType = (
    argumentType: typeof nat,
    resultType: typeof code
) => {
    const builder = new CoreLfTransferScopedBuilder();
    return builder.term(builder.pi(
        'x',
        builder.global(argumentType),
        _ => builder.global(resultType)
    ));
};

interface GenericProofFixture {
    readonly declarations: ReturnType<typeof compileCoreLfDeclarations>;
    readonly module: CoreLfModuleSpec;
    readonly policy: CoreLfTransferPolicyOverlay;
}

const proofPolicy = (
    module: CoreLfModuleSpec,
    revision: string
): CoreLfTransferPolicyOverlay =>
    createCoreLfTransferPolicyOverlay(module, {
        revision,
        moduleRevision: module.revision,
        entries: module.proofRules.map((rule, order) => ({
            order,
            target: {
                kind: 'proof-rule' as const,
                id: rule.id
            },
            policy: 'proof-unification' as const,
            evidence: 'generic proof fixture'
        }))
    });

const proofCall = (
    builder: CoreLfTransferScopedBuilder,
    head: typeof leftHead,
    captureName: string
) => builder.call(
    builder.global(head),
    [{
        plicity: 'explicit',
        value: builder.capture(captureName)
    }]
);

const genericProofFixture = (): GenericProofFixture => {
    const declarationModule = createCoreLfModuleSpec({
        revision: 'generic-proof-declarations-1',
        moduleId: fixtureModuleId,
        fragmentId: 'generic-proof-declarations',
        authorityPath: 'tests/fixtures/generic_proof.lp',
        sourceSha256:
            'sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb',
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
                symbol: code,
                type: { tag: 'type' },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: fixtureSource('symbol Code : TYPE;')
            },
            {
                order: 2,
                symbol: zero,
                type: { tag: 'global', symbol: nat },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: fixtureSource('symbol zero : Nat;')
            },
            {
                order: 3,
                symbol: one,
                type: { tag: 'global', symbol: nat },
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: fixtureSource('symbol one : Nat;')
            },
            ...[
                leftHead,
                rightHead,
                bridgeLeft,
                bridgeRight
            ].map((symbol, index) => ({
                order: index + 4,
                symbol,
                type: functionType(nat, code),
                body: coreLfTransferAbsentBody(),
                modifiers: declarationModifiers,
                provenance: fixtureSource(
                    `symbol ${symbol.name} (x : Nat) : Code;`
                )
            }))
        ],
        inductives: [],
        runtimeRules: [],
        proofRules: []
    });
    const declarationPolicy = createCoreLfTransferPolicyOverlay(
        declarationModule,
        {
            revision: 'generic-proof-declaration-policy-1',
            moduleRevision: declarationModule.revision,
            entries: declarationModule.declarations.map(
                (declaration, order) => ({
                    order,
                    target: {
                        kind: 'declaration' as const,
                        symbol: declaration.symbol
                    },
                    policy: 'opaque-signature' as const,
                    evidence: 'generic proof declaration fixture'
                })
            )
        }
    );
    const linkage = createCoreLfTransferDeclarationLinkage(
        declarationModule,
        {
            revision: 'generic-proof-linkage-1',
            moduleRevision: declarationModule.revision,
            entries: declarationModule.declarations.map(
                (declaration, order) => ({
                    order,
                    symbol: declaration.symbol,
                    kind: 'free-declaration' as const,
                    coreName:
                        `proof_fixture_${declaration.symbol.name}`,
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

    const inject = new CoreLfTransferScopedBuilder();
    const injectTemplate = new CoreLfTransferScopedBuilder();
    const fresh = new CoreLfTransferScopedBuilder();
    const freshTemplate = new CoreLfTransferScopedBuilder();
    const module = createCoreLfModuleSpec({
        revision: 'generic-proof-rules-1',
        moduleId: fixtureModuleId,
        fragmentId: 'generic-proof-rules',
        authorityPath: 'tests/fixtures/generic_proof.lp',
        sourceSha256:
            'sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb',
        dependencies: [],
        externalSymbols: [
            nat,
            leftHead,
            rightHead,
            bridgeLeft,
            bridgeRight
        ].map(symbol => ({
            symbol,
            availability: 'earlier-fragment' as const
        })),
        declarations: [],
        inductives: [],
        runtimeRules: [],
        proofRules: [
            {
                order: 0,
                id: 'fixture.heads.inject',
                sourceOwner: leftHead,
                variables: ['x', 'y'].map(name => ({
                    name,
                    role: 'matched' as const,
                    type: { tag: 'global' as const, symbol: nat }
                })),
                problem: {
                    left: inject.pattern(proofCall(
                        inject,
                        leftHead,
                        'x'
                    )),
                    right: inject.pattern(proofCall(
                        inject,
                        rightHead,
                        'y'
                    ))
                },
                generatedConstraints: [{
                    left: injectTemplate.template(
                        injectTemplate.capture('x')
                    ),
                    right: injectTemplate.template(
                        injectTemplate.capture('y')
                    )
                }],
                provenance: fixtureSource(
                    'unif_rule left_head $x ≡ right_head $y ↪ ' +
                        '[ $x ≡ $y ];'
                )
            },
            {
                order: 1,
                id: 'fixture.bridge.fresh',
                sourceOwner: bridgeLeft,
                variables: [
                    {
                        name: 'x',
                        role: 'matched' as const,
                        type: {
                            tag: 'global' as const,
                            symbol: nat
                        }
                    },
                    {
                        name: 'y',
                        role: 'matched' as const,
                        type: {
                            tag: 'global' as const,
                            symbol: nat
                        }
                    },
                    {
                        name: 'middle',
                        role: 'fresh-constraint' as const,
                        type: {
                            tag: 'global' as const,
                            symbol: nat
                        }
                    }
                ],
                problem: {
                    left: fresh.pattern(proofCall(
                        fresh,
                        bridgeLeft,
                        'x'
                    )),
                    right: fresh.pattern(proofCall(
                        fresh,
                        bridgeRight,
                        'y'
                    ))
                },
                generatedConstraints: [
                    {
                        left: freshTemplate.template(
                            freshTemplate.capture('middle')
                        ),
                        right: freshTemplate.template(
                            freshTemplate.capture('x')
                        )
                    },
                    {
                        left: freshTemplate.template(
                            freshTemplate.capture('middle')
                        ),
                        right: freshTemplate.template(
                            freshTemplate.capture('y')
                        )
                    }
                ],
                provenance: fixtureSource(
                    'unif_rule bridge_left $x ≡ bridge_right $y ↪ ' +
                        '[ $middle ≡ $x; $middle ≡ $y ];'
                )
            }
        ]
    });
    return {
        declarations,
        module,
        policy: proofPolicy(module, 'generic-proof-policy-1')
    };
};

const replaceProofRules = (
    fixture: GenericProofFixture,
    revision: string,
    proofRules: readonly CoreLfTransferProofRule[],
    externalSymbols = fixture.module.externalSymbols
): GenericProofFixture => {
    const module = createCoreLfModuleSpec({
        ...fixture.module,
        revision,
        externalSymbols,
        proofRules
    });
    return {
        declarations: fixture.declarations,
        module,
        policy: proofPolicy(module, `${revision}-policy`)
    };
};

const coreName = (
    fixture: GenericProofFixture,
    symbol: typeof nat
): string => {
    const link = fixture.declarations.declaration(symbol)?.link;
    assert.equal(link?.kind, 'free-declaration');
    if (link?.kind !== 'free-declaration') {
        assert.fail(`Missing fixture free declaration ${symbol.name}`);
    }
    return link.coreName;
};

const fixtureTerm = (
    fixture: GenericProofFixture,
    symbol: typeof nat
) => kernelFree(
    coreName(fixture, symbol),
    provenance('derived', `proof fixture ${symbol.name}`)
);

const fixtureApplication = (
    fixture: GenericProofFixture,
    symbol: typeof leftHead,
    argument: KernelExpression
) => fixture.declarations.application(
    symbol,
    [argument],
    provenance('derived', `proof fixture ${symbol.name} application`)
);

describe('SCALE-0E generic LF proof-time compiler', () => {
    it('strictly compiles an unrelated ordered two-rule program', () => {
        const fixture = genericProofFixture();
        const program = compileCoreLfProofProgram(
            fixture.module,
            fixture.policy,
            fixture.declarations
        );
        assert.equal(program instanceof CoreLfCompiledProofProgram, true);
        assert.deepEqual(program.ruleIds, [
            'fixture.heads.inject',
            'fixture.bridge.fresh'
        ]);
        assert.deepEqual(
            program.rules.map(rule => rule.typingValidation.kind),
            ['typescript-checked', 'typescript-checked']
        );
        assert.deepEqual(
            program.rules.map(rule =>
                rule.checkedWithEarlierRuleIds
            ),
            [[], ['fixture.heads.inject']]
        );
        assert.equal(Object.isFrozen(program), true);
        assertDeepFrozen(program.rules);
        assertDeepFrozen(program.module);
        assertDeepFrozen(program.policy);
    });

    it('matches symmetrically and solves generated meta constraints', () => {
        const fixture = genericProofFixture();
        const program = compileCoreLfProofProgram(
            fixture.module,
            fixture.policy,
            fixture.declarations
        );
        const session = new CoreElaborationSession(
            fixture.declarations.environment.coreEnvironment
        );
        const natType = fixtureTerm(fixture, nat);
        const meta = session.freshMeta(
            session.rootContext,
            natType,
            provenance('derived', 'proof fixture input meta')
        );
        const zeroTerm = fixtureTerm(fixture, zero);
        const result = program.compare(
            fixtureApplication(fixture, rightHead, zeroTerm),
            fixtureApplication(fixture, leftHead, meta),
            { session, stepLimit: 16 }
        );
        assert.equal(result.status, 'solved');
        assert.equal(
            kernelExpressionEquals(session.zonk(meta), zeroTerm),
            true
        );
        assert.deepEqual(
            result.ruleApplications.map(application => [
                application.ruleId,
                application.orientation
            ]),
            [['fixture.heads.inject', 'symmetric']]
        );
        assert.deepEqual(
            result.trace.map(entry => entry.kind),
            ['proof-rule', 'meta-assignment']
        );
    });

    it('allocates RHS-only metas in order and preserves stuck evidence', () => {
        const fixture = genericProofFixture();
        const program = compileCoreLfProofProgram(
            fixture.module,
            fixture.policy,
            fixture.declarations
        );
        const zeroTerm = fixtureTerm(fixture, zero);
        const oneTerm = fixtureTerm(fixture, one);
        const solved = program.compare(
            fixtureApplication(fixture, bridgeLeft, zeroTerm),
            fixtureApplication(fixture, bridgeRight, zeroTerm),
            { stepLimit: 16 }
        );
        assert.equal(solved.status, 'solved');
        assert.equal(solved.ruleApplications.length, 1);
        assert.deepEqual(
            solved.ruleApplications[0].freshMetavariables.map(
                fresh => fresh.name
            ),
            ['middle']
        );
        assert.deepEqual(solved.resolutionOrder, [0, 1, 2]);

        const stuck = program.compare(
            fixtureApplication(fixture, bridgeLeft, zeroTerm),
            fixtureApplication(fixture, bridgeRight, oneTerm),
            { stepLimit: 16 }
        );
        assert.equal(stuck.status, 'stuck');
        if (stuck.status === 'stuck') {
            assert.equal(stuck.reason, 'no-proof-rule');
            assert.equal(stuck.problemId, 2);
        }
        assert.equal(stuck.ruleApplications.length, 1);
        assert.equal(stuck.metavariables.length, 1);
    });

    it('uses one shared bound for recursive proof-rule application', () => {
        const fixture = genericProofFixture();
        const source = fixture.module.proofRules[0];
        const cyclic = replaceProofRules(
            fixture,
            'generic-proof-cycle-1',
            [{
                ...source,
                id: 'fixture.heads.cycle',
                generatedConstraints: [{
                    left: source.problem.left,
                    right: source.problem.right
                }],
                provenance: fixtureSource(
                    'unif_rule left_head $x ≡ right_head $y ↪ ' +
                        '[ left_head $x ≡ right_head $y ];'
                )
            }]
        );
        const program = compileCoreLfProofProgram(
            cyclic.module,
            cyclic.policy,
            cyclic.declarations
        );
        const result = program.compare(
            fixtureApplication(
                cyclic,
                leftHead,
                fixtureTerm(cyclic, zero)
            ),
            fixtureApplication(
                cyclic,
                rightHead,
                fixtureTerm(cyclic, one)
            ),
            { stepLimit: 2 }
        );
        assert.equal(result.status, 'step-limit-exceeded');
        if (result.status === 'step-limit-exceeded') {
            assert.deepEqual(result.next, {
                kind: 'proof-rule',
                ruleId: 'fixture.heads.cycle',
                orientation: 'forward'
            });
        }
        assert.equal(result.steps, 2);
    });

    it('rejects incomplete policy and malformed applications', () => {
        const fixture = genericProofFixture();
        const partialPolicy = createCoreLfTransferPolicyOverlay(
            fixture.module,
            {
                revision: 'generic-proof-partial-policy-1',
                moduleRevision: fixture.module.revision,
                entries: fixture.policy.entries.slice(0, 1)
            }
        );
        expectProofError(
            () => compileCoreLfProofProgram(
                fixture.module,
                partialPolicy,
                fixture.declarations
            ),
            'INCOMPLETE_PROOF_POLICY'
        );

        const source = fixture.module.proofRules[0];
        assert.equal(source.problem.left.tag, 'call');
        if (source.problem.left.tag !== 'call') return;
        const badPlicity = replaceProofRules(
            fixture,
            'generic-proof-bad-plicity-1',
            [{
                ...source,
                problem: {
                    ...source.problem,
                    left: {
                        ...source.problem.left,
                        arguments: [{
                            ...source.problem.left.arguments[0],
                            plicity: 'implicit'
                        }]
                    }
                }
            }]
        );
        expectProofError(
            () => compileCoreLfProofProgram(
                badPlicity.module,
                badPlicity.policy,
                badPlicity.declarations
            ),
            'INVALID_PROOF_APPLICATION'
        );
    });

    it('rejects ill-typed generated constraints', () => {
        const fixture = genericProofFixture();
        const source = fixture.module.proofRules[0];
        const template = new CoreLfTransferScopedBuilder();
        const invalid = replaceProofRules(
            fixture,
            'generic-proof-invalid-type-1',
            [{
                ...source,
                generatedConstraints: [{
                    left: template.template(template.capture('x')),
                    right: template.template(template.call(
                        template.global(leftHead),
                        [{
                            plicity: 'explicit',
                            value: template.capture('x')
                        }]
                    ))
                }]
            }]
        );
        expectProofError(
            () => compileCoreLfProofProgram(
                invalid.module,
                invalid.policy,
                invalid.declarations
            ),
            'INVALID_PROOF_RULE_TYPE'
        );
    });

    it('fails closed on wildcard and higher-order proof patterns', () => {
        const fixture = genericProofFixture();
        const source = fixture.module.proofRules[0];
        assert.equal(source.problem.left.tag, 'call');
        if (source.problem.left.tag !== 'call') return;
        const wildcard = replaceProofRules(
            fixture,
            'generic-proof-wildcard-1',
            [{
                ...source,
                variables: [source.variables[1]],
                problem: {
                    ...source.problem,
                    left: {
                        ...source.problem.left,
                        arguments: [{
                            plicity: 'explicit',
                            value: { tag: 'wildcard' }
                        }]
                    }
                },
                generatedConstraints: [{
                    left: {
                        tag: 'capture',
                        name: 'y'
                    },
                    right: {
                        tag: 'capture',
                        name: 'y'
                    }
                }]
            }]
        );
        expectProofError(
            () => compileCoreLfProofProgram(
                wildcard.module,
                wildcard.policy,
                wildcard.declarations
            ),
            'UNSUPPORTED_PROOF_PATTERN'
        );

        const higher = replaceProofRules(
            fixture,
            'generic-proof-higher-order-1',
            [{
                ...source,
                problem: {
                    ...source.problem,
                    left: {
                        ...source.problem.left,
                        arguments: [{
                            plicity: 'explicit',
                            value: {
                                tag: 'lambda',
                                binder: {
                                    hint: 'z',
                                    mode: {
                                        plicity: 'explicit',
                                        variation: 'functorial'
                                    },
                                    type: {
                                        tag: 'global',
                                        symbol: nat
                                    }
                                },
                                body: {
                                    tag: 'capture',
                                    name: 'x',
                                    allowedBoundIndices: [0]
                                }
                            }
                        }]
                    }
                }
            }]
        );
        expectProofError(
            () => compileCoreLfProofProgram(
                higher.module,
                higher.policy,
                higher.declarations
            ),
            'UNSUPPORTED_HIGHER_ORDER_PATTERN'
        );
    });

    it('makes external typing exceptions exact and self-invalidating', () => {
        const fixture = genericProofFixture();
        expectProofError(
            () => compileCoreLfProofProgram(
                fixture.module,
                fixture.policy,
                fixture.declarations,
                {
                    typingOracle: {
                        authorityPath: fixture.module.authorityPath,
                        ruleIds: ['fixture.heads.inject'],
                        evidence: 'deliberately stale proof exception'
                    }
                }
            ),
            'INVALID_PROOF_TYPING_ORACLE'
        );
        expectProofError(
            () => compileCoreLfProofProgram(
                fixture.module,
                fixture.policy,
                fixture.declarations,
                {
                    typingOracle: {
                        authorityPath: 'tests/fixtures/foreign.lp',
                        ruleIds: [],
                        evidence: 'foreign proof exception'
                    }
                }
            ),
            'INVALID_PROOF_TYPING_ORACLE'
        );
    });

    it('keeps proof rules separate from runtime and browser APIs', () => {
        const fixture = genericProofFixture();
        const program = compileCoreLfProofProgram(
            fixture.module,
            fixture.policy,
            fixture.declarations
        );
        assert.equal('rewriteHead' in program, false);
        assert.equal(
            'compileCoreLfProofProgram' in browser,
            false
        );
        const source = readFileSync(
            resolve(repositoryRoot, 'src/v3_2/lf_transfer_proof.ts'),
            'utf8'
        );
        assert.doesNotMatch(
            source,
            /Hom_cat|Pi_cat|Functord|Transfd|directed/u
        );
        assert.doesNotMatch(
            source,
            /userUnificationRules|addUnificationRule|console\./u
        );
    });
});
