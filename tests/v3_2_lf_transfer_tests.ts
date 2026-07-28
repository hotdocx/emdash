/**
 * Focused SCALE-0B tests for the reviewed typed transfer IR boundary.
 */

import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { describe, it } from 'node:test';
import {
    CORE_DIRECTED_CONTINUATION_PROFILE,
    CORE_LF_SCALE_ARCHITECTURE_REVIEW,
    CORE_MVP_MANIFEST,
    CoreLfModuleSpecInput,
    CoreLfScaleArchitectureReviewError,
    CoreLfScaleArchitectureReviewInput,
    CoreLfTransferError,
    CoreLfTransferExpression,
    CoreLfTransferScopedBuilder,
    binderMode,
    coreLfQualifiedSymbol,
    coreLfTransferAbsentBody,
    coreLfTransferExplicitBody,
    coreLfTransferTacticBody,
    createCoreLfModuleSpec,
    createCoreLfTransferPolicyOverlay,
    validateCoreLfScaleArchitectureReview
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>).forEach(
        assertDeepFrozen
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

const fixtureModule = 'fixture.transfer';
const fixtureBaseModule = 'fixture.base';
const base = coreLfQualifiedSymbol(fixtureBaseModule, 'Base');
const opaque = coreLfQualifiedSymbol(fixtureModule, 'Opaque');
const identity = coreLfQualifiedSymbol(fixtureModule, 'identity');
const tacticProof = coreLfQualifiedSymbol(fixtureModule, 'tactic_proof');
const pair = coreLfQualifiedSymbol(fixtureModule, 'Pair');
const makePair = coreLfQualifiedSymbol(fixtureModule, 'make_pair');
const pairEliminator = coreLfQualifiedSymbol(fixtureModule, 'ind_Pair');

const provenance = (sourceFragment: string) => ({
    authorityPath: 'tests/fixtures/transfer.lp',
    sourceFragment
});

const fixtureInput = (): CoreLfModuleSpecInput => {
    const terms = new CoreLfTransferScopedBuilder();
    const baseTerm = terms.term(terms.global(base));
    const identityType = terms.term(
        terms.pi('x', terms.global(base), _ => terms.global(base))
    );
    const identityBody = terms.term(
        terms.lam('x', terms.global(base), x => x)
    );

    const patterns = new CoreLfTransferScopedBuilder();
    const left = patterns.pattern(patterns.call(
        patterns.global(identity),
        [{
            plicity: 'explicit',
            value: patterns.capture('x')
        }]
    ));
    const right = patterns.template(patterns.capture('x'));

    const proof = new CoreLfTransferScopedBuilder();
    const proofLeft = proof.pattern(proof.call(
        proof.global(identity),
        [{
            plicity: 'explicit',
            value: proof.capture('x')
        }]
    ));
    const proofRight = proof.pattern(proof.capture('x'));
    const freshConstraint = {
        left: proof.template(proof.capture('fresh')),
        right: proof.template(proof.capture('x'))
    };

    return {
        revision: 'fixture-transfer-1',
        moduleId: fixtureModule,
        fragmentId: 'all-mechanisms',
        authorityPath: 'tests/fixtures/transfer.lp',
        sourceSha256:
            'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
        canonicalExport: {
            exporterVersion: 'fixture-exporter-1',
            sha256:
                'sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb'
        },
        dependencies: [fixtureBaseModule],
        externalSymbols: [{
            symbol: base,
            availability: 'dependency-module'
        }],
        declarations: [
            {
                order: 0,
                symbol: opaque,
                type: baseTerm,
                body: coreLfTransferAbsentBody(),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'constant',
                    sourceOpacity: 'opaque'
                },
                provenance: provenance('constant symbol Opaque : Base;')
            },
            {
                order: 1,
                symbol: identity,
                type: identityType,
                body: coreLfTransferExplicitBody(identityBody),
                modifiers: {
                    visibility: 'public',
                    rigidity: 'ordinary',
                    sourceOpacity: 'transparent'
                },
                provenance: provenance(
                    'symbol identity (x : Base) : Base ≔ x;'
                )
            },
            {
                order: 2,
                symbol: tacticProof,
                type: baseTerm,
                body: coreLfTransferTacticBody(
                    'begin\n  exact fixture_witness;\nend'
                ),
                modifiers: {
                    visibility: 'protected',
                    rigidity: 'ordinary',
                    sourceOpacity: 'transparent'
                },
                provenance: provenance(
                    'protected symbol tactic_proof : Base ≔ begin ... end;'
                )
            }
        ],
        inductives: [{
            order: 3,
            symbol: pair,
            parameters: [{
                hint: 'A',
                mode: binderMode('implicit', 'functorial'),
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
                        type: { tag: 'bound', index: 0 }
                    },
                    {
                        hint: 'second',
                        mode: binderMode('explicit', 'functorial'),
                        type: { tag: 'bound', index: 1 }
                    }
                ],
                result: {
                    tag: 'call',
                    callee: {
                        tag: 'global',
                        symbol: pair
                    },
                    arguments: [{
                        plicity: 'implicit',
                        value: { tag: 'bound', index: 2 }
                    }]
                },
                provenance: provenance(
                    '| make_pair [A] (first second : A) : Pair A'
                )
            }],
            generatedSymbols: [pairEliminator],
            modifiers: {
                visibility: 'public',
                rigidity: 'injective',
                sourceOpacity: 'opaque'
            },
            provenance: provenance('inductive Pair [A : TYPE] : TYPE')
        }],
        runtimeRules: [{
            order: 4,
            id: 'fixture.identity.beta',
            groupId: 'fixture.identity',
            clauseOrder: 0,
            sourceOwner: identity,
            variables: [{
                name: 'x',
                type: baseTerm
            }],
            left,
            right,
            provenance: provenance('rule identity $x ↪ $x;')
        }],
        proofRules: [{
            order: 5,
            id: 'fixture.identity.compare',
            sourceOwner: identity,
            variables: [
                {
                    name: 'x',
                    role: 'matched',
                    type: baseTerm
                },
                {
                    name: 'fresh',
                    role: 'fresh-constraint',
                    type: baseTerm
                }
            ],
            problem: {
                left: proofLeft,
                right: proofRight
            },
            generatedConstraints: [freshConstraint],
            provenance: provenance(
                'unif_rule identity $x ≡ $x ↪ [$fresh ≡ $x];'
            )
        }]
    };
};

const activeRepresentativeInput = (): CoreLfModuleSpecInput => {
    const moduleId = 'emdash.emdash3_2';
    const symbol = (name: string) =>
        coreLfQualifiedSymbol(moduleId, name);
    const indEqr = symbol('ind_eqr');
    const eqRefl = symbol('eq_refl');
    const hom = symbol('Hom');
    const object = symbol('Obj');
    const homCategory = symbol('Hom_cat');

    const runtime = new CoreLfTransferScopedBuilder();
    const a = runtime.capture('a');
    const y = runtime.capture('y');
    const u = runtime.capture('u');
    const runtimeLeft = runtime.pattern(runtime.call(
        runtime.global(indEqr),
        [
            { plicity: 'implicit', value: a },
            { plicity: 'implicit', value: y },
            { plicity: 'explicit', value: runtime.wildcard() },
            { plicity: 'explicit', value: u },
            { plicity: 'implicit', value: y },
            {
                plicity: 'explicit',
                value: runtime.call(runtime.global(eqRefl), [
                    { plicity: 'implicit', value: a },
                    { plicity: 'explicit', value: y }
                ])
            }
        ]
    ));

    const proof = new CoreLfTransferScopedBuilder();
    const proofCapture = (name: string) => proof.capture(name);
    const homObject = (
        category: ReturnType<typeof proof.capture>,
        source: ReturnType<typeof proof.capture>,
        target: ReturnType<typeof proof.capture>
    ) => proof.call(proof.global(object), [{
        plicity: 'explicit',
        value: proof.call(proof.global(homCategory), [
            { plicity: 'explicit', value: category },
            { plicity: 'explicit', value: source },
            { plicity: 'explicit', value: target }
        ])
    }]);

    const A = proofCapture('A');
    const X = proofCapture('X');
    const Y = proofCapture('Y');
    const A2 = proofCapture('A2');
    const X2 = proofCapture('X2');
    const Y2 = proofCapture('Y2');
    const type: CoreLfTransferExpression = { tag: 'type' };
    const source = (sourceFragment: string) => ({
        authorityPath: 'emdash2/emdash3_2.lp',
        sourceFragment
    });

    return {
        revision: 'active-mechanism-witness-1',
        moduleId,
        fragmentId: 'scale-representation-witness',
        authorityPath: 'emdash2/emdash3_2.lp',
        sourceSha256:
            'sha256:10638f01b4bd2163b7c7cd254db76d5343b073ddbc7cc7a18c6ca2755c35a91a',
        canonicalExport: {
            exporterVersion: '3.0.0-90-gdb4f780',
            sha256:
                'sha256:c736d3447721ac7a48b6f35f5287734774816283954eb25a35de09c0f0b9c425'
        },
        dependencies: [],
        externalSymbols: [
            indEqr,
            eqRefl,
            hom,
            object,
            homCategory
        ].map(external => ({
            symbol: external,
            availability: 'earlier-fragment' as const
        })),
        declarations: [],
        inductives: [],
        runtimeRules: [{
            order: 0,
            id: 'witness.ind-eqr.reflexivity',
            groupId: 'witness.ind-eqr',
            clauseOrder: 0,
            sourceOwner: indEqr,
            variables: [
                { name: 'a', type },
                { name: 'y', type },
                { name: 'u', type }
            ],
            left: runtimeLeft,
            right: runtime.template(u),
            provenance: source(
                'rule @ind_eqr $a $y _ $u $y ' +
                    '(@eq_refl $a $y) ↪ $u;'
            )
        }],
        proofRules: [{
            order: 1,
            id: 'witness.hom-object.injectivity',
            sourceOwner: hom,
            variables: [
                'A',
                'X',
                'Y',
                'A2',
                'X2',
                'Y2'
            ].map(name => ({
                name,
                role: 'matched' as const,
                type
            })),
            problem: {
                left: proof.pattern(homObject(A, X, Y)),
                right: proof.pattern(homObject(A2, X2, Y2))
            },
            generatedConstraints: [
                {
                    left: proof.template(A),
                    right: proof.template(A2)
                },
                {
                    left: proof.template(X),
                    right: proof.template(X2)
                },
                {
                    left: proof.template(Y),
                    right: proof.template(Y2)
                }
            ],
            provenance: source(
                'unif_rule Obj (Hom_cat $A $X $Y) ≡ ' +
                    "Obj (Hom_cat $A' $X' $Y') ↪ " +
                    "[ $A ≡ $A'; $X ≡ $X'; $Y ≡ $Y' ];"
            )
        }]
    };
};

describe('TypeScript v3.2 reviewed SCALE-0B transfer IR', () => {
    it('records revised H-DTTLF-SCALE-01 without semantic expansion', () => {
        const review = CORE_LF_SCALE_ARCHITECTURE_REVIEW;
        assert.equal(review.gate, 'H-DTTLF-SCALE-01');
        assert.equal(review.decision, 'D-DTTLF-SCALE-001R');
        assert.equal(review.status, 'approved');
        assert.equal(
            review.mandatoryArchitecture.initialProducer,
            'typed-typescript-scoped-builder'
        );
        assert.equal(
            review.canonicalExportRoles.at(-1),
            'optional-later-bulk-parser-or-generator'
        );
        assert.equal(review.productionLambdapiDependency, false);
        assert.deepEqual(review.authorizes, [
            'SCALE-0B-transfer-ir-and-builder',
            'representation-only-conformance-witnesses'
        ]);
        assert.ok(
            review.doesNotAuthorize.includes('canonical-term-parser')
        );
        assert.ok(
            review.doesNotAuthorize.includes('new-proof-time-rule')
        );
        assertDeepFrozen(review);
        assert.doesNotThrow(() =>
            validateCoreLfScaleArchitectureReview()
        );
    });

    it('rejects any expansion of the exact reviewed decision', () => {
        const review = JSON.parse(JSON.stringify(
            CORE_LF_SCALE_ARCHITECTURE_REVIEW
        )) as CoreLfScaleArchitectureReviewInput;
        const changed = {
            ...review,
            productionLambdapiDependency: true
        } as unknown as CoreLfScaleArchitectureReviewInput;
        assert.throws(
            () => validateCoreLfScaleArchitectureReview(changed),
            error =>
                error instanceof CoreLfScaleArchitectureReviewError &&
                error.code === 'INVALID_REVIEW_DECISION'
        );
    });

    it('lowers typed callbacks once to explicit locally nameless syntax', () => {
        const builder = new CoreLfTransferScopedBuilder();
        let outerCalls = 0;
        let innerCalls = 0;
        const expression = builder.term(builder.pi(
            'A',
            builder.type(),
            A => {
                outerCalls++;
                return builder.pi(
                    'x',
                    A,
                    x => {
                        innerCalls++;
                        return x;
                    }
                );
            },
            binderMode('implicit', 'functorial')
        ));

        assert.equal(outerCalls, 1);
        assert.equal(innerCalls, 1);
        assert.equal(expression.tag, 'pi');
        if (expression.tag !== 'pi') return;
        assert.equal(expression.binder.mode.plicity, 'implicit');
        assert.deepEqual(expression.body, {
            tag: 'pi',
            binder: {
                hint: 'x',
                mode: {
                    plicity: 'explicit',
                    variation: 'functorial'
                },
                type: {
                    tag: 'bound',
                    index: 0
                }
            },
            body: {
                tag: 'bound',
                index: 0
            }
        });
        assertDeepFrozen(expression);
    });

    it('desugars let and separates terms, patterns, and templates', () => {
        const builder = new CoreLfTransferScopedBuilder();
        const letTerm = builder.term(builder.let_(
            'x',
            builder.type(),
            builder.type(),
            x => x
        ));
        assert.equal(letTerm.tag, 'call');
        if (letTerm.tag !== 'call') return;
        assert.equal(letTerm.callee.tag, 'lambda');

        const capture = builder.capture('x', []);
        assert.equal(builder.pattern(capture).tag, 'capture');
        assert.equal(builder.template(capture).tag, 'capture');
        assert.equal(builder.pattern(builder.wildcard()).tag, 'wildcard');
        const typedWildcard = builder.pattern(
            builder.wildcard(builder.type())
        );
        assert.deepEqual(typedWildcard, {
            tag: 'wildcard',
            checking: { tag: 'type' }
        });
        assertDeepFrozen(typedWildcard);
        expectTransferError(
            () => builder.term(capture),
            'INVALID_BUILDER_EXPRESSION'
        );
        expectTransferError(
            () => builder.template(builder.wildcard()),
            'INVALID_BUILDER_EXPRESSION'
        );
    });

    it('freezes one module IR with all body and program classes separate', () => {
        const input = fixtureInput();
        const module = createCoreLfModuleSpec(input);
        assert.equal(module.declarations.length, 3);
        assert.deepEqual(
            module.declarations.map(entry => entry.body.kind),
            ['absent', 'explicit-term', 'checked-tactic-source']
        );
        assert.equal(module.inductives.length, 1);
        assert.equal(module.inductives[0].constructors.length, 1);
        assert.equal(module.runtimeRules.length, 1);
        assert.equal(module.proofRules.length, 1);
        assert.ok(
            module.referencedSymbols.some(symbol =>
                symbol.moduleId === fixtureBaseModule &&
                symbol.name === 'Base'
            )
        );
        assertDeepFrozen(module);
        assert.equal(Object.isFrozen(input), false);
        assert.equal(Object.isFrozen(input.declarations), false);
    });

    it('represents nonlinear runtime and proof constraints without owner nodes', () => {
        const module = createCoreLfModuleSpec(
            activeRepresentativeInput()
        );
        const runtime = module.runtimeRules[0];
        const proof = module.proofRules[0];
        const activeSource = readFileSync(module.authorityPath, 'utf8');
        assert.equal(
            'sha256:' + createHash('sha256')
                .update(activeSource)
                .digest('hex'),
            module.sourceSha256
        );
        assert.ok(activeSource.includes(runtime.provenance.sourceFragment));
        assert.ok(activeSource.includes(proof.provenance.sourceFragment));
        assert.equal(runtime.left.tag, 'call');
        assert.equal(runtime.right.tag, 'capture');
        assert.equal(proof.problem.left.tag, 'call');
        assert.equal(proof.generatedConstraints.length, 3);
        assert.deepEqual(
            proof.generatedConstraints.map(constraint => [
                constraint.left,
                constraint.right
            ]),
            [
                [
                    { tag: 'capture', name: 'A' },
                    { tag: 'capture', name: 'A2' }
                ],
                [
                    { tag: 'capture', name: 'X' },
                    { tag: 'capture', name: 'X2' }
                ],
                [
                    { tag: 'capture', name: 'Y' },
                    { tag: 'capture', name: 'Y2' }
                ]
            ]
        );
        assert.deepEqual(
            module.referencedSymbols.map(symbol => symbol.name).sort(),
            ['Hom', 'Hom_cat', 'Obj', 'eq_refl', 'ind_eqr'].sort()
        );
        assert.equal(
            JSON.stringify(module).includes('PiGrpd'),
            false
        );
        assert.equal(
            JSON.stringify(module).includes('NatAdd'),
            false
        );
        assertDeepFrozen(module);
    });

    it('keeps semantic policy separate and target-compatible', () => {
        const module = createCoreLfModuleSpec(fixtureInput());
        const overlay = createCoreLfTransferPolicyOverlay(module, {
            revision: 'fixture-policy-1',
            moduleRevision: module.revision,
            entries: [
                {
                    order: 0,
                    target: {
                        kind: 'declaration',
                        symbol: opaque
                    },
                    policy: 'opaque-signature',
                    evidence: 'fixture representation boundary'
                },
                {
                    order: 1,
                    target: {
                        kind: 'runtime-rule',
                        id: 'fixture.identity.beta'
                    },
                    policy: 'conformance-only',
                    evidence: 'no semantic promotion in SCALE-0B'
                },
                {
                    order: 2,
                    target: {
                        kind: 'proof-rule',
                        id: 'fixture.identity.compare'
                    },
                    policy: 'conformance-only',
                    evidence: 'proof engine is not implemented in SCALE-0B'
                }
            ]
        });
        assert.equal(overlay.moduleId, fixtureModule);
        assert.equal(overlay.entries.length, 3);
        assertDeepFrozen(overlay);

        expectTransferError(
            () => createCoreLfTransferPolicyOverlay(module, {
                revision: 'bad-policy-1',
                moduleRevision: module.revision,
                entries: [{
                    order: 0,
                    target: {
                        kind: 'proof-rule',
                        id: 'fixture.identity.compare'
                    },
                    policy: 'runtime-rewrite',
                    evidence: 'wrong program'
                }]
            }),
            'INVALID_POLICY'
        );
    });

    it('fails closed on scope, dependency, capture, and order drift', () => {
        const dangling = fixtureInput();
        expectTransferError(
            () => createCoreLfModuleSpec({
                ...dangling,
                declarations: [{
                    ...dangling.declarations[0],
                    type: { tag: 'bound', index: 0 }
                }]
            }),
            'INVALID_SCOPE'
        );

        const unresolved = fixtureInput();
        expectTransferError(
            () => createCoreLfModuleSpec({
                ...unresolved,
                externalSymbols: []
            }),
            'UNRESOLVED_GLOBAL'
        );

        const duplicateOrder = fixtureInput();
        expectTransferError(
            () => createCoreLfModuleSpec({
                ...duplicateOrder,
                runtimeRules: [{
                    ...duplicateOrder.runtimeRules[0],
                    order: 3
                }]
            }),
            'DUPLICATE_IDENTITY'
        );

        const undeclaredCapture = fixtureInput();
        expectTransferError(
            () => createCoreLfModuleSpec({
                ...undeclaredCapture,
                runtimeRules: [{
                    ...undeclaredCapture.runtimeRules[0],
                    right: {
                        tag: 'capture',
                        name: 'missing'
                    }
                }]
            }),
            'INVALID_CAPTURE'
        );

        const typeOccurrence = fixtureInput();
        const scoped = new CoreLfTransferScopedBuilder();
        const x = scoped.capture('x');
        const y = scoped.capture('y');
        expectTransferError(
            () => createCoreLfModuleSpec({
                ...typeOccurrence,
                runtimeRules: [{
                    ...typeOccurrence.runtimeRules[0],
                    variables: [
                        { name: 'x', type: { tag: 'type' } },
                        { name: 'y', type: scoped.template(x) }
                    ],
                    left: scoped.pattern(scoped.call(
                        scoped.global(identity),
                        [{ plicity: 'explicit', value: y }]
                    )),
                    right: scoped.template(y)
                }]
            }),
            'INVALID_RULE'
        );
    });

    it('rejects malformed higher-order capture scopes and fresh roles', () => {
        const scoped = fixtureInput();
        const left = scoped.runtimeRules[0].left;
        assert.equal(left.tag, 'call');
        if (left.tag !== 'call') return;
        expectTransferError(
            () => createCoreLfModuleSpec({
                ...scoped,
                runtimeRules: [{
                    ...scoped.runtimeRules[0],
                    left: {
                        ...left,
                        arguments: [{
                            plicity: 'explicit',
                            value: {
                                tag: 'capture',
                                name: 'x',
                                allowedBoundIndices: [0]
                            }
                        }]
                    }
                }]
            }),
            'INVALID_SCOPE'
        );

        const freshInProblem = fixtureInput();
        expectTransferError(
            () => createCoreLfModuleSpec({
                ...freshInProblem,
                proofRules: [{
                    ...freshInProblem.proofRules[0],
                    problem: {
                        left: {
                            tag: 'capture',
                            name: 'fresh'
                        },
                        right:
                            freshInProblem.proofRules[0].problem.right
                    }
                }]
            }),
            'INVALID_CAPTURE'
        );
    });

    it('preserves both reviewed profiles and the browser boundary', () => {
        assert.equal(CORE_MVP_MANIFEST.owners.length, 16);
        assert.equal(CORE_MVP_MANIFEST.rules.length, 3);
        assert.equal(
            CORE_DIRECTED_CONTINUATION_PROFILE.signatureClosure.totalCount,
            29
        );
        assert.equal(
            CORE_DIRECTED_CONTINUATION_PROFILE.runtimeClosure.totalCount,
            10
        );
        assert.equal(
            'CORE_LF_SCALE_ARCHITECTURE_REVIEW' in browser,
            false
        );
        assert.equal('createCoreLfModuleSpec' in browser, false);
        assert.equal('CoreLfTransferScopedBuilder' in browser, false);
    });
});
