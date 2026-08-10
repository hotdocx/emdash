/** Focused SIMP-5B1 tests for proof-producing root simplification. */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CoreLfDeclarationEnvironment,
    CoreProofPlan,
    KernelExpression,
    Plicity,
    binderMode,
    compileCoreProofDocument,
    coreProofPlanExact,
    coreProofPlanHole,
    createCoreProofArtifactFingerprint,
    formatCoreProofExpression,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelFree,
    kernelLambda,
    kernelPi,
    provenance,
    serializeCoreExpression,
    sourceSpan
} from '../src/v3_2';
import {
    CORE_PROOF_SIMPLIFIER_PROFILE,
    CoreProofSimplifierAdapter,
    CoreProofSimplifierError,
    CoreProofSimplifierRule,
    coreProofSimplifierAdapter,
    coreProofSimplifierRule,
    simplifyCoreProofPlan
} from '../src/v3_2/proof_simplifier';

const fixturePath = 'tests/fixtures/v3_2_proof_simplifier.surface.ts';
const at = (line: number) => sourceSpan(
    fixturePath,
    line,
    1,
    line,
    2
);
const because = (line: number, detail: string) => provenance(
    'surface',
    detail,
    at(line)
);
const explicitFunctorial = binderMode('explicit', 'functorial');

const groupoidUniverse = (line: number): KernelExpression =>
    kernelApplication(
        'groupoid-universe',
        [],
        because(line, 'SIMP-5B1 groupoid universe')
    );

const decode = (
    classifier: KernelExpression,
    line: number
): KernelExpression => kernelApplication(
    'decode',
    [{ value: classifier }],
    because(line, 'SIMP-5B1 decoded classifier')
);

const free = (name: string, line: number): KernelExpression =>
    kernelFree(name, because(line, `SIMP-5B1 reference ${name}`));

interface CallArgument {
    readonly plicity: Plicity;
    readonly value: KernelExpression;
}

const call = (
    callee: KernelExpression,
    arguments_: readonly CallArgument[],
    line: number,
    detail: string
): KernelExpression => kernelCall(
    callee,
    arguments_.map(argument => ({ ...argument })),
    because(line, detail)
);

const pi = (
    name: string,
    type: KernelExpression,
    body: KernelExpression,
    plicity: Plicity,
    line: number
): KernelExpression => kernelPi(
    kernelBinder(
        name,
        type,
        binderMode(plicity, 'functorial'),
        because(line, `SIMP-5B1 binder ${name}`)
    ),
    body,
    because(line, `SIMP-5B1 Pi ${name}`)
);

const explicit = (value: KernelExpression): CallArgument => ({
    plicity: 'explicit',
    value
});

const implicit = (value: KernelExpression): CallArgument => ({
    plicity: 'implicit',
    value
});

const bound = (index: number, line: number): KernelExpression =>
    kernelBound(index, because(line, `SIMP-5B1 bound ${index}`));

interface SimplifierFixture {
    readonly environment: CoreLfDeclarationEnvironment;
    readonly adapter: CoreProofSimplifierAdapter;
    readonly reversedAdapter: CoreProofSimplifierAdapter;
    readonly genericRule: CoreProofSimplifierRule;
    readonly specialRule: CoreProofSimplifierRule;
    readonly conditionalRule: CoreProofSimplifierRule;
    readonly opaqueBinderRule: CoreProofSimplifierRule;
    readonly cycleRule: CoreProofSimplifierRule;
    readonly target: KernelExpression;
    readonly alreadySimpleTarget: KernelExpression;
    readonly continuation: CoreProofPlan;
}

const simplifierFixture = (): SimplifierFixture => {
    let environment = CoreLfDeclarationEnvironment.empty();
    const assume = (
        name: string,
        type: KernelExpression,
        line: number
    ): void => {
        environment = environment.extend({
            name,
            type,
            mode: explicitFunctorial,
            provenance: because(line, `SIMP-5B1 declaration ${name}`)
        });
    };

    const grpd = groupoidUniverse(1);
    const equalityType = pi(
        'A',
        grpd,
        pi(
            'left',
            decode(bound(0, 2), 2),
            pi(
                'right',
                decode(bound(1, 2), 2),
                grpd,
                'explicit',
                2
            ),
            'explicit',
            2
        ),
        'implicit',
        2
    );
    assume('SimpEq', equalityType, 2);

    const equalityAtXY = decode(
        call(
            free('SimpEq', 3),
            [
                implicit(bound(2, 3)),
                explicit(bound(1, 3)),
                explicit(bound(0, 3))
            ],
            3,
            'SIMP-5B1 transport equality'
        ),
        3
    );
    const motiveType = pi(
        'value',
        decode(bound(3, 3), 3),
        grpd,
        'explicit',
        3
    );
    const motiveAtY = decode(
        call(
            bound(0, 3),
            [explicit(bound(2, 3))],
            3,
            'SIMP-5B1 motive at y'
        ),
        3
    );
    const motiveAtX = decode(
        call(
            bound(1, 3),
            [explicit(bound(4, 3))],
            3,
            'SIMP-5B1 motive at x'
        ),
        3
    );
    const backwardTransportType = pi(
        'A',
        grpd,
        pi(
            'x',
            decode(bound(0, 3), 3),
            pi(
                'y',
                decode(bound(1, 3), 3),
                pi(
                    'path',
                    equalityAtXY,
                    pi(
                        'motive',
                        motiveType,
                        pi(
                            'base',
                            motiveAtY,
                            motiveAtX,
                            'explicit',
                            3
                        ),
                        'explicit',
                        3
                    ),
                    'explicit',
                    3
                ),
                'implicit',
                3
            ),
            'implicit',
            3
        ),
        'implicit',
        3
    );
    assume('SimpIndEq', backwardTransportType, 3);

    const reversedBase = decode(
        call(
            bound(0, 4),
            [explicit(bound(3, 4))],
            4,
            'SIMP-5B1 reversed motive at x'
        ),
        4
    );
    const reversedResult = decode(
        call(
            bound(1, 4),
            [explicit(bound(3, 4))],
            4,
            'SIMP-5B1 reversed motive at y'
        ),
        4
    );
    const forwardTransportType = pi(
        'A',
        grpd,
        pi(
            'x',
            decode(bound(0, 4), 4),
            pi(
                'y',
                decode(bound(1, 4), 4),
                pi(
                    'path',
                    equalityAtXY,
                    pi(
                        'motive',
                        motiveType,
                        pi(
                            'base',
                            reversedBase,
                            reversedResult,
                            'explicit',
                            4
                        ),
                        'explicit',
                        4
                    ),
                    'explicit',
                    4
                ),
                'implicit',
                4
            ),
            'implicit',
            4
        ),
        'implicit',
        4
    );
    assume('SimpForwardEq', forwardTransportType, 4);

    const wrapType = pi(
        'B',
        grpd,
        pi(
            'value',
            decode(bound(0, 5), 5),
            decode(bound(1, 5), 5),
            'explicit',
            5
        ),
        'implicit',
        5
    );
    assume('simp_wrap', wrapType, 5);
    assume('SimpA', grpd, 6);
    const A = free('SimpA', 6);
    assume('simp_zero', decode(A, 7), 7);
    const zero = free('simp_zero', 7);
    assume(
        'SimpP',
        pi('value', decode(A, 8), grpd, 'explicit', 8),
        8
    );
    const P = free('SimpP', 8);

    const wrapAt = (
        classifier: KernelExpression,
        value: KernelExpression,
        line: number
    ): KernelExpression => call(
        free('simp_wrap', line),
        [implicit(classifier), explicit(value)],
        line,
        'SIMP-5B1 wrapper application'
    );
    const equality = (
        classifier: KernelExpression,
        left: KernelExpression,
        right: KernelExpression,
        line: number
    ): KernelExpression => decode(
        call(
            free('SimpEq', line),
            [implicit(classifier), explicit(left), explicit(right)],
            line,
            'SIMP-5B1 equality proposition'
        ),
        line
    );

    const genericWrap = wrapAt(bound(1, 9), bound(0, 9), 9);
    assume(
        'simp_wrap_rule',
        pi(
            'B',
            grpd,
            pi(
                'value',
                decode(bound(0, 9), 9),
                equality(
                    bound(1, 9),
                    genericWrap,
                    bound(0, 9),
                    9
                ),
                'explicit',
                9
            ),
            'implicit',
            9
        ),
        9
    );

    const closedWrap = wrapAt(A, zero, 10);
    assume(
        'simp_special_rule',
        equality(A, closedWrap, zero, 10),
        10
    );
    assume(
        'simp_cycle_rule',
        pi(
            'B',
            grpd,
            pi(
                'value',
                decode(bound(0, 11), 11),
                equality(
                    bound(1, 11),
                    wrapAt(bound(1, 11), bound(0, 11), 11),
                    wrapAt(bound(1, 11), bound(0, 11), 11),
                    11
                ),
                'explicit',
                11
            ),
            'implicit',
            11
        ),
        11
    );

    assume('SimpCondition', grpd, 12);
    assume(
        'simp_conditional_rule',
        pi(
            'condition',
            decode(free('SimpCondition', 12), 12),
            equality(A, closedWrap, zero, 12),
            'explicit',
            12
        ),
        12
    );

    const endomorphismAtB = pi(
        'z',
        decode(bound(0, 13), 13),
        decode(bound(1, 13), 13),
        'explicit',
        13
    );
    assume(
        'simp_higher',
        pi(
            'B',
            grpd,
            pi(
                'function',
                endomorphismAtB,
                decode(bound(1, 13), 13),
                'explicit',
                13
            ),
            'implicit',
            13
        ),
        13
    );
    const identityLambda = kernelLambda(
        kernelBinder(
            'z',
            decode(bound(1, 14), 14),
            explicitFunctorial,
            because(14, 'SIMP-5B1 opaque lambda binder')
        ),
        bound(0, 14),
        because(14, 'SIMP-5B1 opaque lambda')
    );
    const higherAtB = call(
        free('simp_higher', 14),
        [implicit(bound(1, 14)), explicit(identityLambda)],
        14,
        'SIMP-5B1 higher-order lhs'
    );
    assume(
        'simp_opaque_binder_rule',
        pi(
            'B',
            grpd,
            pi(
                'value',
                decode(bound(0, 14), 14),
                equality(
                    bound(1, 14),
                    higherAtB,
                    bound(0, 14),
                    14
                ),
                'explicit',
                14
            ),
            'implicit',
            14
        ),
        14
    );

    assume(
        'simp_base',
        decode(
            call(P, [explicit(zero)], 15, 'SIMP-5B1 base classifier'),
            15
        ),
        15
    );
    const nested = wrapAt(A, wrapAt(A, zero, 16), 16);
    const target = decode(
        call(P, [explicit(nested)], 16, 'SIMP-5B1 nested target'),
        16
    );
    const alreadySimpleTarget = decode(
        call(P, [explicit(zero)], 17, 'SIMP-5B1 simple target'),
        17
    );

    return {
        environment,
        adapter: coreProofSimplifierAdapter(
            kernelFree('SimpEq', because(18, 'SIMP-5B1 equality adapter')),
            kernelFree(
                'SimpIndEq',
                because(18, 'SIMP-5B1 backward adapter')
            )
        ),
        reversedAdapter: coreProofSimplifierAdapter(
            kernelFree('SimpEq', because(18, 'SIMP-5B1 equality adapter')),
            kernelFree(
                'SimpForwardEq',
                because(18, 'SIMP-5B1 reversed adapter')
            )
        ),
        genericRule: coreProofSimplifierRule(
            'simp.wrap',
            kernelFree('simp_wrap_rule', because(18, 'generic rule'))
        ),
        specialRule: coreProofSimplifierRule(
            'simp.special',
            kernelFree('simp_special_rule', because(18, 'special rule'))
        ),
        conditionalRule: coreProofSimplifierRule(
            'simp.conditional',
            kernelFree(
                'simp_conditional_rule',
                because(18, 'conditional rule')
            )
        ),
        opaqueBinderRule: coreProofSimplifierRule(
            'simp.opaque',
            kernelFree(
                'simp_opaque_binder_rule',
                because(18, 'opaque-binder rule')
            )
        ),
        cycleRule: coreProofSimplifierRule(
            'simp.cycle',
            kernelFree('simp_cycle_rule', because(18, 'cycle rule'))
        ),
        target,
        alreadySimpleTarget,
        continuation: coreProofPlanExact(
            free('simp_base', 18),
            { provenance: because(18, 'SIMP-5B1 continuation') }
        )
    };
};

const expectCode = (
    operation: () => unknown,
    code: CoreProofSimplifierError['code']
): void => {
    assert.throws(operation, (error: unknown) => {
        assert.ok(error instanceof CoreProofSimplifierError);
        assert.equal(error.code, code);
        return true;
    });
};

describe('TypeScript v3.2 SIMP-5B1 proof simplifier', () => {
    it('rewrites inner-first and compiles one checked transport plan', () => {
        const fixture = simplifierFixture();
        const result = simplifyCoreProofPlan({
            environment: fixture.environment,
            target: fixture.target,
            adapter: fixture.adapter,
            rules: [fixture.genericRule],
            continuation: fixture.continuation,
            provenance: because(20, 'SIMP-5B1 positive simplification')
        });

        assert.equal(result.revision, 'emdash-proof-simplifier-v1');
        assert.equal(result.rewriteCount, 2);
        assert.deepEqual(
            result.trace.map(entry => entry.occurrencePath),
            [
                '$.arguments[0].arguments[1]',
                '$.arguments[0]'
            ]
        );
        assert.deepEqual(
            result.trace.map(entry => entry.ruleId),
            ['simp.wrap', 'simp.wrap']
        );
        assert.deepEqual(result.trace[0].theoremOrigin, {
            kind: 'global-declaration',
            name: 'simp_wrap_rule'
        });
        assert.equal(
            serializeCoreExpression(result.simplifiedTarget),
            serializeCoreExpression(fixture.alreadySimpleTarget)
        );
        assert.equal(result.plan.tag, 'have');
        assert.ok(result.transportTerm);
        assert.equal(Object.isFrozen(result), true);
        assert.equal(Object.isFrozen(result.trace), true);
        assert.equal(Object.isFrozen(result.trace[0]), true);
        assert.equal(Object.isFrozen(result.trace[0].theoremOrigin), true);
        assert.equal(Object.isFrozen(result.limits), true);

        const compilation = compileCoreProofDocument({
            moduleId: 'proof.simplifier.fixture',
            declarationId: 'nested_wrapper',
            environment: fixture.environment,
            type: fixture.target,
            plan: result.plan,
            provenance: because(21, 'SIMP-5B1 proof document'),
            fingerprint: createCoreProofArtifactFingerprint({
                source: {
                    id: fixturePath,
                    sha256: `sha256:${'a'.repeat(64)}`
                },
                profileSha256: `sha256:${'b'.repeat(64)}`
            })
        });
        assert.equal(compilation.artifact.state.status, 'complete');
        assert.ok(compilation.checkedTerm);
        assert.match(
            compilation.artifact.checkedCore ?? '',
            /SimpIndEq/u
        );
        assert.equal(
            CORE_PROOF_SIMPLIFIER_PROFILE.addsCoreExpressionTags,
            false
        );
        assert.equal(
            CORE_PROOF_SIMPLIFIER_PROFILE.addsProofPlanTags,
            false
        );
    });

    it('uses caller rule order at the first postorder occurrence', () => {
        const fixture = simplifierFixture();
        const result = simplifyCoreProofPlan({
            environment: fixture.environment,
            target: fixture.target,
            adapter: fixture.adapter,
            rules: [fixture.specialRule, fixture.genericRule],
            continuation: fixture.continuation,
            provenance: because(22, 'SIMP-5B1 ordered rules')
        });
        assert.equal(result.trace[0].ruleId, 'simp.special');
        assert.equal(result.trace[1].ruleId, 'simp.special');
    });

    it('exposes one stable simplified-target hole without a callback', () => {
        const fixture = simplifierFixture();
        const result = simplifyCoreProofPlan({
            environment: fixture.environment,
            target: fixture.target,
            adapter: fixture.adapter,
            rules: [fixture.genericRule],
            continuation: coreProofPlanHole('simplified_goal', {
                provenance: because(22, 'SIMP-5B1 named continuation')
            }),
            provenance: because(22, 'SIMP-5B1 hole simplification')
        });
        const compilation = compileCoreProofDocument({
            moduleId: 'proof.simplifier.fixture',
            declarationId: 'open_nested_wrapper',
            environment: fixture.environment,
            type: fixture.target,
            plan: result.plan,
            provenance: because(22, 'SIMP-5B1 open proof document'),
            fingerprint: createCoreProofArtifactFingerprint({
                source: {
                    id: fixturePath,
                    sha256: `sha256:${'c'.repeat(64)}`
                },
                profileSha256: `sha256:${'d'.repeat(64)}`
            })
        });
        assert.equal(compilation.artifact.state.status, 'incomplete');
        assert.equal(compilation.artifact.state.goals.length, 1);
        assert.equal(
            compilation.artifact.state.goals[0].id,
            'simplified_goal'
        );
        assert.equal(
            compilation.artifact.state.goals[0].target,
            formatCoreProofExpression(result.simplifiedTarget)
        );
    });

    it('returns the exact continuation when no rule fires', () => {
        const fixture = simplifierFixture();
        const result = simplifyCoreProofPlan({
            environment: fixture.environment,
            target: fixture.alreadySimpleTarget,
            adapter: fixture.adapter,
            rules: [fixture.genericRule],
            continuation: fixture.continuation,
            provenance: because(23, 'SIMP-5B1 no rewrite')
        });
        assert.equal(result.rewriteCount, 0);
        assert.equal(result.trace.length, 0);
        assert.equal(result.transportTerm, undefined);
        assert.equal(result.simplifiedTarget, fixture.alreadySimpleTarget);
        assert.equal(result.plan, fixture.continuation);
    });

    it('rejects conditional and opaque-binder rules before traversal', () => {
        const fixture = simplifierFixture();
        for (const rule of [
            fixture.conditionalRule,
            fixture.opaqueBinderRule
        ]) {
            expectCode(() => simplifyCoreProofPlan({
                environment: fixture.environment,
                target: fixture.target,
                adapter: fixture.adapter,
                rules: [rule],
                continuation: fixture.continuation,
                provenance: because(24, 'SIMP-5B1 invalid rule')
            }), 'INVALID_RULE');
        }
    });

    it('rejects a forward transport adapter even without a rewrite', () => {
        const fixture = simplifierFixture();
        expectCode(() => simplifyCoreProofPlan({
            environment: fixture.environment,
            target: fixture.alreadySimpleTarget,
            adapter: fixture.reversedAdapter,
            rules: [],
            continuation: fixture.continuation,
            provenance: because(25, 'SIMP-5B1 reversed transport')
        }), 'INVALID_ADAPTER');
    });

    it('detects an equality rewrite cycle before returning partial data', () => {
        const fixture = simplifierFixture();
        expectCode(() => simplifyCoreProofPlan({
            environment: fixture.environment,
            target: fixture.target,
            adapter: fixture.adapter,
            rules: [fixture.cycleRule],
            continuation: fixture.continuation,
            provenance: because(26, 'SIMP-5B1 cycle')
        }), 'CYCLE_DETECTED');
    });

    it('enforces visit, attempt, and rewrite budgets independently', () => {
        const fixture = simplifierFixture();
        const cases: readonly [
            Record<string, number>,
            CoreProofSimplifierError['code']
        ][] = [
            [{ maximumVisits: 0 }, 'VISIT_LIMIT_EXCEEDED'],
            [
                { maximumRuleAttempts: 0 },
                'RULE_ATTEMPT_LIMIT_EXCEEDED'
            ],
            [{ maximumRewrites: 0 }, 'REWRITE_LIMIT_EXCEEDED']
        ];
        for (const [limits, code] of cases) {
            expectCode(() => simplifyCoreProofPlan({
                environment: fixture.environment,
                target: fixture.target,
                adapter: fixture.adapter,
                rules: [fixture.genericRule],
                continuation: fixture.continuation,
                provenance: because(27, `SIMP-5B1 ${code}`),
                limits
            }), code);
        }
    });

    it('rejects invalid safe-integer limits and duplicate IDs', () => {
        const fixture = simplifierFixture();
        expectCode(() => simplifyCoreProofPlan({
            environment: fixture.environment,
            target: fixture.target,
            adapter: fixture.adapter,
            rules: [fixture.genericRule],
            continuation: fixture.continuation,
            provenance: because(28, 'SIMP-5B1 invalid limit'),
            limits: { maximumVisits: -1 }
        }), 'INVALID_LIMIT');
        expectCode(() => simplifyCoreProofPlan({
            environment: fixture.environment,
            target: fixture.target,
            adapter: fixture.adapter,
            rules: [fixture.genericRule, fixture.genericRule],
            continuation: fixture.continuation,
            provenance: because(28, 'SIMP-5B1 duplicate rule')
        }), 'DUPLICATE_RULE_ID');
    });
});
