/**
 * Focused proposal evidence for H-DTTLF-SCALE-STRESS-01.
 */

import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_STRESS_1B_ACQUISITION_CONTRACTS,
    CORE_LF_SCALE_STRESS_1B_CORE_ACQUISITION,
    CORE_LF_SCALE_STRESS_1B_PROPOSAL,
    CoreLfScaleStress1bProposal,
    CoreLfScaleStress1bProposalError,
    KernelExpression,
    checkLambdapiProbe,
    compileCoreLfScaleStress1bProposal,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    provenance,
    validateCoreLfScaleStress1bProposal
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

const cloneProposal = (): CoreLfScaleStress1bProposal =>
    JSON.parse(JSON.stringify(
        CORE_LF_SCALE_STRESS_1B_PROPOSAL
    )) as CoreLfScaleStress1bProposal;

describe('TypeScript v3.2 SCALE-STRESS-1B semantic proposal', () => {
    it('freezes an exact non-active decision boundary', () => {
        const proposal = CORE_LF_SCALE_STRESS_1B_PROPOSAL;
        assert.equal(
            proposal.gate,
            'H-DTTLF-SCALE-STRESS-01'
        );
        assert.equal(
            proposal.decision,
            'D-DTTLF-SCALE-STRESS-001'
        );
        assert.equal(
            proposal.status,
            'proposal-awaiting-human-approval'
        );
        assert.deepEqual(proposal.productEffects, []);
        assert.deepEqual(
            proposal.proposedEnvelope.generatedOwnersWithheld,
            ['ind_nat', 'ind_τΣ_']
        );
        assert.ok(
            proposal.doesNotAuthorize.includes(
                'mechanical-transfer-graduation'
            )
        );
        assertDeepFrozen(proposal);
        assert.doesNotThrow(() =>
            validateCoreLfScaleStress1bProposal()
        );
    });

    it('pins the dependency-closed source command selection', () => {
        assert.equal(
            CORE_LF_SCALE_STRESS_1B_ACQUISITION_CONTRACTS.length,
            2
        );
        assert.deepEqual(
            CORE_LF_SCALE_STRESS_1B_CORE_ACQUISITION.commands.map(
                command => command.ordinal
            ),
            [10, 12, 13, 14, 38, 39, 40, 54, 63, 64, 74, 75]
        );
        assert.deepEqual(
            CORE_LF_SCALE_STRESS_1B_CORE_ACQUISITION.commands.map(
                command => command.id
            ),
            [
                'foundation.equality',
                'foundation.reflexivity',
                'outer-j.declaration',
                'outer-j.reflexivity-beta',
                'foundation.nat-inductive',
                'foundation.nat-classifier',
                'foundation.nat-decode',
                'sigma.decoded-inductive',
                'sigma.eliminator',
                'sigma.eliminator-beta',
                'pi.decoded-classifier',
                'pi.decoding-beta'
            ]
        );
    });

    it('proposes exact source order and policy without proof rules', () => {
        const proposal = CORE_LF_SCALE_STRESS_1B_PROPOSAL;
        const items = [
            ...proposal.core.module.declarations,
            ...proposal.core.module.inductives,
            ...proposal.core.module.runtimeRules
        ].sort((left, right) => left.order - right.order);
        assert.deepEqual(
            items.map(item =>
                item.provenance.canonicalCommandOrdinal
            ),
            [10, 12, 13, 14, 38, 39, 40, 54, 63, 64, 74, 75]
        );
        assert.deepEqual(
            proposal.core.policy.entries.map(entry => entry.policy),
            [
                'opaque-signature',
                'opaque-signature',
                'opaque-signature',
                'runtime-rewrite',
                'opaque-signature',
                'opaque-signature',
                'runtime-rewrite',
                'opaque-signature',
                'opaque-signature',
                'runtime-rewrite',
                'opaque-signature',
                'runtime-rewrite'
            ]
        );
        assert.deepEqual(
            proposal.nat.policy.entries.map(entry => entry.policy),
            [
                'opaque-signature',
                'runtime-rewrite',
                'runtime-rewrite',
                'runtime-rewrite'
            ]
        );
        assert.equal(
            proposal.core.module.inductives.find(
                block => block.symbol.name === 'nat'
            )?.modifiers.rigidity,
            'injective'
        );
        assert.deepEqual(proposal.core.module.proofRules, []);
        assert.deepEqual(proposal.nat.module.proofRules, []);
    });

    it('compiles the proposed profile only as isolated evidence', () => {
        const compiled = compileCoreLfScaleStress1bProposal();
        assert.deepEqual(
            compiled.core.latestRuntime?.runtime.ruleIds,
            [
                'stress.outer-j.reflexivity',
                'stress.nat-grpd.decode',
                'stress.sigma.eliminator-beta',
                'stress.pi-grpd.decode'
            ]
        );
        assert.deepEqual(
            compiled.nat.latestRuntime?.runtime.ruleIds,
            CORE_LF_SCALE_STRESS_1B_PROPOSAL
                .proposedEnvelope.runtimeRules
        );
        assert.deepEqual(
            compiled.core.phases.map(phase => phase.kind),
            [
                'declaration',
                'declaration',
                'declaration',
                'runtime',
                'inductive-signature',
                'declaration',
                'runtime',
                'inductive-signature',
                'declaration',
                'runtime',
                'declaration',
                'runtime'
            ]
        );
        assert.ok(
            compiled.core.phases
                .filter(phase => phase.kind === 'runtime')
                .flatMap(phase => phase.runtime.localProgram.rules)
                .every(rule =>
                    rule.subjectValidation.kind ===
                        'typescript-checked'
                )
        );
        assert.ok(
            compiled.nat.latestRuntime?.localProgram.rules.every(
                rule =>
                    rule.subjectValidation.kind ===
                        'typescript-checked'
            )
        );
    });

    it('exercises J guards, Pi/Sigma beta, and grouped Nat priority', () => {
        const compiled = compileCoreLfScaleStress1bProposal();
        const nodeSource = provenance(
            'derived',
            'SCALE-STRESS-1B proposal runtime witness'
        );
        const term = (name: string): KernelExpression =>
            kernelFree(name, nodeSource);
        const coreRuntime = compiled.core.latestRuntime?.runtime;
        const natRuntime = compiled.nat.latestRuntime?.runtime;
        assert.notEqual(coreRuntime, undefined);
        assert.notEqual(natRuntime, undefined);
        if (coreRuntime === undefined || natRuntime === undefined) {
            return;
        }
        const localCoreProgram = (id: string) => {
            const phase = compiled.core.phases.find(candidate =>
                candidate.kind === 'runtime' &&
                candidate.runtime.localProgram.rule(id) !== undefined
            );
            assert.equal(phase?.kind, 'runtime');
            if (phase?.kind !== 'runtime') {
                throw new Error(`Missing core runtime rule '${id}'`);
            }
            return phase.runtime.localProgram;
        };

        const jProgram = localCoreProgram(
            'stress.outer-j.reflexivity'
        );
        const jRule = jProgram.rule(
            'stress.outer-j.reflexivity'
        );
        assert.notEqual(jRule, undefined);
        if (jRule === undefined) return;
        const a = term('witness_A');
        const y = term('witness_y');
        const motive = term('witness_P');
        const supplied = term('witness_u');
        const jRedex = jProgram.instantiateRuleLeft(
            jRule,
            [a, y, motive, supplied],
            nodeSource
        );
        const jRewrite = coreRuntime.rewriteHead(jRedex);
        assert.equal(jRewrite.status, 'rewritten');
        if (jRewrite.status === 'rewritten') {
            assert.equal(jRewrite.ruleId, jRule.id);
            assert.equal(
                kernelExpressionEquals(
                    jRewrite.after,
                    supplied
                ),
                true
            );
        }
        assert.equal(jRedex.tag, 'call');
        if (jRedex.tag !== 'call') return;
        const wrongEndpoint = kernelCall(
            jRedex.callee,
            jRedex.arguments.map((argument, index) => ({
                plicity: argument.plicity,
                value: index === 4
                    ? term('witness_other_endpoint')
                    : argument.value
            })),
            nodeSource
        );
        assert.equal(
            coreRuntime.rewriteHead(wrongEndpoint).status,
            'irreducible'
        );
        const rawProof = kernelCall(
            jRedex.callee,
            jRedex.arguments.map((argument, index) => ({
                plicity: argument.plicity,
                value: index === 5
                    ? term('witness_raw_proof')
                    : argument.value
            })),
            nodeSource
        );
        assert.equal(
            coreRuntime.rewriteHead(rawProof).status,
            'irreducible'
        );

        const piProgram = localCoreProgram(
            'stress.pi-grpd.decode'
        );
        const piRule = piProgram.rule('stress.pi-grpd.decode');
        assert.notEqual(piRule, undefined);
        if (piRule === undefined) return;
        const piRedex = piProgram.instantiateRuleLeft(
            piRule,
            [a, term('witness_B')],
            nodeSource
        );
        const piRewrite = coreRuntime.rewriteHead(piRedex);
        assert.equal(piRewrite.status, 'rewritten');
        if (piRewrite.status === 'rewritten') {
            assert.equal(piRewrite.ruleId, piRule.id);
            assert.equal(piRewrite.after.tag, 'pi');
        }

        const sigmaProgram = localCoreProgram(
            'stress.sigma.eliminator-beta'
        );
        const sigmaRule = sigmaProgram.rule(
            'stress.sigma.eliminator-beta'
        );
        assert.notEqual(sigmaRule, undefined);
        if (sigmaRule === undefined) return;
        const sigmaBindings = [
            a,
            motive,
            term('witness_Q'),
            term('witness_c'),
            term('witness_x'),
            term('witness_sigma_u')
        ];
        const sigmaRedex = sigmaProgram.instantiateRuleLeft(
            sigmaRule,
            sigmaBindings,
            nodeSource
        );
        const sigmaRewrite = coreRuntime.rewriteHead(sigmaRedex);
        assert.equal(sigmaRewrite.status, 'rewritten');
        if (sigmaRewrite.status === 'rewritten') {
            assert.equal(sigmaRewrite.ruleId, sigmaRule.id);
            assert.equal(
                kernelExpressionEquals(
                    sigmaRewrite.after,
                    kernelCall(
                        sigmaBindings[3],
                        [
                            {
                                plicity: 'explicit',
                                value: sigmaBindings[4]
                            },
                            {
                                plicity: 'explicit',
                                value: sigmaBindings[5]
                            }
                        ],
                        nodeSource
                    )
                ),
                true
            );
        }

        const natProgram =
            compiled.nat.latestRuntime?.localProgram;
        assert.notEqual(natProgram, undefined);
        if (natProgram === undefined) return;
        const zeroLeft = natProgram.rule(
            'stress.nat-add.zero-left'
        );
        const succLeft = natProgram.rule(
            'stress.nat-add.succ-left'
        );
        const zeroRight = natProgram.rule(
            'stress.nat-add.zero-right'
        );
        assert.notEqual(zeroLeft, undefined);
        assert.notEqual(succLeft, undefined);
        assert.notEqual(zeroRight, undefined);
        if (
            zeroLeft === undefined ||
            succLeft === undefined ||
            zeroRight === undefined
        ) return;
        const n = term('witness_n');
        const m = term('witness_m');
        const zeroTerm = term('stress_zero');
        const zeroLeftRedex = natProgram.instantiateRuleLeft(
            zeroLeft,
            [n],
            nodeSource
        );
        const zeroLeftRewrite =
            natRuntime.rewriteHead(zeroLeftRedex);
        assert.equal(zeroLeftRewrite.status, 'rewritten');
        if (zeroLeftRewrite.status === 'rewritten') {
            assert.equal(zeroLeftRewrite.ruleId, zeroLeft.id);
            assert.equal(
                kernelExpressionEquals(zeroLeftRewrite.after, n),
                true
            );
        }
        const succRedex = natProgram.instantiateRuleLeft(
            succLeft,
            [m, n],
            nodeSource
        );
        const succRewrite = natRuntime.rewriteHead(succRedex);
        assert.equal(succRewrite.status, 'rewritten');
        if (succRewrite.status === 'rewritten') {
            assert.equal(succRewrite.ruleId, succLeft.id);
        }
        const overlap = natProgram.instantiateRuleLeft(
            zeroRight,
            [zeroTerm],
            nodeSource
        );
        const overlapRewrite = natRuntime.rewriteHead(overlap);
        assert.equal(overlapRewrite.status, 'rewritten');
        if (overlapRewrite.status === 'rewritten') {
            assert.equal(overlapRewrite.ruleId, zeroLeft.id);
        }
        const openRight = natProgram.instantiateRuleLeft(
            zeroRight,
            [m],
            nodeSource
        );
        const openRightRewrite = natRuntime.rewriteHead(openRight);
        assert.equal(openRightRewrite.status, 'rewritten');
        if (openRightRewrite.status === 'rewritten') {
            assert.equal(openRightRewrite.ruleId, zeroRight.id);
            assert.equal(
                kernelExpressionEquals(openRightRewrite.after, m),
                true
            );
        }
    });

    it(
        'matches bounded Lambdapi stress reductions and non-conversion',
        {
            skip:
                process.env
                    .EMDASH_RUN_LAMBDAPI_SCALE_STRESS_PROBES !== '1'
        },
        () => {
            const header = [
                'require open emdash.emdash3_2;',
                'require open emdash.emdash3_2_nat_arithmetic;'
            ];
            const positive = checkLambdapiProbe(
                {
                    source: [
                        ...header,
                        'assert [A : Grpd]',
                        '  (y : τ A)',
                        '  (P : Π x : τ A, τ (x = y) → Grpd)',
                        '  (u : τ (P y (eq_refl y))) ⊢',
                        '  @ind_eqr A y P u y (eq_refl y) ≡ u;',
                        'assert [A : Grpd]',
                        '  [P : τ A → Grpd]',
                        '  (Q : @τΣ_ A P → Grpd)',
                        '  (c : Π x : τ A, Π u : τ (P x),',
                        '    τ (Q (@Struct_sigma A P x u)))',
                        '  (x : τ A) (u : τ (P x)) ⊢',
                        '  @sigma_ind A P Q c',
                        '    (@Struct_sigma A P x u) ≡ c x u;',
                        'assert [A : Grpd]',
                        '  [B : τ A → Grpd] ⊢',
                        '  τ (@Pi_grpd A B) ≡',
                        '    Π x : τ A, τ (B x);',
                        'assert (n : τ Nat_grpd) ⊢',
                        '  @nat_add zero n ≡ n;',
                        'assert (m n : τ Nat_grpd) ⊢',
                        '  @nat_add (succ m) n ≡',
                        '    succ (@nat_add m n);',
                        'assert (m : τ Nat_grpd) ⊢',
                        '  @nat_add m zero ≡ m;',
                        'assert (m : τ Nat_grpd) ⊢',
                        '  @nat_add (succ m) zero ≡ succ m;',
                        'assertnot (m n : τ Nat_grpd) ⊢',
                        '  @nat_add m n ≡ @nat_add n m;'
                    ].join('\n'),
                    sourceMap: []
                },
                {
                    packageRoot: resolve(repositoryRoot, 'emdash2'),
                    timeoutMs: 30_000
                }
            );
            assert.equal(
                positive.accepted,
                true,
                positive.diagnostics
            );
            assert.equal(positive.timedOut, false);

            const negative = checkLambdapiProbe(
                {
                    source: [
                        ...header,
                        'assert (m n : τ Nat_grpd) ⊢',
                        '  @nat_add m n ≡ @nat_add n m;'
                    ].join('\n'),
                    sourceMap: []
                },
                {
                    packageRoot: resolve(repositoryRoot, 'emdash2'),
                    timeoutMs: 30_000
                }
            );
            assert.equal(negative.accepted, false);
            assert.equal(negative.timedOut, false);
            assert.match(
                negative.diagnostics,
                /Assertion failed/u
            );
        }
    );

    it('rejects proposal drift and stays out of the browser barrel', () => {
        const activated = cloneProposal();
        (
            activated as {
                status: string;
            }
        ).status = 'approved';
        assert.throws(
            () => validateCoreLfScaleStress1bProposal(
                activated
            ),
            error =>
                error instanceof CoreLfScaleStress1bProposalError &&
                error.code === 'INVALID_PROPOSAL_BOUNDARY'
        );

        const proposal = cloneProposal();
        (
            proposal.proposedEnvelope.runtimeRules as string[]
        ).pop();
        assert.throws(
            () => validateCoreLfScaleStress1bProposal(proposal),
            error =>
                error instanceof CoreLfScaleStress1bProposalError &&
                error.code === 'PROPOSAL_DRIFT'
        );
        assert.equal(
            'CORE_LF_SCALE_STRESS_1B_PROPOSAL' in browser,
            false
        );
        assert.equal(
            'compileCoreLfScaleStress1bProposal' in browser,
            false
        );
    });
});
