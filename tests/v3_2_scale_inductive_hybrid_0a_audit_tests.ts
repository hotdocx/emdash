/**
 * SCALE-INDUCTIVE-HYBRID-0A lean generated-owner audit evidence.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_INDUCTIVE_HYBRID_0A_AUDIT,
    CORE_LF_SCALE_INDUCTIVE_HYBRID_0A_SYMBOLS,
    KernelExpression,
    checkLambdapiProbe,
    compileCoreLfScaleInductiveHybrid0aAudit,
    coreLfDefinitionalCompare,
    kernelCall,
    kernelFree,
    provenance
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value as object).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe('SCALE-INDUCTIVE-HYBRID-0A expanded ind_nat audit', () => {
    it('freezes the lean architectural conclusion and non-effects', () => {
        const audit =
            CORE_LF_SCALE_INDUCTIVE_HYBRID_0A_AUDIT;
        assertDeepFrozen(audit);
        assert.equal(
            audit.conclusion.semanticTransferBaseline,
            'ordinary-explicit-declaration-and-runtime-rules'
        );
        assert.equal(
            audit.conclusion.associationDependency,
            'none'
        );
        assert.equal(
            audit.conclusion.positivityRequirement,
            'not-required-for-expanded-symbol-transfer'
        );
        assert.deepEqual(audit.productEffects, []);
    });

    it('compiles the recursive generated owner through ordinary engines', () => {
        const compiled =
            compileCoreLfScaleInductiveHybrid0aAudit();
        assert.deepEqual(
            compiled.signatureModule.inductives[0].constructors
                .map(constructor => constructor.symbol.name),
            ['zero', 'succ']
        );
        assert.deepEqual(
            compiled.contract.phases.map(phase => phase.kind),
            [
                'declaration',
                'runtime',
                'declaration',
                'runtime',
                'declaration'
            ]
        );
        assert.deepEqual(
            compiled.contract.declarations.modules.flatMap(module =>
                module.declarations.map(declaration => [
                    declaration.symbol.name,
                    declaration.status
                ])
            ),
            [
                ['ind_nat', 'installed-opaque'],
                ['Nat_grpd', 'installed-opaque'],
                ['nat_elim', 'installed-transparent']
            ]
        );
        assert.deepEqual(
            compiled.contract.latestRuntime?.runtime.ruleIds,
            [
                'inductive.expanded.nat-zero',
                'inductive.expanded.nat-succ',
                'inductive.expanded.nat-grpd-decode'
            ]
        );
        assert.ok(
            compiled.contract.phases
                .filter(phase => phase.kind === 'runtime')
                .flatMap(phase => phase.runtime.localProgram.rules)
                .every(rule =>
                    rule.subjectValidation.kind ===
                        'typescript-checked'
                )
        );
    });

    it('reduces the existing nat_elim consumer at both constructors', () => {
        const compiled =
            compileCoreLfScaleInductiveHybrid0aAudit();
        const at = provenance(
            'derived',
            'SCALE-INDUCTIVE-HYBRID-0A TypeScript consumer'
        );
        const term = (name: string): KernelExpression =>
            kernelFree(name, at);
        const P = term('hybrid_nat_P');
        const uZero = term('hybrid_nat_u_zero');
        const uSucc = term('hybrid_nat_u_succ');
        const zeroTerm = term('scale_inductive_hybrid_zero');
        const succ = term('scale_inductive_hybrid_succ');
        const natElim = term('scale_inductive_hybrid_nat_elim');
        const apply = (
            callee: KernelExpression,
            values: readonly KernelExpression[]
        ): KernelExpression => kernelCall(
            callee,
            values.map(value => ({
                plicity: 'explicit' as const,
                value
            })),
            at
        );
        const eliminate = (n: KernelExpression): KernelExpression =>
            apply(natElim, [P, uZero, uSucc, n]);
        const runtime =
            compiled.contract.latestRuntime?.runtime;

        const atZero = coreLfDefinitionalCompare(
            compiled.contract.declarations.environment,
            eliminate(zeroTerm),
            uZero,
            32,
            undefined,
            runtime
        );
        assert.equal(atZero.status, 'equal');

        const successorZero = apply(succ, [zeroTerm]);
        const expectedSuccessor = apply(
            uSucc,
            [zeroTerm, uZero]
        );
        const atSuccessor = coreLfDefinitionalCompare(
            compiled.contract.declarations.environment,
            eliminate(successorZero),
            expectedSuccessor,
            64,
            undefined,
            runtime
        );
        assert.equal(atSuccessor.status, 'equal');
        assert.equal(
            atSuccessor.trace.some(entry =>
                entry.reduction.kind === 'runtime' &&
                entry.reduction.ruleId ===
                    'inductive.expanded.nat-succ'
            ),
            true
        );
    });

    it('uses no recursive association or browser/product path', () => {
        const implementation = readFileSync(
            'src/v3_2/scale_inductive_hybrid_0a_audit.ts',
            'utf8'
        );
        assert.doesNotMatch(
            implementation,
            /associateCoreLfGeneratedInductiveContract|compileCoreLfGeneratedInductiveContract/u
        );
        assert.equal(
            'compileCoreLfScaleInductiveHybrid0aAudit' in browser,
            false
        );
        assert.equal(
            CORE_LF_SCALE_INDUCTIVE_HYBRID_0A_SYMBOLS
                .generatedIndNat.name,
            'ind_nat'
        );
    });

    it(
        'matches the active generated rules and nat_elim in Lambdapi',
        {
            skip:
                process.env
                    .EMDASH_RUN_LAMBDAPI_SCALE_INDUCTIVE_HYBRID_PROBES !==
                '1'
        },
        () => {
            const result = checkLambdapiProbe(
                {
                    source: `
require open emdash.emdash3_2;

assert
  (P : τ Nat_grpd → Grpd)
  (u_zero : τ (P zero))
  (u_succ : Π n : τ Nat_grpd,
    τ (P n) → τ (P (succ n)))
  ⊢ nat_elim P u_zero u_succ zero
    ≡ u_zero;

assert
  (P : τ Nat_grpd → Grpd)
  (u_zero : τ (P zero))
  (u_succ : Π n : τ Nat_grpd,
    τ (P n) → τ (P (succ n)))
  (n : τ Nat_grpd)
  ⊢ nat_elim P u_zero u_succ (succ n)
    ≡ u_succ n (nat_elim P u_zero u_succ n);
`,
                    sourceMap: []
                },
                {
                    packageRoot: resolve('emdash2'),
                    timeoutMs: 20_000
                }
            );
            assert.equal(result.timedOut, false);
            assert.equal(
                result.accepted,
                true,
                result.diagnostics
            );
        }
    );
});
