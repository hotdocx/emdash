/**
 * SCALE-INDUCTIVE-1B1 generated-owner audit and proposal evidence.
 */

import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { describe, it } from 'node:test';
import {
    CORE_LF_SCALE_INDUCTIVE_1B1_PROPOSAL,
    CORE_LF_SCALE_INDUCTIVE_1B1_SYMBOLS,
    CoreLfScaleInductive1b1Proposal,
    CoreLfScaleInductive1b1ProposalError,
    checkLambdapiProbe,
    compileCoreLfScaleInductive1b1Proposal,
    coreLfDefinitionalCompare,
    correctedTauSigmaBlock,
    kernelCall,
    kernelFree,
    provenance,
    tauSigmaErasedSignaturesRemainIdentical,
    validateCoreLfScaleInductive1b1Proposal
} from '../src/v3_2';
import * as browser from '../src/v3_2/browser';

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value as Record<string, unknown>)
        .forEach(assertDeepFrozen);
};

const mutableCopy = (
    proposal: CoreLfScaleInductive1b1Proposal
): CoreLfScaleInductive1b1Proposal =>
    JSON.parse(JSON.stringify(proposal)) as
        CoreLfScaleInductive1b1Proposal;

describe('SCALE-INDUCTIVE-1B1 generated-owner proposal', () => {
    it('freezes the exact gate, correction, and non-effects', () => {
        const proposal =
            validateCoreLfScaleInductive1b1Proposal();
        assertDeepFrozen(proposal);
        assert.equal(proposal.parent, 'SCALE-INDUCTIVE-1B');
        assert.equal(
            proposal.decision.question,
            'Approve H-DTTLF-SCALE-INDUCTIVE-01/' +
                'D-DTTLF-SCALE-INDUCTIVE-001 as proposed.'
        );
        assert.deepEqual(
            proposal.representationCorrection.correctedIndices,
            ['a', 'P']
        );
        assert.equal(
            proposal.doesNotAuthorize.includes(
                'recursive-or-mutual-inductive-graduation'
            ),
            true
        );
    });

    it('reclassifies inline binders without changing 1A erasure', () => {
        const corrected = correctedTauSigmaBlock();
        assert.deepEqual(corrected.parameters, []);
        assert.deepEqual(
            corrected.indices.map(binder => [
                binder.hint,
                binder.mode.plicity
            ]),
            [
                ['a', 'implicit'],
                ['P', 'explicit']
            ]
        );
        assert.deepEqual(
            corrected.constructors[0].binders.map(binder => [
                binder.hint,
                binder.mode.plicity
            ]),
            [
                ['a', 'implicit'],
                ['P', 'implicit'],
                ['sigma_Fst', 'explicit'],
                ['sigma_Snd', 'explicit']
            ]
        );
        assert.equal(
            corrected.constructors[0].parameterModes,
            undefined
        );
        assert.equal(tauSigmaErasedSignaturesRemainIdentical(), true);
    });

    it('compiles the explicit contract through existing generic engines', () => {
        const compiled =
            compileCoreLfScaleInductive1b1Proposal();
        assert.deepEqual(
            compiled.association.classification,
            {
                kind: 'nonrecursive-indexed',
                parameterCount: 0,
                indexCount: 2,
                constructorCount: 1,
                recursiveOccurrencePaths: [],
                strictPositivity: 'trivial-nonrecursive'
            }
        );
        assert.equal(
            compiled.association.generatedOwner.name,
            'ind_τΣ_'
        );
        assert.deepEqual(
            compiled.contract.phases.map(phase => phase.kind),
            ['declaration', 'declaration', 'runtime']
        );
        assert.deepEqual(
            compiled.contract.declarations.modules.flatMap(module =>
                module.declarations.map(declaration => [
                    declaration.symbol.name,
                    declaration.status
                ])
            ),
            [
                ['ind_τΣ_', 'installed-opaque'],
                [
                    'scale_generated_sigma_fst',
                    'installed-transparent'
                ]
            ]
        );
        assert.deepEqual(
            compiled.contract.latestRuntime?.runtime.ruleIds,
            ['inductive.generated.tau-sigma-beta']
        );
    });

    it('reduces the polymorphic generated first projection', () => {
        const compiled =
            compileCoreLfScaleInductive1b1Proposal();
        const at = provenance(
            'derived',
            'SCALE-INDUCTIVE-1B1 TypeScript consumer'
        );
        const A = kernelFree('inductive_witness_A', at);
        const P = kernelFree('inductive_witness_P', at);
        const x = kernelFree('inductive_witness_x', at);
        const u = kernelFree('inductive_witness_u', at);
        const pair = kernelCall(
            kernelFree('scale_inductive_struct_sigma', at),
            [
                { plicity: 'implicit', value: A },
                { plicity: 'implicit', value: P },
                { plicity: 'explicit', value: x },
                { plicity: 'explicit', value: u }
            ],
            at
        );
        const first = kernelCall(
            kernelFree(
                'scale_inductive_generated_sigma_fst',
                at
            ),
            [
                { plicity: 'explicit', value: A },
                { plicity: 'explicit', value: P },
                { plicity: 'explicit', value: pair }
            ],
            at
        );
        const comparison = coreLfDefinitionalCompare(
            compiled.contract.declarations.environment,
            first,
            x,
            32,
            undefined,
            compiled.contract.latestRuntime?.runtime
        );
        assert.equal(comparison.status, 'equal');
        assert.equal(
            comparison.trace.some(entry =>
                entry.reduction.kind === 'runtime' &&
                entry.reduction.ruleId ===
                    'inductive.generated.tau-sigma-beta'
            ),
            true
        );
    });

    it('rejects authority and parameter/index boundary drift', () => {
        const authority = mutableCopy(
            CORE_LF_SCALE_INDUCTIVE_1B1_PROPOSAL
        );
        (authority.measuredAuthority as {
            generatedRuleCount: number;
        }).generatedRuleCount = 2;
        assert.throws(
            () => validateCoreLfScaleInductive1b1Proposal(authority),
            error =>
                error instanceof CoreLfScaleInductive1b1ProposalError &&
                error.code === 'INVALID_GENERATED_AUTHORITY'
        );

        const classification = mutableCopy(
            CORE_LF_SCALE_INDUCTIVE_1B1_PROPOSAL
        );
        (classification.representationCorrection as {
            inlineBinders: string;
        }).inlineBinders = 'parameters';
        assert.throws(
            () => validateCoreLfScaleInductive1b1Proposal(
                classification
            ),
            error =>
                error instanceof CoreLfScaleInductive1b1ProposalError &&
                error.code === 'PARAMETER_INDEX_BOUNDARY_DRIFT'
        );
    });

    it('keeps the proposal owner-agnostic and outside the browser API', () => {
        const implementation = readFileSync(
            resolve(
                'src/v3_2/lf_transfer_inductive.ts'
            ),
            'utf8'
        );
        assert.doesNotMatch(
            implementation,
            /τΣ_|Struct_sigma|ind_τΣ_/u
        );
        assert.equal(
            'compileCoreLfScaleInductive1b1Proposal' in browser,
            false
        );
        assert.equal(
            CORE_LF_SCALE_INDUCTIVE_1B1_SYMBOLS
                .generatedIndTauSigma.name,
            'ind_τΣ_'
        );
    });

    it(
        'matches the generated type, beta, and consumer in live Lambdapi',
        {
            skip:
                process.env
                    .EMDASH_RUN_LAMBDAPI_SCALE_INDUCTIVE_PROBES !==
                '1'
        },
        () => {
            const source = `
require open emdash.emdash3_2;

symbol scale_generated_sigma_fst
  : Π A : Grpd,
    Π P : τ A → Grpd,
    Π s : @τΣ_ A P,
    τ A
≔ ind_τΣ_
    (λ A : Grpd,
     λ P : τ A → Grpd,
     λ _ : @τΣ_ A P,
     A)
    (λ A : Grpd,
     λ P : τ A → Grpd,
     λ x : τ A,
     λ _ : τ (P x),
     x);

assert A P x u
  ⊢ scale_generated_sigma_fst
      A
      P
      (@Struct_sigma A P x u)
    ≡ x;
`;
            const result = checkLambdapiProbe(
                { source, sourceMap: [] },
                {
                    packageRoot: resolve('emdash2'),
                    timeoutMs: 20_000
                }
            );
            assert.equal(result.timedOut, false);
            assert.equal(result.accepted, true, result.diagnostics);
        }
    );
});
