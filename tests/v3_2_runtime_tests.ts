/**
 * Focused TSK-2A tests for reviewed runtime-rule compilation.
 */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CORE_MVP_MANIFEST,
    CORE_MVP_RUNTIME_PROGRAM,
    CoreCompiledRulePattern,
    CoreManifestRuleInput,
    CoreManifestValidationError,
    CoreMvpManifestInput,
    CoreRuntimeCompilationError,
    CoreRuntimeCompilationErrorCode,
    compileCoreMvpRuntime,
    compileCoreRuntimeRuleCandidate,
    coreRuntimePatternsMayOverlap
} from '../src/v3_2';

const cloneMvpManifest = (): CoreMvpManifestInput =>
    JSON.parse(JSON.stringify(CORE_MVP_MANIFEST));

const cloneRuntimeRule = (index = 0): CoreManifestRuleInput =>
    JSON.parse(JSON.stringify(CORE_MVP_MANIFEST.rules[index]));

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Object.values(value).forEach(assertDeepFrozen);
};

const collectVariableSlots = (
    pattern: CoreCompiledRulePattern,
    result: number[] = []
): readonly number[] => {
    switch (pattern.tag) {
        case 'variable':
            result.push(pattern.slot);
            return result;
        case 'owner-application':
            pattern.arguments.forEach(argument =>
                collectVariableSlots(argument, result)
            );
            return result;
        default: {
            const exhaustive: never = pattern;
            return exhaustive;
        }
    }
};

const expectRuntimeCompilationError = (
    mutate: (rule: any) => void,
    code: CoreRuntimeCompilationErrorCode
): CoreRuntimeCompilationError => {
    const rule = cloneRuntimeRule() as any;
    mutate(rule);
    try {
        compileCoreRuntimeRuleCandidate(
            rule,
            CORE_MVP_RUNTIME_PROGRAM.ownerIds
        );
    } catch (error: unknown) {
        assert.ok(error instanceof CoreRuntimeCompilationError);
        assert.equal(error.code, code);
        return error;
    }
    assert.fail(`Expected CoreRuntimeCompilationError ${code}`);
};

describe('TypeScript v3.2 TSK-2A runtime compilation', () => {
    it('compiles only the reviewed manifest identity and runtime rules', () => {
        assert.equal(
            CORE_MVP_RUNTIME_PROGRAM.status,
            'candidate-awaiting-h04'
        );
        assert.equal(
            CORE_MVP_RUNTIME_PROGRAM.manifestRevision,
            CORE_MVP_MANIFEST.revision
        );
        assert.equal(
            CORE_MVP_RUNTIME_PROGRAM.manifestContentHash,
            CORE_MVP_MANIFEST.contentHash
        );
        assert.deepEqual(
            CORE_MVP_RUNTIME_PROGRAM.ownerIds,
            CORE_MVP_MANIFEST.owners.map(owner => owner.owner)
        );
        assert.deepEqual(
            CORE_MVP_RUNTIME_PROGRAM.rules.map(rule => rule.id),
            [
                'projection.functor-hom.evaluate',
                'projection.transfor-component.evaluate',
                'projection.transfor-hom.evaluate'
            ]
        );
        assert.equal(
            CORE_MVP_RUNTIME_PROGRAM.rules.some(rule =>
                rule.id === 'comparison.constant-section'
            ),
            false
        );
    });

    it('compiles variables to deterministic slots and owners to rigid heads', () => {
        for (const rule of CORE_MVP_RUNTIME_PROGRAM.rules) {
            assert.equal(rule.left.tag, 'owner-application');
            assert.equal(rule.rootOwner, 'functor-object');
            assert.equal(rule.left.tag === 'owner-application'
                ? rule.left.owner
                : undefined, rule.rootOwner);

            const leftSlots = collectVariableSlots(rule.left);
            const rightSlots = collectVariableSlots(rule.right);
            assert.ok(leftSlots.length > rightSlots.length);
            assert.deepEqual(
                [...new Set(leftSlots)].sort((left, right) => left - right),
                rule.variables.map((_, slot) => slot)
            );
            assert.deepEqual(
                rightSlots,
                rule.variables.map((_, slot) => slot)
            );
        }
        assert.deepEqual(
            CORE_MVP_RUNTIME_PROGRAM.ruleIndicesByRoot,
            {
                'functor-object': [0, 1, 2]
            }
        );
    });

    it('records the exact full-to-capped decrease certificates', () => {
        assert.deepEqual(
            CORE_MVP_RUNTIME_PROGRAM.rules.map(rule => ({
                pair: rule.safety.projectionPair,
                evaluator: rule.safety.evaluatorOwner,
                full: rule.safety.eliminatedFullOwner,
                capped: rule.safety.introducedCappedOwner,
                decrease: rule.safety.explicitFullOwnerDecrease,
                nonDuplicating: rule.safety.nonDuplicatingVariables
            })),
            [{
                pair: 'functor-hom',
                evaluator: 'functor-object',
                full: 'functor-hom-full',
                capped: 'functor-hom-capped',
                decrease: 1,
                nonDuplicating: true
            }, {
                pair: 'transfor-component',
                evaluator: 'functor-object',
                full: 'transfor-component-full',
                capped: 'transfor-component-capped',
                decrease: 1,
                nonDuplicating: true
            }, {
                pair: 'transfor-hom',
                evaluator: 'functor-object',
                full: 'transfor-hom-full',
                capped: 'transfor-hom-capped',
                decrease: 1,
                nonDuplicating: true
            }]
        );

        for (const rule of CORE_MVP_RUNTIME_PROGRAM.rules) {
            assert.equal(
                rule.safety.rightVariableOccurrences.every(
                    (count, slot) =>
                        count <= rule.safety.leftVariableOccurrences[slot]
                ),
                true
            );
        }
    });

    it('finds rigid pairwise discriminators without claiming confluence', () => {
        const rules = CORE_MVP_RUNTIME_PROGRAM.rules;
        for (let left = 0; left < rules.length; left++) {
            assert.equal(
                coreRuntimePatternsMayOverlap(
                    rules[left].left,
                    rules[left].left
                ),
                true
            );
            for (let right = left + 1; right < rules.length; right++) {
                assert.equal(
                    coreRuntimePatternsMayOverlap(
                        rules[left].left,
                        rules[right].left
                    ),
                    false
                );
            }
        }
        assert.deepEqual(CORE_MVP_RUNTIME_PROGRAM.safety, {
            pairwiseLeftOverlapFree: true,
            leftLinear: false,
            terminationEvidence:
                'one-explicit-full-owner-decrease-without-variable-duplication',
            confluenceEvidence:
                'pairwise-rigid-left-discrimination-only',
            subjectReductionEvidence:
                'reviewed-lambdapi-provenance-only',
            claimsAuthorized: false,
            reviewGate: 'H-04'
        });
    });

    it('is deeply immutable, deterministic, and backend-neutral', () => {
        assertDeepFrozen(CORE_MVP_RUNTIME_PROGRAM);
        const recompiled = compileCoreMvpRuntime(cloneMvpManifest());
        assert.deepEqual(recompiled, CORE_MVP_RUNTIME_PROGRAM);
        assertDeepFrozen(recompiled);
        assert.doesNotMatch(
            JSON.stringify(CORE_MVP_RUNTIME_PROGRAM),
            /emdash3_2\.lp|fapp0|fapp1_func|tapp0_func|tapp1_func|Pi_cat/
        );
    });

    it('rejects manifest drift before executable compilation', () => {
        const changedStatus = cloneMvpManifest() as any;
        changedStatus.status = 'candidate-runtime';
        assert.throws(
            () => compileCoreMvpRuntime(changedStatus),
            (error: unknown) => {
                assert.ok(error instanceof CoreManifestValidationError);
                assert.equal(error.code, 'INVALID_FROZEN_STATUS');
                return true;
            }
        );

        const changedRule = cloneMvpManifest() as any;
        changedRule.rules[0].authority = 'proof-time-comparison';
        assert.throws(
            () => compileCoreMvpRuntime(changedRule),
            (error: unknown) => {
                assert.ok(error instanceof CoreManifestValidationError);
                assert.equal(error.code, 'FROZEN_RULE_MISMATCH');
                return true;
            }
        );
    });

    it('rejects malformed executable shapes without granting membership', () => {
        assert.match(
            expectRuntimeCompilationError(
                rule => {
                    rule.authority = 'proof-time-comparison';
                },
                'NON_RUNTIME_RULE'
            ).message,
            /not an H-03-reviewed runtime rule/
        );
        assert.match(
            expectRuntimeCompilationError(
                rule => {
                    rule.variables[1] = rule.variables[0];
                },
                'INVALID_COMPILED_VARIABLES'
            ).message,
            /duplicate variable names/
        );
        assert.match(
            expectRuntimeCompilationError(
                rule => {
                    rule.variables[0] = 'not-portable';
                },
                'INVALID_COMPILED_VARIABLES'
            ).message,
            /noncanonical variable list/
        );
        assert.match(
            expectRuntimeCompilationError(
                rule => {
                    rule.left.owner = 'displayed-pullback';
                },
                'UNKNOWN_COMPILED_OWNER'
            ).message,
            /outside the reviewed MVP owners/
        );
        assert.match(
            expectRuntimeCompilationError(
                rule => {
                    rule.left.arguments.pop();
                },
                'INVALID_COMPILED_OWNER_ARITY'
            ).message,
            /expected 4/
        );
        assert.match(
            expectRuntimeCompilationError(
                rule => {
                    rule.left.arguments[0] = {
                        tag: 'unknown-pattern'
                    };
                },
                'MALFORMED_COMPILED_PATTERN'
            ).message,
            /unknown pattern tag/
        );
        assert.match(
            expectRuntimeCompilationError(
                rule => {
                    rule.right.arguments[0] = {
                        tag: 'variable',
                        name: 'f'
                    };
                },
                'DUPLICATING_RUNTIME_VARIABLE'
            ).message,
            /duplicates a matched variable/
        );
        assert.match(
            expectRuntimeCompilationError(
                rule => {
                    rule.right = rule.left;
                },
                'INVALID_PROJECTION_DECREASE'
            ).message,
            /eliminate exactly one/
        );
    });

    it('keeps the H-03 manifest frozen while H-04 claims remain pending', () => {
        assert.ok(
            CORE_MVP_MANIFEST.trustBoundary
                .frozenButDeferredMechanisms
                .includes('runtime-pattern-compilation')
        );
        assert.equal(
            CORE_MVP_RUNTIME_PROGRAM.safety.claimsAuthorized,
            false
        );
        assert.equal(CORE_MVP_RUNTIME_PROGRAM.safety.reviewGate, 'H-04');
    });
});
