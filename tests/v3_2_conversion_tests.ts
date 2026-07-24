/**
 * Focused TSK-2C tests for conversion, authority, and H-04 evidence.
 */

import assert from 'node:assert';
import { describe, it } from 'node:test';
import {
    CORE_MVP_MANIFEST,
    CORE_MVP_MANIFEST_PROPOSAL,
    CORE_MVP_RUNTIME_PROGRAM,
    CORE_RUNTIME_H04_RECOMMENDATION,
    CORE_CHECKER_RUNTIME_COMPARISON_STEP_LIMIT,
    CoreChecker,
    CoreCheckerError,
    CoreDeclarationEnvironment,
    CoreElaborationSession,
    CoreRuntimeEvaluationError,
    CoreRuntimeH04RecommendationInput,
    CoreRuntimeMetatheoryError,
    CoreRulePatternInput,
    KernelExpression,
    binderMode,
    coreRuntimeDefinitionalCompare,
    coreRuntimeFullProjectionCount,
    coreRuntimeRewriteHead,
    kernelApplication,
    kernelBinder,
    kernelBound,
    kernelCall,
    kernelExpressionEquals,
    kernelFree,
    kernelLambda,
    kernelPi,
    kernelUniverse,
    provenance,
    sourceSpan,
    validateCoreRuntimeH04Recommendation
} from '../src/v3_2';

const fixture = 'tests/fixtures/v3_2_conversion.core.ts';
const at = (line: number) =>
    sourceSpan(fixture, line, 1, line, 60);
const because = (line: number, detail: string) =>
    provenance('surface', detail, at(line));

const cloneRecommendation = (): CoreRuntimeH04RecommendationInput =>
    JSON.parse(JSON.stringify(CORE_RUNTIME_H04_RECOMMENDATION));

const instantiateCompiledPattern = (
    pattern: typeof CORE_MVP_RUNTIME_PROGRAM.rules[number]['left'],
    bindings: readonly KernelExpression[],
    line: number
): KernelExpression => {
    switch (pattern.tag) {
        case 'variable':
            return bindings[pattern.slot];
        case 'owner-application':
            return kernelApplication(
                pattern.owner,
                pattern.arguments.map(argument => ({
                    value: instantiateCompiledPattern(
                        argument,
                        bindings,
                        line
                    )
                })),
                because(line, `compiled pattern owner ${pattern.owner}`)
            );
        default: {
            const exhaustive: never = pattern;
            return exhaustive;
        }
    }
};

interface RuntimePair {
    readonly left: KernelExpression;
    readonly right: KernelExpression;
    readonly bindings: readonly KernelExpression[];
}

const runtimePair = (
    ruleIndex: number,
    line: number,
    overrides: Readonly<Record<string, KernelExpression>> = {}
): RuntimePair => {
    const rule = CORE_MVP_RUNTIME_PROGRAM.rules[ruleIndex];
    const bindings = rule.variables.map(variable =>
        overrides[variable] ?? kernelFree(
            `conversion_${ruleIndex}_${variable}`,
            because(line, `runtime binding ${variable}`)
        )
    );
    return {
        left: instantiateCompiledPattern(rule.left, bindings, line),
        right: instantiateCompiledPattern(rule.right, bindings, line),
        bindings
    };
};

const instantiateManifestPattern = (
    pattern: CoreRulePatternInput,
    bindings: Readonly<Record<string, KernelExpression>>,
    line: number
): KernelExpression => {
    switch (pattern.tag) {
        case 'variable': {
            const binding = bindings[pattern.name];
            assert.ok(binding, `Missing manifest binding ${pattern.name}`);
            return binding;
        }
        case 'owner-application':
            return kernelApplication(
                pattern.owner as Parameters<typeof kernelApplication>[0],
                pattern.arguments.map(argument => ({
                    value: instantiateManifestPattern(
                        argument,
                        bindings,
                        line
                    )
                })),
                because(line, `manifest pattern owner ${pattern.owner}`)
            );
        default: {
            const exhaustive: never = pattern;
            return exhaustive;
        }
    }
};

const collectFreeNames = (
    expression: KernelExpression,
    names: Set<string>
): void => {
    switch (expression.tag) {
        case 'universe':
        case 'bound':
            return;
        case 'reference':
            names.add(expression.name);
            return;
        case 'meta':
            expression.spine.forEach(item =>
                collectFreeNames(item, names)
            );
            return;
        case 'application':
            expression.arguments.forEach(argument =>
                collectFreeNames(argument.value, names)
            );
            return;
        case 'call':
            collectFreeNames(expression.callee, names);
            expression.arguments.forEach(argument =>
                collectFreeNames(argument.value, names)
            );
            return;
        case 'pi':
        case 'lambda':
            collectFreeNames(expression.binder.type, names);
            collectFreeNames(expression.body, names);
            return;
        default: {
            const exhaustive: never = expression;
            return exhaustive;
        }
    }
};

const comparisonType = (
    endpoint: KernelExpression,
    category: KernelExpression,
    line: number
): KernelExpression => kernelApplication('decode', [{
    value: kernelApplication('hom-classifier', [
        { value: category },
        { value: endpoint },
        { value: endpoint }
    ], because(line, 'conversion comparison classifier'))
}], because(line, 'conversion comparison type'));

const checkerFixture = (
    declaredType: KernelExpression,
    expectedType: KernelExpression,
    line: number
): {
    readonly checker: CoreChecker;
    readonly witness: KernelExpression;
    readonly expectedType: KernelExpression;
} => {
    const names = new Set<string>();
    collectFreeNames(declaredType, names);
    collectFreeNames(expectedType, names);
    let environment = CoreDeclarationEnvironment.empty();
    for (const name of names) {
        environment = environment.extend({
            name,
            type: kernelUniverse(
                because(line, `scope declaration ${name}`)
            ),
            mode: binderMode('explicit', 'functorial'),
            provenance: because(line, `scope declaration ${name}`)
        });
    }
    environment = environment.extend({
        name: 'conversion_witness',
        type: declaredType,
        mode: binderMode('explicit', 'functorial'),
        provenance: because(line, 'conversion witness')
    });
    const witness = environment.lookup('conversion_witness');
    assert.ok(witness);
    return {
        checker: new CoreChecker(
            new CoreElaborationSession(environment)
        ),
        witness: witness.reference,
        expectedType
    };
};

describe('TypeScript v3.2 TSK-2C definitional comparison', () => {
    it('keeps structural equality zero-step and provenance-insensitive', () => {
        const left = kernelFree('conversion_same', because(10, 'left'));
        const right = kernelFree('conversion_same', because(11, 'right'));
        assert.equal(kernelExpressionEquals(left, right), true);
        assert.deepEqual(
            coreRuntimeDefinitionalCompare(left, right, 0),
            {
                status: 'equal',
                steps: 0,
                trace: []
            }
        );
    });

    it('compares all three reviewed runtime conversions symmetrically', () => {
        CORE_MVP_RUNTIME_PROGRAM.rules.forEach((_rule, index) => {
            const pair = runtimePair(index, 20 + index);
            assert.equal(kernelExpressionEquals(pair.left, pair.right), false);

            const forward = coreRuntimeDefinitionalCompare(
                pair.left,
                pair.right,
                1
            );
            assert.equal(forward.status, 'equal');
            assert.equal(forward.steps, 1);
            assert.equal(forward.trace[0].side, 'left');
            assert.deepEqual(forward.trace[0].path, ['$']);

            const reverse = coreRuntimeDefinitionalCompare(
                pair.right,
                pair.left,
                1
            );
            assert.equal(reverse.status, 'equal');
            assert.equal(reverse.steps, 1);
            assert.equal(reverse.trace[0].side, 'right');
        });
    });

    it('shares one deterministic step budget across nested congruence', () => {
        const first = runtimePair(0, 30);
        const second = runtimePair(1, 31);
        const category = kernelFree(
            'conversion_nested_category',
            because(32, 'nested category')
        );
        const left = kernelApplication('hom-classifier', [
            { value: category },
            { value: first.left },
            { value: second.left }
        ], because(32, 'nested comparison left'));
        const right = kernelApplication('hom-classifier', [
            { value: category },
            { value: first.right },
            { value: second.right }
        ], because(33, 'nested comparison right'));

        const exhausted = coreRuntimeDefinitionalCompare(left, right, 1);
        assert.equal(exhausted.status, 'step-limit-exceeded');
        assert.equal(exhausted.steps, 1);
        if (exhausted.status === 'step-limit-exceeded') {
            assert.equal(exhausted.side, 'left');
            assert.deepEqual(exhausted.path, [
                '$',
                'application:hom-classifier:argument:2'
            ]);
            assert.equal(
                exhausted.nextRuleId,
                'projection.transfor-component.evaluate'
            );
        }

        const equal = coreRuntimeDefinitionalCompare(left, right, 2);
        assert.equal(equal.status, 'equal');
        assert.equal(equal.steps, 2);
        assert.deepEqual(
            equal.trace.map(entry => entry.step),
            [0, 1]
        );
    });

    it('closes reviewed conversion under calls and binders', () => {
        const pair = runtimePair(2, 35);
        const callee = kernelFree(
            'conversion_congruence_callee',
            because(35, 'congruence callee')
        );
        const leftCall = kernelCall(callee, [{
            plicity: 'explicit',
            value: pair.left
        }], because(35, 'left congruence call'));
        const rightCall = kernelCall(callee, [{
            plicity: 'explicit',
            value: pair.right
        }], because(36, 'right congruence call'));
        const callComparison = coreRuntimeDefinitionalCompare(
            leftCall,
            rightCall,
            1
        );
        assert.equal(callComparison.status, 'equal');
        assert.deepEqual(callComparison.trace[0].path, [
            '$',
            'call:argument:0'
        ]);

        const mode = binderMode('explicit', 'natural');
        const leftPi = kernelPi(
            kernelBinder(
                'leftHint',
                kernelUniverse(because(37, 'left binder type')),
                mode,
                because(37, 'left binder')
            ),
            pair.left,
            because(37, 'left Pi')
        );
        const rightPi = kernelPi(
            kernelBinder(
                'rightHint',
                kernelUniverse(because(38, 'right binder type')),
                mode,
                because(38, 'right binder')
            ),
            pair.right,
            because(38, 'right Pi')
        );
        const piComparison = coreRuntimeDefinitionalCompare(
            leftPi,
            rightPi,
            1
        );
        assert.equal(piComparison.status, 'equal');
        assert.deepEqual(piComparison.trace[0].path, [
            '$',
            'pi:body'
        ]);
    });

    it('reports deterministic rigid mismatches and invalid limits', () => {
        const left = kernelFree('conversion_left', because(40, 'left'));
        const right = kernelFree('conversion_right', because(41, 'right'));
        const mismatch = coreRuntimeDefinitionalCompare(left, right, 0);
        assert.equal(mismatch.status, 'not-equal');
        assert.equal(mismatch.steps, 0);
        if (mismatch.status === 'not-equal') {
            assert.equal(
                mismatch.mismatch.code,
                'REFERENCE_MISMATCH'
            );
            assert.deepEqual(mismatch.mismatch.path, ['$']);
        }

        assert.throws(
            () => coreRuntimeDefinitionalCompare(left, right, -1),
            (error: unknown) => {
                assert.ok(error instanceof CoreRuntimeEvaluationError);
                assert.equal(error.code, 'INVALID_STEP_LIMIT');
                assert.deepEqual(error.provenance, left.provenance);
                return true;
            }
        );
    });

    it('integrates reviewed conversion into the checker constraint boundary', () => {
        const pair = runtimePair(0, 50);
        const category = kernelFree(
            'conversion_checker_category',
            because(50, 'checker category')
        );
        const leftType = comparisonType(pair.left, category, 51);
        const rightType = comparisonType(pair.right, category, 52);
        assert.equal(kernelExpressionEquals(leftType, rightType), false);

        const fixture = checkerFixture(
            leftType,
            rightType,
            53
        );
        const checked = fixture.checker.check(
            fixture.checker.rootContext,
            fixture.witness,
            fixture.expectedType
        );
        assert.equal(checked.term, fixture.witness);
        assert.equal(kernelExpressionEquals(checked.type, rightType), true);
    });

    it('reports checker conversion-budget exhaustion deterministically', () => {
        const pair = runtimePair(0, 55);
        const category = kernelFree(
            'conversion_limit_category',
            because(55, 'limit category')
        );
        let left = kernelFree(
            'conversion_limit_base',
            because(55, 'limit base')
        ) as KernelExpression;
        let right = left;
        for (
            let index = 0;
            index <= CORE_CHECKER_RUNTIME_COMPARISON_STEP_LIMIT;
            index++
        ) {
            left = kernelApplication('hom-classifier', [
                { value: category },
                { value: pair.left },
                { value: left }
            ], because(55, `limit left layer ${index}`));
            right = kernelApplication('hom-classifier', [
                { value: category },
                { value: pair.right },
                { value: right }
            ], because(56, `limit right layer ${index}`));
        }
        const fixture = checkerFixture(
            comparisonType(left, category, 57),
            comparisonType(right, category, 58),
            59
        );

        assert.throws(
            () => fixture.checker.check(
                fixture.checker.rootContext,
                fixture.witness,
                fixture.expectedType
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreCheckerError);
                assert.equal(error.code, 'CONVERSION_STEP_LIMIT');
                assert.match(error.message, /before rule/);
                return true;
            }
        );
    });

    it('executes no proof-time, non-conversion, or generic beta rule', () => {
        const K = kernelFree('conversion_K', because(60, 'K'));
        const A = kernelFree('conversion_A', because(60, 'A'));
        const bindings = {
            K,
            A,
            KPrime: K,
            APrime: A
        };

        for (const rule of CORE_MVP_MANIFEST_PROPOSAL.rules.slice(3)) {
            const left = instantiateManifestPattern(
                rule.left,
                bindings,
                61
            );
            const right = instantiateManifestPattern(
                rule.right,
                bindings,
                62
            );
            const comparison = coreRuntimeDefinitionalCompare(
                left,
                right,
                4
            );
            assert.equal(comparison.status, 'not-equal');
            assert.equal(comparison.steps, 0);
        }

        const nonConversion = CORE_MVP_MANIFEST_PROPOSAL.rules[4];
        const left = instantiateManifestPattern(
            nonConversion.left,
            bindings,
            63
        );
        const right = instantiateManifestPattern(
            nonConversion.right,
            bindings,
            64
        );
        const leftType = comparisonType(left, K, 65);
        const rightType = comparisonType(right, K, 66);
        const fixture = checkerFixture(
            leftType,
            rightType,
            67
        );
        assert.throws(
            () => fixture.checker.check(
                fixture.checker.rootContext,
                fixture.witness,
                fixture.expectedType
            ),
            (error: unknown) => {
                assert.ok(error instanceof CoreCheckerError);
                assert.equal(error.code, 'TYPE_MISMATCH');
                return true;
            }
        );

        assert.deepEqual(
            CORE_MVP_RUNTIME_PROGRAM.rules.map(rule => rule.id),
            CORE_MVP_MANIFEST.rules.map(rule => rule.id)
        );

        const betaArgument = kernelFree(
            'conversion_beta_argument',
            because(69, 'beta argument')
        );
        const betaLambda = kernelLambda(
            kernelBinder(
                'x',
                kernelUniverse(because(69, 'beta binder type')),
                binderMode('explicit', 'functorial'),
                because(69, 'beta binder')
            ),
            kernelBound(0, because(69, 'beta body')),
            because(69, 'beta lambda')
        );
        const betaCall = kernelCall(betaLambda, [{
            plicity: 'explicit',
            value: betaArgument
        }], because(69, 'unselected beta call'));
        const betaComparison = coreRuntimeDefinitionalCompare(
            betaCall,
            betaArgument,
            4
        );
        assert.equal(betaComparison.status, 'not-equal');
        assert.equal(betaComparison.steps, 0);
    });

    it('strictly decreases the global full-projection measure', () => {
        CORE_MVP_RUNTIME_PROGRAM.rules.forEach((_rule, index) => {
            const pair = runtimePair(index, 70 + index);
            const rewrite = coreRuntimeRewriteHead(pair.left);
            assert.equal(rewrite.status, 'rewritten');
            if (rewrite.status !== 'rewritten') {
                throw new Error('Expected a reviewed rewrite');
            }
            assert.equal(
                coreRuntimeFullProjectionCount(rewrite.before) -
                    coreRuntimeFullProjectionCount(rewrite.after),
                1
            );
        });

        const captured = runtimePair(1, 75).left;
        const nested = runtimePair(0, 76, { f: captured });
        const rewrite = coreRuntimeRewriteHead(nested.left);
        assert.equal(rewrite.status, 'rewritten');
        if (rewrite.status !== 'rewritten') {
            throw new Error('Expected the nested reviewed rewrite');
        }
        assert.equal(coreRuntimeFullProjectionCount(rewrite.before), 2);
        assert.equal(coreRuntimeFullProjectionCount(rewrite.after), 1);

        const repeated = runtimePair(0, 77, { F: captured });
        const repeatedRewrite = coreRuntimeRewriteHead(repeated.left);
        assert.equal(repeatedRewrite.status, 'rewritten');
        if (repeatedRewrite.status !== 'rewritten') {
            throw new Error('Expected the repeated-subterm rewrite');
        }
        assert.equal(
            coreRuntimeFullProjectionCount(repeatedRewrite.before),
            4
        );
        assert.equal(
            coreRuntimeFullProjectionCount(repeatedRewrite.after),
            1
        );
    });

    it('publishes an immutable, drift-checked H-04 recommendation only', () => {
        assert.equal(
            CORE_RUNTIME_H04_RECOMMENDATION.status,
            'proposed-awaiting-h04'
        );
        assert.equal(
            CORE_RUNTIME_H04_RECOMMENDATION.claims.termination.recommendation,
            'authorize-exact-fragment'
        );
        assert.equal(
            CORE_RUNTIME_H04_RECOMMENDATION.claims.confluence.recommendation,
            'withhold-general-claim'
        );
        assert.equal(
            CORE_RUNTIME_H04_RECOMMENDATION
                .claims.subjectReduction.recommendation,
            'withhold-typescript-theorem'
        );
        assert.equal(
            CORE_RUNTIME_H04_RECOMMENDATION.claimsAuthorized,
            false
        );
        assert.deepEqual(
            CORE_RUNTIME_H04_RECOMMENDATION.nonExecutableEvidenceIds,
            [
                'comparison.constant-section',
                'nonconversion.constant-section.runtime'
            ]
        );
        assert.equal(
            Object.isFrozen(CORE_RUNTIME_H04_RECOMMENDATION),
            true
        );
        assert.equal(
            Object.isFrozen(CORE_RUNTIME_H04_RECOMMENDATION.claims),
            true
        );

        validateCoreRuntimeH04Recommendation(cloneRecommendation());
        const drift = cloneRecommendation() as any;
        drift.claims.confluence.recommendation = 'authorize';
        assert.throws(
            () => validateCoreRuntimeH04Recommendation(drift),
            (error: unknown) => {
                assert.ok(error instanceof CoreRuntimeMetatheoryError);
                assert.equal(error.code, 'H04_RECOMMENDATION_MISMATCH');
                return true;
            }
        );
    });
});
