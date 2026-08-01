/**
 * DIRECT-MIXED-CONSTANT-MIDDLE-COMPOSITION-1M generic transfer coverage.
 */

import assert from 'node:assert/strict';
import {
    createHash
} from 'node:crypto';
import {
    readFileSync
} from 'node:fs';
import {
    resolve
} from 'node:path';
import {
    describe,
    it
} from 'node:test';
import {
    CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_BOUNDARY,
    CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_CORE_NAMES,
    CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_RUNTIME_MODULE,
    CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_RUNTIME_POLICY,
    CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_MODULE,
    CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_POLICY,
    CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256,
    compileCoreCategoricalDirectMixedConstantMiddleTransfer,
    kernelApplication,
    kernelCall,
    kernelFree,
    provenance,
    serializeCoreExpression
} from '../src/v3_2';
import type {
    KernelExpression,
    Plicity
} from '../src/v3_2';

const activeKernelPath = resolve(
    __dirname,
    '..',
    'emdash2',
    'emdash3_2.lp'
);

const assertDeepFrozen = (value: unknown): void => {
    if (value === null || typeof value !== 'object') return;
    assert.equal(Object.isFrozen(value), true);
    Reflect.ownKeys(value).forEach(key =>
        assertDeepFrozen(
            (value as Record<PropertyKey, unknown>)[key]
        )
    );
};

describe('DIRECT-MIXED-CONSTANT-MIDDLE-1M transfer', () => {
    it('pins the exact three-declaration/four-rule generic boundary', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_MODULE
                .declarations.map(entry => entry.symbol.name),
            [
                'comp_prod_func',
                'Functor_comp_pair_func',
                'Functor_comp_pair_funcd'
            ]
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_MODULE
                .declarations.map(entry => entry.body.kind),
            ['absent', 'explicit-term', 'absent']
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_POLICY
                .entries.map(entry => entry.policy),
            [
                'opaque-signature',
                'checked-transparent-definition',
                'opaque-signature'
            ]
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_RUNTIME_MODULE
                .runtimeRules.map(rule => rule.id),
            [
                'categorical.direct-mixed-constant-middle.ordinary-point',
                'categorical.direct-mixed-constant-middle.point',
                'categorical.direct-mixed-constant-middle.full-action',
                'categorical.direct-mixed-constant-middle.capped-action'
            ]
        );
        assert.deepEqual(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_RUNTIME_POLICY
                .entries.map(entry => entry.policy),
            Array.from({ length: 4 }, () => 'runtime-rewrite')
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_BOUNDARY.decision,
            'D-DTTLF-USABILITY-052'
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_BOUNDARY
                .directNestedIntroductionRemainsFundamental,
            true
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_BOUNDARY
                .contextualCurryDependency,
            false
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_BOUNDARY
                .totalContextSectionDependency,
            false
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_BOUNDARY
                .ordinaryPointTransferScope,
            'Cat_cat-specialization'
        );
        assert.equal(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_BOUNDARY
                .ordinaryPointRightPresentation,
            'checked-transparent-comp_cat_fapp0'
        );
        assert.doesNotMatch(
            JSON.stringify({
                declarations:
                    CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_TRANSFER_MODULE,
                runtime:
                    CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_RUNTIME_MODULE
            }),
            /mixed_curry|mix_uncurried_family|coerc|cast/u
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_BOUNDARY
        );
    });

    it('checks every declaration and runtime subject generically', () => {
        const compilation =
            compileCoreCategoricalDirectMixedConstantMiddleTransfer();

        assert.equal(compilation.compiled.declarations.length, 3);
        assert.equal(compilation.runtimeFragment.localProgram.rules.length, 4);
        assert.deepEqual(
            compilation.runtimeFragment.localProgram.rules.map(rule =>
                rule.subjectValidation.kind
            ),
            Array.from({ length: 4 }, () => 'typescript-checked')
        );
        assert.deepEqual(
            compilation.composedRuntime.ruleIds.slice(-4),
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_BOUNDARY
                .runtimeRuleIds
        );
        assertDeepFrozen(compilation.compiled.declarations);
        assertDeepFrozen(compilation.runtimeFragment.localProgram.rules);
    });

    it('computes ordinary object and inner-arrow action after point beta',
    () => {
        const compilation =
            compileCoreCategoricalDirectMixedConstantMiddleTransfer();
        const runtime = compilation.composedRuntime;
        const p = provenance('derived', 'constant-middle computation');
        const free = (name: string): KernelExpression => kernelFree(name, p);
        const call = (
            name: string,
            arguments_: readonly {
                readonly plicity: Plicity;
                readonly value: KernelExpression;
            }[]
        ): KernelExpression => kernelCall(
            kernelFree(name, p),
            arguments_,
            p
        );
        const A = kernelApplication('category-of-categories', [], p);
        const W = free('constant_middle_W');
        const X = free('constant_middle_X');
        const Z = free('constant_middle_Z');
        const pg = free('constant_middle_pair');
        const a = free('constant_middle_a');
        const aPrime = free('constant_middle_a_prime');
        const alpha = free('constant_middle_alpha');
        const compositionPair = call(
            CORE_CATEGORICAL_DIRECT_MIXED_CONSTANT_MIDDLE_CORE_NAMES
                .ordinaryCompositionPair,
            [
                { plicity: 'implicit', value: A },
                { plicity: 'implicit', value: W },
                { plicity: 'implicit', value: X },
                { plicity: 'implicit', value: Z }
            ]
        );
        const point = runtime.rewriteHead(kernelApplication(
            'functor-object',
            [
                { value: free('constant_middle_product_hom') },
                { value: free('constant_middle_target_hom') },
                { value: compositionPair },
                { value: pg }
            ],
            p
        ));

        assert.equal(point.status, 'rewritten');
        if (point.status !== 'rewritten') {
            assert.fail('Ordinary composition-pair point beta did not fire');
        }
        assert.equal(
            point.ruleId,
            'categorical.direct-mixed-constant-middle.ordinary-point'
        );
        assert.match(serializeCoreExpression(point.after), /comp_cat_fapp0/u);

        const objectAction = runtime.rewriteHead(kernelApplication(
            'functor-object',
            [
                { value: W },
                { value: Z },
                { value: point.after },
                { value: a }
            ],
            p
        ));
        const arrowAction = runtime.rewriteHead(kernelApplication(
            'functor-hom-capped',
            [
                { value: W },
                { value: Z },
                { value: point.after },
                { value: a },
                { value: aPrime },
                { value: alpha }
            ],
            p
        ));

        assert.equal(objectAction.status, 'rewritten');
        assert.equal(arrowAction.status, 'rewritten');
        if (
            objectAction.status === 'rewritten' &&
            arrowAction.status === 'rewritten'
        ) {
            assert.match(
                serializeCoreExpression(objectAction.after),
                /functor-object/u
            );
            assert.match(
                serializeCoreExpression(arrowAction.after),
                /functor-hom-capped/u
            );
        }
    });

    it('pins the current active kernel bytes and owner package', () => {
        const source = readFileSync(activeKernelPath, 'utf8');
        assert.equal(
            'sha256:' + createHash('sha256')
                .update(source)
                .digest('hex'),
            CORE_CATEGORICAL_MIXED_MODE_SOURCE_SHA256
        );
        assert.match(
            source,
            /injective symbol Functor_comp_pair_funcd/u
        );
        assert.match(
            source,
            /rule @tapp1_fapp0[\s\S]*@Functor_comp_pair_funcd/u
        );
    });
});
