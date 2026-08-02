/**
 * HOM-CATD-ACTION-TRANSFER-1AF existing-authority transfer evidence.
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
    CORE_CATEGORICAL_HOM_CATD_ACTION_CORE_NAMES,
    CORE_CATEGORICAL_HOM_CATD_ACTION_RUNTIME_MODULE,
    CORE_CATEGORICAL_HOM_CATD_ACTION_RUNTIME_POLICY,
    CORE_CATEGORICAL_HOM_CATD_ACTION_SOURCE_SHA256,
    CORE_CATEGORICAL_HOM_CATD_ACTION_SYMBOLS,
    CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY,
    CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_LINKAGE,
    CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_MODULE,
    CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_POLICY,
    CoreCategoricalHomCatdActionSymbolId,
    CoreCategoricalProgram,
    compileCoreCategoricalHomCatdActionTransfer,
    coreCategoricalDependentCompositionCoreName,
    coreCategoricalDisplayedNdHigherFoundationCoreName,
    coreCategoricalHomCatdActionCoreName,
    kernelApplication,
    kernelCall,
    kernelFree,
    provenance
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

interface CallArgument {
    readonly plicity: Plicity;
    readonly value: KernelExpression;
}

describe('HOM-CATD-ACTION-TRANSFER-1AF generic transfer', () => {
    it('pins the approved three-signature and nine-rule boundary', () => {
        assert.deepEqual(
            CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                .declarationNames,
            [
                'Hom_catd_fapp1_func',
                'Hom_catd_fapp1_fapp0',
                'Hom_catd_fapp1_fapp0_point'
            ]
        );
        assert.deepEqual(
            CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                .runtimeRuleIds,
            [
                'categorical.hom-catd-action.capped-identity',
                'categorical.hom-catd-action.capped-composition',
                'categorical.hom-catd-action.point-composition',
                'categorical.hom-catd-action.transfor-full',
                'categorical.hom-catd-action.transfor-capped',
                'categorical.hom-catd-action.generic-full',
                'categorical.hom-catd-action.generic-capped',
                'categorical.hom-catd-action.full-to-capped',
                'categorical.hom-catd-action.capped-to-point'
            ]
        );
        assert.deepEqual(
            [
                CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                    .declarationCount,
                CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                    .runtimeRuleCount,
                CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                    .proofRuleCount,
                CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                    .omittedConstantCatRuntimeRuleCount,
                CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                    .importedProfunctorDeclarationCount,
                CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                    .intrinsicCoreOwnerDelta,
                CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                    .ownerSpecificCheckerOrEvaluatorDelta,
                CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                    .contextualBinderDelta,
                CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                    .externalCoherenceEvidenceDelta,
                CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                    .textOrBrowserDelta
            ],
            [3, 9, 0, 2, 0, 0, 0, 0, 0, 0]
        );
        assert.equal(
            CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                .decision,
            'D-DTTLF-USABILITY-064'
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
        );
    });

    it('uses immutable generic policies and one Core-name contract', () => {
        for (const id of Object.keys(
            CORE_CATEGORICAL_HOM_CATD_ACTION_CORE_NAMES
        ) as CoreCategoricalHomCatdActionSymbolId[]) {
            const symbol =
                CORE_CATEGORICAL_HOM_CATD_ACTION_SYMBOLS[id];
            const link =
                CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_LINKAGE
                    .entries
                    .find(candidate =>
                        candidate.symbol.moduleId === symbol.moduleId &&
                        candidate.symbol.name === symbol.name
                    );
            assert.equal(
                link?.kind === 'free-declaration'
                    ? link.coreName
                    : undefined,
                CORE_CATEGORICAL_HOM_CATD_ACTION_CORE_NAMES[id]
            );
            assert.equal(
                coreCategoricalHomCatdActionCoreName(id),
                CORE_CATEGORICAL_HOM_CATD_ACTION_CORE_NAMES[id]
            );
        }
        assert.deepEqual(
            CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_POLICY.entries
                .map(entry => entry.policy),
            ['opaque-signature', 'opaque-signature', 'opaque-signature']
        );
        assert.deepEqual(
            CORE_CATEGORICAL_HOM_CATD_ACTION_RUNTIME_POLICY.entries
                .map(entry => entry.policy),
            Array(9).fill('runtime-rewrite')
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_HOM_CATD_ACTION_CORE_NAMES
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_MODULE
        );
        assertDeepFrozen(
            CORE_CATEGORICAL_HOM_CATD_ACTION_RUNTIME_MODULE
        );
    });

    it('pins the active owner and rule authority', () => {
        const source = readFileSync(activeKernelPath, 'utf8');
        assert.equal(
            'sha256:' + createHash('sha256')
                .update(source)
                .digest('hex'),
            CORE_CATEGORICAL_HOM_CATD_ACTION_SOURCE_SHA256
        );
        const ownerPositions = [
            'injective symbol Hom_catd_fapp1_func',
            'injective symbol Hom_catd_fapp1_fapp0',
            'injective symbol Hom_catd_fapp1_fapp0_point'
        ].map(marker => source.indexOf(marker));
        assert.equal(ownerPositions.every(position => position >= 0), true);
        assert.equal(ownerPositions[0] < ownerPositions[1], true);
        assert.equal(ownerPositions[1] < ownerPositions[2], true);
        assert.match(
            source,
            /rule @Hom_catd_fapp1_fapp0[\s\S]*?\(@id \$K \$x\)/u
        );
        assert.match(
            source,
            /rule @fapp1_fapp0[\s\S]*?\(@Transf_catd/u
        );
        assert.match(
            source,
            /rule fapp0[\s\S]*?@Hom_catd_fapp1_func/u
        );
        assert.equal(
            CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_MODULE
                .declarations.length,
            3
        );
        assert.equal(
            CORE_CATEGORICAL_HOM_CATD_ACTION_RUNTIME_MODULE
                .runtimeRules.length,
            9
        );
    });

    it('subject-checks all declarations and runtime rules generically',
    () => {
        const compilation =
            compileCoreCategoricalHomCatdActionTransfer();
        assert.deepEqual(
            compilation.compiled.declarations.map(declaration => ({
                name: declaration.symbol.name,
                status: declaration.status,
                hasBody: declaration.body !== undefined
            })),
            [
                {
                    name: 'Hom_catd_fapp1_func',
                    status: 'installed-opaque',
                    hasBody: false
                },
                {
                    name: 'Hom_catd_fapp1_fapp0',
                    status: 'installed-opaque',
                    hasBody: false
                },
                {
                    name: 'Hom_catd_fapp1_fapp0_point',
                    status: 'installed-opaque',
                    hasBody: false
                }
            ]
        );
        assert.deepEqual(
            compilation.runtime.rules.map(rule =>
                rule.subjectValidation.kind
            ),
            Array(9).fill('typescript-checked')
        );
        assert.deepEqual(
            compilation.composedRuntime.ruleIds.slice(-9),
            CORE_CATEGORICAL_HOM_CATD_ACTION_TRANSFER_BOUNDARY
                .runtimeRuleIds
        );
        assert.doesNotThrow(
            () => compilation.compiled.createChecker()
                .validateEnvironment()
        );
    });

    it('executes identity and both composition laws without collapse',
    () => {
        const compilation =
            compileCoreCategoricalHomCatdActionTransfer();
        const origin = provenance(
            'derived',
            'displayed Hom action law witness'
        );
        const free = (name: string): KernelExpression =>
            kernelFree(name, origin);
        const call = (
            name: string,
            arguments_: readonly CallArgument[]
        ): KernelExpression => kernelCall(
            kernelFree(name, origin),
            arguments_,
            origin
        );
        const implicit = (value: KernelExpression): CallArgument => ({
            plicity: 'implicit',
            value
        });
        const explicit = (value: KernelExpression): CallArgument => ({
            plicity: 'explicit',
            value
        });
        const K = free('hom_action_law_K');
        const E = free('hom_action_law_E');
        const X = free('hom_action_law_X');
        const Y = free('hom_action_law_Y');
        const x = free('hom_action_law_x');
        const y = free('hom_action_law_y');
        const z = free('hom_action_law_z');
        const p = free('hom_action_law_p');
        const q = free('hom_action_law_q');
        const h = free('hom_action_law_h');
        const capped = (
            source: KernelExpression,
            target: KernelExpression,
            arrow: KernelExpression
        ): KernelExpression => call(
            coreCategoricalHomCatdActionCoreName('capped'),
            [
                implicit(K),
                implicit(E),
                implicit(X),
                implicit(Y),
                implicit(source),
                implicit(target),
                explicit(arrow)
            ]
        );
        const point = (
            source: KernelExpression,
            target: KernelExpression,
            arrow: KernelExpression,
            fibreArrow: KernelExpression
        ): KernelExpression => call(
            coreCategoricalHomCatdActionCoreName('point'),
            [
                implicit(K),
                implicit(E),
                implicit(X),
                implicit(Y),
                implicit(source),
                implicit(target),
                explicit(arrow),
                explicit(fibreArrow)
            ]
        );
        const identity = call(
            coreCategoricalDisplayedNdHigherFoundationCoreName(
                'identityArrow'
            ),
            [explicit(K), explicit(x)]
        );
        const identityResult =
            compilation.composedRuntime.rewriteHead(
                capped(x, x, identity)
            );
        assert.equal(identityResult.status, 'rewritten');
        if (identityResult.status !== 'rewritten') {
            assert.fail('Displayed Hom capped identity did not reduce');
        }
        assert.equal(
            identityResult.ruleId,
            'categorical.hom-catd-action.capped-identity'
        );

        const composition = call(
            coreCategoricalDependentCompositionCoreName(
                'generic-category-composition'
            ),
            [
                implicit(kernelApplication(
                    'category-of-categories',
                    [],
                    origin
                )),
                implicit(free('hom_action_law_Hx')),
                implicit(free('hom_action_law_Hy')),
                implicit(free('hom_action_law_Hz')),
                explicit(capped(y, z, q)),
                explicit(capped(x, y, p))
            ]
        );
        const compositionResult =
            compilation.composedRuntime.rewriteHead(composition);
        assert.equal(compositionResult.status, 'rewritten');
        if (compositionResult.status !== 'rewritten') {
            assert.fail('Displayed Hom capped composition did not reduce');
        }
        assert.equal(
            compositionResult.ruleId,
            'categorical.hom-catd-action.capped-composition'
        );

        const pointCompositionResult =
            compilation.composedRuntime.rewriteHead(
                point(y, z, q, point(x, y, p, h))
            );
        assert.equal(pointCompositionResult.status, 'rewritten');
        if (pointCompositionResult.status !== 'rewritten') {
            assert.fail('Displayed Hom point composition did not reduce');
        }
        assert.equal(
            pointCompositionResult.ruleId,
            'categorical.hom-catd-action.point-composition'
        );
        assert.notEqual(
            compilation.composedRuntime.rewriteHead(
                capped(x, y, p)
            ).status,
            'rewritten'
        );
    });

    it('computes the fixed Transf_catd contextual action directly', () => {
        const compilation =
            compileCoreCategoricalHomCatdActionTransfer();
        const emdash = new CoreCategoricalProgram({
            sourceFile:
                'tests/fixtures/categorical-hom-catd-action-transfer.ts',
            profile: 'fibred-displayed-mixed-nest-1'
        });
        const K = emdash.category('hom_action_consumer_K');
        const opK = emdash.oppositeCategory(K);
        const A = emdash.displayedFamily(
            'hom_action_consumer_A',
            opK
        );
        const B = emdash.displayedFamily(
            'hom_action_consumer_B',
            K
        );
        const functors = emdash.mixedDisplayedFunctorFamily(A, B);
        const negativeFunctors =
            emdash.oppositeDisplayedFamily(functors);
        const alpha = emdash.section(
            'hom_action_consumer_alpha',
            negativeFunctors
        );
        const beta = emdash.section(
            'hom_action_consumer_beta',
            functors
        );
        const target = emdash.mixedDisplayedTransforFamily(
            A,
            B,
            alpha,
            beta
        );
        const E = emdash.displayedFamily(
            'hom_action_consumer_E',
            K
        );
        const P = emdash.displayedFunctor(
            'hom_action_consumer_P',
            E,
            target
        );
        const Q = emdash.displayedFunctor(
            'hom_action_consumer_Q',
            E,
            target
        );
        const eta = emdash.displayedTransfor(
            'hom_action_consumer_eta',
            P,
            Q
        );
        const contextual = emdash.displayedTransforContextLambda(
            'a',
            P,
            Q,
            a => emdash.apply(eta, a, {
                expectedShape: 'point-component'
            })
        );
        assert.equal(emdash.compare(contextual, eta).status, 'equal');
        assert.equal(
            emdash.compile(contextual).surfaceType.tag,
            'displayed-transfor'
        );

        const x = emdash.object('hom_action_consumer_x', K);
        const y = emdash.object('hom_action_consumer_y', K);
        const p = emdash.hom('hom_action_consumer_p', K, x, y);
        const h = emdash.object(
            'hom_action_consumer_h',
            emdash.fibre(target, x)
        );
        const origin = provenance(
            'derived',
            'fixed Transf_catd contextual action transfer consumer'
        );
        const targetCore = (
            target as unknown as {
                readonly expression: KernelExpression;
            }
        ).expression;
        const cappedResult = compilation.composedRuntime.rewriteHead(
            kernelApplication(
                'functor-hom-capped',
                [
                    { value: kernelFree('hom_action_consumer_K', origin) },
                    {
                        value: kernelApplication(
                            'category-of-categories',
                            [],
                            origin
                        )
                    },
                    { value: targetCore },
                    { value: emdash.compile(x).explicitTerm },
                    { value: emdash.compile(y).explicitTerm },
                    { value: emdash.compile(p).explicitTerm }
                ],
                origin
            )
        );
        assert.equal(cappedResult.status, 'rewritten');
        if (cappedResult.status !== 'rewritten') {
            assert.fail('Fixed Transf_catd action did not reduce');
        }
        assert.equal(
            cappedResult.ruleId,
            'categorical.hom-catd-action.transfor-capped'
        );
        assert.equal(cappedResult.after.tag, 'call');
        if (
            cappedResult.after.tag !== 'call' ||
            cappedResult.after.callee.tag !== 'reference'
        ) {
            assert.fail('Fixed Transf_catd action lost its capped owner');
        }
        assert.equal(
            cappedResult.after.callee.name,
            coreCategoricalHomCatdActionCoreName('capped')
        );

        const pointResult = compilation.composedRuntime.rewriteHead(
            kernelApplication(
                'functor-object',
                [
                    {
                        value: kernelFree(
                            'hom_action_consumer_source_hom',
                            origin
                        )
                    },
                    {
                        value: kernelFree(
                            'hom_action_consumer_target_hom',
                            origin
                        )
                    },
                    { value: cappedResult.after },
                    { value: emdash.compile(h).explicitTerm }
                ],
                origin
            )
        );
        assert.equal(pointResult.status, 'rewritten');
        if (pointResult.status !== 'rewritten') {
            assert.fail('Fixed Transf_catd point did not reduce');
        }
        assert.equal(
            pointResult.ruleId,
            'categorical.hom-catd-action.capped-to-point'
        );
        assert.notEqual(
            compilation.composedRuntime.rewriteHead(
                cappedResult.after
            ).status,
            'rewritten'
        );
    });
});
